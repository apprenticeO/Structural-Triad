# esse_research_fixed.py

import numpy as np
import matplotlib.pyplot as plt
from typing import List, Tuple, Dict, Optional
from qutip import (
    Qobj, qeye, tensor, sigmax, sigmay, sigmaz, basis, mesolve, expect, ptrace
)
import math
import os, csv
from datetime import datetime
# from esse_core_simulation import ESSESimulation
import importlib.util, sys
BASE_DIR = os.path.dirname(__file__)
_CORE_PATH = os.path.join(BASE_DIR, '1_esse_core_simulation.py')
spec = importlib.util.spec_from_file_location('esse_core_simulation', _CORE_PATH)
core = importlib.util.module_from_spec(spec)
assert spec is not None and spec.loader is not None, 'Cannot load core simulation module'
spec.loader.exec_module(core)
ESSESimulation = core.ESSESimulation

# ------------------------ Configuration Defaults ------------------------

DEFAULT_N = 8
DEFAULT_SUBSYSTEM = [0, 1]
DEFAULT_T = 10.0
DEFAULT_STEPS = 200
DEFAULT_SEED = 42

# ------------------------ Pauli and State Utilities ------------------------

def pauli(op: str) -> Qobj:
    return {"x": sigmax(), "y": sigmay(), "z": sigmaz(), "i": qeye(2)}[op.lower()]

def haar_random_product_state(n: int, seed: Optional[int] = None) -> Qobj:
    rng = np.random.default_rng(seed)
    def qubit():
        u, v = rng.random(), rng.random()
        theta, phi = np.arccos(1 - 2 * u), 2 * np.pi * v
        return (np.cos(theta/2)*basis(2,0) + np.exp(1j*phi)*np.sin(theta/2)*basis(2,1)).unit()
    return tensor([qubit() for _ in range(n)])

# ------------------------ Hamiltonian Construction ------------------------

def op_at(n: int, op: Qobj, i: int) -> Qobj:
    ops = [qeye(2)]*n
    ops[i] = op
    return tensor(ops)

def build_ising(n: int, J=1.0, hx=1.0, hz=0.5) -> Qobj:
    sx, sz = sigmax(), sigmaz()
    H = 0
    for i in range(n-1):
        H += -J * op_at(n, sz, i) * op_at(n, sz, i+1)
    for i in range(n):
        H += hx * op_at(n, sx, i)
        H += -hz * op_at(n, sz, i)
    return H

def build_HA_full(n: int, A: List[int], J=1.0, hx=1.0, hz=0.5) -> Qobj:
    sx, sz = sigmax(), sigmaz()
    Aset = set(A)
    Hloc = 0
    for i in A:
        Hloc += hx * op_at(n, sx, i)
        Hloc += -hz * op_at(n, sz, i)
    # internal ZZ
    for i in range(n-1):
        if i in Aset and (i+1) in Aset:
            Hloc += -J * op_at(n, sz, i) * op_at(n, sz, i+1)
    # boundary ZZ with 1/2 splitting
    for i in range(n-1):
        if (i in Aset) ^ ((i+1) in Aset):
            Hloc += -0.5 * J * op_at(n, sz, i) * op_at(n, sz, i+1)
    return Hloc

# ------------------------ ESSE Metrics ------------------------

def compute_metrics(n: int, A: List[int], J: float, hx: float, hz: float, T: float, steps: int) -> Dict[str, float]:
    # Use canonical ESSESimulation pipeline to ensure δ_A, τ_A^4, v0, c_lin handling
    sim = ESSESimulation(N=n, hbar=1.0, hx=hx, hz=hz, J=J)
    trials = sim.run(commuting=False, t_max=T, n_points=steps, n_trials=1, partition=[tuple(A)])
    tr = trials[0]
    Pi_avg = float(tr['time_avg'][-1])
    epsilons = (1e-8, 1e-6, 1e-4)
    deltaA = {e: tr['deltaA'][e][0] for e in epsilons}
    tau4 = float(tr['tau4_list'][0])
    v0 = float(tr['v0_list'][0])
    # Canonical structural thresholds and intensive triad
    energy_triad_lhs = float(tr.get('energy_prod_mean', 0.0))
    rhs_capped = float(tr.get('capped_rhs_energy', 0.0))
    rhs_speed = float(tr.get('speed_rhs_energy', 0.0))
    psi_hat_mean = float(tr.get('triad_hat_mean', 0.0))
    floors = tr.get('floors', {})
    delta_speed = float(floors.get('delta', 0.0))
    return dict(Pi_avg=Pi_avg, deltaA=deltaA, tau4=tau4, v0=v0,
                energy_triad_lhs=energy_triad_lhs, rhs_capped=rhs_capped, rhs_speed=rhs_speed,
                psi_hat_mean=psi_hat_mean, delta_speed=delta_speed)

# ------------------------ Research Test: Weak Interaction ------------------------

def run_weak_interaction_test():
    n = DEFAULT_N
    A = DEFAULT_SUBSYSTEM
    J_vals = np.logspace(-3, 0, 8)
    Pi_vals = []
    lhs_vals = []
    cap_vals = []
    spd_vals = []
    psi_vals = []
    delta_vals = []
    for J in J_vals:
        print(f"Simulating for J = {J:.4f} ...")
        stats = compute_metrics(n, A, J=J, hx=1.0, hz=0.5, T=DEFAULT_T, steps=DEFAULT_STEPS)
        Pi_vals.append(stats["Pi_avg"]) 
        lhs_vals.append(stats["energy_triad_lhs"]) 
        cap_vals.append(stats["rhs_capped"]) 
        spd_vals.append(stats["rhs_speed"]) 
        psi_vals.append(stats["psi_hat_mean"]) 
        delta_vals.append(stats["delta_speed"]) 
        print(f"  Thresholds: LHS={lhs_vals[-1]:.6f}, RHS_capped={cap_vals[-1]:.6f}, RHS_speed={spd_vals[-1]:.6f}, ⟨Ψ̂⟩={psi_vals[-1]:.6f}, δ={delta_vals[-1]:.3f}")
    # Outputs
    out_dir = os.path.join(os.path.dirname(__file__), 'plots', 'weak')
    os.makedirs(out_dir, exist_ok=True)
    stamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    # Plot
    plt.figure(figsize=(8,5))
    plt.plot(J_vals, Pi_vals, 'o-', label='⟨Π⟩_T')
    plt.xscale('log')
    plt.xlabel("Interaction strength J"); plt.ylabel("Activity")
    plt.title("Π vs J (Ising model, weak coupling)")
    plt.grid(True); plt.legend(); plt.tight_layout()
    png_path = os.path.join(out_dir, f'weak_J_sweep_{stamp}.png')
    plt.savefig(png_path, dpi=150)
    plt.close()
    # CSV
    csv_path = os.path.join(out_dir, f'weak_J_sweep_{stamp}.csv')
    with open(csv_path, 'w', newline='') as f:
        w = csv.writer(f)
        w.writerow(['J','Pi_avg','LHS_energy_triad','RHS_capped','RHS_speed','psi_hat_mean','delta_speed'])
        for J, Pi_avg, lhs, cap, spd, psi, delt in zip(J_vals, Pi_vals, lhs_vals, cap_vals, spd_vals, psi_vals, delta_vals):
            w.writerow([J, Pi_avg, lhs, cap, spd, psi, delt])
    print(f"Saved plot: {png_path}")
    print(f"Saved CSV:  {csv_path}")

# ------------------------ Main Entry ------------------------

if __name__ == "__main__":
    run_weak_interaction_test()
