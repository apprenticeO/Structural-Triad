#!/usr/bin/env python3
"""
ESSE Mixed-State Quench Stress Test
- Systems: N in {4,6,8}
- Temperatures: T in {0.5, 1.0, 2.0}
- Quench strengths: hx in {0.5, 1.0}
- Partitions: A sizes in {1, 2}
For each config:
  • Prepare thermal ρ0 of H0 = -J Σ σzσz + hz Σ σz
  • Evolve under H1 = H0 + hx Σ σx (noncommuting)
  • Compute Elephant triad Ψ_A(t) = sqrt(F(ρ_A, H_A,small)) · S_A · I(A:Ḃ)
  • Report final ⟨Ψ_A⟩, v0(A), δ_A ladder (dual), τ_A^4 proxy
Saves a CSV summary and simple aggregate plots.
"""
from __future__ import annotations
import os, csv
from dataclasses import dataclass
from typing import List, Tuple
import numpy as np
from qutip import *  # type: ignore
import matplotlib.pyplot as plt

# Helpers for A-only local generators (for SLD-QFI on ρ_A)
def local_op_A(op: Qobj, i: int, A: int) -> Qobj:
    return tensor([op if j == i else qeye(2) for j in range(A)])

def build_HA_on_A(A_size: int, J: float, hz: float, hx: float) -> Qobj:
    sz, sx = sigmaz(), sigmax()
    H = 0
    for i in range(A_size):
        H += hz * local_op_A(sz, i, A_size)
        H += hx * local_op_A(sx, i, A_size)
    for i in range(A_size - 1):
        H += -J * local_op_A(sz, i, A_size) * local_op_A(sz, i + 1, A_size)
    return H

# Defaults (can be overridden by env)
JS = float(os.getenv('ESSEJ', '1.0'))
HZ = float(os.getenv('ESSEHZ', '0.5'))
HBAR = float(os.getenv('ESSEHBAR', '1.0'))
T_MAX = float(os.getenv('ESSETMAX', '10.0'))
N_POINTS = int(os.getenv('ESSEPOINTS', '400'))

N_LIST = [int(x) for x in os.getenv('ESSENLIST', '4,6').split(',')]
T_LIST = [float(x) for x in os.getenv('ESSETLIST', '0.5,1.0,2.0').split(',')]
HX_LIST = [float(x) for x in os.getenv('ESSEHXLIST', '0.5,1.0').split(',')]
A_LIST = [int(x) for x in os.getenv('ESSEALIST', '1,2').split(',')]

EPSILONS = (1e-8, 1e-6, 1e-4)


def local_op(op: Qobj, i: int, N: int) -> Qobj:
    return tensor([op if j == i else qeye(2) for j in range(N)])


def build_H0(N: int, J: float, hz: float) -> Qobj:
    sz = sigmaz()
    H = 0
    for i in range(N - 1):
        H += -J * local_op(sz, i, N) * local_op(sz, i + 1, N)
    for i in range(N):
        H += hz * local_op(sz, i, N)
    return H


def build_H1(N: int, J: float, hz: float, hx: float) -> Qobj:
    H = build_H0(N, J, hz)
    sx = sigmax()
    for i in range(N):
        H += hx * local_op(sx, i, N)
    return H


def build_HA_full(N: int, A_size: int, J: float, hz: float, hx: float) -> Qobj:
    sz, sx = sigmaz(), sigmax()
    Hloc = 0
    # On-site over first A_size sites
    for i in range(A_size):
        Hloc += hz * local_op(sz, i, N)
        Hloc += hx * local_op(sx, i, N)
    # Internal ZZ within A (full weight)
    for i in range(A_size - 1):
        Hloc += -J * local_op(sz, i, N) * local_op(sz, i + 1, N)
    # Boundary ZZ: split 1/2 to the A endpoint
    if A_size < N:
        i = A_size - 1
        Hloc += -0.5 * J * local_op(sz, i, N) * local_op(sz, i + 1, N)
    return Hloc


def qfi_spectral_unitary(rho_A: Qobj, H_loc_A: Qobj) -> float:
    evals, evecs = rho_A.eigenstates()
    lam = np.real(np.array(evals, dtype=float))
    F = 0.0
    d = len(lam)
    for i in range(d):
        for j in range(d):
            denom = lam[i] + lam[j]
            if denom <= 1e-15:
                continue
            Hij_q = (evecs[i].dag() * H_loc_A * evecs[j])
            Hij = complex(Hij_q.full()[0, 0]) if hasattr(Hij_q, 'full') else complex(Hij_q)
            diff = lam[i] - lam[j]
            F += 2.0 * (diff * diff / denom) * (abs(Hij) ** 2)
    return float(np.real(F))


@dataclass
class ResultRow:
    N: int
    A: int
    T: float
    hx: float
    Pi1_avg: float
    v0: float
    delta_1e8: float
    delta_1e6: float
    delta_1e4: float
    tau4: float


def run_case(N: int, A: int, T: float, hx: float) -> ResultRow:
    H0 = build_H0(N, JS, HZ)
    H1 = build_H1(N, JS, HZ, hx)
    rho0 = (-H0 / T).expm(); rho0 = rho0 / rho0.tr()

    tlist = np.linspace(0.0, T_MAX, N_POINTS)
    res = mesolve(H1, rho0, tlist, [], [])
    states = res.states

    H_A_full = build_HA_full(N, A, JS, HZ, hx)
    # Canonical A-only generator for QFI (avoid ptrace artifacts)
    H_A_small = build_HA_on_A(A, JS, HZ, hx)

    Psi_list: List[float] = []
    comm_list: List[float] = []
    dH_list: List[float] = []
    d_list: List[float] = []
    S_list: List[float] = []
    I_list: List[float] = []
    sqrtF_list: List[float] = []
    psi_hat_list: List[float] = []

    for rho in states:
        rho_A = rho.ptrace(list(range(A)))
        rho_B = rho.ptrace(list(range(A, N)))
        S_A = float(entropy_vn(rho_A, base=np.e))
        S_B = float(entropy_vn(rho_B, base=np.e))
        S_AB = float(entropy_vn(rho, base=np.e))
        I_AB = S_A + S_B - S_AB

        F = qfi_spectral_unitary(rho_A, H_A_small)
        sqrtF = float(np.sqrt(max(F, 0.0)))
        Psi_list.append(sqrtF * S_A * I_AB)
        sqrtF_list.append(sqrtF)
        S_list.append(S_A)
        I_list.append(I_AB)

        expH = expect(H_A_full, rho); expH2 = expect(H_A_full * H_A_full, rho)
        var = max(0.0, float(np.real(expH2 - expH**2)))
        dH_list.append(float(np.sqrt(var)))
        comm = H_A_full * rho - rho * H_A_full
        comm_list.append(float(comm.norm('fro')))

        # trace distance to product
        sigma = tensor(rho_A, rho_B)
        diff = rho - sigma
        try:
            d_tr = float(diff.norm('tr'))
        except Exception:
            d_tr = float(diff.norm('fro'))
        d_list.append(d_tr)

        # Intensive triad Ψ̂ per Eq. (12): (ħ√F_Q)/(2||H_A||)·(S_A/log d_A)·(I/(2 log d_min))
        try:
            H_norm = float(H_A_full.norm('spectral'))
        except Exception:
            H_norm = float(np.max(np.abs(np.real(np.asarray(H_A_full.eigenenergies(), dtype=float)))))
        dA = 2**A; dbar = 2**(N - A); dmin = min(dA, dbar)
        psi_hat = (HBAR * sqrtF) / (2.0 * max(H_norm, 1e-12)) * (S_A / max(np.log(dA), 1e-12)) * (I_AB / (2.0 * max(np.log(dmin), 1e-12)))
        psi_hat_list.append(float(psi_hat))

    Pi1_arr = np.array(Psi_list)
    avg_series = np.cumsum(Pi1_arr) / np.arange(1, len(Pi1_arr) + 1)
    Pi1_avg = float(avg_series[-1])

    # v0 and δ ladder
    evals = np.sort(np.real(np.asarray(H_A_full.eigenenergies(), dtype=float)))
    gaps = np.diff(evals); gaps = gaps[gaps > 1e-12]
    v0 = 0.25 * float(np.min(gaps)) if gaps.size > 0 else 0.0

    comm_arr = np.array(comm_list); dH_arr = np.array(dH_list)
    delta = {e: float(np.mean(np.logical_and(comm_arr > e, dH_arr >= v0))) for e in EPSILONS}

    # τ4 proxy
    d_arr = np.array(d_list); d4 = d_arr ** 4
    cums = np.cumsum(d4); avg = cums / (np.arange(len(d4)) + 1)
    W = max(1, len(d4) // 8)
    lim = np.array([np.min(avg[max(0, i - W + 1): i + 1]) for i in range(len(d4))])
    tau4 = float(lim[-1])

    # === Canonical structural thresholds (Elephant Eqs. 308 & 343) ===
    # Energy triad (LHS): time-average of ΔH_A · S_A · I(A:Ā)
    energy_triad_lhs = float(np.mean(dH_arr * np.array(S_list) * np.array(I_list))) if len(S_list) else 0.0
    # Capped RHS: 2 (log d_min)^2 ||H_A||_op ⟨Ψ̂⟩
    try:
        H_norm_final = float(H_A_full.norm('spectral'))
    except Exception:
        H_norm_final = float(np.max(np.abs(np.real(np.asarray(H_A_full.eigenenergies(), dtype=float)))))
    dA = 2**A; dbar = 2**(N - A); dmin = min(dA, dbar)
    psi_hat_mean = float(np.mean(psi_hat_list)) if psi_hat_list else 0.0
    rhs_capped = 2.0 * (np.log(dmin)**2) * H_norm_final * psi_hat_mean
    # Speed-based RHS: (ħ/2) δ ε_F ε_S ε_I with floors from time series (q10)
    if sqrtF_list:
        epsF = float(np.quantile(np.array(sqrtF_list), 0.10))
        epsS = float(np.quantile(np.array(S_list), 0.10))
        epsI = float(np.quantile(np.array(I_list), 0.10))
    else:
        epsF = epsS = epsI = 0.0
    # Active fraction as fraction of times all three legs exceed floors
    mask_all = (np.array(sqrtF_list) >= epsF) & (np.array(S_list) >= epsS) & (np.array(I_list) >= epsI) if sqrtF_list else np.array([False])
    delta_speed = float(np.mean(mask_all)) if mask_all.size else 0.0
    rhs_speed = 0.5 * HBAR * delta_speed * epsF * epsS * epsI
    print(f"Canonical thresholds (N={N}, A={A}, T={T}, hx={hx}): LHS={energy_triad_lhs:.6f}, RHS_capped={rhs_capped:.6f}, RHS_speed={rhs_speed:.6f}, ⟨Ψ̂⟩={psi_hat_mean:.6f}, δ={delta_speed:.3f}")

    return ResultRow(N=N, A=A, T=T, hx=hx, Pi1_avg=Pi1_avg, v0=float(v0),
                     delta_1e8=delta[1e-8], delta_1e6=delta[1e-6], delta_1e4=delta[1e-4],
                     tau4=tau4)


def main():
    # Save outputs directly into the Annex A11 directory
    out_dir = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'Annex results', 'A11'))
    os.makedirs(out_dir, exist_ok=True)
    csv_path = os.path.join(out_dir, 'A11_mixed_quench_summary.csv')

    rows: List[ResultRow] = []
    for N in N_LIST:
        for T in T_LIST:
            for hx in HX_LIST:
                for A in A_LIST:
                    if A > N: continue
                    try:
                        r = run_case(N, A, T, hx)
                        rows.append(r)
                        print(f"Done: N={N}, A={A}, T={T}, hx={hx} | Pi1_avg={r.Pi1_avg:.4f}")
                    except Exception as e:
                        print(f"Skip N={N},A={A},T={T},hx={hx}: {e}")

    # Write CSV
    with open(csv_path, 'w', newline='') as f:
        w = csv.writer(f)
        w.writerow(['N','A','T','hx','Pi1_avg','v0','delta_1e8','delta_1e6','delta_1e4','tau4'])
        for r in rows:
            w.writerow([r.N, r.A, r.T, r.hx, r.Pi1_avg, r.v0, r.delta_1e8, r.delta_1e6, r.delta_1e4, r.tau4])
    print(f"Saved summary CSV: {csv_path}")

    # Quick plots: Pi1_avg vs T per N,hx (A=1 only)
    try:
        for N in N_LIST:
            for hx in HX_LIST:
                xs, ys = [], []
                for r in rows:
                    if r.N == N and r.hx == hx and r.A == 1:
                        xs.append(r.T); ys.append(r.Pi1_avg)
                if xs:
                    order = np.argsort(xs); xs = np.array(xs)[order]; ys = np.array(ys)[order]
                    plt.figure(figsize=(6,4))
                    plt.plot(xs, ys, 'o-', label=f'N={N}, hx={hx}')
                    plt.xlabel('T'); plt.ylabel('Final average Π^(1)')
                    plt.title('Mixed-state quench: Π^(1) vs T (A=1)')
                    plt.grid(True, alpha=0.3); plt.legend(); plt.tight_layout()
                    png = os.path.join(out_dir, f'stress_Pi1_vs_T_N{N}_hx{hx}.png')
                    plt.savefig(png, dpi=150); plt.close()
                    print(f"Saved plot: {png}")
    except Exception:
        pass


if __name__ == '__main__':
    main() 