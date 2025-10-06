# esse_master_allinone_with_thresholds.py
"""
ALL‑IN‑ONE runner with STRUCTURAL THRESHOLDS:
- Defines ESSESimulation (PDF‑consistent Π, boundary‑aware H_A, robust r, ε‑ladder comm fractions)
- Runs baselines (non‑commuting, commuting) and a partition stress test (1/2/3‑site)
- Prints BOTH raw Π and normalized Π̃=Π/|partition| sliding lim‑inf tables
- IMPLEMENTS structural thresholds from Elephant paper:
  * Hamiltonian-capped threshold (Eq. 308): 2(log d_min)² ||H||_min ⟨Ψ̂⟩
  * Speed-based threshold (Eq. 343): (ℏ/2) δ ε_F ε_S ε_I

Requires: QuTiP installed.
"""
from __future__ import annotations
import numpy as np
import time
import math
from typing import List, Tuple, Dict, Optional

import matplotlib.pyplot as plt
import os, importlib.util
# from esse_core_simulation import ESSESimulation
BASE_DIR = os.path.dirname(__file__)
_CORE_PATH = os.path.join(BASE_DIR, '1_esse_core_simulation.py')
spec = importlib.util.spec_from_file_location('esse_core_simulation', _CORE_PATH)
core = importlib.util.module_from_spec(spec)
assert spec is not None and spec.loader is not None, 'Cannot load core simulation module'
spec.loader.exec_module(core)
ESSESimulation = core.ESSESimulation

# --------------------------- Helpers & Runner ---------------------------

def contiguous_blocks(N: int, k: int) -> List[Tuple[int,...]]:
    return [tuple(range(i, min(i+k, N))) for i in range(0, N, k)]


def summarize_liminf_from_series(t: np.ndarray, series: np.ndarray) -> Dict[str, float]:
    runavg = np.cumsum(series) / (np.arange(len(series)) + 1)
    W = max(1, len(series)//8)
    lim = np.array([np.min(runavg[max(0,i-W+1):i+1]) for i in range(len(series))])
    final = float(lim[-1])
    mn, mx = float(lim.min()), float(lim.max())
    tol = 0.01*abs(final) if final != 0 else 1e-6
    idx = int(np.argmax(np.abs(lim - final) <= tol))
    conv = float(t[idx]) if idx > 0 else 0.0
    return dict(final=final, min=mn, max=mx, conv=conv)


def extract_threshold_data(trials: List[Dict]) -> Dict[str, float]:
    """
    Extract threshold data from ESSESimulation trials.
    Returns both Hamiltonian-capped and speed-based threshold values.
    """
    if not trials:
        return {
            'capped_rhs_mean': 0.0, 'capped_rhs_std': 0.0,
            'speed_rhs_mean': 0.0, 'speed_rhs_std': 0.0,
            'triad_hat_mean': 0.0, 'triad_hat_std': 0.0,
            'epsF_mean': 0.0, 'epsS_mean': 0.0, 'epsI_mean': 0.0, 'delta_mean': 0.0
        }
    
    # Extract threshold values from trials
    capped_rhs_values = [float(tr.get('capped_rhs_energy', 0.0)) for tr in trials]
    speed_rhs_values = [float(tr.get('speed_rhs_energy', 0.0)) for tr in trials]
    triad_hat_values = [float(tr.get('triad_hat_mean', 0.0)) for tr in trials]
    
    # Extract floor values
    epsF_values = [float(tr.get('floors', {}).get('epsF', 0.0)) for tr in trials]
    epsS_values = [float(tr.get('floors', {}).get('epsS', 0.0)) for tr in trials]
    epsI_values = [float(tr.get('floors', {}).get('epsI', 0.0)) for tr in trials]
    delta_values = [float(tr.get('floors', {}).get('delta', 0.0)) for tr in trials]
    
    return {
        'capped_rhs_mean': float(np.mean(capped_rhs_values)),
        'capped_rhs_std': float(np.std(capped_rhs_values)),
        'speed_rhs_mean': float(np.mean(speed_rhs_values)),
        'speed_rhs_std': float(np.std(speed_rhs_values)),
        'triad_hat_mean': float(np.mean(triad_hat_values)),
        'triad_hat_std': float(np.std(triad_hat_values)),
        'epsF_mean': float(np.mean(epsF_values)),
        'epsS_mean': float(np.mean(epsS_values)),
        'epsI_mean': float(np.mean(epsI_values)),
        'delta_mean': float(np.mean(delta_values))
    }


def print_table(title: str, rows: List[Dict[str,float]]):
    print(title)
    print("| Trial | Final Liminf | Min Liminf | Max Liminf | Convergence Time |")
    for i, r in enumerate(rows, 1):
        print(f"| {i} | {r['final']:.3f} | {r['min']:.3f} | {r['max']:.3f} | t = {r['conv']:.2f} |")
    vals = np.array([r['final'] for r in rows])
    mins = np.array([r['min'] for r in rows])
    maxs = np.array([r['max'] for r in rows])
    convs = np.array([r['conv'] for r in rows])
    print(f"**Mean ± Std** | **{vals.mean():.3f} ± {vals.std(ddof=0):.3f}** | {mins.mean():.3f} | {maxs.mean():.3f} | t ≈ {convs.mean():.2f}\n")


def print_threshold_summary(title: str, threshold_data: Dict[str, float]):
    """Print structural threshold summary."""
    print(f"\n{title}")
    print("=" * 60)
    print("STRUCTURAL THRESHOLDS (Elephant Paper)")
    print("-" * 40)
    print(f"1. Hamiltonian-Capped Threshold (Eq. 308):")
    print(f"   RHS = 2(log d_min)² ||H||_min ⟨Ψ̂⟩")
    print(f"   Mean ± Std: {threshold_data['capped_rhs_mean']:.6e} ± {threshold_data['capped_rhs_std']:.6e}")
    print(f"   Intensive Triad ⟨Ψ̂⟩: {threshold_data['triad_hat_mean']:.6f} ± {threshold_data['triad_hat_std']:.6f}")
    print()
    print(f"2. Speed-Based Threshold (Eq. 343):")
    print(f"   RHS = (ℏ/2) δ ε_F ε_S ε_I")
    print(f"   Mean ± Std: {threshold_data['speed_rhs_mean']:.6e} ± {threshold_data['speed_rhs_std']:.6e}")
    print(f"   Floors: ε_F={threshold_data['epsF_mean']:.3f}, ε_S={threshold_data['epsS_mean']:.3f}, ε_I={threshold_data['epsI_mean']:.3f}")
    print(f"   Density δ: {threshold_data['delta_mean']:.3f}")
    print("=" * 60)


if __name__ == "__main__":
    N = 6  # keep small for laptops

    # ---- Baselines, 1‑site partition ----
    part1 = [(i,) for i in range(N)]

    print("Running Non-Commuting Simulation...")
    sim_nc = ESSESimulation(N=N, hbar=1.0, hx=1.0, hz=0.5, J=1.0, J2=0.3)
    T_nc = sim_nc.run(commuting=False, t_max=20, n_points=400, n_trials=3, partition=part1)
    rows_nc = [summarize_liminf_from_series(tr['tlist'], tr['Pi_t']) for tr in T_nc]
    print_table("=== Non‑Commuting (1‑site) ===", rows_nc)
    
    # Extract threshold data for non-commuting
    threshold_data_nc = extract_threshold_data(T_nc)
    print_threshold_summary("NON-COMMUTING STRUCTURAL THRESHOLDS", threshold_data_nc)

    print("\nRunning Commuting Simulation...")
    sim_c = ESSESimulation(N=N, hbar=1.0, hx=0.0, hz=1.0, J=1.0, J2=0.0)
    T_c = sim_c.run(commuting=True, t_max=20, n_points=400, n_trials=3, partition=part1)
    rows_c = [summarize_liminf_from_series(tr['tlist'], tr['Pi_t']) for tr in T_c]
    print_table("=== Commuting (1‑site) ===", rows_c)
    
    # Extract threshold data for commuting
    threshold_data_c = extract_threshold_data(T_c)
    print_threshold_summary("COMMUTING STRUCTURAL THRESHOLDS", threshold_data_c)

    # Compare thresholds
    print("\nTHRESHOLD COMPARISON")
    print("=" * 40)
    print(f"Non-commuting/Commuting ratio:")
    print(f"  Π liminf: {(np.mean([r['final'] for r in rows_nc]) / max(1e-12, np.mean([r['final'] for r in rows_c]))):.3f}")
    print(f"  Capped RHS: {(threshold_data_nc['capped_rhs_mean'] / max(1e-12, threshold_data_c['capped_rhs_mean'])):.3f}")
    print(f"  Speed RHS: {(threshold_data_nc['speed_rhs_mean'] / max(1e-12, threshold_data_c['speed_rhs_mean'])):.3f}")
    print(f"  Intensive Triad: {(threshold_data_nc['triad_hat_mean'] / max(1e-12, threshold_data_c['triad_hat_mean'])):.3f}")

    # ---- Partition stress on non‑commuting: raw and normalized ----
    print("\n" + "="*60)
    print("PARTITION STRESS TEST")
    print("="*60)
    
    parts = {
        '1‑site': part1,
        '2‑site': contiguous_blocks(N, 2),
        '3‑site': contiguous_blocks(N, 3),
    }
    
    partition_threshold_data = {}
    
    for pname, part in parts.items():
        print(f"\nRunning {pname} partition test...")
        sim = ESSESimulation(N=N, hbar=1.0, hx=1.0, hz=0.5, J=1.0, J2=0.3)
        T = sim.run(commuting=False, t_max=20, n_points=400, n_trials=3, partition=part)
        
        # Raw Π
        rows_raw = [summarize_liminf_from_series(tr['tlist'], tr['Pi_t']) for tr in T]
        print_table(f"=== Non‑Commuting ({pname}) — Raw Π ===", rows_raw)
        
        # Normalized Π̃
        rows_norm = [summarize_liminf_from_series(tr['tlist'], tr['Pi_tilde']) for tr in T]
        print_table(f"=== Non‑Commuting ({pname}) — Normalized Π̃ ===", rows_norm)
        
        # Extract threshold data for this partition
        threshold_data_part = extract_threshold_data(T)
        partition_threshold_data[pname] = threshold_data_part
        print_threshold_summary(f"{pname.upper()} PARTITION STRUCTURAL THRESHOLDS", threshold_data_part)

    # Summary comparison across partitions
    print("\n" + "="*60)
    print("PARTITION THRESHOLD COMPARISON")
    print("="*60)
    print("| Partition | Capped RHS (mean) | Speed RHS (mean) | Intensive Triad |")
    print("|-----------|-------------------|------------------|-----------------|")
    for pname, data in partition_threshold_data.items():
        print(f"| {pname:8} | {data['capped_rhs_mean']:15.3e} | {data['speed_rhs_mean']:14.3e} | {data['triad_hat_mean']:13.6f} |")

    print("\nDone.")
