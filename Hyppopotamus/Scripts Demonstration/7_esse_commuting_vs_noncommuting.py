# esse_refactor.py
# Full refactor implementing PDF-consistent Π(t), admissibility, and boundary-aware H_A
# ENHANCED WITH STRUCTURAL THRESHOLDS from Elephant paper
from __future__ import annotations
import numpy as np
import time
from typing import List, Tuple, Dict

# Prefer dynamic import from 1_esse_core_simulation.py if module not present
import importlib.util, os, json, csv
from datetime import datetime
import matplotlib.pyplot as plt

def _last_time_avg(tr: dict) -> float:
    x = tr.get('time_avg')
    if x is None:
        return 0.0
    try:
        arr = np.asarray(x)
        if arr.size == 0:
            return 0.0
        return float(arr[-1])
    except Exception:
        try:
            return float(x)
        except Exception:
            return 0.0

def extract_threshold_data(trials: List[Dict]) -> Dict:
    """Extract threshold data from trials"""
    threshold_data = {
        'capped_rhs_values': [],
        'speed_rhs_values': [],
        'energy_triad_values': [],
        'intensive_triad_values': [],
        'floor_values': {'epsF': [], 'epsS': [], 'epsI': [], 'delta': []}
    }
    
    for trial in trials:
        # Extract threshold values if available
        if 'capped_rhs_energy' in trial:
            threshold_data['capped_rhs_values'].append(trial['capped_rhs_energy'])
        if 'speed_rhs_energy' in trial:
            threshold_data['speed_rhs_values'].append(trial['speed_rhs_energy'])
        if 'energy_triad_sum' in trial:
            threshold_data['energy_triad_values'].append(trial['energy_triad_sum'])
        if 'triad_hat_mean' in trial:
            threshold_data['intensive_triad_values'].append(trial['triad_hat_mean'])
        
        # Extract floor values
        if 'epsF' in trial:
            threshold_data['floor_values']['epsF'].append(trial['epsF'])
        if 'epsS' in trial:
            threshold_data['floor_values']['epsS'].append(trial['epsS'])
        if 'epsI' in trial:
            threshold_data['floor_values']['epsI'].append(trial['epsI'])
        if 'delta' in trial:
            threshold_data['floor_values']['delta'].append(trial['delta'])
    
    return threshold_data

def print_threshold_summary(case_name: str, threshold_data: Dict):
    """Print threshold summary for a case"""
    print(f"\n=== {case_name.upper()} STRUCTURAL THRESHOLDS ===")
    
    # Hamiltonian-capped threshold (Eq. 308)
    if threshold_data['capped_rhs_values']:
        capped_mean = np.mean(threshold_data['capped_rhs_values'])
        capped_std = np.std(threshold_data['capped_rhs_values'])
        print(f"RHS_capped (Hamiltonian-capped): {capped_mean:.6f} ± {capped_std:.6f}")
        print(f"  Formula: 2(log d_min)² ||H||_min ⟨Ψ̂⟩ (Eq. 308)")
    
    # Speed-based threshold (Eq. 343)
    if threshold_data['speed_rhs_values']:
        speed_mean = np.mean(threshold_data['speed_rhs_values'])
        speed_std = np.std(threshold_data['speed_rhs_values'])
        print(f"RHS_speed (Speed-based): {speed_mean:.6f} ± {speed_std:.6f}")
        print(f"  Formula: (ℏ/2) δ ε_F ε_S ε_I (Eq. 343)")
    
    # Energy triad
    if threshold_data['energy_triad_values']:
        energy_mean = np.mean(threshold_data['energy_triad_values'])
        energy_std = np.std(threshold_data['energy_triad_values'])
        print(f"Energy triad ⟨∑_A ΔE_A S_A I⟩: {energy_mean:.6f} ± {energy_std:.6f}")
    
    # Intensive triad
    if threshold_data['intensive_triad_values']:
        intensive_mean = np.mean(threshold_data['intensive_triad_values'])
        intensive_std = np.std(threshold_data['intensive_triad_values'])
        print(f"Intensive triad ⟨Ψ̂⟩: {intensive_mean:.6f} ± {intensive_std:.6f}")
    
    # Floor parameters
    floors = threshold_data['floor_values']
    if floors['epsF'] and floors['epsS'] and floors['epsI'] and floors['delta']:
        epsF_mean = np.mean(floors['epsF'])
        epsS_mean = np.mean(floors['epsS'])
        epsI_mean = np.mean(floors['epsI'])
        delta_mean = np.mean(floors['delta'])
        print(f"Floors (ε_F, ε_S, ε_I, δ): ({epsF_mean:.3f}, {epsS_mean:.3f}, {epsI_mean:.3f}, {delta_mean:.3f})")

def load_ESSESimulation():
    try:
        from esse_core_simulation import ESSESimulation  # type: ignore
        return ESSESimulation
    except Exception:
        here = os.path.dirname(__file__)
        core_path = os.path.join(here, '1_esse_core_simulation.py')
        spec = importlib.util.spec_from_file_location('esse_core_simulation_dynamic', core_path)
        if spec is None or spec.loader is None:
            raise ImportError('Cannot locate ESSESimulation at 1_esse_core_simulation.py')
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)  # type: ignore
        return getattr(mod, 'ESSESimulation')


class LegacyESSESimulation:
    """
    Wrapper retained for backward-compatibility import paths.
    Use ESSESimulation loaded via load_ESSESimulation instead.
    """
    pass


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser(description='Compare commuting vs non-commuting ESSE trials with structural thresholds')
    ap.add_argument('--N', type=int, default=6)
    ap.add_argument('--t-max', type=float, default=20.0, dest='t_max')
    ap.add_argument('--n-points', type=int, default=300, dest='n_points')
    ap.add_argument('--n-trials', type=int, default=3, dest='n_trials')
    ap.add_argument('--out-dir', type=str, default=os.path.join(os.path.dirname(__file__), 'plots', 'comm_vs_noncomm'))
    args = ap.parse_args()

    ESSESimulation = load_ESSESimulation()
    sim = ESSESimulation(N=args.N)

    print("Running non-commuting trials...")
    trials_nc = sim.run(commuting=False, t_max=args.t_max, n_points=args.n_points, n_trials=args.n_trials)
    
    print("Running commuting trials...")
    trials_c  = sim.run(commuting=True,  t_max=args.t_max, n_points=args.n_points, n_trials=args.n_trials)

    # Extract threshold data
    threshold_data_nc = extract_threshold_data(trials_nc)
    threshold_data_c = extract_threshold_data(trials_c)

    # Print threshold summaries
    print_threshold_summary("Non-commuting", threshold_data_nc)
    print_threshold_summary("Commuting", threshold_data_c)

    # Minimal textual summary (guard missing keys)
    for name, trials in [('Non-comm', trials_nc), ('Comm', trials_c)]:
        finals = [_last_time_avg(tr) for tr in trials]
        r_stat = [tr.get('r_stat') for tr in trials]
        print(f"\n{name}: <Π>_T = {np.mean(finals):.6f} ± {np.std(finals):.6f}")

    # Save CSV, sidecar JSON, and plots
    out_dir = args.out_dir
    os.makedirs(out_dir, exist_ok=True)
    stamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    csv_path = os.path.join(out_dir, f'comm_vs_noncomm_{stamp}.csv')
    with open(csv_path, 'w', newline='') as f:
        w = csv.writer(f)
        w.writerow(["case","trial","Pi_time_avg_final","r","r_robust"])
        for case, trials in [('noncomm', trials_nc), ('comm', trials_c)]:
            for i, tr in enumerate(trials, 1):
                w.writerow([
                    case, i,
                    _last_time_avg(tr),
                    tr.get("r_stat"), tr.get("r_robust")
                ])
    print(f"Saved CSV to: {csv_path}")

    # Sidecar JSON with run configuration and notes if present
    sidecar = {
        'config': {'N': args.N, 't_max': args.t_max, 'n_points': args.n_points, 'n_trials': args.n_trials},
        'notes_noncomm': trials_nc[0].get('notes') if trials_nc else None,
        'notes_comm': trials_c[0].get('notes') if trials_c else None,
        'threshold_data': {
            'noncomm': threshold_data_nc,
            'comm': threshold_data_c
        }
    }
    json_path = os.path.join(out_dir, f'comm_vs_noncomm_{stamp}_config.json')
    with open(json_path, 'w') as jf:
        json.dump(sidecar, jf, indent=2)
    print(f"Saved config JSON to: {json_path}")
