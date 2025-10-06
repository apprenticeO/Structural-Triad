#!/usr/bin/env python3
from __future__ import annotations
import os
import csv
import numpy as np
import matplotlib.pyplot as plt
from datetime import datetime
import importlib.util, sys

# Canonical simulation consistent with Hyppotamus_Framework.tex
# from esse_core_simulation import ESSESimulation
BASE_DIR = os.path.dirname(__file__)
_CORE_PATH = os.path.join(BASE_DIR, '1_esse_core_simulation.py')
spec = importlib.util.spec_from_file_location('esse_core_simulation', _CORE_PATH)
core = importlib.util.module_from_spec(spec)
assert spec is not None and spec.loader is not None, 'Cannot load core simulation module'
spec.loader.exec_module(core)
ESSESimulation = core.ESSESimulation

# Parameters (pure global evolution only)
N = int(os.environ.get('ESSE_N', '6'))
T_MAX = float(os.environ.get('ESSE_TMAX', '12'))
N_POINTS = int(os.environ.get('ESSE_POINTS', '200'))
N_TRIALS = int(os.environ.get('ESSE_TRIALS', '2'))

# Output paths
OUT_DIR = os.path.join(BASE_DIR, 'plots', 'pure')
os.makedirs(OUT_DIR, exist_ok=True)
STAMP = datetime.now().strftime('%Y%m%d_%H%M%S')
CSV_PATH = os.path.join(OUT_DIR, f'pure_state_summary_{STAMP}.csv')

headers = [
    'case', 'trial', 'N', 't_max', 'n_points',
    'Pi_rate_time_avg_final', 'Pi_rate_liminf_proxy_final', 'r_stat',
    'energy_prod_mean', 'RHS_capped', 'RHS_speed', 'epsF', 'epsS', 'epsI', 'delta'
]
with open(CSV_PATH, 'w', newline='') as f:
    csv.writer(f).writerow(headers)

for commuting in [False, True]:
    case = 'noncomm' if not commuting else 'comm'
    # Reseed per case for independent draws
    sim = ESSESimulation(N=N)

    trials = sim.run(
        commuting=commuting,
        t_max=T_MAX,
        n_points=N_POINTS,
        n_trials=N_TRIALS,
        visualize=False
    )

    for idx, tr in enumerate(trials):
        t = tr['tlist']
        Pi_t = tr['Pi_t']
        time_avg = tr['time_avg']
        liminf_proxy = tr['liminf_proxy']
        r_stat = tr.get('r_stat', float('nan'))

        # Optional metrics
        energy_prod_t = tr.get('energy_prod_t', None)
        energy_prod_mean = float(tr.get('energy_prod_mean', np.nan))
        rhs_capped = float(tr.get('capped_rhs_energy', np.nan))
        rhs_speed = float(tr.get('speed_rhs_energy', np.nan))
        floors = tr.get('floors', {})
        epsF = floors.get('epsF', np.nan)
        epsS = floors.get('epsS', np.nan)
        epsI = floors.get('epsI', np.nan)
        delta = floors.get('delta', np.nan)

        # Save CSV row
        with open(CSV_PATH, 'a', newline='') as f:
            writer = csv.writer(f)
            writer.writerow([
                case, idx+1, N, T_MAX, N_POINTS,
                float(time_avg[-1]), float(liminf_proxy[-1]), r_stat,
                energy_prod_mean, rhs_capped, rhs_speed, epsF, epsS, epsI, delta
            ])

        # Extract metrics for plots
        epsilons = tr.get('deltaA', {}).keys()
        if epsilons:
            try:
                keys_sorted = sorted(epsilons, key=float)
            except Exception:
                keys_sorted = list(epsilons)
            e_plot = keys_sorted[len(keys_sorted)//2]
        else:
            e_plot = 1e-6
        deltaA = tr.get('deltaA', {})
        delta_vec = deltaA.get(e_plot, next(iter(deltaA.values())) if deltaA else [])
        tau4_list = tr.get('tau4_list', [])

        # Plots
        fig, axs = plt.subplots(2, 2, figsize=(12, 9), constrained_layout=True)
        axs[0,0].plot(t, Pi_t, label='Π_rate(t)')
        axs[0,0].plot(t, time_avg, label='⟨Π_rate⟩(t)')
        axs[0,0].plot(t, liminf_proxy, label='liminf proxy')
        axs[0,0].set_title('Triad rate (pure, closed)')
        axs[0,0].set_ylabel('rate')
        if energy_prod_t is not None:
            ax2 = axs[0,0].twinx()
            ax2.plot(t, energy_prod_t, 'r--', lw=1.5, label='Σ ΔE·S·I (energy)')
            ax2.set_ylabel('energy')
            h1,l1 = axs[0,0].get_legend_handles_labels()
            h2,l2 = ax2.get_legend_handles_labels()
            axs[0,0].legend(h1+h2, l1+l2, loc='upper left')
        else:
            axs[0,0].legend(loc='upper left')
        axs[0,0].grid(True, alpha=0.3)

        # Triad components over time
        sqrtF_blocks = tr.get('sqrtF_blocks', np.array([]))
        S_blocks = tr.get('S_blocks', np.array([]))
        I_blocks = tr.get('I_blocks', np.array([]))
        if sqrtF_blocks.size > 0 and S_blocks.size > 0 and I_blocks.size > 0:
            axs[0,1].plot(t, sqrtF_blocks.mean(axis=0), label='⟨√F_Q⟩', color='#1f77b4', lw=2)
            axs[0,1].plot(t, S_blocks.mean(axis=0), label='⟨S_A⟩', color='#ff7f0e', lw=2)
            axs[0,1].plot(t, I_blocks.mean(axis=0), label='⟨I(A:Ā)⟩', color='#2ca02c', lw=2)
            axs[0,1].set_title('Triad Components')
            axs[0,1].set_xlabel('time'); axs[0,1].set_ylabel('value')
            axs[0,1].legend(frameon=True)
            axs[0,1].grid(True, alpha=0.3)
        else:
            axs[0,1].text(0.5, 0.5, 'No triad data', ha='center', va='center', transform=axs[0,1].transAxes)
            axs[0,1].set_title('Triad Components (No Data)')

        axs[1,0].bar(range(len(tau4_list)), tau4_list, color='orange')
        axs[1,0].set_title('τ_A^4 (liminf of avg d^4)')
        axs[1,0].set_xlabel('A index')
        axs[1,0].grid(True, axis='y', alpha=0.2)

        axs[1,1].bar(range(len(delta_vec)), delta_vec, color='green')
        axs[1,1].set_title(f'δ_A at ε={e_plot}')
        axs[1,1].set_xlabel('A index')
        axs[1,1].set_ylim(0, 1.05)
        axs[1,1].grid(True, axis='y', alpha=0.2)

        fig.suptitle(f"{tr.get('label','Pure-state')} | seed={tr.get('seed', 'N/A')}")
        png_path = os.path.join(OUT_DIR, f'{case}_trial{idx+1}_{STAMP}.png')
        fig.savefig(png_path, dpi=150, bbox_inches='tight')
        plt.close(fig)

print(f"Saved pure-state summary CSV to: {CSV_PATH}")
print(f"Saved pure-state plots to: {OUT_DIR}") 