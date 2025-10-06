import numpy as np
from qutip import *
import matplotlib.pyplot as plt
import os, csv, json
from datetime import datetime
import importlib.util

# ---------------------------------------------------------------------
# Parameters (overridable via CLI)
# ---------------------------------------------------------------------
N = 8                # Number of qubits
hbar = 1.0
hx = 1.0
hz = 0.5
J = 1.0
J2 = 0.3
subsystem_indices = [0, 1]  # Subsystem A: can be [0], [1,2], etc.

# Time evolution parameters
T_max = 10.0        # Maximum time for evolution
Nt = 200            # Number of time points
use_time_evolution = False  # Set to True to enable time evolution

# ---------------------------------------------------------------------
# Helper: Local ops
# ---------------------------------------------------------------------
sx = sigmax()
sz = sigmaz()
id2 = qeye(2)

def local_op(op, i, N):
    return tensor([op if j == i else id2 for j in range(N)])

def two_site_op(op1, i, op2, j, N):
    return tensor([op1 if k == i else op2 if k == j else id2 for k in range(N)])

# ---------------------------------------------------------------------
# Build non-integrable Hamiltonian
# ---------------------------------------------------------------------
def build_nonintegrable_hamiltonian(N):
    H = 0
    # Nearest-neighbor Ising interactions
    for i in range(N - 1):
        H += -J * two_site_op(sz, i, sz, i+1, N)
    # Next-nearest neighbor interactions (non-integrability)
    for i in range(N - 2):
        H += -J2 * two_site_op(sz, i, sz, i+2, N)
    # Transverse field
    for i in range(N):
        H += hx * local_op(sx, i, N)
    # Staggered longitudinal field
    for i in range(N):
        H += hz * (i % 2 - 0.5) * local_op(sz, i, N)
    return H

# ---------------------------------------------------------------------
# ESSE utilities (metrics consistent with core simulation)
# ---------------------------------------------------------------------
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

def qfi_sld_unitary(rho: np.ndarray, H: np.ndarray) -> float:
    rho = 0.5 * (rho + rho.conj().T)
    vals, vecs = np.linalg.eigh(rho)
    He = vecs.conj().T @ H @ vecs
    F = 0.0
    for i in range(len(vals)):
        for j in range(len(vals)):
            denom = vals[i] + vals[j]
            if denom > 0.0:
                num = (vals[i] - vals[j]) ** 2
                F += 2.0 * (num / denom) * (abs(He[i, j]) ** 2)
    return float(np.real(F))

def compute_time_evolution_metrics(H, psi0, H_A_full, H_A_on_A, subsystem_indices, N, hbar, ts):
    """Compute per-time metrics for time evolution"""
    S_list, I_list, F_list, dH_list, Psi_hat_list = [], [], [], [], []
    
    for psi_t in psi0:
        # Reduced states
        rhoA = psi_t.ptrace(subsystem_indices)
        rhoB = psi_t.ptrace([i for i in range(N) if i not in subsystem_indices])
        
        # Entropy and mutual information
        SA = entropy_vn(rhoA, base=np.e)
        SAB = entropy_vn(ket2dm(psi_t), base=np.e)  # 0 if pure
        IAB = SA + entropy_vn(rhoB, base=np.e) - SAB
        
        # QFI computation
        F = qfi_sld_unitary(rhoA.full(), H_A_on_A.full())
        sqrtF = np.sqrt(max(F, 0.0))
        
        # Variance on reduced state (clarity)
        EA = H_A_on_A.full()
        rA = rhoA.full()
        mu = np.trace(rA @ EA)
        mu2 = np.trace(rA @ (EA @ EA))
        dH = float(np.sqrt(max(0.0, np.real(mu2 - mu*mu))))
        
        # Intensive Ψ̂ via Eq.(12)
        dA = 2**len(subsystem_indices)
        dbar = 2**(N - len(subsystem_indices))
        dmin = min(dA, dbar)
        try:
            Hnorm = float(H_A_full.norm("fro"))
        except Exception:
            Hnorm = float(np.max(np.abs(np.real(np.asarray(H_A_full.eigenenergies(), dtype=float)))))
        Psi_hat = (hbar * sqrtF) / (2 * Hnorm) * (SA / np.log(dA)) * (IAB / (2 * np.log(dmin)))
        Hnorm = float(np.max(np.abs(np.real(np.asarray(H_A_full.eigenenergies(), dtype=float)))))
        Psi_hat = (hbar * sqrtF) / (2 * Hnorm) * (SA / np.log(dA)) * (IAB / (2 * np.log(dmin)))
        
        S_list.append(SA)
        I_list.append(IAB)
        F_list.append(sqrtF)
        dH_list.append(dH)
        Psi_hat_list.append(Psi_hat)
    
    return S_list, I_list, F_list, dH_list, Psi_hat_list

def detect_active_epoch(F_list, S_list, I_list, ts, tauF=1e-6, tauS=1e-6, tauI=1e-6):
    """Detect active epoch K* and estimate floors and density"""
    # Define indicator sets
    K_idx = [k for k, (f, s, i) in enumerate(zip(F_list, S_list, I_list)) 
             if (f >= tauF and s >= tauS and i >= tauI)]
    
    # Empirical lower density
    delta = len(K_idx) / len(ts) if len(ts) > 0 else 0.0
    
    # Floors on K*
    epsF = min(F_list[k] for k in K_idx) if K_idx else 0.0
    epsS = min(S_list[k] for k in K_idx) if K_idx else 0.0
    epsI = min(I_list[k] for k in K_idx) if K_idx else 0.0
    
    return delta, epsF, epsS, epsI, K_idx

def compute_structural_thresholds(sqrtF, S_A, I_AB, delta_H, H_A_full, subsystem_indices, N, hbar=1.0, 
                                 time_evolution_data=None):
    """Compute structural thresholds from Elephant paper - CORRECTED FOR EIGENSTATES AND TIME EVOLUTION"""
    
    # Determine if we're evaluating a stationary snapshot (eigenstate) or a trajectory
    is_stationary_snapshot = time_evolution_data is None
    
    # Get subsystem dimensions
    d_A = 2**len(subsystem_indices)
    d_bar = 2**(N - len(subsystem_indices))
    d_min = min(d_A, d_bar)
    
    # Get operator norm
    try:
        H_norm = float(H_A_full.norm('spectral'))
    except Exception:
        H_norm = float(np.max(np.abs(np.real(np.asarray(H_A_full.eigenenergies(), dtype=float)))))
    
    if is_stationary_snapshot:
        # Single eigenstate computation
        denom_op = max(H_norm, 1e-12)
        denom_S = max(np.log(d_A), 1e-12)
        denom_I = max(2.0 * np.log(d_min), 1e-12)
        
        Psi_hat = (hbar * sqrtF) / (2.0 * denom_op) * (S_A / denom_S) * (I_AB / denom_I)
        energy_triad_lhs = delta_H * S_A * I_AB
        
        # |E|=1 specialization of Eq. (13): H_min = ||H_A||_op, <Psi_cut>_t = Psi_hat (stationary)
        capped_rhs = 2.0 * (np.log(d_min)**2) * H_norm * Psi_hat
        
        # speed-based threshold cannot be invoked for a stationary eigenstate
        delta = 0.0
        epsF = epsS = epsI = 0.0
        speed_rhs = 0.0
        
    else:
        # Time evolution computation
        S_list, I_list, F_list, dH_list, Psi_hat_list = time_evolution_data
        
        # Time averages
        energy_triad_lhs = np.mean([dH_list[k] * S_list[k] * I_list[k] for k in range(len(S_list))])
        psi_hat_time = np.mean(Psi_hat_list)
        
        # |E|=1 specialization of Eq. (13): H_min = ||H_A||_op, <Psi_cut>_t = Psi_hat (time-averaged)
        capped_rhs = 2.0 * (np.log(d_min)**2) * H_norm * psi_hat_time
        
        # Detect active epoch and compute floors
        delta, epsF, epsS, epsI, K_idx = detect_active_epoch(F_list, S_list, I_list, 
                                                             range(len(S_list)))
        
        # Speed-based threshold (Eq. 14) - only if delta > 0
        if delta > 0:
            speed_rhs = 0.5 * hbar * delta * epsF * epsS * epsI
        else:
            speed_rhs = 0.0
    
    # Check if thresholds are satisfied
    hamiltonian_satisfied = energy_triad_lhs >= capped_rhs
    speed_satisfied = energy_triad_lhs >= speed_rhs if not is_stationary_snapshot and delta > 0 else None
    
    return {
        'energy_triad_lhs': energy_triad_lhs,  # LHS of inequalities
        'capped_rhs': capped_rhs,             # Hamiltonian-capped RHS
        'speed_rhs': speed_rhs,               # Speed-based RHS
        'intensive_triad': psi_hat_time if not is_stationary_snapshot else (hbar * sqrtF) / (2.0 * H_norm) * (S_A / np.log(d_A)) * (I_AB / (2.0 * np.log(d_min))),
        'floors': {'epsF': float(epsF), 'epsS': float(epsS), 'epsI': float(epsI), 'delta': float(delta)},
        'dimensions': {'d_A': d_A, 'd_bar': d_bar, 'd_min': d_min},
        'H_norm': H_norm,
        'thresholds_satisfied': {
            'hamiltonian_capped': hamiltonian_satisfied,
            'speed_based': speed_satisfied
        },
        'is_stationary_snapshot': is_stationary_snapshot,
        'time_evolution_data': time_evolution_data
    }

def print_threshold_summary(threshold_data):
    """Print threshold summary - CORRECTED FOR EIGENSTATES AND TIME EVOLUTION"""
    print("\n=== STRUCTURAL THRESHOLDS ===")
    if threshold_data['is_stationary_snapshot']:
        print("Mode: STATIONARY EIGENSTATE")
    else:
        print("Mode: TIME EVOLUTION")
    
    print(f"Energy triad LHS ⟨∑_A ΔE_A S_A I⟩: {threshold_data['energy_triad_lhs']:.6f}")
    print(f"RHS_capped (Hamiltonian-capped): {threshold_data['capped_rhs']:.6f}")
    print(f"  Formula: 2(log d_min)² ||H||_min ⟨Ψ̂⟩ (Eq. 308)")
    
    if threshold_data['is_stationary_snapshot']:
        print(f"RHS_speed (Speed-based): {threshold_data['speed_rhs']:.6f}")
        print(f"  Formula: (ℏ/2) δ ε_F ε_S ε_I (Eq. 343) - DISABLED for eigenstate (δ=0)")
    else:
        print(f"RHS_speed (Speed-based): {threshold_data['speed_rhs']:.6f}")
        if threshold_data['floors']['delta'] > 0:
            print(f"  Formula: (ℏ/2) δ ε_F ε_S ε_I (Eq. 343) - INVOKED (δ>0)")
        else:
            print(f"  Formula: (ℏ/2) δ ε_F ε_S ε_I (Eq. 343) - INAPPLICABLE (δ=0)")
    
    print(f"Intensive triad ⟨Ψ̂⟩: {threshold_data['intensive_triad']:.6f}")
    print(f"Floors (ε_F, ε_S, ε_I, δ): ({threshold_data['floors']['epsF']:.6f}, {threshold_data['floors']['epsS']:.6f}, {threshold_data['floors']['epsI']:.6f}, {threshold_data['floors']['delta']:.6f})")
    print(f"Dimensions: d_A={threshold_data['dimensions']['d_A']}, d_Ā={threshold_data['dimensions']['d_bar']}, d_min={threshold_data['dimensions']['d_min']}")
    print(f"Operator norm ||H_A||: {threshold_data['H_norm']:.6f}")
    
    # Show threshold satisfaction
    print(f"\n=== THRESHOLD VALIDATION ===")
    print(f"[Assumption] Threshold mode: {'stationary-eigenstate' if threshold_data['is_stationary_snapshot'] else 'time-series'}")
    
    print(f"Hamiltonian-capped threshold satisfied: {threshold_data['thresholds_satisfied']['hamiltonian_capped']}")
    if threshold_data['thresholds_satisfied']['hamiltonian_capped']:
        margin = threshold_data['energy_triad_lhs'] - threshold_data['capped_rhs']
        print(f"Hamiltonian-capped margin: +{margin:.6f}")
    else:
        deficit = threshold_data['capped_rhs'] - threshold_data['energy_triad_lhs']
        print(f"Hamiltonian-capped deficit: -{deficit:.6f}")
    
    if threshold_data['is_stationary_snapshot']:
        print("Speed-based threshold: disabled (δ=0, floors undefined for a single snapshot)")
    elif threshold_data['floors']['delta'] > 0:
        print(f"Speed-based threshold satisfied: {threshold_data['thresholds_satisfied']['speed_based']}")
        if threshold_data['thresholds_satisfied']['speed_based']:
            margin = threshold_data['energy_triad_lhs'] - threshold_data['speed_rhs']
            print(f"Speed-based margin: +{margin:.6f}")
        else:
            deficit = threshold_data['speed_rhs'] - threshold_data['energy_triad_lhs']
            print(f"Speed-based deficit: -{deficit:.6f}")
        print("Speed-based bound invoked ONLY because δ>0 and positive floors exist on K*")
    else:
        print("Speed-based threshold: inapplicable (δ=0)")

# ---------------------------------------------------------------------
# Main computation
# ---------------------------------------------------------------------
if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description='ETH eigenstate validation with CORRECTED structural thresholds')
    parser.add_argument('--N', type=int, default=N, help='Number of qubits')
    parser.add_argument('--subsystem', type=int, nargs='+', default=subsystem_indices, help='Subsystem indices')
    parser.add_argument('--hx', type=float, default=hx, help='Transverse field strength')
    parser.add_argument('--hz', type=float, default=hz, help='Longitudinal field strength')
    parser.add_argument('--J', type=float, default=J, help='Ising coupling')
    parser.add_argument('--J2', type=float, default=J2, help='Next-nearest neighbor coupling')
    parser.add_argument('--time-evolution', action='store_true', help='Enable time evolution')
    parser.add_argument('--T-max', type=float, default=T_max, help='Maximum time for evolution')
    parser.add_argument('--Nt', type=int, default=Nt, help='Number of time points')
    args = parser.parse_args()
    
    N = args.N
    subsystem_indices = args.subsystem
    hx, hz, J, J2 = args.hx, args.hz, args.J, args.J2
    use_time_evolution = args.time_evolution
    T_max = args.T_max
    Nt = args.Nt
    
    print(f"ETH eigenstate validation: N={N}, A={subsystem_indices}")
    print(f"Parameters: hx={hx}, hz={hz}, J={J}, J2={J2}")
    print(f"Time evolution: {'ENABLED' if use_time_evolution else 'DISABLED'}")
    if use_time_evolution:
        print(f"Time parameters: T_max={T_max}, Nt={Nt}")
    
    # Build Hamiltonian
    H = build_nonintegrable_hamiltonian(N)
    
    # Use ESSESimulation for level-spacing ratio
    ESSESimulation = load_ESSESimulation()
    sim = ESSESimulation(N=N, hbar=hbar, hx=hx, hz=hz, J=J, J2=J2, seed=41)
    r_stat = sim.level_spacing_ratio(H)
    r_robust = None
    r_note = None
    if np.isnan(r_stat):
        r_note = "degenerate/too-few-gaps; diagnostic only; ESSE metrics unaffected"
        try:
            eps = 1e-9
            jitter = 0
            for i in range(N):
                jitter += float(np.random.default_rng(41).normal()) * local_op(sz, i, N)
            H_eps = H + eps * jitter
            r_eps = sim.level_spacing_ratio(H_eps)
            if not np.isnan(r_eps):
                r_robust = float(r_eps)
        except Exception:
            pass

    # H_A on FULL space via symmetric 1/2 splitting, summed over sites in A
    H_loc_full = sim.build_local_energy_ops(commuting=False)
    H_A_full = 0
    for i in subsystem_indices:
        H_A_full += H_loc_full[i]
    
    H_A_on_A = H_A_full.ptrace(subsystem_indices)
    
    if use_time_evolution:
        # Time evolution computation
        print(f"\n=== TIME EVOLUTION COMPUTATION ===")
        
        # Get initial state (not an eigenstate to ensure non-stationarity)
        eigenvals, eigenvecs = H.eigenstates()
        # Use a superposition of eigenstates to ensure dynamics
        psi0 = (eigenvecs[0] + eigenvecs[1] + eigenvecs[2]) / np.sqrt(3)
        
        # Time evolution
        ts = np.linspace(0, T_max, Nt)
        result = sesolve(H, psi0, ts)
        psis = result.states
        
        # Compute per-time metrics
        S_list, I_list, F_list, dH_list, Psi_hat_list = compute_time_evolution_metrics(
            H, psis, H_A_full, H_A_on_A, subsystem_indices, N, hbar, ts)
        
        # Guards: QFI-variance bound check
        viol = [(F_list[k] > 2.0 * dH_list[k] / hbar + 1e-10) for k in range(len(ts))]
        if any(viol):
            print("⍰ Warning: QFI–variance inequality violated numerically at some times [Braunstein & Caves, 1994].")
        
        # Pure-state identity check
        pure_violations = [abs(I_list[k] - 2*S_list[k]) > 1e-10 for k in range(len(ts))]
        if any(pure_violations):
            print("⍰ Warning: Pure-state identity I(A:Ā) = 2S_A violated numerically at some times.")
        
        # Compute structural thresholds with time evolution data
        threshold_data = compute_structural_thresholds(
            None, None, None, None, H_A_full, subsystem_indices, N, hbar, 
            time_evolution_data=(S_list, I_list, F_list, dH_list, Psi_hat_list))
        
        # Print threshold summary
        print_threshold_summary(threshold_data)
        
        # Print time evolution metrics
        print(f"\n=== TIME EVOLUTION METRICS ===")
        print(f"Time window: [0, {T_max}] with {Nt} points")
        print(f"Active epoch density δ(K*): {threshold_data['floors']['delta']:.6f}")
        print(f"Floors on K*: ε_F={threshold_data['floors']['epsF']:.6f}, ε_S={threshold_data['floors']['epsS']:.6f}, ε_I={threshold_data['floors']['epsI']:.6f}")
        print(f"Time-averaged S_A: {np.mean(S_list):.6f}")
        print(f"Time-averaged √F_Q: {np.mean(F_list):.6f}")
        print(f"Time-averaged I(A:Ā): {np.mean(I_list):.6f}")
        print(f"Time-averaged ΔH_A: {np.mean(dH_list):.6f}")
        
        # Save time evolution data
        out_dir = os.path.join(os.path.dirname(__file__), 'plots', 'eigen')
        os.makedirs(out_dir, exist_ok=True)
        stamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        
        # CSV output
        csv_path = os.path.join(out_dir, f'time_evolution_{stamp}.csv')
        with open(csv_path, 'w', newline='') as f:
            w = csv.DictWriter(f, fieldnames=['t','S_A','sqrtF','I_AB','DeltaH_A','Psi_hat','energy_triad'])
            w.writeheader()
            for k, t in enumerate(ts):
                w.writerow({
                    't': t, 'S_A': S_list[k], 'sqrtF': F_list[k], 'I_AB': I_list[k],
                    'DeltaH_A': dH_list[k], 'Psi_hat': Psi_hat_list[k],
                    'energy_triad': dH_list[k] * S_list[k] * I_list[k]
                })
        print(f"Saved time evolution CSV to: {csv_path}")
        
    else:
        # Single eigenstate computation
        print(f"\n=== SINGLE EIGENSTATE COMPUTATION ===")
        
        # Get mid-spectrum eigenstate
        eigenvals, eigenvecs = H.eigenstates()
        mid_idx = len(eigenvals) // 2
        psi = eigenvecs[mid_idx]
        E = eigenvals[mid_idx]
        
        print(f"Selected eigenstate: E = {E:.6f} (mid-spectrum)")
        
        # Reduced state
        rho_A = psi.ptrace(subsystem_indices)
        S_A = entropy_vn(rho_A, base=np.e)
        
        # Optional clarity: compute ΔH on ρA and add invariant checks
        # Equivalent variance (clarity)
        EA = H_A_on_A.full()
        rhoA = rho_A.full()
        mu = np.trace(rhoA @ EA)
        mu2 = np.trace(rhoA @ (EA @ EA))
        delta_H = float(np.sqrt(max(0.0, np.real(mu2 - mu*mu))))
        
        # Compute QFI for reduced state ρ_A with respect to H_A
        F = qfi_sld_unitary(rho_A.full(), H_A_on_A.full())
        sqrtF = np.sqrt(max(F, 0.0))
        
        # QFI–variance sanity check (Mandelstam–Tamm / Lemma 1)
        # Check: sqrtF <= 2*delta_H/hbar
        if sqrtF > 2.0*delta_H/hbar + 1e-10:
            print("⍰ Warning: QFI–variance inequality appears violated numerically.")
        
        # For pure states: I(A:Ā) = 2S_A, but should verify
        rho_bar = psi.ptrace([i for i in range(N) if i not in subsystem_indices])
        S_bar = entropy_vn(rho_bar, base=np.e)
        S_AB = entropy_vn(ket2dm(psi), base=np.e)  # Should be 0 for pure states
        I_AB = S_A + S_bar - S_AB
        
        # Canonical ESSE Π = √F_Q · S_A · I(A:Ā)
        Pi = sqrtF * S_A * I_AB
        
        # CORRECTED: Compute structural thresholds
        threshold_data = compute_structural_thresholds(sqrtF, S_A, I_AB, delta_H, H_A_full, subsystem_indices, N, hbar)
        
        # Print threshold summary
        print_threshold_summary(threshold_data)
        
        print(f"\n=== EIGENSTATE METRICS ===")
        print(f"Entanglement entropy S_A: {S_A:.6f}")
        print(f"Energy fluctuation ΔH_A: {delta_H:.6f}")
        print(f"QFI square root √F_Q: {sqrtF:.6f}")
        print(f"Mutual information I(A:Ā): {I_AB:.6f}")
        print(f"Canonical triad Π_A: {Pi:.6f}")
        print(f"Level-spacing ratio r: {r_stat:.6f}")
        if r_robust is not None:
            print(f"Robust level-spacing ratio: {r_robust:.6f}")
        if r_note:
            print(f"Note: {r_note}")
        
        # Save results
        out_dir = os.path.join(os.path.dirname(__file__), 'plots', 'eigen')
        os.makedirs(out_dir, exist_ok=True)
        stamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        
        # CSV output
        csv_path = os.path.join(out_dir, f'eigen_snapshot_{stamp}.csv')
        with open(csv_path, 'w', newline='') as f:
            w = csv.DictWriter(f, fieldnames=['A','S_A','DeltaH_A','Pi','sqrtF','I_AB','r','r_robust','energy_triad_lhs','capped_rhs','speed_rhs','intensive_triad','hamiltonian_satisfied','speed_satisfied','notes'])
            w.writeheader()
            w.writerow({
                'A': str(subsystem_indices), 'S_A': S_A, 'DeltaH_A': delta_H, 'Pi': Pi,
                'sqrtF': sqrtF, 'I_AB': I_AB, 'r': r_stat, 'r_robust': r_robust,
                'energy_triad_lhs': threshold_data['energy_triad_lhs'], 
                'capped_rhs': threshold_data['capped_rhs'], 
                'speed_rhs': threshold_data['speed_rhs'],
                'intensive_triad': threshold_data['intensive_triad'],
                'hamiltonian_satisfied': bool(threshold_data['thresholds_satisfied']['hamiltonian_capped']),
                'speed_satisfied': bool(threshold_data['thresholds_satisfied']['speed_based']) if threshold_data['thresholds_satisfied']['speed_based'] is not None else None,
                'notes': json.dumps(r_note) if r_note else None
            })
        print(f"Saved eigenstate snapshot CSV to: {csv_path}")
    
    # JSON output with threshold data (convert numpy types to Python types)
    json_path = os.path.join(out_dir, f'threshold_data_{stamp}.json')
    threshold_data_json = {
        'energy_triad_lhs': float(threshold_data['energy_triad_lhs']),
        'capped_rhs': float(threshold_data['capped_rhs']),
        'speed_rhs': float(threshold_data['speed_rhs']),
        'intensive_triad': float(threshold_data['intensive_triad']),
        'floors': threshold_data['floors'],  # Already converted to float in compute_structural_thresholds
        'dimensions': {k: int(v) for k, v in threshold_data['dimensions'].items()},
        'H_norm': float(threshold_data['H_norm']),
        'thresholds_satisfied': {
            'hamiltonian_capped': bool(threshold_data['thresholds_satisfied']['hamiltonian_capped']),
            'speed_based': bool(threshold_data['thresholds_satisfied']['speed_based']) if threshold_data['thresholds_satisfied']['speed_based'] is not None else None
        },
        'is_stationary_snapshot': threshold_data['is_stationary_snapshot']
    }
    with open(json_path, 'w') as f:
        json.dump({
            'config': {'N': N, 'subsystem': subsystem_indices, 'hx': hx, 'hz': hz, 'J': J, 'J2': J2, 'use_time_evolution': use_time_evolution, 'T_max': T_max, 'Nt': Nt},
            'metrics': {'r': r_stat, 'r_robust': r_robust},
            'threshold_data': threshold_data_json
        }, f, indent=2)
    print(f"Saved threshold data JSON to: {json_path}")

    # Plot
    fig, axs = plt.subplots(2, 2, figsize=(12, 10))
    
    if use_time_evolution:
        # Time evolution plots
        axs[0,0].plot(ts, S_list, 'b-', label='S_A(t)')
        axs[0,0].set_title('Entropy Evolution')
        axs[0,0].set_xlabel('Time')
        axs[0,0].set_ylabel('S_A')
        axs[0,0].legend()
        
        axs[0,1].plot(ts, F_list, 'g-', label='√F_Q(t)')
        axs[0,1].set_title('QFI Evolution')
        axs[0,1].set_xlabel('Time')
        axs[0,1].set_ylabel('√F_Q')
        axs[0,1].legend()
        
        axs[1,0].plot(ts, I_list, 'r-', label='I(A:Ā)(t)')
        axs[1,0].set_title('Mutual Information Evolution')
        axs[1,0].set_xlabel('Time')
        axs[1,0].set_ylabel('I(A:Ā)')
        axs[1,0].legend()
        
        # Threshold comparison
        energy_triad_time = [dH_list[k] * S_list[k] * I_list[k] for k in range(len(ts))]
        axs[1,1].plot(ts, energy_triad_time, 'c-', label='Energy Triad LHS')
        axs[1,1].axhline(y=threshold_data['capped_rhs'], color='orange', linestyle='--', label='RHS_capped')
        if threshold_data['floors']['delta'] > 0:
            axs[1,1].axhline(y=threshold_data['speed_rhs'], color='purple', linestyle='--', label='RHS_speed')
        axs[1,1].set_title('Threshold Validation Over Time')
        axs[1,1].set_xlabel('Time')
        axs[1,1].set_ylabel('Energy')
        axs[1,1].legend()
        
    else:
        # Single eigenstate plots
        axs[0,0].bar(['√F_Q', 'S_A', 'I(A:Ā)'], [sqrtF, S_A, I_AB], color=['tab:blue', 'tab:green', 'tab:red'])
        axs[0,0].set_title('Triad Components')
        axs[0,0].set_ylabel('Value')
        
        # CORRECTED: Threshold comparison
        axs[0,1].bar(['Energy Triad', 'RHS_capped', 'RHS_speed'], 
                    [threshold_data['energy_triad_lhs'], threshold_data['capped_rhs'], threshold_data['speed_rhs']], 
                    color=['tab:cyan', 'tab:orange', 'tab:purple'])
        axs[0,1].set_title('Threshold Validation')
        axs[0,1].set_ylabel('Energy')
        axs[0,1].axhline(y=threshold_data['energy_triad_lhs'], color='tab:cyan', linestyle='--', alpha=0.7, label='LHS')
        
        # Canonical triad
        axs[1,0].bar(['Π_A'], [Pi], color='tab:cyan')
        axs[1,0].set_title('Canonical Triad')
        axs[1,0].set_ylabel('Rate')
        
        # Threshold satisfaction
        satisfaction = [threshold_data['thresholds_satisfied']['hamiltonian_capped'], 
                       1 if threshold_data['thresholds_satisfied']['speed_based'] else 0 if threshold_data['thresholds_satisfied']['speed_based'] is not None else 0]
        axs[1,1].bar(['Hamiltonian-capped', 'Speed-based'], satisfaction, color=['tab:green', 'tab:red'])
        axs[1,1].set_title('Threshold Satisfaction')
        axs[1,1].set_ylabel('Satisfied (1) / Not Satisfied (0)')
        axs[1,1].set_ylim(0, 1.2)
    
    plt.tight_layout()
    plot_name = f'time_evolution_{stamp}.png' if use_time_evolution else f'eigen_snapshot_{stamp}.png'
    png_path = os.path.join(out_dir, plot_name)
    plt.savefig(png_path, dpi=150)
    plt.close(fig)
    print(f"Saved plot to: {png_path}")
