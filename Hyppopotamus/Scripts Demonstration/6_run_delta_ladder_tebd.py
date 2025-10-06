#!/usr/bin/env python3
import json, os
from dataclasses import dataclass, asdict
from typing import List, Tuple, Dict, Optional
import numpy as np
import quimb.tensor as qtn

# Canonical SLD-QFI helpers (adapted from A4)
def _partial_trace_rho(rho: np.ndarray, L: int, keep: list[int]) -> np.ndarray:
    rho_t = rho.reshape([2] * (2 * L))
    keep_set = set(keep)
    for k in range(L - 1, -1, -1):
        if k not in keep_set:
            half = rho_t.ndim // 2
            rho_t = np.trace(rho_t, axis1=k, axis2=half + k)
    return rho_t.reshape(2 ** len(keep), 2 ** len(keep))

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

def build_dense_HA_on_A(ell: int, J: float = 1.0, h: float = 0.0) -> np.ndarray:
    id2 = np.eye(2, dtype=complex)
    sx = np.array([[0, 1], [1, 0]], dtype=complex)
    sy = np.array([[0, -1j], [1j, 0]], dtype=complex)
    sz = np.array([[1, 0], [0, -1]], dtype=complex)
    H = np.zeros((2 ** ell, 2 ** ell), dtype=complex)
    if h != 0.0:
        for i in range(ell):
            ops = [id2] * ell
            ops[i] = sz
            term = ops[0]
            for k in range(1, ell):
                term = np.kron(term, ops[k])
            H = H + h * term
    for i in range(ell - 1):
        for A, B in (sx, sx), (sy, sy), (sz, sz):
            ops = [id2] * ell
            ops[i] = A
            ops[i + 1] = B
            term = ops[0]
            for k in range(1, ell):
                term = np.kron(term, ops[k])
            H = H + J * term
    return H

@dataclass
class DeltaResult:
    L: int; ell: int; J: float; h: float; dt: float; steps: int; chi: int; cut: float
    epsilons: List[float]
    # Dual witness (commutator) ladder
    delta_ladder_comm: Dict[str, List[float]]
    # Operator norm per A and norm-cap ladder (variance-only)
    opnormA: List[float]
    delta_ladder_opnorm: Dict[str, List[float]]
    # Full triad ladder requiring (ΔH_A ≥ α||H_A||_op) & entropy & MI floors
    triad_ladder: Dict[str, List[float]]
    # CORRECTED: Canonical triad components and values
    triad_values: List[List[float]]  # Π_A values for each A at each time step
    sqrtF_values: List[List[float]]  # √F_Q values for each A at each time step
    S_values: List[List[float]]      # S_A values for each A at each time step
    I_values: List[List[float]]     # I(A:Ā) values for each A at each time step
    # Speed-based structural threshold components
    epsF: float               # Proxy floor for √F_Q
    epsS: float               # Proxy floor for S_A
    epsI: float               # Proxy floor for I(A:Ā)
    delta: float              # Fraction of good times
    rhs_speed: float          # Speed-based RHS bound
    # Optional: legacy gap-based floor for diagnostics
    v0A: Optional[List[float]] = None
    # Notes
    notes: Optional[Dict[str, bool]] = None


def entanglement_entropy_nats(mps, A: int) -> float:
    """Bond entropy across cut after site A (between sites A and A+1), in nats.
    Quimb's MPS.entropy expects bond index i with 1 <= i <= L-1 for an L-site chain.
    """
    if not (1 <= A <= mps.L - 1):
        return 0.0
    return float(mps.entropy(A)) * float(np.log(2.0))


def build_v0_list(L: int, ell: int, J: float=1.0, h: float=0.0) -> List[float]:
    v0 = []
    for A in range(1, ell+1):
        # small H_A on A only: z-field + internal bonds; boundary split ignored (conservative)
        id2 = np.eye(2, dtype=complex)
        sz = np.array([[1,0],[0,-1]], dtype=complex)
        H = np.zeros((2**A, 2**A), dtype=complex)
        if h != 0.0:
            for i in range(A):
                ops = [id2]*A; ops[i] = sz
                term = ops[0]
                for k in range(1, A): term = np.kron(term, ops[k])
                H += h*term
        for i in range(A-1):
            for P in (np.array([[0,1],[1,0]]), np.array([[0,-1j],[1j,0]]), sz):
                Q = P
                ops = [id2]*A; ops[i]=P; ops[i+1]=Q
                term = ops[0]
                for k in range(1, A): term = np.kron(term, ops[k])
                H += J*term
        evals = np.linalg.eigvalsh(H)
        gaps = np.diff(np.sort(evals))
        gaps = gaps[gaps > 1e-12]
        dE = float(np.min(gaps)) if gaps.size>0 else 0.0
        v0.append(0.25*dE)
    return v0


def run_delta_ladder(L: int, ell: int, J: float, h: float, dt: float, steps: int, chi: int, cut: float,
                     epsilons: List[float], sample_k: int, alpha: float,
                     S_floor: float, I_floor: float, use_norm: bool, report_gap: bool) -> DeltaResult:
    H_local = qtn.ham_1d_heis(L=L, j=J, bz=h, S=0.5, cyclic=False)
    psi = qtn.MPS_computational_state(''.join('01'[i%2] for i in range(L)))
    tebd = qtn.TEBD(psi, H_local, dt=dt, split_opts={'max_bond': chi, 'cutoff': cut}, imag=False)

    # Build full-space H_A per A and their opnorms
    def build_full_HA(A: int):
        id2 = np.eye(2, dtype=complex)
        sz = np.array([[1,0],[0,-1]], dtype=complex)
        sx = np.array([[0,1],[1,0]], dtype=complex)
        sy = np.array([[0,-1j],[1j,0]], dtype=complex)
        H = np.zeros((2**L, 2**L), dtype=complex)
        if h != 0.0:
            for i in range(A):
                ops = [id2]*L; ops[i]=sz
                term = ops[0]
                for k in range(1, L): term = np.kron(term, ops[k])
                H += h*term
        for i in range(L-1):
            left_in = (i < A); right_in = (i + 1 < A)
            w = (J if (left_in and right_in) else (0.5*J if (left_in ^ right_in) else 0.0))
            if w == 0.0: continue
            for P in (sx, sy, sz):
                Q = P
                ops = [id2]*L; ops[i]=P; ops[i+1]=Q
                term = ops[0]
                for k in range(1, L): term = np.kron(term, ops[k])
                H += w*term
        return H

    H_list = [build_full_HA(A) for A in range(1, ell+1)]
    opnormA = [float(np.max(np.abs(np.linalg.eigvalsh(H_list[A-1])))) for A in range(1, ell+1)]

    # Precompute H_A on A only for SLD-QFI
    H_on_A_list = [build_dense_HA_on_A(A, J, h) for A in range(1, ell+1)]

    # Optionally compute v0 gap floors
    v0_list = build_v0_list(L, ell, J, h) if report_gap else None

    # Counters
    counts_comm = {str(e): [0]*ell for e in epsilons}
    counts_normcap = {f"alpha={alpha}": [0]*ell}
    key_triad = f"alpha={alpha},S={S_floor},I={I_floor},normed={1 if use_norm else 0}"
    counts_triad = {key_triad: [0]*ell}
    totals = 0

    def get_mps():
        return getattr(tebd, 'pt', None) or getattr(tebd, 'psi', None)

    # CORRECTED: Add canonical triad calculations
    triad_values = []
    sqrtF_values = []
    S_values = []
    I_values = []
    
    # Calculate proxy floors (10th percentile)
    all_sqrtF = []
    all_S = []
    all_I = []
    good_times = 0
    total_samples = 0

    for step in range(1, steps+1):
        tebd.step()
        if step % sample_k != 0:
            continue
        totals += 1
        mps = get_mps()
        psi_dense = mps.to_dense()
        rho = np.outer(psi_dense, psi_dense.conj())

        # CORRECTED: Calculate canonical triad for each A
        step_triad_values = []
        step_sqrtF_values = []
        step_S_values = []
        step_I_values = []
        
        for A in range(1, ell+1):
            H_A = H_list[A-1]
            # variance on full state
            E1 = float(np.vdot(psi_dense, H_A @ psi_dense))
            E2 = float(np.vdot(psi_dense, H_A @ (H_A @ psi_dense)))
            var = max(E2 - E1*E1, 0.0)
            dH = float(np.sqrt(var))
            
            # Canonical √F_Q from SLD-QFI on reduced ρ_A with H_A on A
            A_sites = list(range(A))
            rho_A = _partial_trace_rho(rho, L, A_sites)
            H_A_on_A = H_on_A_list[A-1]
            F = qfi_sld_unitary(rho_A, H_A_on_A)
            sqrtF = float(np.sqrt(max(F, 0.0)))
            
            # CORRECTED: Calculate complete mutual information
            S_A = entanglement_entropy_nats(mps, A)
            S_Abar = entanglement_entropy_nats(mps, L - A)  # Complement entropy
            
            # CORRECTED: Compute S_AB (global entropy) for complete mutual information
            rho_global = np.outer(psi_dense, psi_dense.conj())
            rho_global = 0.5 * (rho_global + rho_global.conj().T)  # Ensure Hermitian
            vals_global = np.clip(np.linalg.eigvalsh(rho_global), 0.0, 1.0)
            nz_global = vals_global[vals_global > 1e-12]
            S_AB = float(-np.sum(nz_global * np.log(nz_global))) if len(nz_global) > 0 else 0.0
            
            I_AB = S_A + S_Abar - S_AB  # Complete general formula: I(A:Ā) = S_A + S_Ā - S_{AĀ}
            
            # CORRECTED: Canonical triad calculation (no ℏ factor, matches LaTeX Eq. 78)
            Pi_A = sqrtF * S_A * I_AB  # Main triad: √F_Q · S_A · I(A:Ā)
            
            step_triad_values.append(Pi_A)
            step_sqrtF_values.append(sqrtF)
            step_S_values.append(S_A)
            step_I_values.append(I_AB)
            
            # Collect for proxy floors
            all_sqrtF.append(sqrtF)
            all_S.append(S_A)
            all_I.append(I_AB)
            
            # Check if this is a "good time" (all components above floors)
            if sqrtF > 0 and S_A > 0 and I_AB > 0:
                good_times += 1
            total_samples += 1
            
            # Original commutator and norm-cap logic (preserved)
            HA_rho = H_A @ rho; rho_HA = rho @ H_A
            comm = HA_rho - rho_HA
            comm_fro = float(np.linalg.norm(comm))
            for e in epsilons:
                if comm_fro > e:
                    counts_comm[str(e)][A-1] += 1

            # Norm-cap condition
            if dH >= alpha * opnormA[A-1]:
                counts_normcap[f"alpha={alpha}"][A-1] += 1

            # Triad legs: S_A and I=2S_A for pure global (legacy logic preserved)
            SA = entanglement_entropy_nats(mps, A)
            IA = 2.0 * SA
            if use_norm:
                logd = (A * np.log(2.0))
                SA_cmp = SA / max(logd, 1e-12)
                IA_cmp = IA / max(2.0*logd, 1e-12)
                S_ok = (SA_cmp >= S_floor)
                I_ok = (IA_cmp >= I_floor)
            else:
                S_ok = (SA >= S_floor)
                I_ok = (IA >= I_floor)
            if (dH >= alpha * opnormA[A-1]) and S_ok and I_ok:
                counts_triad[key_triad][A-1] += 1
        
        # Store step values
        triad_values.append(step_triad_values)
        sqrtF_values.append(step_sqrtF_values)
        S_values.append(step_S_values)
        I_values.append(step_I_values)

    # CORRECTED: Calculate proxy floors (10th percentile)
    use_min = bool(globals().get('USE_MIN_POSITIVE', False))
    if use_min:
        def min_pos(arr):
            arr = np.array(arr, dtype=float)
            arr = arr[arr > 0]
            return float(arr.min()) if arr.size else 0.0
        epsF = min_pos(all_sqrtF) if all_sqrtF else 0.0
        epsS = min_pos(all_S) if all_S else 0.0
        epsI = min_pos(all_I) if all_I else 0.0
    else:
        epsF = float(np.percentile(all_sqrtF, 10)) if all_sqrtF else 0.0
        epsS = float(np.percentile(all_S, 10)) if all_S else 0.0
        epsI = float(np.percentile(all_I, 10)) if all_I else 0.0
    delta = (good_times / total_samples) if total_samples > 0 else 0.0
    
    # CORRECTED: Calculate speed-based RHS bound (matches LaTeX Eq. 331)
    hbar = 1.0  # Natural units
    rhs_speed = (hbar / 2.0) * epsF * epsS * epsI * delta

    # Fractions
    delta_comm = {k: [ (counts_comm[k][i]/totals if totals>0 else 0.0) for i in range(ell) ] for k in counts_comm}
    delta_normcap = {k: [ (counts_normcap[k][i]/totals if totals>0 else 0.0) for i in range(ell) ] for k in counts_normcap}
    delta_triad = {k: [ (counts_triad[k][i]/totals if totals>0 else 0.0) for i in range(ell) ] for k in counts_triad}

    return DeltaResult(L=L, ell=ell, J=J, h=h, dt=dt, steps=steps, chi=chi, cut=cut,
                       epsilons=epsilons, delta_ladder_comm=delta_comm,
                       opnormA=opnormA, delta_ladder_opnorm=delta_normcap,
                       triad_ladder=delta_triad, triad_values=triad_values,
                       sqrtF_values=sqrtF_values, S_values=S_values, I_values=I_values,
                       epsF=epsF, epsS=epsS, epsI=epsI, delta=delta, rhs_speed=rhs_speed,
                       v0A=v0_list, notes={"pure_state": True, "I_equals_2S": True})


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser(description='ESSE δ_A ladders via operator-norm cap and triad condition (TEBD) - CORRECTED')
    ap.add_argument('--L', type=int, default=12)
    ap.add_argument('--ell', type=int, default=8)
    ap.add_argument('--J', type=float, default=1.0)
    ap.add_argument('--h', type=float, default=0.0)
    ap.add_argument('--dt', type=float, default=0.05)
    ap.add_argument('--steps', type=int, default=150)
    ap.add_argument('--chi', type=int, default=128)
    ap.add_argument('--cut', type=float, default=1e-9)
    ap.add_argument('--eps', type=float, nargs='+', default=[1e-8, 1e-6, 1e-4])
    ap.add_argument('--sample-k', type=int, default=10)
    ap.add_argument('--alpha', type=float, default=1.0)
    ap.add_argument('--S-floor', type=float, default=0.0, dest='S_floor')
    ap.add_argument('--I-floor', type=float, default=0.0, dest='I_floor')
    ap.add_argument('--use-normalized-entropies', action='store_true')
    ap.add_argument('--no-percentile', action='store_true', help='Use min-positive floors instead of percentile floors')
    ap.add_argument('--report-gap-floor', action='store_true')
    ap.add_argument('--out-prefix', type=str, default='results/esse_delta_ladder')
    args = ap.parse_args()

    os.makedirs(os.path.dirname(args.out_prefix), exist_ok=True)
    # Wire a flag through by monkey-patching global behavior (simple approach to avoid signature churn)
    globals()['USE_MIN_POSITIVE'] = bool(args.no_percentile)
    res = run_delta_ladder(args.L, args.ell, args.J, args.h, args.dt, args.steps, args.chi, args.cut,
                           args.eps, args.sample_k, args.alpha, args.S_floor, args.I_floor,
                           args.use_normalized_entropies, args.report_gap_floor)
    outj = f"{args.out_prefix}_L{args.L}_ell{args.ell}_k{args.sample_k}.json"
    with open(outj, 'w') as f:
        json.dump(asdict(res), f, indent=2)
    print(json.dumps(asdict(res), indent=2))
