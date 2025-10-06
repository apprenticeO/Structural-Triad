# esse_xx_integrable_test.py
import numpy as np
import matplotlib.pyplot as plt
from qutip import *
import math
import os, csv
from datetime import datetime

# Parameters
N = 6              # Number of qubits (moderate size for integrable)
J = 1.0            # Coupling strength
hbar = 1.0
t_max = 10
n_points = 500
tlist = np.linspace(0, t_max, n_points)

epsilons = (1e-8, 1e-6, 1e-4)

# Pauli operators and identity
sx, sy, sz = sigmax(), sigmay(), sigmaz()
id2 = qeye(2)

# Helper functions to embed operators
def local_op(op, i, N):
    return tensor([op if j == i else id2 for j in range(N)])

# === A-only helpers for canonical SLD-QFI and generator ===
def local_op_A(op: Qobj, i: int, A_size: int) -> Qobj:
    return tensor([op if j == i else id2 for j in range(A_size)])

def build_HA_on_A_xx(A_size: int, J: float) -> Qobj:
    H = 0
    for i in range(A_size - 1):
        H += J * (local_op_A(sx, i, A_size) * local_op_A(sx, i + 1, A_size) +
                  local_op_A(sy, i, A_size) * local_op_A(sy, i + 1, A_size))
    return H

def qfi_sld_unitary(rho: Qobj, H: Qobj, eps: float = 1e-12) -> float:
    # Canonical SLD-QFI for unitary family e^{-i\theta H}
    evals, evecs = rho.eigenstates()
    p = np.real(np.array(evals, dtype=float))
    # Ensure non-negative and normalized
    p[p < 0] = 0.0
    if p.sum() > 0:
        p = p / p.sum()
    Q = 0.0
    dim = len(p)
    for i in range(dim):
        if p[i] <= eps:
            continue
        vi = evecs[i]
        for j in range(dim):
            pj = p[j]
            if i == j or (p[i] + pj) <= eps:
                continue
            vj = evecs[j]
            hij_q = (vi.dag() * H * vj)
            try:
                hij = complex(hij_q.full()[0, 0])
            except Exception:
                try:
                    hij = complex(hij_q[0, 0])
                except Exception:
                    hij = complex(hij_q)
            mod2 = float(np.abs(hij) ** 2)
            num = (p[i] - pj) ** 2
            den = (p[i] + pj)
            Q += 2.0 * num / den * mod2
    return float(max(0.0, Q))

def xx_hamiltonian(N, J, hz=0.0):
    H = 0
    for i in range(N - 1):
        H += J * (local_op(sx, i, N) * local_op(sx, i+1, N) +
                  local_op(sy, i, N) * local_op(sy, i+1, N))
    if hz != 0.0:
        for i in range(N):
            H += hz * local_op(sz, i, N)
    return H

def level_spacing_ratio(H: Qobj) -> float:
    e = np.sort(H.eigenenergies())
    s = np.diff(e)
    eps = 1e-12
    s = s[np.abs(s) > eps]
    if s.size < 2:
        return float('nan')
    a, b = s[:-1], s[1:]
    denom = np.maximum(np.abs(a), np.abs(b))
    mask = denom > eps
    if not np.any(mask):
        return float('nan')
    ratios = np.minimum(np.abs(a[mask]), np.abs(b[mask])) / denom[mask]
    return float(np.nanmean(ratios))

# Build Hamiltonian (integrable XX model)
H = xx_hamiltonian(N, J)

# r diagnostic (robust, reporting-only)
r = level_spacing_ratio(H)
if np.isnan(r):
    print("Level-spacing r: n/a (degenerate/too-few-gaps). ESSE metrics are unaffected.")
    try:
        eps = 1e-9
        rng = np.random.default_rng(41)
        jitter = 0
        for i in range(N):
            jitter += float(rng.normal()) * local_op(sz, i, N)
        r_eps = level_spacing_ratio(H + eps*jitter)
        if not np.isnan(r_eps):
            print(f"Level-spacing r_robust ≈ {r_eps:.3f} (ε-jitter diagnostic)")
    except Exception:
        pass
else:
    print(f"Level-spacing r ≈ {r:.3f} (integrable ≲ 0.39, GOE ~0.53)")

# Initial state: product state in z-basis (eigenstates of conserved quantities)
# Try |010101⟩ for maximum suppression
initial_bits = [i % 2 for i in range(N)]  # Alternating ↑↓
kets = [basis(2, b) for b in initial_bits]
psi0 = tensor(kets)

# Define subsystem A (e.g., first 2 qubits)
A_sites = [0, 1]

# Build H_A for subsystem A with 1/2 splitting of boundary couplings
H_A = 0
for i in A_sites:
    # No on-site fields in pure XX baseline
    pass
# Internal XX couplings within A (FULL weight)
for i in range(len(A_sites)-1):
    a = A_sites[i]; b = A_sites[i+1]
    H_A += J * (local_op(sx, a, N) * local_op(sx, b, N) +
                local_op(sy, a, N) * local_op(sy, b, N))
# Boundary coupling to B: (A_last, A_last+1) if exists with 1/2 splitting
last = A_sites[-1]
if last + 1 < N:
    H_A += 0.5 * J * (local_op(sx, last, N) * local_op(sx, last+1, N) +
                      local_op(sy, last, N) * local_op(sy, last+1, N))

# A-only generator for canonical QFI
H_A_on_A = build_HA_on_A_xx(len(A_sites), J)
try:
    H_norm_A = float(H_A_on_A.norm('spectral'))
except Exception:
    try:
        H_norm_A = float(np.max(np.abs(np.real(np.asarray(H_A_on_A.eigenenergies(), dtype=float)))))
    except Exception:
        H_norm_A = 0.0

# Time evolution
result = sesolve(H, psi0, tlist)
states = result.states

# Storage
S_list = []
I_list = []
sqrtF_list = []
psi_hat_list = []
delta_HA_list = []
Pi_list = []
comm_list = []
d_list = []

for ket in states:
    rho = ket2dm(ket)

    # Reduced density matrix for subsystem A
    rho_A = rho.ptrace(A_sites)
    S = entropy_vn(rho_A, base=np.e)
    S_list.append(S)

    # Mutual information I(A:Ā)
    bar_sites = [i for i in range(N) if i not in A_sites]
    rho_B = rho.ptrace(bar_sites)
    S_B = entropy_vn(rho_B, base=np.e)
    S_AB = entropy_vn(rho, base=np.e)
    I_val = S + S_B - S_AB
    I_list.append(float(max(0.0, I_val)))

    # Energy fluctuation ΔH_A (FULL state)
    exp_H = expect(H_A, rho)
    exp_H2 = expect(H_A * H_A, rho)
    var = max(0.0, np.real(exp_H2 - exp_H**2))
    delta_H = np.sqrt(var)
    delta_HA_list.append(delta_H)

    # ESSE activity Π(t)
    Pi_t = (4 / hbar) * delta_H * (S ** 2)
    Pi_list.append(Pi_t)

    # Commutator norm ‖[H_A, ρ]‖_F
    comm = H_A * rho - rho * H_A
    comm_list.append(float(comm.norm('fro')))

    # Trace distance to product
    sigma = tensor(rho_A, rho_B)
    # Reorder sigma to match [0..N-1]
    concat = A_sites + bar_sites
    perm = [concat.index(i) for i in range(N)]
    sigma_full = sigma.permute(perm)
    diff = rho - sigma_full
    try:
        d = float(diff.norm('tr'))
    except Exception:
        d = float(diff.norm('fro'))
    d_list.append(d)

    # Canonical SLD-QFI on A-only generator
    QFI = qfi_sld_unitary(rho_A, H_A_on_A)
    sqrtF = float(np.sqrt(max(0.0, QFI)))
    sqrtF_list.append(sqrtF)

    # Intensive normalized triad Ψ̂
    dA = 2 ** len(A_sites)
    dbar = 2 ** (N - len(A_sites))
    dmin = min(dA, dbar)
    if H_norm_A > 0 and dA > 1 and dmin > 1:
        psi_hat = (hbar * sqrtF) / (2.0 * H_norm_A)
        psi_hat *= (S / np.log(dA))
        psi_hat *= (I_val / (2.0 * np.log(dmin)))
        psi_hat_list.append(float(max(0.0, np.real(psi_hat))))
    else:
        psi_hat_list.append(0.0)

# Aggregate metrics
comm_arr = np.array(comm_list)
d_arr = np.array(d_list)
P_arr = np.array(Pi_list)

# v0(A) from H_A gap (boundary-split full-space local generator)
evals = np.sort(np.real(np.asarray(H_A.eigenenergies(), dtype=float)))
gaps = np.diff(evals)
gaps = gaps[gaps > 1e-12]
deltaE = float(np.min(gaps)) if gaps.size > 0 else 0.0
v0 = 0.25*deltaE

# δ_A counts frames where comm_norm>ε AND ΔH_A ≥ v0
dH_arr = np.array(delta_HA_list)
good_var = dH_arr >= v0
deltaA = {e: float(np.mean(np.logical_and(comm_arr > e, good_var))) for e in epsilons}
d4 = d_arr**4
cums = np.cumsum(d4)
avg = cums/(np.arange(len(d4))+1)
w = max(1, len(d4)//8)
lim = np.array([np.min(avg[max(0,i-w+1):i+1]) for i in range(len(d4))])
tau4 = float(lim[-1])

# perC with c_lin=0.5 (nats)
c_lin = 0.5
perC_A = (4.0/hbar) * v0 * (c_lin**2) * deltaA[1e-6] * tau4

# === Canonical structural thresholds (Elephant Eqs. 308 & 343) ===
I_arr = np.array(I_list) if I_list else np.zeros_like(dH_arr)
S_arr = np.array(S_list) if S_list else np.zeros_like(dH_arr)
sqrtF_arr = np.array(sqrtF_list) if sqrtF_list else np.zeros_like(dH_arr)
energy_triad_lhs = float(np.mean(dH_arr * S_arr * I_arr)) if dH_arr.size else 0.0

# Capped RHS: 2 (log d_min)^2 ||H_A||_op ⟨Ψ̂⟩
dA = 2 ** len(A_sites)
dbar = 2 ** (N - len(A_sites))
dmin = min(dA, dbar)
psi_hat_mean = float(np.mean(psi_hat_list)) if psi_hat_list else 0.0
rhs_capped = 2.0 * (np.log(dmin)**2) * H_norm_A * psi_hat_mean

# Speed-based RHS: (ħ/2) δ ε_F ε_S ε_I with floors from time series (q10)
if sqrtF_arr.size:
    epsF = float(np.quantile(sqrtF_arr, 0.10))
    epsS = float(np.quantile(S_arr, 0.10))
    epsI = float(np.quantile(I_arr, 0.10))
else:
    epsF = epsS = epsI = 0.0
mask_all = (sqrtF_arr >= epsF) & (S_arr >= epsS) & (I_arr >= epsI) if sqrtF_arr.size else np.array([False])
delta_speed = float(np.mean(mask_all)) if mask_all.size else 0.0
rhs_speed = 0.5 * hbar * delta_speed * epsF * epsS * epsI

# Outputs directory
out_dir = os.path.join(os.path.dirname(__file__), 'plots', 'integrable')
os.makedirs(out_dir, exist_ok=True)
stamp = datetime.now().strftime('%Y%m%d_%H%M%S')

# Plotting and save
plt.figure(figsize=(10, 6))
plt.plot(tlist, Pi_list, label="Π(t)", alpha=0.6)
Pi_avg = np.cumsum(P_arr) / np.arange(1, len(P_arr)+1)
plt.plot(tlist, Pi_avg, label="Time-averaged $\\overline{\\Pi}(T)$", linewidth=2, color='orange')
plt.axhline(y=Pi_avg[-1], color='red', linestyle='--', label=f"Final $c \\approx$ {Pi_avg[-1]:.4f}")
plt.xlabel("Time t")
plt.ylabel("Quantum Activity $\\Pi$")
plt.title("ESSE Activity for Integrable XX Chain\nInitial State: Alternating Product |010101⟩")
plt.legend(); plt.grid(True); plt.tight_layout()
png_path = os.path.join(out_dir, f'xx_integrable_N{N}_{stamp}.png')
plt.savefig(png_path, dpi=150)
plt.close()

# Save CSV summary
csv_path = os.path.join(out_dir, f'xx_integrable_N{N}_{stamp}.csv')
with open(csv_path, 'w', newline='') as f:
    w = csv.writer(f)
    w.writerow(["t","S_A","DeltaH_A","Pi","Pi_avg"])
    for i, t in enumerate(tlist):
        w.writerow([t, S_list[i], delta_HA_list[i], Pi_list[i], Pi_avg[i]])

# Save canonical thresholds summary
thr_csv = os.path.join(out_dir, f'xx_integrable_thresholds_N{N}_{stamp}.csv')
with open(thr_csv, 'w', newline='') as f:
    w = csv.writer(f)
    w.writerow(["N","A_size","LHS_energy_triad","RHS_capped","RHS_speed","psi_hat_mean","delta_speed","H_norm_A","dmin"]) 
    w.writerow([N, len(A_sites), energy_triad_lhs, rhs_capped, rhs_speed, psi_hat_mean, delta_speed, H_norm_A, dmin])

# Print result
print("="*50)
print("FINAL ESSE ANALYSIS (XX integrable):")
print(f"Final ⟨Π⟩_T = {Pi_avg[-1]:.6f}")
print(f"δ_A ladder: {deltaA}")
print(f"τ_A^4 = {tau4:.6e}")
print(f"v0(A) ≈ 0.25·ΔE_min = {v0:.6e}")
print(f"perC_A ≈ {perC_A:.6e}")
print(f"Canonical thresholds: LHS={energy_triad_lhs:.6f}, RHS_capped={rhs_capped:.6f}, RHS_speed={rhs_speed:.6f}, ⟨Ψ̂⟩={psi_hat_mean:.6f}, δ={delta_speed:.3f}")
print(f"Saved plot: {png_path}")
print(f"Saved CSV:  {csv_path}")
print(f"Saved thresholds CSV: {thr_csv}")
print("="*50)
