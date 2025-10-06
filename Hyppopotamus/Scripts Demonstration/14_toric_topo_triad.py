#!/usr/bin/env python3
from __future__ import annotations
import os, json, math
from dataclasses import dataclass, asdict
from typing import List, Tuple, Dict

import numpy as np
from qutip import Qobj, qeye, sigmax, sigmaz, tensor, entropy_vn
try:
    import matplotlib.pyplot as plt  # type: ignore
except Exception:
    plt = None
import csv


# -------------------------------
# Toric code on an LxL torus (qubits on edges)
# -------------------------------


def edge_index_map(L: int):
    """Return helpers to map (x,y,dir) -> linear index in [0, 2*L*L).
    dir = 'h' for horizontal edge from (x,y) to (x+1,y),
          'v' for vertical edge from (x,y) to (x,y+1).
    """
    def idx_h(x: int, y: int) -> int:
        return y * L + x

    def idx_v(x: int, y: int) -> int:
        return L * L + y * L + x

    def wrap(a: int) -> int:
        return a % L

    return idx_h, idx_v, wrap


def local_op(op: Qobj, i: int, N: int) -> Qobj:
    ops = [qeye(2)] * N
    ops[i] = op
    return tensor(ops)


def build_av(L: int) -> List[Tuple[Tuple[int, str], ...]]:
    """Star operators A_v as lists of (edge_index, 'x') acting with sigma^x."""
    idx_h, idx_v, w = edge_index_map(L)
    stars: List[Tuple[Tuple[int, str], ...]] = []
    for x in range(L):
        for y in range(L):
            # Edges incident to vertex (x,y): left/right horizontal, down/up vertical
            e1 = (idx_h(w(x - 1), y), 'x')  # horizontal left of v
            e2 = (idx_h(x, y), 'x')         # horizontal right of v
            e3 = (idx_v(x, w(y - 1)), 'x')  # vertical below v
            e4 = (idx_v(x, y), 'x')         # vertical above v
            stars.append((e1, e2, e3, e4))
    return stars


def build_bp(L: int) -> List[Tuple[Tuple[int, str], ...]]:
    """Plaquette operators B_p as lists of (edge_index, 'z') acting with sigma^z."""
    idx_h, idx_v, w = edge_index_map(L)
    pls: List[Tuple[Tuple[int, str], ...]] = []
    for x in range(L):
        for y in range(L):
            # Plaquette with lower-left corner at (x,y)
            # Order: bottom h(x,y), right v(x+1,y), top h(x,y+1), left v(x,y)
            e1 = (idx_h(x, y), 'z')
            e2 = (idx_v(w(x + 1), y), 'z')
            e3 = (idx_h(x, w(y + 1)), 'z')
            e4 = (idx_v(x, y), 'z')
            pls.append((e1, e2, e3, e4))
    return pls


def build_operator_from_edges(L: int, ops: Tuple[Tuple[int, str], ...]) -> Qobj:
    N = 2 * L * L
    out = None
    for idx, kind in ops:
        term = local_op(sigmax() if kind == 'x' else sigmaz(), idx, N)
        out = term if out is None else out * term
    assert out is not None
    return out


def build_hamiltonian(L: int, Je: float, Jm: float) -> Qobj:
    N = 2 * L * L
    # Initialize a zero operator with correct dims (avoids int->Qobj coercion)
    H = 0 * local_op(sigmaz(), 0, N)
    for star in build_av(L):
        H += -Je * build_operator_from_edges(L, star)
    for plaq in build_bp(L):
        H += -Jm * build_operator_from_edges(L, plaq)
    return H


def logical_wilson_loops(L: int) -> Dict[str, Qobj]:
    idx_h, idx_v, w = edge_index_map(L)
    # Z-loop around x direction (horizontal ring at y=0)
    loop_z = tuple((idx_h(x, 0), 'z') for x in range(L))
    # X-loop around y direction (vertical ring at x=0)
    loop_x = tuple((idx_v(0, y), 'x') for y in range(L))
    return {
        'Wz_x': build_operator_from_edges(L, loop_z),
        'Wx_y': build_operator_from_edges(L, loop_x),
    }


def ground_space(H: Qobj, tol: float = 1e-8) -> List[Qobj]:
    evals, evecs = H.eigenstates()
    Emin = float(np.min(np.real(evals)))
    gs = []
    for val, vec in zip(evals, evecs):
        if abs(np.real(val) - Emin) <= tol:
            gs.append(vec.unit())
    return gs


def projector(psi: Qobj) -> Qobj:
    return psi * psi.dag()


def region_edges_half_x(L: int) -> List[int]:
    idx_h, idx_v, _ = edge_index_map(L)
    edges: List[int] = []
    for x in range(L):
        for y in range(L):
            if x < (L // 2):
                edges.append(idx_h(x, y))
                edges.append(idx_v(x, y))
    return edges


def reduced_state(rho: Qobj, keep: List[int], L: int) -> Qobj:
    N = 2 * L * L
    keep_sorted = sorted(keep)
    return rho.ptrace(keep_sorted)


def mutual_information(rho: Qobj, A_idx: List[int], L: int) -> float:
    N = 2 * L * L
    A_sorted = sorted(A_idx)
    B_sorted = [i for i in range(N) if i not in A_sorted]
    rho_A = rho.ptrace(A_sorted)
    rho_B = rho.ptrace(B_sorted)
    SA = float(entropy_vn(rho_A, base=np.e))
    SB = float(entropy_vn(rho_B, base=np.e))
    SAB = float(entropy_vn(rho, base=np.e))
    return SA + SB - SAB


@dataclass
class Result:
    L: int
    N_qubits: int
    Je: float
    Jm: float
    state: str  # 'pure-gs' or 'mixed-gs' or 'thermal'
    degeneracy: int
    SA: float
    IAB: float
    Delta_x: float
    Delta_z: float
    Wx_expect: float
    Wz_expect: float
    Pi_topo_x: float
    Pi_topo_z: float
    entropy_base: str
    loop_defs: Dict[str, str]


def run(L: int = 2, Je: float = 1.0, Jm: float = 1.0, state: str = 'mixed-gs', beta: float | None = None) -> Result:
    N = 2 * L * L
    H = build_hamiltonian(L, Je, Jm)
    gs = ground_space(H)
    assert gs, 'No ground states found'

    if state == 'pure-gs':
        rho = projector(gs[0])
    elif state == 'mixed-gs':
        # Equal mixture over ground space to expose logical fluctuations
        rho = sum(projector(v) for v in gs) / len(gs)
    elif state == 'thermal':
        assert beta is not None and beta >= 0.0, 'thermal state requires nonnegative beta'
        X = (-beta * H).expm()
        rho = X / X.tr()
    else:
        raise ValueError("state must be one of {'pure-gs','mixed-gs','thermal'}")

    loops = logical_wilson_loops(L)
    # Variances of Wilson loops (Pauli strings): L^2 = I => Var(L) = 1 - <L>^2
    def variance(op: Qobj) -> float:
        exp = float((op * rho).tr().real)
        return math.sqrt(max(1.0 - exp * exp, 0.0))

    # Expectations and variances
    Wx_exp = float((loops['Wx_y'] * rho).tr().real)
    Wz_exp = float((loops['Wz_x'] * rho).tr().real)
    Dx = math.sqrt(max(1.0 - Wx_exp * Wx_exp, 0.0))
    Dz = math.sqrt(max(1.0 - Wz_exp * Wz_exp, 0.0))

    A_idx = region_edges_half_x(L)
    rho_A = reduced_state(rho, A_idx, L)
    SA = float(entropy_vn(rho_A, base=np.e))
    IAB = float(mutual_information(rho, A_idx, L))

    Pi_x = Dx * SA * IAB
    Pi_z = Dz * SA * IAB

    return Result(
        L=L,
        N_qubits=N,
        Je=Je,
        Jm=Jm,
        state=state,
        degeneracy=len(gs),
        SA=SA,
        IAB=IAB,
        Delta_x=Dx,
        Delta_z=Dz,
        Wx_expect=Wx_exp,
        Wz_expect=Wz_exp,
        Pi_topo_x=Pi_x,
        Pi_topo_z=Pi_z,
        entropy_base='nats',
        loop_defs={
            'Wz_x': 'Z loop around x-direction (horizontal ring at y=0)',
            'Wx_y': 'X loop around y-direction (vertical ring at x=0)'
        },
    )


def main():
    import argparse
    ap = argparse.ArgumentParser(description='Toric-code generalized triad (proof-of-concept)')
    ap.add_argument('--L', type=int, default=2)
    ap.add_argument('--Je', type=float, default=1.0)
    ap.add_argument('--Jm', type=float, default=1.0)
    ap.add_argument('--state', type=str, default='mixed-gs', choices=['pure-gs', 'mixed-gs', 'thermal'])
    ap.add_argument('--beta', type=float, default=None, help='Inverse temperature for thermal state')
    ap.add_argument('--out-prefix', type=str, default=os.path.join(os.path.dirname(__file__), '..', 'Annex results', 'A14', 'toric_topo_triad'))
    args = ap.parse_args()

    os.makedirs(os.path.dirname(args.out_prefix), exist_ok=True)
    res = run(L=args.L, Je=args.Je, Jm=args.Jm, state=args.state, beta=args.beta)

    out_json = f"{args.out_prefix}_L{args.L}_{args.state}.json"
    with open(out_json, 'w') as f:
        json.dump(asdict(res), f, indent=2)

    # Minimal CSV for annex
    out_csv = f"{args.out_prefix}_summary.csv"
    header = 'L,N_qubits,degeneracy,Je,Jm,state,SA,IAB,Delta_x,Delta_z,Wx_expect,Wz_expect,Pi_topo_x,Pi_topo_z,entropy_base'\
        if not os.path.exists(out_csv) else None
    with open(out_csv, 'a') as f:
        if header:
            f.write(header + "\n")
        f.write(
            f"{res.L},{res.N_qubits},{res.degeneracy},{res.Je},{res.Jm},{res.state},{res.SA:.6f},{res.IAB:.6f},{res.Delta_x:.6f},{res.Delta_z:.6f},{res.Wx_expect:.6f},{res.Wz_expect:.6f},{res.Pi_topo_x:.6f},{res.Pi_topo_z:.6f},{res.entropy_base}\n"
        )

    print(json.dumps(asdict(res), indent=2))
    print(f"Saved: {out_json}")
    print(f"Appended: {out_csv}")

    # Quick visualization for the latest run (bar chart of legs and Π_topo)
    try:
        if plt is not None:
            labels = ['S_A', 'I(A:Ā)', 'Δ_x', 'Δ_z', 'Π_x', 'Π_z']
            vals = [res.SA, res.IAB, res.Delta_x, res.Delta_z, res.Pi_topo_x, res.Pi_topo_z]
            fig, ax = plt.subplots(figsize=(6, 3.2))
            ax.bar(range(len(labels)), vals, color=['#1f77b4','#2ca02c','#ff7f0e','#ff7f0e','#9467bd','#8c564b'])
            ax.set_xticks(range(len(labels)))
            ax.set_xticklabels(labels)
            ax.set_ylabel('value')
            ax.set_title(f'Toric triad summary (L={res.L}, state={res.state})')
            ax.grid(axis='y', alpha=0.2)
            png = f"{args.out_prefix}_L{res.L}_{res.state}.png"
            fig.tight_layout(); fig.savefig(png, dpi=150)
            plt.close(fig)
            print(f"Saved plot: {png}")
    except Exception:
        pass


if __name__ == '__main__':
    main()


