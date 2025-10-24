#!/usr/bin/env python3
import argparse
import csv
import json
import math
from dataclasses import dataclass, asdict


HBAR = 1.054_571_817e-34  # J*s
LN2 = math.log(2.0)


@dataclass
class QubitToyInputs:
    frequency_ghz: float = 5.0
    T1_microseconds: float = 100.0
    T2_microseconds: float | None = None
    entropy_S_nats: float = 1.0
    mutual_information_nats: float = 0.1
    active_epoch_density: float = 0.3
    subsystem_dim_dA: int = 2
    complement_min_dim_dbar_min: int = 2
    theta_pz: float = 0.5


@dataclass
class QubitToyOutputs:
    omega_rad_per_s: float
    epsilon_F_per_s: float
    pi_product_rate: float
    speed_based_threshold_energy: float
    psi_hat: float
    notes: str


def compute_estimates(params: QubitToyInputs) -> QubitToyOutputs:
    omega = 2.0 * math.pi * params.frequency_ghz * 1e9
    T2_us = params.T2_microseconds if params.T2_microseconds is not None else params.T1_microseconds
    epsilon_F = 1.0 / (T2_us * 1e-6)

    pi_rate = epsilon_F * params.entropy_S_nats * params.mutual_information_nats

    speed_threshold_energy = (
        0.5 * HBAR * params.active_epoch_density * epsilon_F * params.entropy_S_nats * params.mutual_information_nats
    )

    d_min = min(params.subsystem_dim_dA, params.complement_min_dim_dbar_min)
    denom_h_norm = (2.0 * (HBAR * omega / 2.0))
    factor_qfi = HBAR * epsilon_F / denom_h_norm if denom_h_norm > 0 else 0.0
    factor_S = params.entropy_S_nats / math.log(params.subsystem_dim_dA)
    factor_I = params.mutual_information_nats / (2.0 * math.log(d_min))
    psi_hat = max(0.0, min(1.0, factor_qfi * factor_S * factor_I))

    return QubitToyOutputs(
        omega_rad_per_s=omega,
        epsilon_F_per_s=epsilon_F,
        pi_product_rate=pi_rate,
        speed_based_threshold_energy=speed_threshold_energy,
        psi_hat=psi_hat,
        notes=(
            "epsilon_F uses 1/T2 (conservative); psi_hat uses ||H|| = ħω/2, d_min = min(dA, dbar_min)."
        ),
    )


def main() -> None:
    parser = argparse.ArgumentParser(description="Toy estimate of triad quantities for a superconducting qubit.")
    parser.add_argument("--fghz", type=float, default=5.0, help="Qubit frequency in GHz (default: 5.0)")
    parser.add_argument("--T1_us", type=float, default=100.0, help="T1 in microseconds (default: 100.0)")
    parser.add_argument("--T2_us", type=float, default=None, help="T2 in microseconds (default: use T1)")
    parser.add_argument("--S", type=float, default=1.0, help="Local entropy S (nats), default 1.0")
    parser.add_argument("--I", type=float, default=0.1, help="Mutual information I (nats), default 0.1")
    parser.add_argument("--delta", type=float, default=0.3, help="Active epoch density δ in [0,1], default 0.3")
    parser.add_argument("--dA", type=int, default=2, help="Subsystem dimension d_A (default: 2)")
    parser.add_argument("--dbar_min", type=int, default=2, help="Min complement dimension d̄_min (default: 2)")
    parser.add_argument("--theta", type=float, default=0.5, help="θ for PZ notes (not used in calc), default 0.5")
    parser.add_argument("--csv_out", type=str, default=None, help="Optional path to write CSV output")
    parser.add_argument("--json_out", type=str, default=None, help="Optional path to write JSON output")
    args = parser.parse_args()

    inputs = QubitToyInputs(
        frequency_ghz=args.fghz,
        T1_microseconds=args.T1_us,
        T2_microseconds=args.T2_us,
        entropy_S_nats=args.S,
        mutual_information_nats=args.I,
        active_epoch_density=args.delta,
        subsystem_dim_dA=args.dA,
        complement_min_dim_dbar_min=args.dbar_min,
        theta_pz=args.theta,
    )
    outputs = compute_estimates(inputs)

    print("Inputs:")
    for k, v in asdict(inputs).items():
        print(f"  {k}: {v}")
    print("\nEstimates:")
    print(f"  omega_rad_per_s:           {outputs.omega_rad_per_s:.6e}")
    print(f"  epsilon_F_per_s:           {outputs.epsilon_F_per_s:.6e}")
    print(f"  pi_product_rate (1/s):     {outputs.pi_product_rate:.6e}")
    print(f"  speed_threshold_energy (J):{outputs.speed_based_threshold_energy:.6e}")
    print(f"  psi_hat (dimensionless):   {outputs.psi_hat:.6e}")
    print(f"  notes:                     {outputs.notes}")

    if args.csv_out:
        with open(args.csv_out, "w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=[*asdict(inputs).keys(), *asdict(outputs).keys()])
            writer.writeheader()
            row = {**asdict(inputs), **asdict(outputs)}
            writer.writerow(row)

    if args.json_out:
        with open(args.json_out, "w") as f:
            json.dump({"inputs": asdict(inputs), "outputs": asdict(outputs)}, f, indent=2)


if __name__ == "__main__":
    main()


