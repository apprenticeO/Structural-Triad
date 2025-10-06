# Reproducibility Note

This artifact accompanies `Hyppopotamus/Scripts Demonstration/hyppo_esse_derivation.tex` and the modular triad formalization.

## Requirements
- Coq / Rocq (project ships a generated `CoqMakefile`)
- Coq Stdlib
- Coquelicot (used by `EntropyClean.v`; keep installed even if not directly exercised)

## Build
```bash
# From repo root
make -C Hyppopotamus/rocq-project -f CoqMakefile -j"$(nproc)" | cat
```
- A successful build produces `.vo` files under `src_clean/`.
- A snapshot of the last build is saved as `Hyppopotamus/rocq-project/build.log` (if you tee it there).

## Check (coqchk)
The logical root for compiled objects is `ESSEClean` (mapped to `src_clean`).

Minimal core check (legacy constructive + triad variant):
```bash
coqchk -R Hyppopotamus/rocq-project/src_clean ESSEClean \
  ESSEClean.ESSEBoxed ESSEClean.ESSEList ESSEClean.PerBoundClean \
  ESSEClean.PinskerClean ESSEClean.PinskerSquaredClean ESSEClean.GapFloorClean \
  ESSEClean.AveragingPerA ESSEClean.PiClean ESSEClean.Positivity \
  ESSEClean.PurityClean ESSEClean.FisherClean ESSEClean.EntropyClean \
  ESSEClean.TimeAvgClean ESSEClean.ESSEUniversal ESSEClean.ESSEUniversal_structure
```

Modular triad check (new theory modules):
```bash
coqchk -R Hyppopotamus/rocq-project/src_clean ESSEClean \
  ESSEClean.theory.SystemSpec \
  ESSEClean.theory.TriadSignals \
  ESSEClean.theory.Bridges \
  ESSEClean.theory.LegFloors \
  ESSEClean.theory.Normalization \
  ESSEClean.theory.SumLifting \
  ESSEClean.theory.HCap \
  ESSEClean.theory.SpeedBound \
  ESSEClean.open.Channels \
  ESSEClean.open.SpeedOpen \
  ESSEClean.tests.TriadExamples
```
- A successful run prints nothing and returns exit code 0. You can capture it with `; echo EXIT_CODE=$?`.
- We recommend running both the legacy and modular checks.

## How to "summon" modules (Require Import)
All new files are under the logical path `ESSEClean`. For example:
```coq
From Stdlib Require Import Reals.
Require Import ESSEClean.theory.SystemSpec.
Require Import ESSEClean.theory.Normalization.
```
In CoqIDE or `coqtop` you can load the project with:
```bash
coqtop -R Hyppopotamus/rocq-project/src_clean ESSEClean
```
then inside `coqtop`:
```coq
Require Import ESSEClean.theory.SystemSpec ESSEClean.theory.Normalization.
```

## Mapping (Paper → Coq)
- Sec. 1–2: `PurityClean.v`, `EntropyClean.v`
- Sec. 3: `PiClean.v`, `FisherClean.v`
- Sec. 4.1: `PinskerClean.v`, `PinskerSquaredClean.v`
- Sec. 4.2: `GapFloorClean.v`
- Sec. 5: `TimeAvgClean.v`, `AveragingPerA.v`
- Sec. 6: `ESSEList.v`, `ESSEUniversal.v` (constructive floor; universal corollary)
- Boxed summary and positivity: `ESSEBoxed.v`, `Positivity.v`
- Triad (state‑agnostic) variant: `ESSEUniversal_structure.v`
- Modular triad architecture (new):
  - `theory/SystemSpec.v`: system interface (`CutSpec`, `Admissible`), minima helpers
  - `theory/TriadSignals.v`: discrete-time signals and good-epoch predicates
  - `theory/Bridges.v`: physics→inequalities axioms (QFI/variance, Bures speed)
  - `theory/LegFloors.v`: floors from H1–H3 witnesses
  - `theory/Normalization.v`: intensive triad `Psi_hat` with 0 ≤ Ψ̂ ≤ 1
  - `theory/SumLifting.v`: monotone product and averaging lifts
  - `theory/HCap.v`: Hamiltonian‑capped inequality (skeleton)
  - `theory/SpeedBound.v`: speed‑based inequality (skeleton)
  - `open/Channels.v`, `open/SpeedOpen.v`: open‑system stubs
  - `tests/TriadExamples.v`: dummy instance and sanity checks

## Conventions
- Log base: proofs in legacy part are parameterized by `c_lin` (paper sets nats with `c_lin = 1/2`).
- Time-averaging: `δ_A` and related Cesàro lemmas appear in `TimeAvgClean.v` and are mirrored by `TriadSignals.v` usage.

## Contact
This code is self-contained; see module headers for paper cross-references and intent. 