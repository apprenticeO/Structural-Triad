# ESSE Coq Development (rocq-project)

This repository formalizes the derivation in `Hyppopotamus/Scripts Demonstration/hyppo_esse_derivation.tex` and its modular, state‑agnostic triad variant.

## Mapping: LaTeX → Coq Modules

- Notation/System (Sec. 1–2)
  - `PurityClean.v`: I(A:Ā) = 2 S_A for pure bipartitions (used by π‑baseline)
  - `EntropyClean.v`: entropy/real‑inequality utilities (nonnegativity, ln on [0,1])

- Activity (Sec. 3)
  - `PiClean.v`: term = ΔH_A · S_A^2, Π_sys = (4/ħ) Σ_A term
  - `FisherClean.v`: F = 4 (ΔH)^2 ⇒ √F ≤ 2 ΔH (conceptual link)

- Pinsker and Quartic Bound (Sec. 4.1)
  - `PinskerClean.v`: linear Pinsker constant (abstract `c_lin`)
  - `PinskerSquaredClean.v`: square‑and‑align step behind S_A^2 ≥ (c_lin^2) ‖·‖_1^4

- Variance Floor (Sec. 4.2)
  - `GapFloorClean.v`: ΔH_A ≥ (1/4)·gap(A); v0(A) = (1/4)·δE_min(A)

- Averaging and Operational Metrics (Sec. 5)
  - `TimeAvgClean.v`, `AveragingPerA.v`: density‑of‑good‑times (δ_A), Cesàro lemmas

- Constructive Floor (Sec. 6)
  - `ESSEList.v`: lifts per‑A inequalities to sums; Π_sys ≥ C_sum
  - `ESSEUniversal.v`: factorization, constructive floor, and universal corollary

- Boxed Summary
  - `ESSEBoxed.v`, `Positivity.v`

### Universal variants
- `ESSEUniversal_structure.v` (Elephant triad, state‑agnostic):
  - Encodes Ψ_A ≈ √F_Q · S_A · I(A:Ā) in a discrete‑time shell using signals rA,sA,iA and a good‑time predicate, with per‑A floors and a witness/minima lemma.
  - The ΔH·S^2 constructive path in `ESSEUniversal.v` remains available but is not required by the triad results.

### Modular triad architecture (new)
- `theory/SystemSpec.v`: system interface (`CutSpec`, `Admissible`), minima helpers
- `theory/TriadSignals.v`: discrete‑time signals and good‑epoch predicates
- `theory/Bridges.v`: physics→inequalities axioms (QFI/variance, Bures speed)
- `theory/LegFloors.v`: floors from H1–H3 witnesses
- `theory/Normalization.v`: intensive triad `Psi_hat`, proofs 0 ≤ Ψ̂ ≤ 1
- `theory/SumLifting.v`: monotone product and averaging lifts
- `theory/HCap.v`: Hamiltonian‑capped inequality (skeleton)
- `theory/SpeedBound.v`: speed‑based inequality (skeleton)
- `open/Channels.v`, `open/SpeedOpen.v`: open‑system stubs
- `tests/TriadExamples.v`: dummy `Admissible`, toy streams, sanity lemmas

## Build

  ```bash
# From repo root
  make -C Hyppopotamus/rocq-project -f CoqMakefile -j"$(nproc)" | cat
  ```

## Check (coqchk)

Legacy + triad variant:
  ```bash
  coqchk -R Hyppopotamus/rocq-project/src_clean ESSEClean \
    ESSEClean.ESSEBoxed ESSEClean.ESSEList ESSEClean.PerBoundClean \
    ESSEClean.PinskerClean ESSEClean.PinskerSquaredClean ESSEClean.GapFloorClean \
    ESSEClean.AveragingPerA ESSEClean.PiClean ESSEClean.Positivity \
    ESSEClean.PurityClean ESSEClean.FisherClean ESSEClean.EntropyClean \
  ESSEClean.TimeAvgClean ESSEClean.ESSEUniversal ESSEClean.ESSEUniversal_structure
```

Modular theory:
```bash
coqchk -R Hyppopotamus/rocq-project/src_clean ESSEClean \
  ESSEClean.theory.SystemSpec ESSEClean.theory.TriadSignals \
  ESSEClean.theory.Bridges ESSEClean.theory.LegFloors \
  ESSEClean.theory.Normalization ESSEClean.theory.SumLifting \
  ESSEClean.theory.HCap ESSEClean.theory.SpeedBound \
  ESSEClean.open.Channels ESSEClean.open.SpeedOpen \
  ESSEClean.tests.TriadExamples
```

## Using the modules (Require Import)

```coq
From Stdlib Require Import Reals.
Require Import ESSEClean.theory.SystemSpec.
Require Import ESSEClean.theory.Normalization.
```

Load a Coq REPL with the project root:
```bash
coqtop -R Hyppopotamus/rocq-project/src_clean ESSEClean
```
then:
```coq
Require Import ESSEClean.theory.SystemSpec ESSEClean.theory.Normalization.
  ```

## Notes
- All recent changes add the modular triad files and tests; legacy interfaces remain unchanged.
- `ESSEUniversal.v` provides the constructive ΔH·S^2 path; `ESSEUniversal_structure.v` provides the state‑agnostic triad/ON route. 