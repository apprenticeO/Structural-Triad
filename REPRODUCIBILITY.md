# Reproducibility (Structural-Triad)

## Manuscript
- Primary PDF: `Hyppopotamus/v3_A_Quantum_Structural_Triad__Fluctuations__Entropy__and_Correlations_as_Interdependent_Primitives_Tataru_.pdf`

## Coq (rocq-project)
- Install the Rocq Prover and tooling per the official site: https://rocq-prover.org/
- Build from repo root:
```
make -C Hyppopotamus/rocq-project -f CoqMakefile -j"$(nproc)" | cat
```
- Check (legacy + triad variant):
```
coqchk -R Hyppopotamus/rocq-project/src_clean ESSEClean \
  ESSEClean.ESSEBoxed ESSEClean.ESSEList ESSEClean.PerBoundClean \
  ESSEClean.PinskerClean ESSEClean.PinskerSquaredClean ESSEClean.GapFloorClean \
  ESSEClean.AveragingPerA ESSEClean.PiClean ESSEClean.Positivity \
  ESSEClean.PurityClean ESSEClean.FisherClean ESSEClean.EntropyClean \
  ESSEClean.TimeAvgClean ESSEClean.ESSEUniversal ESSEClean.ESSEUniversal_structure
```
- Check (modular theory):
```
coqchk -R Hyppopotamus/rocq-project/src_clean ESSEClean \
  ESSEClean.theory.SystemSpec ESSEClean.theory.TriadSignals \
  ESSEClean.theory.Bridges ESSEClean.theory.LegFloors \
  ESSEClean.theory.Normalization ESSEClean.theory.SumLifting \
  ESSEClean.theory.HCap ESSEClean.theory.SpeedBound \
  ESSEClean.open.Channels ESSEClean.open.SpeedOpen \
  ESSEClean.tests.TriadExamples
```
- Note: `theory/HCap.v` is implemented and mechanically checked.
 - Coverage: the speed‑based threshold is not formalized in the Rocq project; `theory/SpeedBound.v` is a placeholder.

## Python scripts (optional)
- Location: `Hyppopotamus/Scripts Demonstration`
- Run with `python3` from the directory of each script. Heavy result artifacts are excluded from version control.

## Artifacts & policy
- Large results, plots, build logs, caches are excluded by `.gitignore`.
- See `EXPORT_GUIDE.md` for packaging a shareable private export.

## Citation
- See `CITATION.cff`.

