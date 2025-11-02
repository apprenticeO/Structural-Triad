# Third-Party Notices

This repository uses the following third‑party tools and libraries. This file provides attribution and links to upstream licenses and documentation. If any third‑party source code is vendored in this repository (e.g., under `Hyppopotamus/rocq-project/coquelicot/`), please refer to the corresponding directory for the original license text.

Note: You are not redistributing the Rocq/Coq toolchain here; it is used for building the Coq development. Python libraries are pulled from their respective package managers at runtime; no binary redistribution is intended.

## Rocq Prover / Coq
- Rocq Prover (formerly Coq Proof Assistant) — installation, documentation, and license information: https://rocq-prover.org/
  - Used to build and check `Hyppopotamus/rocq-project`.
  - Some developments may depend on the Rocq Standard Library.
- Coquelicot (Coq analysis library)
  - This repository includes a `coquelicot/` directory under `Hyppopotamus/rocq-project/` for local builds. See that directory for license files and upstream attribution.

## Python Libraries
The Python scripts under `Hyppopotamus/Scripts Demonstration/` rely on the following libraries (directly or transitively). Please see each project’s upstream license page or repository for current licensing terms.

- NumPy — upstream license: https://numpy.org/doc/stable/license.html
- SciPy — upstream license: https://scipy.org/scipylib/license.html
- Matplotlib — upstream license: https://matplotlib.org/stable/users/project/license.html
- QuTiP (Quantum Toolbox in Python) — upstream repository/license: https://github.com/qutip/qutip (LICENSE in repo)
- Quimb / quimb.tensor — upstream repository/license: https://github.com/jcmgray/quimb (LICENSE in repo)

## Script‑specific dependency notes
The following files use one or more of the libraries listed above. This list is informational and not exhaustive of transitive dependencies.

- `Hyppopotamus/Scripts Demonstration/1_esse_core_simulation.py`
  - Uses: NumPy, QuTiP, Matplotlib
- `Hyppopotamus/Scripts Demonstration/2_esse_pure_state_validation.py`
  - Uses: NumPy, Matplotlib; loads `1_esse_core_simulation.py` (transitively QuTiP)
- `Hyppopotamus/Scripts Demonstration/3_esse_comprehensive_validation.py`
  - Uses: NumPy, Matplotlib; loads `1_esse_core_simulation.py`
- `Hyppopotamus/Scripts Demonstration/4_run_neel_tebd_tau.py`
  - Uses: NumPy, Quimb/quimb.tensor, Matplotlib (optional)
- `Hyppopotamus/Scripts Demonstration/5_run_tebd_perA_metrics.py`
  - Uses: NumPy, Quimb/quimb.tensor
- `Hyppopotamus/Scripts Demonstration/6_run_delta_ladder_tebd.py`
  - Uses: NumPy, Quimb/quimb.tensor
- `Hyppopotamus/Scripts Demonstration/7_esse_commuting_vs_noncommuting.py`
  - Uses: NumPy, Matplotlib; loads `1_esse_core_simulation.py`
- `Hyppopotamus/Scripts Demonstration/8_esse_eigenstate_validation.py`
  - Uses: NumPy, QuTiP, Matplotlib
- `Hyppopotamus/Scripts Demonstration/9_esse_ball_KA_proxy.py`
  - Uses: NumPy, Quimb/quimb.tensor, Matplotlib (optional)
- `Hyppopotamus/Scripts Demonstration/10_triad_density_test.py`
  - Uses: NumPy, Quimb/quimb.tensor, SciPy (linear algebra), Matplotlib (optional)
- `Hyppopotamus/Scripts Demonstration/11_esse_mixed_quench_stress.py`
  - Uses: NumPy, QuTiP, Matplotlib
- `Hyppopotamus/Scripts Demonstration/12_esse_weak_interaction_test.py`
  - Uses: NumPy, QuTiP, Matplotlib; loads `1_esse_core_simulation.py`
- `Hyppopotamus/Scripts Demonstration/13_esse_integrable_validation.py`
  - Uses: NumPy, QuTiP, Matplotlib
- `Hyppopotamus/Scripts Demonstration/14_toric_topo_triad.py`
  - Uses: NumPy, QuTiP, Matplotlib (optional)
- `Hyppopotamus/Scripts Demonstration/15_paley_zygmund_validation.py`
  - Uses: NumPy; may optionally use Matplotlib for plotting
- `Hyppopotamus/Scripts Demonstration/16_qubit_toy_estimate.py`
  - Uses: Standard Library (dataclasses, math); NumPy may be used if extended

If you vendor additional third‑party code in this repository, please include the corresponding license text alongside the code and add an entry here.

## Questions
For questions about third‑party notices or to request updates, contact the repository maintainer.

