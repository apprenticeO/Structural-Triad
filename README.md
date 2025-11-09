#A Quantum Structural Triad: Fluctuations, Entropy, and Correlations as Interdependent Primitives
https://ijqf.org/wp-content/uploads/2025/11/IJQF2025v11n4p20r.pdf 

This repository is a private, shareable subset of the Structural Triad workspace prepared for collaborators. It includes three main components:

- `Hyppopotamus/rocq-project`: Coq sources and build system for the rock/rocq prover artifacts
- `Hyppopotamus/Scripts Demonstration`: Python scripts demonstrating structural triad simulations and validations
- `Hyppopotamus`: Manuscript PDF and annex/results

## Status and intent
- Private repository intended for research sharing.
- License: All rights reserved.
- Some LaTeX sources require review before public distribution.

## Requirements
- Python 3.x (no virtual environment required unless you prefer one)
- Coq (for `Hyppopotamus/rocq-project`) with `make`

## Quick start

### Python scripts (Hyppopotamus/Scripts Demonstration)
- Navigate to `Hyppopotamus/Scripts Demonstration` and run scripts with `python3`.
- Most scripts are self-contained. Heavy result artifacts and large plots are excluded from version control.

### Coq project (Hyppopotamus/rocq-project)
- Navigate to `Hyppopotamus/rocq-project` and use `make` to build the project.
- Build and check logs (`build.log`, `coqchk.log`) and Coq artifacts (`*.vo`, `*.glob`, caches) are ignored to keep the repository light.

### Manuscript (Hyppopotamus/)
- The manuscript is provided as a PDF.
- Primary PDF: `Hyppopotamus/v3_A_Quantum_Structural_Triad__Fluctuations__Entropy__and_Correlations_as_Interdependent_Primitives_Tataru_.pdf`
- Note: LaTeX sources are not included in this repository.

## Included directories
- `Hyppopotamus/rocq-project`
- `Hyppopotamus/Scripts Demonstration`
- `Hyppopotamus/Annex results`
- `Hyppopotamus` (manuscript PDF)

## Data and artifacts policy
- Large artifacts (results, generated plots, build logs, caches) are excluded by design.
- If you require specific outputs, please request them and they can be shared separately.

## Citation
- See `CITATION.cff` for software/research citation metadata.

## Contact
- Email: ovdttr@gmail.com

## License
- All rights reserved. See `LICENSE` for terms.
