# ESSE Conjecture (Private Research Export)

This repository is a private, shareable subset of the ESSE workspace prepared for collaborators. It includes three main components:

- `Hyppopotamus/rocq-project`: Coq sources and build system for the rock/rocq prover artifacts
- `Hyppopotamus/Scripts Demonstration`: Python scripts demonstrating ESSE-related simulations and validations
- `Hyppopotamus/LATEX`: Manuscripts and notes (some items pending review)

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

### LaTeX (Hyppopotamus/LATEX)
- The LaTeX directory contains manuscripts and overviews.
- Note: some `.tex` files are flagged for review. Please read with care.

## Included directories
- `Hyppopotamus/rocq-project`
- `Hyppopotamus/Scripts Demonstration`
- `Hyppopotamus/LATEX`

## Data and artifacts policy
- Large artifacts (results, generated plots, build logs, caches) are excluded by design.
- If you require specific outputs, please request them and they can be shared separately.

## Citation
- See `CITATION.cff` for software/research citation metadata.

## Contact
- Email: ovdttr@gmail.com

## License
- All rights reserved. See `LICENSE` for terms. 