# Sensitive Data Audit Checklist

Review before pushing to the private repository:

## Credentials and secrets
- Search for API keys, tokens, passwords, SSH keys
- Check config files for embedded credentials

## Personal or restricted data
- Ensure no personal data or confidential datasets are included
- Confirm generated outputs do not leak sensitive content

## Heavy artifacts (exclude or share offline)
- Large results, plots, and logs
- Binary artifacts, archives, and caches

## File patterns to avoid
- `*.npz`, `*.npy`, `*.csv` (unless curated and needed)
- `*.log`, `*.aux`, `*.vo`, `*.glob`, caches
- Archives: `*.zip`, `*.gz`, `*.tar*`

## Project-specific notes
- LaTeX (`Hyppopotamus/LATEX`): some `.tex` files need review
- Coq (`Hyppopotamus/rocq-project`): exclude build logs and compiled artifacts
- Python (`Hyppopotamus/Scripts Demonstration`): do not commit large results or plots

If any doubt, remove the file from the commit and share privately if necessary. 