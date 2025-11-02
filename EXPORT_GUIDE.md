# Export Guide (Private Repo)

## Scope to include
- `Hyppopotamus/rocq-project`
- `Hyppopotamus/Scripts Demonstration`
- `Hyppopotamus/LATEX`

Ensure `.gitignore` is present (excludes heavy results, build artifacts, caches, logs).

## Steps
1. Initialize a repo in the workspace root:
   ```
   cd /home/ovidiu/EESH_stablized
   git init
   git checkout -b main
   ```
2. Stage and commit:
   ```
   git add README.md LICENSE .gitignore CITATION.cff CONTRIBUTING.md SECURITY.md docs/ EXPORT_GUIDE.md Hyppopotamus/rocq-project Hyppopotamus/Scripts\ Demonstration Hyppopotamus/LATEX
   git commit -m "Initial Structural Triad private research export"
   ```
3. Create a private repository on GitHub (via web UI) under `apprenticeO/structural-triad` (or your chosen name).
4. Add remote and push:
   ```
   git remote add origin https://github.com/apprenticeO/structural-triad.git
   git push -u origin main
   ```

## Notes
- Do not include large results or logs; the `.gitignore` already excludes common patterns.
- Review LaTeX sources before sharing externally.
- Update `CITATION.cff` and `README.md` as metadata evolves. 