#!/usr/bin/env python3
import argparse, json, os, re, hashlib, subprocess, time
from pathlib import Path

LEMMA_RE = re.compile(r"\b(Lemma|Theorem)\s+([A-Za-z0-9_']+)\b")
ADMITTED_RE = re.compile(r"\bAdmitted\.")

EXPECTED = {
    'ESSEBoxed.v': {'ESSE_boxed_finite_sum', 'ESSE_boxed_strict_pos', 'ESSE_boxed_Pi_sys_pos'},
    'ESSEList.v': {'ESSE_list_boxed', 'Pi_sys_lower_sum'},
    'PerBoundClean.v': {'per_bound_le'},
    'PinskerSquaredClean.v': {'pinsker_squared'},
    'PinskerClean.v': {'linear_trace_bound'},
    'GapFloorClean.v': {'variance_gap_floor'},
    'AveragingPerA.v': {'avg_eventual_lower_perA'},
    'PiClean.v': {'Pi_sys_pos'},
    'Positivity.v': {'Pi_lower_pos'},
    'PurityClean.v': {'mutual_info_pure_global'},
    'FisherClean.v': {'fisher_is_four_var'},
}

def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda: f.read(65536), b''):
            h.update(chunk)
    return h.hexdigest()

def rocq_version() -> str:
    try:
        out = subprocess.check_output(["rocq", "--version"], stderr=subprocess.STDOUT, text=True)
        return out.strip().splitlines()[0]
    except Exception:
        return "unknown"

def extract_statements(vfile: Path):
    try:
        text = vfile.read_text(encoding='utf-8', errors='ignore')
    except Exception:
        return [], False
    names = []
    for _, name in LEMMA_RE.findall(text):
        names.append(name)
    # Deduplicate preserving order
    seen = set(); out = []
    for n in names:
        if n not in seen:
            out.append(n); seen.add(n)
    admitted = bool(ADMITTED_RE.search(text))
    return out, admitted

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--src', required=True, help='Path to src_clean directory with Coq files')
    ap.add_argument('--out', required=True, help='Output JSON path')
    ap.add_argument('--qed-log', help='Optional path to write human-readable QED log (txt)')
    args = ap.parse_args()

    src = Path(args.src).resolve()
    if not src.exists():
        raise SystemExit(f"src not found: {src}")

    modules = []
    for vfile in sorted(src.glob('*.v')):
        vo = vfile.with_suffix('.vo')
        globf = vfile.with_suffix('.glob')
        stmts, admitted = extract_statements(vfile)
        entry = {
            'file': str(vfile),
            'basename': vfile.name,
            'sha256': sha256_file(vfile),
            'compiled': vo.exists(),
            'glob_present': globf.exists(),
            'mtime': time.strftime('%Y-%m-%dT%H:%M:%S', time.localtime(vfile.stat().st_mtime)),
            'statements': stmts,
            'has_admitted': admitted,
        }
        modules.append(entry)

    ledger = {
        'rocq_version': rocq_version(),
        'generated_at': time.strftime('%Y-%m-%dT%H:%M:%S'),
        'modules': modules,
    }

    outp = Path(args.out)
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(json.dumps(ledger, indent=2), encoding='utf-8')
    print(f"Wrote proof ledger to {outp}")

    # Optional human-readable QED log
    if args.qed_log:
        lines = []
        lines.append(f"Rocq: {ledger['rocq_version']} | Generated: {ledger['generated_at']}")
        lines.append("")
        for m in modules:
            status = "compiled" if m['compiled'] else "not-compiled"
            adm = "; Admitted present" if m['has_admitted'] else ""
            lines.append(f"- {m['basename']} [{status}] (mtime: {m['mtime']}){adm}")
            ex = EXPECTED.get(m['basename'])
            if ex:
                present = set(m['statements'])
                ok = ex.issubset(present)
                missing = sorted(list(ex - present))
                lines.append(f"  expected statements present: {'yes' if ok else 'no'}")
                if not ok:
                    lines.append(f"  missing: {', '.join(missing)}")
            for s in m['statements']:
                lines.append(f"  • {s}")
            lines.append("")
        qout = Path(args.qed_log)
        try:
            qout.parent.mkdir(parents=True, exist_ok=True)
        except Exception:
            pass
        qout.write_text("\n".join(lines), encoding='utf-8')
        print(f"Wrote QED log to {qout}")

if __name__ == '__main__':
    main() 