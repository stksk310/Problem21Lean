"""Portable self-check. Run from any location with lake and Python on PATH."""
from pathlib import Path
import subprocess
import sys
import json

root = Path(__file__).resolve().parents[1]
codes = {}

def run(args, output=None):
    result = subprocess.run(args, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            encoding='utf-8', errors='replace')
    codes[' '.join(args)] = result.returncode
    if output:
        (root / output).write_text(result.stdout, encoding='utf-8')
    print(result.stdout)
    (root / 'verification/CHECK_EXIT_CODES.json').write_text(json.dumps(codes, indent=2)+'\n', encoding='utf-8')
    if result.returncode:
        raise SystemExit(result.returncode)

run(['lake', 'build'], 'BUILD_LOG.txt')
run([sys.executable, 'verification/prepare_reports.py'])
run(['lake', 'env', 'lean', 'verification/AxiomCheck.lean'], 'AXIOM_REPORT.txt')
run([sys.executable, 'verification/check_axiom_report.py'])
run(['lake', 'env', 'lean', 'verification/StatementCheck.lean'], 'verification/STATEMENTS.txt')
print('Self-checks completed. Status remains M1 CANDIDATE FOR TRUE AUDIT.')
