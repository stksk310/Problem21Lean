"""Accept only the explicitly permitted standard logical axioms."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parents[1]
data = (root / 'AXIOM_REPORT.txt').read_text(encoding='utf-8-sig')
decls = json.loads((root / 'verification' / 'DECLARATIONS.json').read_text(encoding='utf-8'))
expected = {d['name'] for d in decls if d['kind'] in ('theorem', 'def', 'abbrev')}
standard = {'propext', 'Classical.choice', 'Quot.sound'}
found = {}
for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", data):
    deps = set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*', m[2] or ''))
    if deps - standard:
        raise SystemExit(f'Nonstandard axiom dependencies for {m[1]}: {deps - standard}')
    found[m[1]] = sorted(deps)
if set(found) != expected:
    raise SystemExit(f'Axiom report mismatch. Missing: {expected - set(found)}; extra: {set(found) - expected}')
if re.search(r'\berror:|sorryAx|\bwarning:', data):
    raise SystemExit('Error, warning or proof-debt marker in axiom report.')
(root / 'verification' / 'AXIOM_SUMMARY.json').write_text(json.dumps({
    'checked_declarations': len(found), 'project_specific_axioms': 0,
    'standard_axioms_observed': sorted(set().union(*map(set, found.values()))),
    'declarations': found}, indent=2) + '\n', encoding='utf-8')
print(f'{len(found)} declarations checked; only standard axioms; project-specific dependencies: 0.')
