"""Generate declaration inventories and reproducible Lean inspection commands."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
decls = []
for path in sorted((ROOT / 'P21').rglob('*.lean')):
    namespaces = []
    for lineno, line in enumerate(path.read_text(encoding='utf-8').splitlines(), 1):
        ns = re.match(r'namespace\s+(\S+)', line)
        end = re.match(r'end(?:\s+\S+)?\s*$', line)
        if ns:
            namespaces.append(ns[1])
        elif end:
            if namespaces:
                namespaces.pop()
        match = re.match(r'(?:noncomputable\s+)?(theorem|def|abbrev|structure)\s+(\S+)', line)
        if match:
            decls.append(dict(name='.'.join(namespaces + [match[2]]), kind=match[1],
                              file=path.relative_to(ROOT).as_posix(), line=lineno))

(ROOT / 'verification' / 'DECLARATIONS.json').write_text(
    json.dumps(decls, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
inspect = [d for d in decls if d['kind'] in ('theorem', 'def', 'abbrev')]
(ROOT / 'verification' / 'AxiomCheck.lean').write_text(
    'import P21\n\n' + '\n'.join('#print axioms ' + d['name'] for d in inspect) + '\n', encoding='utf-8')
(ROOT / 'verification' / 'StatementCheck.lean').write_text(
    'import P21\nset_option pp.universes false\n\n' +
    '\n'.join('#check ' + d['name'] for d in decls) +
    '\n#print P21.P21MainStatement\n#print P21.Generators.Setting\n'
    '#print P21.Generators.Minimal\n#print P21.NumericalSemigroup.PF\n'
    '#print P21.NumericalSemigroup.IsFrobenius\n', encoding='utf-8')

scanned = sorted((ROOT / 'P21').rglob('*.lean')) + [ROOT / 'P21.lean'] + sorted((ROOT / 'verification').glob('*.lean'))
tokens = ['sorry', 'admit', 'axiom', 'sorryAx', 'unsafe', 'opaque']
hits = []
for path in scanned:
    for lineno, line in enumerate(path.read_text(encoding='utf-8').splitlines(), 1):
        if re.search(r'\b(?:' + '|'.join(tokens) + r')\b', line):
            hits.append(f'{path.relative_to(ROOT)}:{lineno}: {line}')
report = ['Proof-debt source scan', 'Scope: all project and verification .lean sources; excludes third-party packages.',
          'Method: raw word-boundary scan, including comments and strings.',
          'Tokens: ' + ', '.join(tokens), 'Matches: ' + str(len(hits)), *hits,
          'Project-specific axiom declarations: ' + str(sum(bool(re.search(r'^\s*axiom\b', h.split(': ', 1)[-1])) for h in hits)),
          'Axiom dependency verification is separately recorded in AXIOM_REPORT.txt.',
          'Future target P21MainStatement is a Prop definition; no theorem proves it.', '']
(ROOT / 'PROOF_DEBT_REPORT.txt').write_text('\n'.join(report), encoding='utf-8')
if hits:
    raise SystemExit('Proof-debt scanner found forbidden tokens.')
print(f'{len(decls)} declarations; {sum(d["kind"] == "theorem" for d in decls)} theorems; '
      f'{len(inspect)} axiom inspection commands; {len(scanned)} source files; no debt matches.')
