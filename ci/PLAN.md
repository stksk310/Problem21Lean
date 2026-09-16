# P21 M1 GitHub CI Implementation Plan

**Goal:** Produce externally inspectable CI evidence for the exact M1 candidate.
**Spec:** `ci/REQUEST.md` (the user's execution instruction).
**Architecture:** Preserve the ZIP as the implementation baseline and verify hashes
at checkout and after all checks. Run the original portable suite in a temporary
copy, because it regenerates inspection sources. Build project proofs from scratch;
only pinned third-party mathlib cache downloads are optional.
**Stack:** GitHub Actions / ubuntu-latest, pinned elan, existing Lean lockfiles,
Python standard library, Git.

## Constraints

- NO MATH CHANGE / NO STATEMENT CHANGE / NO PROOF CHANGE / NO DEPENDENCY CHANGE.
- Main branch and public repository are explicitly requested/authorized.
- Only new CI/metadata/scripts and an appended README section may differ.
- Status remains M1 CANDIDATE FOR TRUE AUDIT. CI success is evidence, not an audit ruling.

## Steps

- [x] Extract the authoritative ZIP, verify every embedded manifest entry, and
  commit its 53 original files with line-ending conversion disabled.
- [x] Establish the GitHub identity and check both proposed repository names.
- [x] Add `ci/debt_scan.py` and adversarial lexer tests. Verify comments, nested
  comments, normal/raw strings, escaped quotes, real forbidden tokens, and malformed
  syntax. Run `python -m unittest discover -s ci -p 'test_*.py' -v`.
- [x] Add `ci/audit.py`: source integrity, dependency revisions, clean project
  build, lexical debt scan, the original axiom checker, all original portable
  verification scripts, statement-map consistency, and original package checks.
- [x] Add `.github/workflows/lean-audit.yml`, `.gitignore`, `.gitattributes`, and
  a README appendix. Pin official action commit SHAs and elan release v4.2.4.
- [x] Validate hashes, lexer tests, workflow syntax, and original-file Git blob
  identity locally. Commit only CI additions and the README appendix.
- [ ] Create public `stksk310/Problem21Lean`, push main, and inspect the actual
  GitHub Actions run until it concludes. Fix only CI issues if needed.
- [ ] Download evidence, validate all reports and target SHA, and return a fixed
  commit/run/artifact handoff. Do not claim success before remote evidence exists.

The execution design and publication are already authorized by the detailed user
request; no additional design or merge approval is introduced.
