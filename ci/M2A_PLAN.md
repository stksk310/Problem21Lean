# M2A external CI reproducibility plan

The user-provided CI gate request is the execution specification. This mission
changes CI only; no mathematical source, verification script, pinned dependency,
or statement is edited. The existing M2 branch descends directly from M1 commit
9464b9cd3b6b070f9fa6d1c212f27065d1eb84b3.

- [x] Hash and safely extract the authoritative ZIP; inspect README, source map,
  dependency DAG, integrity report and original verifier.
- [x] Store the exact ZIP under ci/candidate. Compare every candidate file to the
  checkout and Git blobs, except README append and the ZIP-specific manifest.
- [x] Add ci/m2a_audit.py, adversarial integrity tests and m2a-audit.yml.
  Enumerate all non-M1 P21 modules from the ZIP; build them explicitly.
- [ ] Run the candidate lexical scanner, its original regression tests, exact
  axiom checker and unmodified verifier. Run the verifier in a separate source
  copy because it regenerates reports and inspection files.
- [ ] Record the actual critical Lean statements and candidate-preserved scope.
  Verify the external obligation remains a definition, and LOWER requires n>1.
- [x] Keep the legacy M1 job for M1 refs; skip its exact-M1-distribution check
  on the two M2 audit branch names. The M2 job independently checks M1 Git blobs
  and builds the M1 root on the same audited M2 checkout.
- [ ] Validate locally, commit only candidate import/CI additions, push the M2
  branch without merging main, and obtain a successful external Linux run.
- [ ] Download evidence, verify artifact digest and run/commit binding, write
  HANDOFF_RECEIPT_M2A.json and report the exact IDs, attempt and OPEN scope.

Tests: altered Lean bytes, added Lean files, missing verification metadata,
README rewrite versus append, module omission, unexpected axioms and incomplete
axiom coverage must fail. Source hashing includes original verification scripts
and statement/dependency metadata. Final checkout integrity is mandatory even
when an earlier step fails. Success is CI evidence ready, never an audit ruling.
