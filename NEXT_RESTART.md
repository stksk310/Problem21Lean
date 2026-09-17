# Next restart: M2B

Status: **M2B STD_SYM_GLUE + FULL S3 CANDIDATE FOR TRUE AUDIT**.

1. Independently inspect the immutable M2B candidate ZIP and the GitHub evidence
   bound by the separate `HANDOFF_RECEIPT_M2B.json`. Validate the candidate SHA,
   exact audit commit, run attempt, artifact digest and internal evidence hashes.
2. Read `README_M2B.md`, `SOURCE_OF_TRUTH_M2B.md`, `M2B_PROOF_ROUTE.md`,
   `M2B_STATEMENT_MAP.md` and `M2B_DEPENDENCY_DAG.md`. Preserved older M2A
   documents describing STD_SYM_GLUE/FULL S3 as OPEN are milestone history.
3. Check the exact new theorem `P21.Symmetric.symmetric_three_generator_gluing`
   against the unchanged `SymmetricThreeGeneratorGluingStatement`, then inspect
   `P21.Symmetric.symmetric_tail_type_le_four` in the separate FullClosure module.
4. Check every construction field, nonnegative membership witness and the
   exhaustive unique/nonunique Apéry-top proof; verify no reverse closure edge.
5. All pre-M2B Lean files and verification/m2 remain frozen at
   `a0ec51cf93326b6f8dbf22647cfeecf81a931bd8`. Do not alter them or dependency pins.
   Keep branch `m2b-std-sym-glue`; this mission does not merge main.
6. Reproduce with `python3 verification/m2b/verify.py --fresh` in an unbuilt
   extracted source copy and `python3 ci/m2b_audit.py suite` for the untouched
   original M2 suite. See README for Windows and archive-comparison details.

STD_SYM_GLUE and FULL S3 have Lean proofs; independent TRUE AUDIT review remains
external. Nonsymmetric branches, PATH/TYPE II/CHAIN, other external inputs,
Euclidean descent and both long certificates remain outside this milestone.
