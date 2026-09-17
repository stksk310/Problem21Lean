# M2B implementation self-check

Status: **M2B STD_SYM_GLUE + FULL S3 CANDIDATE FOR TRUE AUDIT**.
This is an implementation self-check, not an independent audit ruling.

- The exact frozen `SymmetricThreeGeneratorGluingStatement` is proved in the
  new `P21/External/SymmetricThreeGeneratorProof.lean`. Its only hypotheses are
  `Setting` and `SymmetricTail`; no canonical or supplied relation hypothesis.
- The exhaustive Apéry-top dichotomy constructs a genuine `Equiv.Perm (Fin 3)`
  and `SymmetricGlueData`. Every lower bound, coprimality condition and generator
  equality is proved; `w_mem` retains actual nonnegative coefficients.
- Full S3 uses the newly proved data and the unchanged M2A theorem in a separate
  `FullClosure.lean`. The classification import closure excludes both closure
  modules and its new sources do not reference the reverse symmetry theorem.
- The implementation has 10 new proof modules, 53 explicitly named theorems,
  two definitions and one structure. All 56 named declarations are inspected
  with `#print axioms`. Only subsets of `propext`, `Classical.choice`, and
  `Quot.sound` occur. Project-specific axioms: 0.
- Fresh local verification ran in a separate source copy with no initial
  project `.olean`; only third-party dependency packages were shared. Root,
  all 16 M2A modules and all 10 new M2B modules built successfully. Statement
  and theorem-regression checks exited 0. The frozen original M2 suite also
  passed in a second isolated copy, with its original inventory preserved.
- The original 13 scanner tests and 12 new verifier tests passed. All 49
  project-owned Lean files have zero forbidden proof-debt tokens.
- All 57 protected files, including every one of the 36 pre-M2B Lean files,
  match the frozen commit bytes. Toolchain and dependency pins are unchanged.
- `verification/m2b/LOCAL_VERIFICATION.json` binds these local results to all
  49 checked Lean source hashes. The accompanying local-evidence directory
  contains the underlying logs and statement/dependency evidence.
- A separate internal mathematical source review found no material issues;
  its limited scope is stated in `verification/m2b/INTERNAL_REVIEW.md`.

The immutable ZIP is created before CI. CI must freshly recheck the committed
sources against that ZIP, check the baseline against frozen Git blobs, verify
dependency revisions, rebuild and upload the evidence. The post-run receipt
records actual external CI outcomes, commit, run/attempt and artifact digest;
it is stored separately to keep the candidate ZIP hash immutable.

No nonsymmetric branch, PATH/TYPE II/CHAIN integration, Euclidean descent or
715/3234 certificate is claimed here. No independent promotion is claimed.
