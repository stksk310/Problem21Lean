# M2B STD_SYM_GLUE and full S3

Status: **M2B STD_SYM_GLUE + FULL S3 — CANDIDATE FOR TRUE AUDIT**.
This document describes the M2B extension. Preserved M2A documents saying OPEN
record the earlier milestone and are not the status of the new proof modules.

The new theorem proves the exact, unchanged target definition:

```lean
theorem P21.Symmetric.symmetric_three_generator_gluing :
    P21.Symmetric.SymmetricThreeGeneratorGluingStatement
```

It takes only the frozen `Setting` and `SymmetricTail` hypotheses. The proof
constructs `SymmetricGlueData` with an actual permutation, d,u,v≥2,
gcd(u,v)=gcd(d,w)=1 and nonnegative coefficients representing w in <u,v>.
No canonical condition, supplied pair, uniqueness or critical relation is assumed.

A separate new module connects that proof to frozen M2A:

```lean
theorem P21.Symmetric.symmetric_tail_type_le_four
    (g : P21.Generators) (setting : g.Setting) (F : ℤ)
    (hF : setting.semigroup.IsFrobenius F)
    (hcan : setting.semigroup.Canonical F g.m)
    (hsym : P21.Symmetric.SymmetricTail g) : setting.semigroup.type ≤ 4
```

The classification proof uses an elementary Apéry argument in dimension three:
two distinct representations of the top yield primitive-pair membership;
a unique representation yields a rectangle and a zero boundary coefficient.
See `M2B_PROOF_ROUTE.md`, `M2B_STATEMENT_MAP.md`, and `M2B_DEPENDENCY_DAG.md`.

All 36 pre-existing project-owned Lean files and all verification/m2 files,
toolchain and project dependency configuration remain byte-identical to
`a0ec51cf93326b6f8dbf22647cfeecf81a931bd8` (57 protected files total).
The old OPEN target definition itself is preserved and is now inhabited by the
new proof. M2A `Closure.lean` is preserved. Main is not merged by this mission.

## Reproduce

Use the exact `lean-toolchain` and `lake-manifest.json` files. Third-party cache
is optional; project compiled artifacts are not part of the delivery.

```text
lake build
lake build P21.Symmetric.FullClosure P21.Symmetric.Classification.CriticalRelations
python3 verification/m2b/verify.py
```

The verifier explicitly enumerates/builds every M2A and M2B module, audits every
new named declaration, runs regression checks, checks the immutable baseline,
and records statement and noncircular import evidence. On Windows it uses the
preserved `verification/lake.ps1` path adapter. The original M2A verifier runs
unchanged in a separate copy of its authoritative ZIP through `ci/m2b_audit.py suite`.

The clean GitHub workflow is `.github/workflows/m2b-audit.yml` on branch
`m2b-std-sym-glue`. It produces `P21_M2B_TRUE_AUDIT_EVIDENCE`. Local and CI results
are recorded in their respective logs; a successful CI run is reproducibility
evidence, not an independent mathematical audit ruling.

## Delivery identity

CI compares its checked-out implementation against an immutable source candidate
ZIP stored under `ci/candidate`. The delivered candidate ZIP is byte-identical
to that archive, with the same SHA-256. The post-run handoff receipt is stored
separately and binds this hash to the GitHub commit, run, attempt and downloadable
evidence artifact. The receipt cannot be embedded in its own hashed input archive.
To repeat the CI wrapper's archive comparison after extracting this ZIP, place
the original ZIP under `ci/candidate` and write its SHA-256 as the first token of
`ci/M2B_CANDIDATE_SHA256.txt`. The ordinary local verifier needs neither operation.

## Remaining project scope

The symmetric-tail classification and full S3 are proved in the new modules.
Nonsymmetric classification, PATH/TYPE II/CHAIN integration, further external
inputs, Euclidean descent, and the 715/3234 certificates are outside this mission.
No project-wide Problem 21 closure is claimed.
