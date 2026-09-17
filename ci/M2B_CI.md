# M2B reproducibility gate

The new `m2b-audit.yml` audits M2B without editing the frozen M2 verifier,
frozen Lean files, or dependency configuration. It installs SHA-pinned elan
v4.2.4 and the repository's pinned Lean toolchain on a clean Linux runner.
Only third-party Mathlib/dependency cache is restored; the root build rejects
pre-existing project `.olean` files.

Authoritative source candidate:
`ci/candidate/P21_LEAN_M2B_STD_SYM_GLUE_FULL_S3_CANDIDATE_20260917.zip`.
Its SHA-256 is read from `ci/M2B_CANDIDATE_SHA256.txt`. The ZIP must use a
single root directory equal to its filename stem and contain
`MANIFEST_SHA256.json` with a `files` map covering every other entry. Build
artifacts and VCS directories are forbidden. Executable source/configuration
is compared byte-for-byte against both checkout and committed Git blobs.
Delivery reports may be ZIP-only. Generated M2B checker files are generated
deterministically with LF newlines, committed, and included in exact source equality.

The 57 protected files in `verification/m2b/FROZEN_SHA256.json` are verified
against disk, hashes, and the independent Git tree at
`a0ec51cf93326b6f8dbf22647cfeecf81a931bd8`. The verifier never overwrites
`verification/m2/` or the frozen original checker files.

Local CLI:

```
python verification/m2b/verify.py --prepare
python verification/m2b/verify.py
python verification/m2b/verify.py --fresh
```

`--prepare` performs baseline/debt/scanner checks and generates an inventory
and checker sources. It records whether the final theorems exist but does
not claim completion. The normal/full gate requires both final theorems;
Lean checks their exact requested public types, builds all 16 M2A modules
and every new M2B implementation module, audits every explicit new public
declaration, and compiles `verification/m2b/*Regression.lean`. The `--fresh`
option additionally requires an empty project build cache. Windows uses the
existing `verification/lake.ps1` adapter. Prepare/full runs write generated
checks only beneath `verification/m2b/` and evidence under `audit-evidence/m2b/`.

CI command stages are `init`, `integrity`, `environment`, `cache-modules`,
`dependencies`, `verify`, `suite`, and `complete` in `ci/m2b_audit.py`.
`verify` invokes the full fresh local gate. `suite` extracts the original
M2A ZIP, validates its frozen SHA-256 through the unchanged M2A audit helper,
and executes the unmodified original M2 suite in that isolated copy. Only
third-party dependency packages are shared. Main-checkout M2A builds remain
mandatory independently.

The circularity gate constructs the project import graph, rejects cycles,
then conservatively checks the entire transitive source import closure of
the glue theorem. It rejects imports of `Closure`/`FullClosure` and references
to the downstream type theorem, `symmetric_tail_from_glue_data`, or
`glue_data_symmetric_tail` in every new source in that closure. The frozen
external module necessarily defines the reverse theorem; no new proof may use it.
This is a stronger source/import firewall, not a claim of extracting Lean's
constant-level dependency graph. The separately compiled exact statement
checks and exhaustive kernel axiom roots establish the proof/type gate.

The workflow uploads `P21_M2B_TRUE_AUDIT_EVIDENCE`, including failed runs.
All requested artifact filenames are mandatory; `complete` fails if any
stage/report is absent or either theorem is missing. No script declares
the work frozen or grants a TRUE AUDIT ruling.

Integration note: existing M1 and M2A workflows enforce earlier exact source
inventories and cannot accept additional M2B Lean files. Their branch filters
must be adjusted by the integration owner to skip the M2B audit branch.
Those frozen/previous workflow files are not edited by this addition.
