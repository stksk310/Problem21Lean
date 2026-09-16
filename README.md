# P21 Lean: FOUNDATION + C2

**Status: M1 CANDIDATE FOR TRUE AUDIT**

This project formalizes the foundation and canonical reduction of the supplied
Journal of Algebra submission, §§1.1 and 2.7–2.12. It does not prove the main
type bound. `P21.P21MainStatement` is explicitly an unproved `Prop` definition.

## Results

| Milestone | Result | Main declarations |
|---|---|---|
| C2.1 | Proved | `canonical_all_nonnegative_gaps`, using `translated_gaps_finite` and `gap_below_pf` |
| C2.2 | Proved | `exact_two_layers`, `a0_lower`, `a1_upper`, `iota_mem_a1`, `iota_involutive`, `iota_order_reverse`, `maximal_a1_set`, `minimal_a1_set`, `minimal_a1_card`, `a0_tail_iff` |
| C2.3 | Proved | `key_return_apery`, `return_coordinate_zero`, `key_support_zero`, `key_pair_return`, `key_support_inclusion`, `supported_rectangle` |
| C2.4 | Proved | `tail_signed_m`, `m_mem_tail_group`, `tail_gcd_eq_one`, `tail_cofinite` |
| C2.5 | Proved | `all_q_row_facts`, `select_four_rows`, `tail_minimal`, `tail_minimal_and_cofinite` |

Full names, types, source anchors, and declaration locations are in
`STATEMENT_MAP.json`, `verification/DECLARATIONS.json`, and `verification/STATEMENTS.txt`.

## Build and reproduce

Pinned toolchain: Lean **v4.34.0-rc1**. Pinned mathlib commit:
`de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11` (tag `v4.34.0-rc1`).
All transitive package revisions are fixed in `lake-manifest.json`.

In an extracted project with elan, Git, and Python 3 installed:

```sh
lake exe cache get
lake build
python verification/verify.py
```

The first command obtains the pinned dependencies and mathlib's compiled cache;
network access and adequate disk space are needed on a fresh machine. The ZIP
contains the complete project sources and lockfile, not the Lean installation
or third-party source/build caches. `verification/verify.py` reruns the build,
generates the source scan and inspection commands, checks all project theorems
and definitions for axiom dependencies, and emits a statement snapshot.

`verification/lake.ps1` is a convenience wrapper for the original Windows
workspace only. It uses a process-local Git ownership allowlist and the installed
toolchain. Ordinary reproduction should use `lake` as above.

## Semantics and boundaries

- All elements, gaps, PF numbers, Frobenius numbers, and arithmetic are in `ℤ`.
- Actual factorizations retain coefficient vectors in `ℕ`. Signed representations
  use `ℤ` and only imply membership in an additive **group**.
- Replacement requires containment in the explicitly supplied actual witness.
  Residual arithmetic is in `ℤ`; each `toNat` conversion has a nonnegativity proof.
- `OffDirection i x` is equivalent to an actual nonnegative representation using
  the other two tail generators. No equality of `D(c)` and `SH(q)` is claimed.
- Four selected rows are an injection `Fin 4 → ℤ`, with `RowFacts` for every row.
  The ambient set `Q` is never assumed to have cardinality exactly four.
- `Setting` records the publication hypotheses, not any C2 conclusion. Four
  minimal indexed generators are irredundant, and their distinctness is proved.
- The finite cardinality convention cannot silently discard an infinite PF set:
  `all_pf_finite` proves finiteness for every `NumericalSemigroup` in this interface.

See `SOURCE_OF_TRUTH.md` for the source comparison and `CODEX_SELF_CHECK.md` for
the self-check scope. Independent mathematical/statement review remains necessary
before any subsequent promotion by the user's control process.


## GitHub reproducibility gate

STATUS: M1 CANDIDATE FOR TRUE AUDIT

M1 scope: FOUNDATION + C2 only.

OPEN: symmetric tail; nonsymmetric classification; PATH; TYPE II; CHAIN;
external structure theorems; Euclidean descent; 715-term certificate;
3234-term certificate; main theorem proof.

The workflow **P21 Lean M1 Audit** runs on pushes, pull requests, and manual
requests in a clean `ubuntu-latest` GitHub-hosted job. It installs elan v4.2.4
from its SHA-256-checked official release and selects exactly the unchanged
`lean-toolchain`. Every dependency must match `lake-manifest.json`.
There is no Actions cache restore and no committed compiled Lean artifact.
The job may download mathlib's pinned third-party cache; cache retrieval failure
falls back to compiling missing dependencies from source. The M1 project itself
always starts without compiled artifacts and runs `lake build`.

The authoritative implementation input is preserved at
`ci/candidate/P21_LEAN_M1_FOUNDATION_C2_CANDIDATE_20260916.zip`.
Its SHA-256 is
`37f7a4163b70effbb294e65c39fa5a36e5ec8d9950769df9568047583335d0db`.
`SOURCE_SHA256_BEFORE_GITHUB.txt` is derived from that ZIP and covers all original
Lean sources, toolchain/lock/config files, and verification scripts (20 files).
CI verifies their bytes both in Git and in the working tree, and checks all other
original files too; only an appended root README section is allowed. The original
`MANIFEST_SHA256.json` remains a manifest of the unmodified candidate, not a claim
that its old README digest covers this appended section.

CI runs a tested lexical proof-debt scanner in addition to the original raw scan.
Nested comments and ordinary/raw strings are distinguished from code; malformed
constructs, interpolated strings, and character/quotation literals require manual
inspection and fail closed.
The original axiom checker accepts only `propext`, `Classical.choice`, and
`Quot.sound`. All original portable verification scripts run unchanged in a
separate temporary copy, because `prepare_reports.py` regenerates inspection
sources. `lake.ps1` is an original Windows path adapter, so Linux uses `lake`
directly. A second pristine copy exercises both modes of the original packaging
script and verifies distribution implementation bytes against the input ZIP.
No supplied manuscript certificate-verifier scripts are extracted or executed.

Each run uploads **P21_M1_TRUE_AUDIT_EVIDENCE**, including environment and
versions, build exit code, source hashes, proof-debt and axiom results,
verification-suite output, dependency revisions, and the exact checked commit.
Artifacts are retained for 90 days; download them for longer-term preservation.
A successful workflow establishes CI reproducibility evidence only. It does not
promote the mathematical audit status.

CI implementation details and the user's execution scope are recorded in
`ci/PLAN.md` and `ci/REQUEST.md`. Official installation/cache/action references:
[elan](https://github.com/leanprover/elan),
[mathlib cache at the pinned revision](https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Cache/README.md),
[artifact uploads](https://github.com/actions/upload-artifact).
