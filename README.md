# P21 Lean M2A — Internal symmetric closure

STATUS: M2A INTERNAL SYMMETRIC CLOSURE CANDIDATE FOR TRUE AUDIT

STD_SYM_GLUE OPEN
FULL S3 OPEN

This project proves the complete internal symmetric-tail argument in publication
Section 3 and Appendix A, conditional only on the explicitly supplied standard
gluing normal form. It builds on the unchanged M1 input at commit
`9464b9cd3b6b070f9fa6d1c212f27065d1eb84b3`.

The final theorem is:

```lean
theorem P21.Symmetric.symmetric_tail_from_glue_data
    (g : P21.Generators) (setting : g.Setting) (F : ℤ)
    (hF : setting.semigroup.IsFrobenius F)
    (hcan : setting.semigroup.Canonical F g.m)
    (G : P21.Symmetric.SymmetricGlueData g) :
    setting.semigroup.type ≤ 4
```

The data supplies a permutation, x=du, y=dv, z=w, d,u,v≥2,
gcd(u,v)=gcd(d,w)=1 and an actual nonnegative representation of w in <u,v>.
The theorem that produces this data from symmetry alone is not yet proved.
See `STD_SYM_GLUE_OPEN.md` for its exact statement and next proof obligation.

## Proved scope

- Integer two-generator normal form, representation difference, symmetry, all
  subcritical coefficient facts, and exact 2GI.
- Stable core with every natural index (including zero), GAP-K, FS, the ideal
  property, PF correspondence, BRIDGE and exact TYPE-BRIDGE.
- Gluing normal form and Frobenius formula from explicit data; two-generator
  ideal classification; RAW4 extraction from type at least five.
- Cross-layer rigidity, actual PF provenance, ALL-AP, QM and non-exclusive SPLIT.
- Branch I: same-walk four-hit necessity, the N=1 predecessor exception,
  X-only/Y-only/XY exclusions, and positivity of E=w-L.
- Branch II: k0=1 reduction to the independently proved Branch I; k0=0,e=0;
  and the complete positive-e cross-core argument with the actual predecessor.
- The resulting type bound from explicit glue data.

All 13 protected M1 files, the toolchain and dependencies included, retain their
original bytes. All new mathematics is under `P21/Symmetric` and `P21/External`.
`P21.lean` remains the frozen M1 umbrella, so default `lake build` alone does not
build M2. Run the explicit M2 target or the complete verifier below.

## Reproduction

Lean: `leanprover/lean4:v4.34.0-rc1`.
mathlib: `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`, with all other revisions in the
unchanged `lake-manifest.json`.

```text
lake build
lake build P21.Symmetric.Closure
python3 verification/m2/verify.py
```

The Python verifier uses only the standard library. On Windows it uses the
preserved local `verification/lake.ps1` path adapter; on other platforms it uses
`lake` on PATH. Adapt a copy of that Windows path adapter to your own installed
Lean location if needed; do not alter the pinned toolchain or dependency files.
The published legacy M1 GitHub workflow checks its original M1 ZIP; it is not an
M2 audit job and is omitted from this source distribution. No M2 GitHub CI claim
is made here.

The verifier explicitly builds every M2 module, checks every theorem/definition
root for permitted axioms, runs compile-time regressions, scans all project-owned
Lean code lexically for proof debt, and rechecks M1 integrity. See `BUILD_LOG.txt`,
`AXIOM_REPORT.txt`, `PROOF_DEBT_REPORT.txt`, `M1_FROZEN_INTEGRITY_REPORT.txt`, and
`verification/m2/` for evidence. The distribution contains no project build cache.

## Remaining scope

OPEN: STD_SYM_GLUE and therefore full S3; nonsymmetric classification; PATH;
TYPE II; CHAIN; other external structure theorems; Euclidean descent;
715-term certificate; 3234-term certificate; the main theorem proof.

This is a candidate for independent review. `M2_STATEMENT_MAP.md` maps all new
declarations to the publication. `M2_DEPENDENCY_DAG.md` records proof dependencies.
