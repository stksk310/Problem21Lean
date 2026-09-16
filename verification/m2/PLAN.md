# M2 Symmetric Tail Implementation Plan

> Use subagent-driven-development for independent proof tasks, with statement and proof review.

Goal: prove publication S3, or its full internal closure with only the explicit gluing normal-form input left open.
Spec: REQUEST.md. The user's detailed mathematical design and execution request authorize implementation.
Architecture: new P21/Symmetric modules import immutable M1; no modification of its umbrella or Lake configuration.
Build new modules with explicit Lake targets in addition to the mandatory default lake build.
Stack: Lean 4.34.0-rc1, exact existing mathlib lockfile, Python standard-library verification.

## Fixed constraints
- Base commit 9464b9cd3b6b070f9fa6d1c212f27065d1eb84b3; branch m2-symmetric-tail.
- Thirteen protected M1 files byte-identical, checked against Git blobs and SHA256 baseline.
- No additional mathematical assumptions except the precisely disclosed gluing data if Gate 0 is open.
- No proof placeholders, extra axioms, opaque escape, or finite search over parameters.
- Publication PDF is authoritative; manuscript navigation and frozen provenance are supporting material.

## Tasks
- [x] Create isolated branch, preserve original inputs, save protected-file baseline.
- [x] Gate 0: search pinned mathlib, record exact available results and missing external theorem.
- [x] TwoGenerator.lean: integer normal forms, differences, symmetry, subcritical facts, exact 2GI.
- [x] Symmetry.lean / StableCore.lean: explicit symmetry, Gamma decomposition, GAP-K, minimum, FS, ideal closure.
- [x] TypeBridge.lean: exact minimal-element bijections, CAN consequence, BRIDGE and TYPE-BRIDGE.
- [x] GlueNormalForm.lean / Raw4.lean: normal-form membership, Frobenius formula, ideal classification and actual RAW4.
- [x] BranchI.lean: same-walk four-hit necessity, predecessor exception, all three exclusions.
- [x] BranchII.lean: all three subcases, positivity and actual PF contradiction.
- [x] Closure.lean: only the genuinely proved full or conditional closure, without hidden branch assumptions.
- [x] Regression examples, declaration/statement map, all-new-declaration axiom inspection, debt and M1 integrity.
- [x] Fresh default and explicit M2 builds; independent source-faithfulness review; single verified ZIP and Japanese report.

## Execution ledger
The exact proof obligations and quantifiers are in REQUEST.md and source_excerpts/m2.
Do not label intermediate foundations as internal closure. Do not invent a candidate status before closure is proved.

Completed as Gate-0 outcome C: exact gluing classification OPEN; full internal closure proved.
Fresh separate-copy verification and all-new-root axiom coverage succeeded.
