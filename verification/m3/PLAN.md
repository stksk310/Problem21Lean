# M3 nonsymmetric G4 implementation plan

**Goal:** Prove nonsymmetric selected-four classification and the exact Section
4.16 terminal inputs, then reproduce the exact source on GitHub CI.
**Spec:** REQUEST.md, supplied by the user; publication PDF takes mathematical
precedence over the frozen verification edition and existing Lean code.
**Architecture:** New P21/Nonsymmetric modules only; primitive tail/critical
relations feed Herzog data, actual-row geometry, level matching, color cap,
classification and extraction. No terminal exclusion feeds backwards.
**Tech stack:** Frozen Lean/mathlib and existing Python evidence infrastructure.

## Global constraints

- Base 9a9e01c401a934cfca2da15026986b0ecf83ff4f; branch m3-nonsym-g4; no main merge.
- Every existing project Lean file is byte immutable. Preserve old verification
  sources and toolchain/lockfile too; wrappers go in new modules.
- No sorry, admit, axiom, unsafe, opaque escape, native_decide or run_tac.
- Actual coefficients are nonnegative and tied to the same element. Criticality
  applies only after complete elimination of the m-coordinate.
- Four selected Q rows never implies Q has cardinality four.
- No conjecture is disguised as a proved intermediate structure. Open inputs,
  if any remain, must be explicit Lean propositions and exact conditional scope.

## Tasks and proof gates

- [x] Establish exact base worktree and authoritative local source availability.
- [x] Record source hashes and PDF page anchors; compare Section 4/Appendix B.
- [x] Herzog: inspect pinned mathlib, reuse actual CriticalRelation; prove
  positive nonsymmetric critical cycle, primitive formulas and exact PF pair.
- [x] CriticalBox/Kernel: prove subcritical factorization uniqueness, then the
  exact saturated integer kernel basis from positive minimal critical data.
- [x] Rows/Singletons: actual Q-row package, complement antichain, pure singleton
  ray, bounds on every complement/W factorization and attained W coordinate.
- [x] Atlas/ComplementGeometry: maximal missing-direction gap yields six arms;
  prove critical complement box, corners and coexistence restrictions.
- [x] MatchedPair/ReturnLevels: synchronize depths; choose independent positive
  return minima; same-element four caps; exclude unequal levels including
  g=0/alpha=0 signed intermediate cases; exclude all singleton coexistence.
- [x] SameColor/MixedColor: exact pair geometry and cyclic/color transformations.
- [x] ThreeSingletons: all W fibers first confined to critical box, then unique;
  show full Q cardinality three.
- [ ] ColorCap: exact relative lattice tetrahedron and White consequence,
  minimal m-level k=1, symbolic finite box-path positive exit; both colors.
- [x] Classification/Extraction, conditional on the two explicit ColorCap residuals:
  finite selected-four case analysis; extract
  exact PATH, TYPE II, CHAIN data in the same semigroup/F/m/W.
- [x] Review mathematical scope; exact statement and axiom/debt regressions.
- [x] Fresh local builds and unchanged M1/M2A/M2B suites in isolated copies.
- [ ] Immutable candidate ZIP, exact Git source comparison, push, clean M3 CI,
  downloaded artifact verification, receipt and Japanese final report.

## Ownership and interface review

Root owns actual row geometry, integration, verification and delivery. A Herzog
worker owns HerzogData/HerzogClassification; a kernel worker owns CriticalBox/
Kernel; a ColorCap worker first audits and formalizes the independent Appendix B
input. Shared interfaces are sent explicitly before dependent implementations.
Builds must be serialized or run in separate build copies to avoid Lake races.

Ruling: the user's detailed specification already authorizes implementation and
GitHub CI; no additional design approval is needed. This research-sized proof is
developed in checked lemmas rather than pretending a complete proof script is
known before the route audit. Full closure remains the target; Section 37 governs
honest reduced scope if a mathematical input cannot be completed.
