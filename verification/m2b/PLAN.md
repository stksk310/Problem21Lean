# M2B direct three-generator classification implementation plan

Specification: REQUEST.md. Base: a0ec51cf93326b6f8dbf22647cfeecf81a931bd8.
All existing Lean files, verification/m2 contents and pinned toolchain/configuration
are immutable. New assumptions in the public gluing theorem are prohibited.

- [x] Record frozen source hashes and short pinned-mathlib route audit.
- [x] TailNumericalSemigroup: obtain positivity, nonnegativity, minimality,
  cofiniteness and common-divisor-one from Setting + integer symmetry only.
- [x] CriticalRelations: least positive multiples with actual off-direction
  witnesses; analyze symmetric three-generator relation rigidity.
- [x] GcdDecomposition: construct primitive quotients and the actual permutation
  gluing data from a mathematically proved special pair, retaining nonnegative witnesses.
- [x] SymmetricRigidity: prove the special pair exists without canonical or
  supplied critical-relations assumptions; keep the exact residual obligation
  explicit if closure is not attained.
- [x] GlueExistence and FullClosure: prove the exact frozen external Prop, then
  use M2A closure in a separate module. Never use M2A closure to prove classification.
- [x] Add theorem-level regression checks, all-declaration axiom/debt checks,
  frozen integrity checks and noncircular import/dependency evidence.
- [x] Fresh local root, M2A, M2B builds plus original verifier in an isolated copy.
- [ ] Package exact candidate, push separate branch, run clean GitHub CI,
  verify downloaded artifact digest and create final single ZIP/receipt.

Work ownership: root owns tail numerical foundations and integration; independent
workers own critical-relation/rigidity route analysis and quotient arithmetic.
Interfaces are explicit structures/theorems and are reviewed before integration.
No broad complete-intersection library is planned. Full closure is the primary
target; the user permits a precise, substantially smaller best reduction if needed.
