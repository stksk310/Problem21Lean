# C8 Chain Boundary/Window Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize publication Section 8 from the frozen C7 `ChainCore` API through the exhaustive `RegionU ∨ RegionD` handoff.

**Architecture:** Add a forward-only family of focused modules under `P21/Nonsymmetric/Chain/C8/`. Each module consumes compiled declarations from its predecessor, preserves actual-factorization provenance in structures, and exposes the exact named equations and inequalities needed by the next gate. C7 mathematical source remains byte-identical to commit `80b36191937b2e2f0dc251ac6006d63f088e03b2`.

**Tech Stack:** Lean 4.34.0-rc1, pinned mathlib, `omega`, `linarith`, `nlinarith`, `ring`, existing `integer_kernel_span`, Python verification scripts, GitHub Actions.

**Spec:** `verification/c8/REQUEST.md` (verbatim user Section 8 request; created with the verification harness task)

## Global Constraints

- Create only new C8 mathematical modules; do not edit any Lean file present at frozen commit `80b36191937b2e2f0dc251ac6006d63f088e03b2`.
- The only permitted C7 edit is the documentation-only naming repair in `C7_STATEMENT_MAP.md`.
- Signed identities and actual semigroup membership remain distinct.
- PACKET must record the same-element lift and coefficientwise common-source removal.
- Strict results explicitly require `K.chain.alpha < K.Croot`; boundary results never use `FK_strong`.
- Do not import Section 9, Section 10, CHAIN impossibility, or the final theorem.
- No finite numerical scan, `sorry`, `admit`, new axiom, `native_decide`, `run_tac`, or opaque proof escape.

---

### Task 1: Exact first-fit arithmetic and actual upper face

**Files:**
- Create: `P21/Nonsymmetric/Chain/C8/FirstFit.lean`
- Test: `verification/c8/FirstFitGate.lean`

**Interfaces:**
- Consumes: `ChainCore`, `Returns`, `Caps`, `Slopes`, exact C7 row/root equations.
- Produces: `hrj`, exact integer ceiling `nZeta`, `IZeta`, `JZeta`, `FirstFit`, `firstCaps`, `Xi`, `omegaHatActual`.

- [ ] Prove the alternative actual W face and arbitrary signed HRJ equation.
- [ ] Define integer ceiling using `Int.ediv` and prove its lower/upper characterization.
- [ ] Prove `IZeta ∈ [0,d-1]`, strict growth of `nZeta`, `nZeta 1 ≥ 2`, and the exact `J_d` identity.
- [ ] Construct the nonempty fitting set, its genuine minimum `zhat`, and FIRST-CAPS.
- [ ] Show `Xi ≤ 0` gives a coefficientwise actual factorization of `F`; conclude `Xi ≥ 1` and construct the zero-k actual `OmegaHat` factorization.
- [ ] Run `lake build P21.Nonsymmetric.Chain.C8.FirstFit` and `lake env lean verification/c8/FirstFitGate.lean`; commit.

### Task 2: Central FK, same-element PACKET, and walls

**Files:**
- Create: `P21/Nonsymmetric/Chain/C8/Packet.lean`
- Test: `verification/c8/PacketGate.lean`

**Interfaces:**
- Consumes: `FirstFit`, C7 `FI_A`, `FI_B`, `FJ` and actual return witnesses.
- Produces: signed `centralFK`, actual `centralFKUpper`, `Packet` with common upper element, `boundaryWall`, `windowWall`.

- [ ] Derive C-FK as signed only and its strict zero-k upper face as actual.
- [ ] Prove `DF ≥ beta > 0`, `EF ≥ a_j > 0` from FIRST-CAPS.
- [ ] Define a `Packet` structure carrying both nonnegative sides, same named upper element, common `I/J` containment, and the max-split equality.
- [ ] Insert the boundary packet separately into EA, EB and Qj to prove BOUNDARY-WALL.
- [ ] Insert the general packet only into FI-A and FJ to prove WINDOW-WALL; encode a regression showing no EB T-window theorem is exported.
- [ ] Build both gate files and commit.

### Task 3: Pure-H kernel coefficients and ONE relations

**Files:**
- Create: `P21/Nonsymmetric/Chain/C8/KernelOne.lean`
- Test: `verification/c8/KernelOneGate.lean`

**Interfaces:**
- Consumes: WINDOW-WALL and frozen `integer_kernel_span`.
- Produces: `EAKernel`, `QJKernel`, `EAOne`, `QJOne` with positive kernel coefficients and second coefficient exactly one.

- [ ] Eliminate m completely in EA and invoke `integer_kernel_span` on the exact pure-H vector.
- [ ] Prove both EA coefficients positive; use HRJ minimization plus WINDOW-WALL to exclude `y ≥ 2`.
- [ ] Repeat independently for Qj and exclude `v ≥ 2`.
- [ ] Expose the exact EA-ONE/QJ-ONE coordinate identities and build the theorem-level gate; commit.

### Task 4: Empty triangle, determinant one, parameters and level split

**Files:**
- Create: `P21/Nonsymmetric/Chain/C8/Triangle.lean`
- Test: `verification/c8/TriangleGate.lean`

**Interfaces:**
- Consumes: `EAOne`, `QJOne`, WINDOW-WALL.
- Produces: internal lattice-index lemma, `detOne`, `ParamData`, exhaustive `LevelSplit`.

- [ ] Formalize affine I/J values on the closed triangle and exclude every nonvertex integer point.
- [ ] Prove an elementary determinant/index lemma internally: determinant at least two supplies a nonzero parallelogram representative whose point or reflection lies in the triangle.
- [ ] Apply it to prove `x*M-z*L=1`; do not add DET1 as a field or assumption.
- [ ] Derive all PARAM identities and `V>0` by ring arithmetic.
- [ ] Prove the exact two-branch LEVEL-SPLIT with no third case; build and commit.

### Task 5: k-ceiling and boundary synchronization

**Files:**
- Create: `P21/Nonsymmetric/Chain/C8/KCeiling.lean`
- Create: `P21/Nonsymmetric/Chain/C8/BoundarySync.lean`
- Test: `verification/c8/BoundaryGate.lean`

**Interfaces:**
- Consumes: PARAM, actual FJ, exact EA/EB rows.
- Produces: `H0_nonneg`, general `kCeiling`, boundary-only simplification, actual synchronized level-one EB, boundary unit identities.

- [ ] Use EA-ONE as an exact actual packet inside the same FJ factorization to prove epsilon ceiling and `H0 ≥ 0`.
- [ ] Derive general K-CEILING retaining `L*Croot-alpha`.
- [ ] Under `Croot=alpha`, compare exact EA/EB equations, prove EB synchronization and derive the boundary level-one system.
- [ ] Prove boundary `H0<0`, excluding the level-one alternative; build and commit.

### Task 6: Boundary multiplicity and complete boundary elimination

**Files:**
- Create: `P21/Nonsymmetric/Chain/C8/BoundaryMultiplicity.lean`
- Test: `verification/c8/BoundaryMultiplicityGate.lean`

**Interfaces:**
- Consumes: strict boundary level split and synchronized equations.
- Produces: positive common cross-product scale, `boundMult`, `posCoeff`, `boundaryImpossible`.

- [ ] Derive both cross-product triples from equations and retain the positive common scale `sigma` supplied by primitive-generator proportionality.
- [ ] Prove BOUND-MULT by strict multiplicity without normalizing `sigma` to one.
- [ ] Expand the publication POS-COEFF decomposition and prove every coefficient positive.
- [ ] Combine POS-COEFF with BOUND-MULT to close `Croot=alpha`; build and commit.

### Task 7: Strict packet window

**Files:**
- Create: `P21/Nonsymmetric/Chain/C8/StrictWindow.lean`
- Test: `verification/c8/StrictWindowGate.lean`

**Interfaces:**
- Consumes: strict level branch, PARAM, K-CEILING, multiplicity.
- Produces: STRICT-J, exact EX1/EX2/EX3 classification, STRICT-K decompositions, `strictWindow`, shallow closure and deep inequalities.

- [ ] Prove STRICT-J and expand `mhat-Jcal` with exact `Ea`, positive delta/beta coefficients.
- [ ] Classify `Ea<0` symbolically into exactly EX1, EX2, EX3 using integer inequalities.
- [ ] Prove `Aprime>0`, `Bprime>0`, STRICT-K and the Dbase decomposition.
- [ ] Close Q=1 and each exception with exact positive coefficients; conclude `Croot>alpha ∧ chi≤T ∧ Li≥2 → False`.
- [ ] Derive shallow strict closure and exact Region-D source-shortage inequalities; build and commit.

### Task 8: Unit boundary and surviving RegionU

**Files:**
- Create: `P21/Nonsymmetric/Chain/C8/UnitBoundary.lean`
- Test: `verification/c8/UnitBoundaryGate.lean`

**Interfaces:**
- Consumes: WINDOW-WALL failure at `Li≥2`, I-level, LEVEL-SPLIT, K-CEILING, COMPACT.
- Produces: `UnitParam`, exact unit first point/eta, compact specialization, UNIT-MULT, `Du>0`, `Q>R`, actual level-one EB.

- [ ] Prove `Li=1`, `lambda=d`, `q0=2` and the exceptional level split.
- [ ] Derive UNIT-PARAM, the exact first-fit values, UNIT-ETA and compact specialization.
- [ ] Prove all actual EA returns in a surviving unit configuration have level one without assuming uniqueness.
- [ ] Prove Mdelta/Mbeta positivity and UNIT-MULT; conclude `Du>0` and `Q>R`.
- [ ] Construct the level-one EB factorization as an actual witness; build and commit.

### Task 9: Region structures and exhaustive handoff

**Files:**
- Create: `P21/Nonsymmetric/Chain/C8/Handoff.lean`
- Create: `P21/Nonsymmetric/Chain/C8.lean`
- Test: `verification/c8/BranchTable.lean`

**Interfaces:**
- Consumes: all preceding C8 gates.
- Produces: `RegionU`, `RegionD`, `ChainCore.c8_handoff`, complete four-entry branch table.

- [ ] Define `RegionU` and `RegionD` with original `K`, `E`, caps/slopes, actual provenance, and all downstream equations as fields or derivable theorems.
- [ ] Split on `Croot=alpha`, `chi≤T`, and `Li≥2`; discharge each excluded branch with the scoped theorem and construct U/D in survivors.
- [ ] Prove the exact branch-table regression and public aggregate import; build and commit.

### Task 10: Audit harness, candidate, push and CI

**Files:**
- Create: `verification/c8/*`, `.github/workflows/c8-audit.yml`, C8 documentation and candidate receipt.
- Modify: `NEXT_RESTART.md`.

**Interfaces:**
- Consumes: complete C8 public interface.
- Produces: reproducible candidate ZIP and TRUE AUDIT evidence artifact.

- [ ] Add statement/declaration/axiom/debt/DAG/frozen-integrity checks and M1–C7 regressions.
- [ ] Run project-local fresh root build, explicit C8 build and every regression suite.
- [ ] Verify C7 mathematical source hashes against `80b3619`; require proof debt and project-specific axioms to be zero.
- [ ] Build `P21_LEAN_C8_CHAIN_BOUNDARY_WINDOW_CANDIDATE_20260918.zip`, record SHA-256, commit and push only the final candidate.
- [ ] Wait for clean GitHub Actions, verify `P21_C8_TRUE_AUDIT_EVIDENCE`, and record run/artifact IDs and digests.
