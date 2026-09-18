# P5 PATH Exclusion Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the unchanged PATH input impossible and expose residual-free post-PATH selected-terminal wrappers.

**Architecture:** New narrowly scoped modules follow publication P5.0 through P5.7. Actual-return structures, signed-root structures, full reversal transport, and pure-H comparison lemmas keep the actuality and criticality firewalls explicit.

**Tech Stack:** Lean 4.24.0, pinned Mathlib, Lake, Python 3 audit tooling, GitHub Actions.

**Spec:** `docs/superpowers/specs/2026-09-18-p5-path-exclusion-design.md`; authoritative request: `verification/p5/REQUEST.md`.

## Global Constraints

- Frozen mathematical base is exactly `fd4ea0c7cbc57df6e935790a1387242bcf9e0087`.
- No pre-existing mathematical Lean source may change.
- `PathInput` and `TerminalInputExists` remain unchanged.
- Actual factorizations use nonnegative coefficients of the same named element.
- Criticality is called only after eliminating the m-coordinate.
- No Section 6 or later theorem may be imported into P5.
- Project-specific axioms and proof-debt tokens remain zero.

---

### Task 1: Freeze inventory, statement gate, and P5.0 setup

**Files:**
- Create: `verification/p5/StatementGate.lean`
- Create: `P21/Nonsymmetric/Path/Setup.lean`

**Interfaces:**
- Consumes: frozen `PathInput`, `HerzogCriticalData` relations.
- Produces: `PathInput.beta`, `alpha`, `P0`, `T`; positivity and canonical row identities.

- [ ] **Step 1: Write the failing statement gate**

```lean
import P21.Nonsymmetric.Extraction
#check P21.Nonsymmetric.PathInput.beta_pos
#check P21.Nonsymmetric.PathInput.P0_eq
```

- [ ] **Step 2: Run the gate and verify unknown-constant failures**

Run: `lake env lean verification/p5/StatementGate.lean`
Expected: failure naming `PathInput.beta_pos` first.

- [ ] **Step 3: Implement derived coordinates and proofs in `Setup.lean`**

```lean
namespace P21.Nonsymmetric.PathInput
def beta (P : PathInput s F D) : ℤ := D.b 0 - P.lambda
def alpha (P : PathInput s F D) : ℤ := D.a 2 - P.nu
def P0 (P : PathInput s F D) : ℤ := D.rho 0 - P.lambda
def T (P : PathInput s F D) : ℤ := D.rho 2 - P.nu
end P21.Nonsymmetric.PathInput
```

- [ ] **Step 4: Compile the gate and module**

Run: `lake env lean P21/Nonsymmetric/Path/Setup.lean` and the statement gate.
Expected: both exit 0.

- [ ] **Step 5: Commit the setup gate**

```text
git add P21/Nonsymmetric/Path/Setup.lean verification/p5/StatementGate.lean
git commit -m "prove P5 path setup coordinates"
```

### Task 2: Actual returns and full reversal

**Files:**
- Create: `P21/Nonsymmetric/Path/Returns.lean`
- Create: `P21/Nonsymmetric/Path/Dual.lean`
- Extend: `verification/p5/StatementGate.lean`

**Interfaces:**
- Consumes: Q membership, missing direction, singleton status, relabel APIs.
- Produces: `TailReturn`, left/right endpoint return constructors, `PathInput.reverse` and involutive field equations.

- [ ] **Step 1: Add failing checks for `TailReturn` and `PathInput.reverse`**
- [ ] **Step 2: Verify the checks fail on absent declarations**
- [ ] **Step 3: Implement return extraction from the same `ActualFactorization4`, proving the removed coordinate zero and m-level positive**
- [ ] **Step 4: Implement all fields of full left-right reversal and prove the gate**
- [ ] **Step 5: Commit with `git commit -m "add actual PATH returns and reversal"`**

### Task 3: Genuine PAIR and exhaustive central split

**Files:**
- Create: `P21/Nonsymmetric/Path/Pair.lean`
- Create: `P21/Nonsymmetric/Path/NoPairNormalization.lean`
- Extend: `verification/p5/StatementGate.lean`

**Interfaces:**
- Produces `PairData` with `X,H0,Z ≥ 0`, normalized actual central factorizations, `PFreeData`, and
  `pair_or_pfree_or_dual : PairData ... ∨ PFreeData ... ∨ PFreeData ...reverse...`.

- [ ] **Step 1: Add failing checks for all structures and the exhaustive split**
- [ ] **Step 2: Compile and confirm the missing declaration failure**
- [ ] **Step 3: Implement actual `qA+m` and `qB+m` tail factorizations**
- [ ] **Step 4: Implement within-factorization HCR reductions using the sum of reducible coefficients as termination measure**
- [ ] **Step 5: Compare normalized vectors in the three `H0/J0` cases and derive exact PFREE or transported dual PFREE**
- [ ] **Step 6: Compile and commit with `git commit -m "prove PATH pair or PFREE split"`**

### Task 4: PAIR weak root, walls, and finite normalization

**Files:**
- Create: `P21/Nonsymmetric/Path/WeakRoot.lean`
- Create: `P21/Nonsymmetric/Path/RootNormalization.lean`
- Extend: `verification/p5/StatementGate.lean`

**Interfaces:**
- Produces signed `WeakRoot`, reusable `weak_root_walls`, signed HCR normalization step, and `NormalizedRoot` with `b2 ≤ K < rho2`.

- [ ] **Step 1: Add failing checks proving signed roots expose equality and bounds but no automatic membership**
- [ ] **Step 2: Verify failure before implementation**
- [ ] **Step 3: Derive the PAIR root and strong-left orientation via formal reversal**
- [ ] **Step 4: Prove `S<R` using the actual LK return, then `e≥T` using the same W**
- [ ] **Step 5: Implement well-founded descent on positive integer K and prove every WeakRoot hypothesis is preserved**
- [ ] **Step 6: Compile and commit with `git commit -m "normalize PATH weak roots"`**

### Task 5: Endpoint level and PAIR absorption

**Files:**
- Create: `P21/Nonsymmetric/Path/EndpointLevel.lean`
- Extend: `verification/p5/StatementGate.lean`

**Interfaces:**
- Produces the C-cap, `ell ≥ 2` for every genuine LJ, and contradiction for either PAIR orientation.

- [ ] **Step 1: Add failing checks for C-cap, endpoint level, and PAIR exclusion**
- [ ] **Step 2: Verify failure**
- [ ] **Step 3: Prove the exact F identity used by the C-cap**
- [ ] **Step 4: Under `ell=1`, eliminate m and call k-criticality on the resulting pure-H relation**
- [ ] **Step 5: Build the coefficientwise nonnegative factorization of F and transport the opposite orientation**
- [ ] **Step 6: Compile and commit with `git commit -m "exclude the PATH pair branch"`**

### Task 6: PFREE sign interface

**Files:**
- Create: `P21/Nonsymmetric/Path/PFreeSign.lean`
- Extend: `verification/p5/StatementGate.lean`

**Interfaces:**
- Produces M+/M-, actual right-singleton returns, four F-absorption certificates, unit levels `r=s=1`, endpoint caps, and `F0 ≥ 1`.

- [ ] **Step 1: Add failing checks that expose eta without a sign field and require a theorem for `F0_pos`**
- [ ] **Step 2: Verify failure**
- [ ] **Step 3: Derive exact signed identities and actual returns from qR**
- [ ] **Step 4: Prove the four absorption certificates and force both return levels to one**
- [ ] **Step 5: Eliminate m, split `V≥Z`/`V<Z`, and use only pure-H criticality**
- [ ] **Step 6: Compile and commit with `git commit -m "prove the PATH PFREE sign"`**

### Task 7: PFREE absorption and repaired FIX-J

**Files:**
- Create: `P21/Nonsymmetric/Path/PFreeAbsorption.lean`
- Extend: `verification/p5/StatementGate.lean`

**Interfaces:**
- Produces direct absorption for `ell≥2`, the level-one split, and exact FIX-J using `Pc=rho0` followed by subcritical j/k criticality.

- [ ] **Step 1: Add failing checks for `pFree_direct_or_fixJ`**
- [ ] **Step 2: Verify failure**
- [ ] **Step 3: Derive C and A caps from the same LJ witness**
- [ ] **Step 4: Prove direct F absorption for `ell≥2`**
- [ ] **Step 5: Close `Qc<0`; in `Qc≥0` prove `Pc=rho0`, then `Qc=b1` and `Kc=a2` without the obsolete upper bound**
- [ ] **Step 6: Compile and commit with `git commit -m "prove repaired PATH PFREE absorption"`**

### Task 8: Double-unit endgame

**Files:**
- Create: `P21/Nonsymmetric/Path/DoubleUnit.lean`
- Extend: `verification/p5/StatementGate.lean`

**Interfaces:**
- Produces the second-return direct absorption, pure-H PIN, ROOT+/ROOT-T, and contradiction from the opposite singleton return.

- [ ] **Step 1: Add failing checks for PIN and double-unit impossibility**
- [ ] **Step 2: Verify failure**
- [ ] **Step 3: Force the second return to unit level and eliminate m between unit returns**
- [ ] **Step 4: Prove PIN by pure-H criticality**
- [ ] **Step 5: Derive exact roots; handle opposite return levels `r≥2` and `r=1` with actual F absorption or subcritical k-criticality**
- [ ] **Step 6: Compile and commit with `git commit -m "exclude the PATH double-unit branch"`**

### Task 9: P5.7 closure and post-PATH integration

**Files:**
- Create: `P21/Nonsymmetric/Path/Closure.lean`
- Create: `P21/Nonsymmetric/Path/Integration.lean`
- Extend: `verification/p5/StatementGate.lean`

**Interfaces:**
- Produces `path_input_impossible`, `SelectedTerminalAfterPath`, same-row `selected_terminal_after_path`, and Q-cardinality wrapper.

- [ ] **Step 1: Add the exact failing check for `path_input_impossible` with no extra hypotheses**
- [ ] **Step 2: Verify failure**
- [ ] **Step 3: Exhaust PAIR/PFREE/dual-PFREE using Tasks 5-8**
- [ ] **Step 4: Remove only the PATH disjunct from `TerminalInputExists`, preserving selected values definitionally**
- [ ] **Step 5: Compile and commit with `git commit -m "close P5 PATH exclusion"`**

### Task 10: Verification, documentation, package, and CI

**Files:**
- Create: `verification/p5/verify.py`, manifests, generated checks, and local evidence
- Create: `ci/p5_audit.py`, `.github/workflows/p5-audit.yml`
- Create: `README_P5.md`, `SOURCE_OF_TRUTH_P5.md`, `P5_STATEMENT_MAP.md`, `P5_PROOF_ROUTE.md`, `P5_DEPENDENCY_DAG.md`
- Create: `verification/p5/package.py`, candidate ZIP and receipt

**Interfaces:**
- Produces reproducible local and GitHub evidence bound to the exact candidate commit.

- [ ] **Step 1: Hash all 101 frozen Lean blobs from the base commit and reject any changed path**
- [ ] **Step 2: Inventory and `#print axioms` every new declaration; scan forbidden proof debt and reverse imports**
- [ ] **Step 3: Empty `.lake/build`, run root build and explicit P5 module build**
- [ ] **Step 4: Run isolated M1, M2A, M2B, M3A, M3B1, M3B2 suites and P5 statement gates**
- [ ] **Step 5: Build the candidate ZIP from tracked source and record SHA-256**
- [ ] **Step 6: Commit, push `p5-path-exclusion`, wait for clean GitHub Actions, and record run/artifact metadata**
