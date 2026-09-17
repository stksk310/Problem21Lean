# M3B2 DPE / Box Positive Exit Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the exact frozen `P21.Nonsymmetric.ColorCap.BoxPositiveExitStatement` with no extra mathematical assumptions and compose it with frozen MINBOX to obtain residual-free ColorCap and selected-four wrappers.

**Architecture:** Preserve every Lean file at base `9c9a1b6f76f78a2927b12bf8a0663dfdc29ea7a1`. New modules first recover the chronological firing trace and its exact endpoint from `BoxPath`, then prove the common prefix/rank arithmetic, the two terminal two-color cases, and both first-third-color cases. A closure module exhausts the actual trace and an integration module composes DPE with `minimum_one_proved` and the frozen conditional wrappers.

**Tech Stack:** Lean `4.34.0-rc1`, pinned mathlib, Lake, Python verification scripts, GitHub Actions.

**Spec:** `C:/Users/stksk/.codex/attachments/7dcc207b-af5d-4674-9bed-411215ca4099/pasted-text.txt`

## Global Constraints

- Exact base: `9c9a1b6f76f78a2927b12bf8a0663dfdc29ea7a1`; branch `m3b2-dpe-box-positive-exit`; no main merge.
- All pre-existing mathematical Lean files are byte-immutable.
- Target is exactly `BoxPositiveExitStatement`; no extra hypotheses, preselected firing order, or strengthened residue bounds.
- Every chronological count or prefix must be derived from the supplied `BoxPath`.
- `K_s = 1`, `q = 0`, and `X = 0` are explicit regression boundaries.
- No `sorry`, `admit`, `axiom`, `unsafe`, proof-opaque escape, `native_decide`, or `run_tac` proof substitution.
- Weighted certificates use nonnegative integer row counts and coefficientwise nonnegative vectors.
- Final fresh build explicitly targets every new module and reruns M1/M2A/M2B/M3A/M3B1 suites.

---

### Task 1: Chronological BoxPath trace

**Files:**
- Create: `P21/Nonsymmetric/ColorCap/DPE/Trace.lean`
- Create: `verification/m3b2/TraceRegression.lean`

**Interfaces:**
- Consumes: `BoxPath D.upper D.rows t D.x u`, `BoxInput.in_box_fire_unique`.
- Produces: `BoxPath.trace`, trace length, endpoint execution/count formula, prefix reconstruction, and actual in-box state for each proper prefix.

- [ ] **Step 1: Write the failing regression** importing `DPE.Trace` and checking trace length, endpoint reconstruction, and prefix-state membership.
- [ ] **Step 2: Run** `verification/lake.ps1 env lean verification/m3b2/TraceRegression.lean`; require failure because `DPE.Trace` is absent.
- [ ] **Step 3: Implement** a recursive trace extracted from the proof, with no trace supplied as an assumption:

```lean
def BoxPath.trace : {t u v : _} -> BoxPath upper C t u v -> List (Fin 3)
theorem BoxPath.trace_length (h : BoxPath upper C t u v) : h.trace.length = t
theorem BoxPath.exec_trace (h : BoxPath upper C t u v) : exec C h.trace u = v
theorem BoxPath.prefix_state_in_box (h : BoxPath upper C t u v)
    (hp : l <+: h.trace) : InBox upper (exec C l u)
```

- [ ] **Step 4: Prove** the endpoint row-count formula and uniqueness of the next chronological firing using `in_box_fire_unique`.
- [ ] **Step 5: Rerun** the trace regression and targeted module build; require success.

### Task 2: Canonical first firing and exact START transport

**Files:**
- Create: `P21/Nonsymmetric/ColorCap/DPE/Rotation.lean`
- Create: `verification/m3b2/RotationRegression.lean`

**Interfaces:**
- Consumes: `BoxInput.initial_positive_firing`, `rotatePerm`, trace layer.
- Produces: cyclic `BoxInput` transport, path/fire/InBox transport, and a canonical first-row path satisfying START.

- [ ] **Step 1: Write the failing regression** checking that any initial positive firing either exits immediately or transports to row `0` with `x 0 < y 0`, `y 1 + b 1 < x 1`, and `y 2 < x 2`.
- [ ] **Step 2: Run the regression** and observe the missing transport theorem.
- [ ] **Step 3: Implement** coordinate and row transport under `rotatePerm i`; prove `fire`, `InBox`, and `BoxPath` commute with it by `fin_cases`.
- [ ] **Step 4: Derive START** from the genuine first in-box firing, never from a WLOG assumption.
- [ ] **Step 5: Rerun** both trace and rotation regressions.

### Task 3: Successful chronological prefix

**Files:**
- Create: `P21/Nonsymmetric/ColorCap/DPE/SuccessfulPrefix.lean`
- Create: `verification/m3b2/PrefixRegression.lean`

**Interfaces:**
- Consumes: canonical trace and frozen `crossing_separator`, `successful_prefix_separator`, `prefix_residue_antichain`, `prefix_residue_distinct`, `residue_slot_bound`.
- Produces: actual chronological crossing records `N_q`, `E_q`, `U_q`, RES ranges, PREFIX, LR, and ELR with explicit positivity/range premises.

- [ ] **Step 1: Write failing theorem-level tests** for successful-crossing membership in the actual trace and for ELR refusing missing `E/U` range inputs.
- [ ] **Step 2: Verify RED** by compiling the regression before the module exists.
- [ ] **Step 3: Define** a crossing record that stores the exact trace split and in-box proof, rather than free arithmetic counts.
- [ ] **Step 4: Prove** RES and chronological initial-prefix indexing by induction over the trace and unique in-box continuation.
- [ ] **Step 5: Derive** PREFIX, coordinate injectivity, LR, and ELR via the frozen arithmetic lemmas and finite slot counting.
- [ ] **Step 6: Rerun** regressions and explicit builds.

### Task 4: Reciprocal rank with actual-state provenance

**Files:**
- Create: `P21/Nonsymmetric/ColorCap/DPE/ReciprocalRank.lean`
- Create: `verification/m3b2/ReciprocalRankRegression.lean`

**Interfaces:**
- Consumes: chronological successful prefix and its final row-0 run.
- Produces: `H + E + V <= a + d - b`, with each dual residue tied to an original traversed trace state.

- [ ] **Step 1: Write failing regressions** for `K_s = 1` and a general shifted state; the former must reference the initial row-0 run and no index-zero crossing object.
- [ ] **Step 2: Verify RED** against the absent theorem.
- [ ] **Step 3: Prove** dual PREFIX algebraically from original PREFIX for every `1 <= s < H`.
- [ ] **Step 4: Construct** the original count pair `(s + K_s, K_s)` and prove its state is an actual prefix state; split `K_s = 1`, `K_s < Q`, and `K_s = Q`.
- [ ] **Step 5: Apply** injectivity/antichain slot counting to derive reciprocal rank.
- [ ] **Step 6: Rerun** regressions and dependency checks.

### Task 5: Complete two-color terminal exclusions

**Files:**
- Create: `P21/Nonsymmetric/ColorCap/DPE/TwoColor12.lean`
- Create: `P21/Nonsymmetric/ColorCap/DPE/TwoColor13.lean`
- Create: `verification/m3b2/TwoColorRegression.lean`

**Interfaces:**
- Consumes: START, successful prefix, LR/ELR/reciprocal rank, frozen positive minors, and `weighted_certificate_impossible`.
- Produces: contradictions for every sink at the end of an actual `{0,1}` or `{0,2}` trace.

- [ ] **Step 1: Write failing checks** naming both orientation theorems and a separate `{0,1}` `X = 0` boundary theorem.
- [ ] **Step 2: Verify RED**.
- [ ] **Step 3: Implement `{0,1}`** cases: sink A minor, sink D certificate, final row 1/LR certificate, final row 0 sink B with `X >= 0` reciprocal rank including `X = 0`, final row 0 sink B with `X < 0` split at `D`, and sink C with ELR.
- [ ] **Step 4: Implement `{0,2}`** independently: sink B minor, sink D certificate, final row 2/LR, row 0 sink A/reciprocal rank, and row 0 sink C/shifted slots.
- [ ] **Step 5: For every certificate**, prove row counts and coefficient vector nonnegative, mass inequality, and weight identity before invoking the frozen contradiction.
- [ ] **Step 6: Rerun** all regressions.

### Task 6: First occurrence of the third color

**Files:**
- Create: `P21/Nonsymmetric/ColorCap/DPE/ThirdColor.lean`
- Create: `verification/m3b2/ThirdColorRegression.lean`

**Interfaces:**
- Consumes: actual trace, first-third occurrence split, PREFIX and slot bounds.
- Produces: contradictions for `{0,1} -> 2` and `{0,2} -> 1`.

- [ ] **Step 1: Write failing checks** for both orientations and for the lemma excluding an immediately repeated non-first color before the third color.
- [ ] **Step 2: Verify RED**.
- [ ] **Step 3: Prove** the third color must follow row `0` from the actual adjacent trace entries and START.
- [ ] **Step 4: Close `{0,1} -> 2`** by deriving every-prior-`E` from PREFIX, the `D >= 0`/`D < 0` split, slot bounds, and its certificate.
- [ ] **Step 5: Close `{0,2} -> 1`** by separately deriving every-prior `E > P` and `U > W*`, including the integral early-exit strip, then its certificate.
- [ ] **Step 6: Rerun** all regressions.

### Task 7: DPE exhaustion and residual-free integration

**Files:**
- Create: `P21/Nonsymmetric/ColorCap/DPE/Closure.lean`
- Create: `P21/Nonsymmetric/ColorCap/FullColorCap.lean`
- Create: `verification/m3b2/StatementRegression.lean`

**Interfaces:**
- Consumes: all previous modules and frozen `minimum_one_proved`/conditional wrappers.
- Produces: `box_positive_exit_proved : BoxPositiveExitStatement` and unconditional wrappers for three-arm, actual labels, selected four, and `Q` cardinal extraction.

- [ ] **Step 1: Write the failing exact-statement regression**:

```lean
example : BoxPositiveExitStatement := box_positive_exit_proved
example : MinimumOneStatement := minimum_one_proved
#print axioms box_positive_exit_proved
```

- [ ] **Step 2: Verify RED** before closure exists.
- [ ] **Step 3: Exhaust** nonempty canonical traces into one color, exactly two colors, or first occurrence of all three, using actual list membership/order.
- [ ] **Step 4: Prove** `box_positive_exit_proved` and compose it with `minimum_one_proved` in new wrappers whose types contain neither residual premise.
- [ ] **Step 5: Compile** all statement regressions and inspect printed types.

### Task 8: Verification, candidate, and CI

**Files:**
- Create: `verification/m3b2/verify.py` and manifests/reports.
- Create: `ci/m3b2_audit.py`, `.github/workflows/m3b2-audit.yml`.
- Create: `README_M3B2.md`, `SOURCE_OF_TRUTH_M3B2.md`, `M3B2_STATEMENT_MAP.md`, `M3B2_PROOF_ROUTE.md`, `M3B2_DEPENDENCY_DAG.md`.
- Modify: `NEXT_RESTART.md` only as documentation; do not modify old Lean.

**Interfaces:**
- Consumes: exact base Git blobs, all new source, old suite entrypoints.
- Produces: immutable candidate ZIP, full local evidence, GitHub artifact, and handoff receipt.

- [ ] **Step 1: Generate** the new-module and declaration inventories from actual source files.
- [ ] **Step 2: Verify** every pre-existing Lean blob against base and scan all project source for prohibited escapes.
- [ ] **Step 3: Move aside the development project build safely and run** fresh root, every old module, every new module, statement regressions, all-new-declaration axiom inspection, and scanner tests.
- [ ] **Step 4: Run** isolated unchanged M1/M2A/M2B/M3A/M3B1 suites.
- [ ] **Step 5: Package exactly** `P21_LEAN_M3B2_DPE_BOX_POSITIVE_EXIT_CANDIDATE_20260917.zip`, bind source hashes and candidate SHA-256, and refuse overwriting it.
- [ ] **Step 6: Commit and push** only `m3b2-dpe-box-positive-exit`; do not merge main.
- [ ] **Step 7: Require** fresh GitHub workflow success and download/verify `P21_M3B2_TRUE_AUDIT_EVIDENCE`, including run/head/attempt, artifact digest, manifest, source hashes, and candidate digest.

## Self-review

- Spec coverage: Tasks 1–7 cover chronological provenance, one/two/three-color exhaustion, both orientations, reciprocal rank, `K_s=1`, `X=0`, certificates, exact DPE, and integration. Task 8 covers all source, axiom, regression, build, package, and CI gates.
- Placeholder scan: no proof obligation is deferred; every source case is assigned to a concrete task and module.
- Type consistency: all final theorems consume the exact frozen `BoxInput`, `BoxPath`, `MinimumOneStatement`, and residual wrapper signatures.
