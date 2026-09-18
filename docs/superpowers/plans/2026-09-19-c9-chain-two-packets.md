# C9 Chain Two-Packet Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize publication Section 9 from the frozen C8 `RegionU ∨ RegionD` handoff through an abstract, first-fit-free `EuclideanSeed` containing two genuine packets and a determinant-one embedding.

**Architecture:** Add a forward-only module family under `P21/Nonsymmetric/Chain/C9/`. Region U modules consume only `OneData.RegionU`; Region D modules consume `RegionD` plus frozen C7/C8 interfaces and never construct `OneData`. Certificate proof data is deterministically generated from the exact frozen 715-term table and checked by Lean. Every mathematical Lean file present at commit `7769545a357c0c4d24520ec7a9fc8994f3f664e7` remains byte-identical.

**Tech Stack:** Lean 4.34.0-rc1, pinned mathlib, `omega`, `linarith`, `nlinarith`, `ring`, Python certificate generation, GitHub Actions.

**Spec:** `verification/c9/REQUEST.md` (verbatim user C9 request).

## Global Constraints

- Work only on branch `c9-chain-two-packets` based exactly on `7769545a357c0c4d24520ec7a9fc8994f3f664e7`.
- Create only new C9 mathematical Lean modules; do not edit any Lean file existing at the base commit.
- Preserve the Region U/Region D scope firewall and all actual/nonnegative, signed-relation, SAME-element, multiplicity-scale, and certificate provenance firewalls.
- Do not import or prove Section 10 results.
- Do not use `sorry`, `admit`, new axioms, `native_decide`, `run_tac`, external PASS messages as proofs, or finite search as a mathematical proof.

---

### Task 1: Freeze inventory, exact request, and certificate inputs

**Files:**
- Create: `verification/c9/REQUEST.md`
- Create: `verification/c9/frozen_manifest.json`
- Create: `verification/c9/generate_linear_certificate.py`

- [x] Record hashes of every base mathematical Lean source and exact supplement inputs.
- [x] Locate and compare both 715-term JSON copies, verifier, expected output, term count, variable order, constant 35, and specified table hash.
- [x] Implement deterministic generation of committed Lean certificate data.
- [x] Run the frozen verifier and generator reproducibility checks; commit.

### Task 2: Eliminate Region U

**Files:**
- Create: `P21/Nonsymmetric/Chain/C9/RegionUSetup.lean`
- Create: `P21/Nonsymmetric/Chain/C9/RegionUCapacity.lean`
- Create: `P21/Nonsymmetric/Chain/C9/RegionUExclusion.lean`
- Test: `verification/c9/RegionUGate.lean`

- [x] Expose exact U-PARAM/U-SIGNS data, packet repetition count, and capacities from `O.RegionU` only.
- [x] Prove every repeated exchange coefficientwise inside the same actual upper element.
- [x] Close all capacity branches and prove `RegionU.impossible` without extra assumptions.
- [x] Build the modules and gate; commit.

### Task 3: Region D setup, first caps, and multiplicity master

**Files:**
- Create: `P21/Nonsymmetric/Chain/C9/DSetup.lean`
- Create: `P21/Nonsymmetric/Chain/C9/DFirstCaps.lean`
- Create: `P21/Nonsymmetric/Chain/C9/MultiplicityMaster.lean`
- Test: `verification/c9/DSetupGate.lean`

- [x] Derive only Section-9-valid D data from `RegionD`, intrinsic data, SHIFT-NEW, SUM-NOTCH, FK-STRONG, Caps and Slopes.
- [x] Prove the last crossing is an h-step and FIRST-CAPS plus NV/ZV identities.
- [x] Retain a positive common multiplicity scale and prove the exact M-MASTER identity with coefficientwise sign lemmas.
- [x] Build and commit.

### Task 4: Close high-q and nonlinear-first branches

**Files:**
- Create: `P21/Nonsymmetric/Chain/C9/HighQ.lean`
- Create: `P21/Nonsymmetric/Chain/C9/NonlinearFirst.lean`
- Test: `verification/c9/ReductionGate.lean`

- [ ] Prove all HIGH-Q lower decompositions and exclude `q0 ≥ 3` by strict multiplicity.
- [ ] For `q0 = 2`, prove the predecessor/PREFIX minimality argument, SMALL-R bounds, and nonlinear-first lower decompositions.
- [ ] Exclude `N ≥ z+2` and expose exactly `q0=2 ∧ N=z+1` for survivors.
- [ ] Build and commit.

### Task 5: Linear-first parameterization and the first two packet identities

**Files:**
- Create: `P21/Nonsymmetric/Chain/C9/LinearFirst.lean`
- Create: `P21/Nonsymmetric/Chain/C9/Packets.lean`
- Create: `P21/Nonsymmetric/Chain/C9/PacketDeterminant.lean`
- Test: `verification/c9/LinearGate.lean`

- [ ] Derive the exact `k,Q,upsilon,G,E,b,c,B,a` parameterization and all positivity/range fields.
- [ ] Prove D-LINEAR and INTRINSIC-LINEAR as genuine nonnegative packet equalities with actual provenance.
- [ ] Prove DSCR directly from strict multiplicity and its exact decomposition.
- [ ] Build and commit.

### Task 6: Lean-kernel 715-term certificate and I-FIT

**Files:**
- Create: `P21/Nonsymmetric/Chain/C9/GeneratedLinearCertificate.lean`
- Create: `P21/Nonsymmetric/Chain/C9/LinearCertificate.lean`
- Create: `P21/Nonsymmetric/Chain/C9/IFit.lean`
- Test: `verification/c9/CertificateGate.lean`

- [ ] Commit deterministic proof data generated from the exact frozen table.
- [ ] Prove in Lean the exact 715-term polynomial identity and positivity from shifted nonnegative variables.
- [ ] Prove derivative monotonicity and the exact I-FIT inequality; keep the threshold as an evaluation point only.
- [ ] Regenerate, byte-compare, build, and commit.

### Task 7: J-shortage, complementary packet, and determinant-one embedding

**Files:**
- Create: `P21/Nonsymmetric/Chain/C9/JShortage.lean`
- Create: `P21/Nonsymmetric/Chain/C9/ComplementaryPacket.lean`
- Create: `P21/Nonsymmetric/Chain/C9/MatrixEmbedding.lean`
- Test: `verification/c9/PacketGate.lean`

- [ ] Perform `f+1` replacements inside the exact actual upper element and exclude `theta ≥ upsilon+1`.
- [ ] Produce the zero-j actual representation for `1≤theta≤upsilon`.
- [ ] Prove COMPLEMENTARY as a genuine packet and the positive-entry determinant-one matrix, `L>M`, exact row identities, and positive packet determinant.
- [ ] Build and commit.

### Task 8: Abstract Euclidean seed and full C9 handoff

**Files:**
- Create: `P21/Nonsymmetric/Chain/C9/EuclideanSeed.lean`
- Create: `P21/Nonsymmetric/Chain/C9/Handoff.lean`
- Create: `P21/Nonsymmetric/Chain/C9.lean`
- Test: `verification/c9/StatementGate.lean`
- Test: `verification/c9/Regression.lean`

- [ ] Define `EuclideanSeed` using only exact Section 10 abstract inputs, excluding FirstFit, RegionD, zhat/N/I/J/q0/ROOT/PF-row baggage.
- [ ] Construct `RegionD.toEuclideanSeed` from the completed linear branch.
- [ ] Combine frozen `c8_handoff`, `RegionU.impossible`, and Region D conversion into `ChainCore.c9_handoff`.
- [ ] Add structural regression checks for all requested scope and packet invariants; build and commit.

### Task 9: Documentation, verification harness, and CI

**Files:**
- Create: `README_C8.md`, `SOURCE_OF_TRUTH_C8.md`, `C8_STATEMENT_MAP.md`, `C8_PROOF_ROUTE.md`, `C8_DEPENDENCY_DAG.md`
- Create: `README_C9.md`, `SOURCE_OF_TRUTH_C9.md`, `C9_STATEMENT_MAP.md`, `C9_PROOF_ROUTE.md`, `C9_DEPENDENCY_DAG.md`
- Update: `NEXT_RESTART.md`
- Create: `verification/c9/verify.py`, generated gates/reports, and `.github/workflows/c9-audit.yml`

- [ ] Reconstruct C8 documentation from frozen declarations without changing C8 mathematics.
- [ ] Document exact C9 statements, sources, proof route, dependency DAG, and open C10 frontier.
- [ ] Implement fresh-source, proof-debt, axiom, dependency, circularity, frozen-integrity, certificate, and full regression checks.
- [ ] Run fresh root/C9 builds and M1/M2A/M2B/M3A/M3B1/M3B2/P5/T6/C7/C8 regressions; commit.

### Task 10: Candidate, GitHub CI, and evidence artifact

**Files:**
- Create: `P21_LEAN_C9_CHAIN_TWO_PACKET_CANDIDATE_20260919.zip`
- Create: C9 evidence manifest and candidate hash manifest

- [ ] Run `superpowers:verification-before-completion`; verify the final diff contains no base mathematical Lean changes and no C10 reverse dependency.
- [ ] Create the exact candidate ZIP, compute SHA-256, and verify a fresh extracted copy.
- [ ] Push only the completed candidate branch and wait for a clean `c9-audit.yml` run.
- [ ] Download and independently verify `P21_C9_TRUE_AUDIT_EVIDENCE`, recording run ID, artifact ID, GitHub digest, commit, and candidate hash.
- [ ] Report success only as `C9 CHAIN TWO-PACKET CANDIDATE FOR TRUE AUDIT`.

