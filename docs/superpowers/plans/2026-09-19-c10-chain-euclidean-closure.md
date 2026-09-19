# C10 Chain Euclidean Closure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize Section 10's canonical-free Euclidean descent from the frozen C9 seed through full CHAIN impossibility, with a Lean-kernel-checked 3234-monomial terminal certificate and reproducible audit evidence.

**Architecture:** Project the frozen `EuclideanSeed` into a new C10-only `EuclideanState`, prove the algebraic terminal/nonterminal dichotomy and color-exchange preservation using only HCR and state fields, then close `EuclideanState.f_mem` by strong induction on `(E + chi).toNat`. Keep the large frozen certificate reproducible by generating transparent, chunked Lean data from the exact supplement ZIP; connect the abstract theorem back to C9 and the post-Type-II wrappers only in new C10 modules.

**Tech Stack:** Lean 4, Mathlib, Lake, Python 3 standard library, Git, GitHub Actions.

**Spec:** `verification/c10/REQUEST.md`

## Global Constraints

- Base commit is exactly `50d65c7982aebe67856cb85e81771d0452d62fec`; branch is `c10-chain-euclidean-closure`.
- Modify no pre-existing mathematical Lean source; create only new C10 modules and verification/documentation/CI files. If an old mathematical source change is unavoidable, stop with `SOURCE CHANGE REQUIRED` and `FROZEN RE-AUDIT REQUIRED`.
- `EuclideanState` omits canonicality, first-fit, RegionD, q0, ROOT, PF rows, return levels, and first-point minimality; no descent proof may inspect `seed.canonical`.
- Derive the scale from HCR and positive generators only. Preserve actual/nonnegative factorization, SAME-W provenance, and signed-relation separation.
- The only recursive measure is `(E + chi).toNat`; color exchange must strictly decrease it.
- The terminal certificate must be transparent and Lean-kernel checked; `native_decide`, `run_tac`, axioms, and Python-to-theorem trust are forbidden.
- Supplement ZIP SHA-256 is `24a02d34651c35aa3d07f707fd38b7ca29d0f8bbfa86190d956657308b498c5e`; table SHA-256 is `495504b4bcb8427db04b242cf09b83fbe7bde1188f9324b7e977036a5a4db9b3`; verifier SHA-256 is `23fcf03275bbe36ef7b9ca78a6cddb6b75dd1f04216d3675fbe0da759b9d048e`.
- Expected frozen verifier result SHA is `12a22a7ed7899ccb10cb8ff608ca4fc738da76ec0ed761c5fd72a4ab87967087`; stdout SHA is `a298d66b61ca2b82ce9a429cbb795b7bd56c83f85795da7781e5c043ae12425f`; summary is PASS, 35 identities, 3234 monomials, degree 7, constant 63.
- Do not begin Section 11. Push only the completed final candidate, then require a clean GitHub Actions run and produce `P21_C10_TRUE_AUDIT_EVIDENCE`.

## Review Focus

- Erased canonical field: the abstract C10 gate must import only C10 state/descent APIs and prove `EuclideanState.f_mem` without a canonical hypothesis.
- Terminal signed coefficients: positive/negative-part conversion must retain equality and use `replaceWithinActualFactorization` only after proving source containment in the same actual factorization of W.
- Euclidean boundaries: tests must cover `u % theta = 0`, the terminal equality `kstar = T - 1`, and the nonterminal lower/upper remainder bounds.
- Relabeling orientation: exchange tests must prove matrix, determinant, packets, RHO, W, F-gap, and strict measure preservation without adding a firing/order assumption.
- Generated certificate drift: regeneration must reject a wrong ZIP/table/verifier hash, verify both tables byte-identically, and byte-compare every committed generated Lean file.

---

### Task 1: Frozen Input Inventory and Certificate Generator

**Files:**
- Create: `verification/c10/generate_euclidean_certificate.py`
- Create: `verification/c10/test_generate_euclidean_certificate.py`
- Create: `verification/c10/FROZEN_INPUT_SHA256.json`
- Create: `verification/c10/README.md`

**Interfaces:**
- Consumes: `reference_inputs/P21_supplement_v1.zip` and the exact hashes in the spec.
- Produces: deterministic `P21/Nonsymmetric/Chain/C10/GeneratedTerminalCertificate*.lean` files and a machine-readable validated source manifest.

- [ ] Write Python tests that invoke the generator in check mode, assert all frozen hashes/summary/table facts, mutate one copied input byte to assert rejection, and assert a second generation is byte-identical.
- [ ] Run `python -m unittest verification.c10.test_generate_euclidean_certificate -v`; expect failure because the generator is absent.
- [ ] Implement ZIP-only parsing, verifier execution, JSON schema/fact checks, deterministic term sorting/chunking, and atomic output/check modes with no third-party dependency.
- [ ] Run the test again; expect PASS and generated Lean sources whose constant is 63 and whose total term count is 3234.
- [ ] Commit request, plan, generator, tests, manifests, and generated sources as `feat(c10): freeze Euclidean certificate inputs`.

### Task 2: Canonical-Free State and Projection

**Files:**
- Create: `P21/Nonsymmetric/Chain/C10/State.lean`
- Create: `P21/Nonsymmetric/Chain/C10/Projection.lean`
- Create: `verification/c10/CanonicalFreeGate.lean`

**Interfaces:**
- Consumes: frozen `EuclideanSeed` field equations and `HerzogCriticalData`.
- Produces: `EuclideanState`, its named derived quantities, positivity/equality accessors, and `EuclideanSeed.toState` whose definition never references `canonical` except that `seed.frobenius` supplies `F_gap`.

- [ ] Write `CanonicalFreeGate.lean` against the planned `EuclideanState`/`toState` signatures and an abstract theorem declaration; run `lake env lean verification/c10/CanonicalFreeGate.lean`; expect unknown-identifier failure.
- [ ] Define the exact §10.2 state, `Ical/Jcal/Kcal`, `I0/J0/M0/K0`, `mhat`, `Phi`, `measureZ`, and `measureNat`, then implement the C9 projection.
- [ ] Add `rg` scope checks proving `canonical`, `FirstFit`, `RegionD`, `ROOT`, and return-level APIs occur nowhere under `P21/Nonsymmetric/Chain/C10`.
- [ ] Build the two modules and gate; expect PASS.
- [ ] Commit as `feat(c10): add canonical-free Euclidean state`.

### Task 3: HCR Scale, Matrix Order, and Elimination Algebra

**Files:**
- Create: `P21/Nonsymmetric/Chain/C10/CrossProductScale.lean`
- Create: `P21/Nonsymmetric/Chain/C10/MatrixOrder.lean`
- Create: `P21/Nonsymmetric/Chain/C10/Elimination.lean`
- Create: `verification/c10/AlgebraGate.lean`

**Interfaces:**
- Consumes: `EuclideanState` plus frozen HCR identities and generator positivity.
- Produces: positive `Ical/Jcal/Kcal`, a positive rational `sigma`, all three scale equalities, `p ≥ v+1`, `q ≥ t`, packet elimination, `A*M-B*L=delta-beta`, the determinant identity, and `m = sigma*mhat`.

- [ ] Write an algebra gate invoking each promised theorem, including matrix edge values and absence of canonical assumptions; expect missing-theorem failure.
- [ ] Prove cross-product expansions and generator cross-multiplications directly from HCR, then construct `sigma` and prove positivity without gcd/canonicality.
- [ ] Prove ORDER from determinant one and `L>M`, including contradictions for `p≤v` and `q<t`.
- [ ] Prove `M0=rho_j+a_j`, `K0=rho_k+b_k`, packet elimination, source determinant, `I0*K0-M0*J0=-Dp*(delta-beta)`, and the rational mhat formula.
- [ ] Build `AlgebraGate.lean`; expect PASS, then commit as `feat(c10): prove HCR scale and elimination algebra`.

### Task 4: Phi, Euclidean Split, and Terminal Certificate

**Files:**
- Create: `P21/Nonsymmetric/Chain/C10/Phi.lean`
- Create: `P21/Nonsymmetric/Chain/C10/TerminalSetup.lean`
- Create: `P21/Nonsymmetric/Chain/C10/TerminalCertificate.lean`
- Create: `verification/c10/TerminalCertificateGate.lean`

**Interfaces:**
- Consumes: Task 1 generated polynomial and Task 3 scale/elimination theorems.
- Produces: finite-difference monotonicity, measure casts, `nu/Z/N/jstar/kstar`, terminal signed identity, all 16 nonnegative shifts, the transparent polynomial identity, and `Phi (B+nu*A)>0`.

- [ ] Write the terminal gate for the divisible remainder case and `kstar=T-1`, and request certificate positivity/identity; expect missing-theorem failure.
- [ ] Prove `Phi(Px+1)-Phi(Px)=-(Dp+M0)`, antitonicity at the threshold, and exact `measureNat` cast/positivity lemmas.
- [ ] Define integer quotient data and prove `nu≥2`, `jstar≤R-1`, terminal condition, and the signed packet identity, including `u % theta = 0`.
- [ ] Prove nonnegativity of the 16 shifted variables from ORDER/positivity/remainder/terminal hypotheses.
- [ ] Connect the generated chunks to a generic nonnegative monomial lemma, prove polynomial `≥63`, and prove the exact symbolic certificate identity using `ring` or checked chunk identities.
- [ ] Regenerate-and-compare, run the frozen verifier, and build the terminal gate; expect PASS, then commit as `feat(c10): verify terminal positivity certificate`.

### Task 5: Terminal SAME-W Replacement and FINAL-EXACT

**Files:**
- Create: `P21/Nonsymmetric/Chain/C10/TerminalPacket.lean`
- Create: `P21/Nonsymmetric/Chain/C10/TerminalFit.lean`
- Create: `verification/c10/TerminalActualityGate.lean`

**Interfaces:**
- Consumes: terminal signed packet, certificate positivity, `replaceWithinActualFactorization`, and `removeOne`.
- Produces: positive-part packet decompositions, terminal `P≤B+nu*A` via i-fit, same-W source containment, an actual replacement factorization, and `terminal_f_mem : TerminalState → F ∈ g.Gamma`.

- [ ] Write a gate that distinguishes signed equality from actual coefficients and calls the final SAME-W membership theorem; expect missing-theorem failure.
- [ ] Prove generic integer positive/negative-part decomposition and coefficient nonnegativity; derive the actual terminal packet only after moving negative parts to the source side.
- [ ] Use `Phi` positivity and the mhat scale to prove i-source fit and the exact source multiplicity bounds.
- [ ] Construct the source inside the original actual W factorization with `removeOne`; call `replaceWithinActualFactorization` and prove the replacement remains a factorization of that same W.
- [ ] Complete FINAL-EXACT arithmetic and convert the replacement into `F ∈ Gamma`.
- [ ] Build the actuality gate; expect PASS, then commit as `feat(c10): close terminal same-W replacement`.

### Task 6: Nonterminal Euclidean Packet and Color Exchange

**Files:**
- Create: `P21/Nonsymmetric/Chain/C10/Nonterminal.lean`
- Create: `P21/Nonsymmetric/Chain/C10/ColorExchange.lean`
- Create: `verification/c10/ExchangeGate.lean`

**Interfaces:**
- Consumes: nonterminal `T≤kstar`, exact quotient data, relabeling APIs, and Task 2 state.
- Produces: quotient/remainder identities, `nu=e+1`, `R≤rhoRem<theta`, `1≤kappa≤w`, a genuine new packet, and a transformed `EuclideanState` with strict `measureNat` decrease.

- [ ] Write an exchange gate covering zero remainder, both remainder inequalities, packet genuineness, and every preservation field; expect missing-theorem failure.
- [ ] Define exact Euclidean quotient/remainders and prove `nu=e+1` with `R≤rhoRem<theta` and `1≤kappa≤w` under nonterminality.
- [ ] Build NEW-PACKET with nonnegative coefficients and prove its exact relation.
- [ ] Define the abstract color exchange/relabeling and reconstruct matrix/source/DP/PP/determinant/RHO/W/F-gap fields explicitly.
- [ ] Prove `(new.E+new.chi).toNat < (old.E+old.chi).toNat` and no other recursive measure is used.
- [ ] Build the exchange gate; expect PASS, then commit as `feat(c10): construct strict Euclidean color exchange`.

### Task 7: Strong Induction and C9 Seed Closure

**Files:**
- Create: `P21/Nonsymmetric/Chain/C10/Descent.lean`
- Create: `P21/Nonsymmetric/Chain/C10/SeedClosure.lean`
- Create: `verification/c10/DescentGate.lean`

**Interfaces:**
- Consumes: terminal membership and nonterminal transformed state with strict measure.
- Produces: `EuclideanState.f_mem`, `EuclideanSeed.impossible`, and a gate showing the induction theorem has no canonical parameter.

- [ ] Write the descent gate invoking `EuclideanState.f_mem` on an arbitrary state and `EuclideanSeed.impossible`; expect missing-theorem failure.
- [ ] Prove the terminal/nonterminal exhaustive split and strong induction on `measureNat`, recursively applying only the transformed state's smaller measure.
- [ ] Project a frozen C9 seed, obtain `F ∈ Gamma`, and contradict only `seed.frobenius.not_mem` (or its exact frozen equivalent).
- [ ] Run the canonical scope grep and build the descent gate; expect PASS.
- [ ] Commit as `feat(c10): close Euclidean descent by strong induction`.

### Task 8: CHAIN and Post-Type-II Integration

**Files:**
- Create: `P21/Nonsymmetric/Chain/C10/ChainClosure.lean`
- Create: `P21/Nonsymmetric/Chain/C10/Integration.lean`
- Create: `P21/Nonsymmetric/Chain/C10.lean`
- Create: `verification/c10/IntegrationGate.lean`

**Interfaces:**
- Consumes: C9 seed extraction/orientations, `EuclideanSeed.impossible`, frozen ChainCore/ChainInput, post-Type-II and selected-four APIs.
- Produces: `ChainCore.impossible`, `ChainInput.impossible`, both post-Type-II orientations, nonsymmetric selected-four closure, and nonsymmetric `Q≥4` closure, without Section 11 assembly.

- [ ] Write the integration gate for every requested wrapper in both orientations; expect missing-theorem failure.
- [ ] Map an oriented core to the existing C9 seed and discharge it with `EuclideanSeed.impossible`; transport the reversed orientation through the exact frozen relabeling theorems.
- [ ] Prove `ChainInput.impossible` and the two post-Type-II terminal CHAIN wrappers.
- [ ] Add residual-free selected-four and `Q≥4` wrappers using only frozen upstream APIs and the new CHAIN theorem.
- [ ] Build the umbrella module and integration gate; expect PASS; confirm no Section 11 module/import exists.
- [ ] Commit as `feat(c10): close chain integration`.

### Task 9: Reproducibility, Regression, and Proof-Debt Audit

**Files:**
- Create: `verification/c10/verify.ps1`
- Create: `verification/c10/audit_axioms.lean`
- Create: `verification/c10/SOURCE_INTEGRITY_SHA256.json`
- Create: `verification/c10/REPORT.md`
- Modify: `.github/workflows/lean.yml` only if the existing workflow does not discover the new verification entrypoint.

**Interfaces:**
- Consumes: all C10 modules and frozen historical verification entrypoints.
- Produces: one deterministic local command that regenerates the certificate, checks hashes/scope/reverse dependencies/proof debt, builds C10, and runs M1/M2A/M2B/M3A/M3B1/M3B2/P5/T6/C7/C8/C9 regressions.

- [ ] Write `verify.ps1` checks first and run it; expect failure until all expected declarations/manifests are present.
- [ ] Add `#print axioms` audit coverage for every public closure theorem and reject `sorry`, `admit`, `axiom`, `native_decide`, `run_tac`, unsafe certificate imports, and reverse dependencies from frozen source into C10.
- [ ] Hash every pre-existing mathematical Lean source against the C9 base and make the script fail on any difference.
- [ ] Run fresh root build, explicit C10 build, every listed historical suite, generator byte-compare, and audit checks; expect all PASS.
- [ ] Fill `REPORT.md` with exact declarations, inherited/project-specific axioms, source integrity, and command results; commit as `test(c10): add reproducibility and regression gate`.

### Task 10: Candidate Packaging, GitHub CI, and Audit Evidence

**Files:**
- Create: `delivery/P21_LEAN_C10_CHAIN_EUCLIDEAN_CLOSURE_CANDIDATE_20260919.zip`
- Create: `delivery/P21_C10_TRUE_AUDIT_EVIDENCE/`
- Create: `delivery/C10_CANDIDATE_SHA256.txt`

**Interfaces:**
- Consumes: clean committed branch and Task 9 verification outputs.
- Produces: deterministic candidate ZIP, one final GitHub push, a clean Actions run, downloaded evidence artifact, and a locally verified evidence manifest.

- [ ] Run the complete verification script from a fresh local state and inspect every result; expect PASS.
- [ ] Produce the exact candidate ZIP with sorted paths/fixed metadata, exclude build/git/scratch data, hash it, unpack to a temporary directory, and rerun its verification gate.
- [ ] Commit delivery metadata and candidate, verify clean status, then push `c10-chain-euclidean-closure` once to `stksk310/Problem21Lean`.
- [ ] Wait for the exact pushed SHA's GitHub Actions run; require conclusion `success` and record run ID/attempt.
- [ ] Download `P21_C10_TRUE_AUDIT_EVIDENCE`, verify `EVIDENCE_SHA256.json` and artifact digest locally, and record all hashes/IDs in the report.
- [ ] Run final whole-branch self-review against `verification/c10/REQUEST.md`, fix any Critical/Important finding with a RED→GREEN gate, and report the exact success status and next frontier from the spec.
