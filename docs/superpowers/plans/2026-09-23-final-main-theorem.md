# Final Main Theorem Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Assemble the frozen symmetric and nonsymmetric closures into a Lean proof of `P21MainStatement`, then deliver a reproducible lightweight candidate and GitHub audit evidence.

**Architecture:** Add one mathematical module, `P21/MainTheorem.lean`, importing the two frozen branch closures. Split on `SymmetricTail`; discharge the symmetric branch with the frozen type bound and the nonsymmetric branch with the frozen `Q.ncard ≥ 4` impossibility. Keep every pre-existing Lean source byte-identical to commit `e4799d8` and place all gates, reports, packaging, and CI support outside the frozen mathematical tree.

**Tech Stack:** Lean 4, Mathlib, Lake, PowerShell, Python 3, Git, GitHub Actions.

**Spec:** `verification/final/REQUEST.md`

## Global Constraints

- Base commit is exactly `e4799d8044fd524a94b960ab19c333b08a8c93bb`; branch is `final-main-theorem`.
- No pre-existing mathematical Lean source may change. If one is required, stop with `SOURCE CHANGE REQUIRED` and `FROZEN RE-AUDIT REQUIRED`.
- The nonsymmetric theorem receives `4 ≤ (s.semigroup.Q F).ncard`; do not replace it with an equality assumption.
- No frozen source may import `P21.MainTheorem`; final assembly is one-way only.
- Final status is at most `FINAL MAIN THEOREM CANDIDATE FOR TRUE AUDIT`.
- The candidate ZIP must exclude old ZIPs, `.git`, `.lake`, caches, and duplicate evidence, and must pass fresh-extraction verification.

### Task 1: Final theorem spine

- [ ] Copy the exact request into `verification/final/REQUEST.md` and write a failing gate importing `P21.MainTheorem`.
- [ ] Record the expected missing-module failure.
- [ ] Add `P21/MainTheorem.lean` with `q_ge_four_impossible`, `q_card_le_three`, `type_le_four`, and `main_theorem`.
- [ ] Add `P21Final.lean` and make the statement gate pass.
- [ ] Verify no old Lean source changed and commit.

### Task 2: Audit gates and documentation

- [ ] Add final axiom, dependency, source-integrity, statement-map, and proof-debt gates.
- [ ] Add the five missing C10 documentation files without changing C10 mathematics.
- [ ] Update `NEXT_RESTART.md` with the required final-candidate status.
- [ ] Run the focused final gates and commit.

### Task 3: Reproducible verification and evidence

- [ ] Add `verification/final/verify.ps1` and deterministic evidence scripts.
- [ ] Run root, final module, M1–C10 regression, statement, axiom, proof-debt, dependency, and frozen-source checks.
- [ ] Run both pinned SymPy 1.14.0 certificate verifiers and verify their exact counts and table hashes.
- [ ] Produce and verify source and evidence SHA-256 manifests.
- [ ] Commit verification support and reports.

### Task 4: Lightweight candidate and fresh extraction

- [ ] Build `P21_LEAN_FINAL_MAIN_THEOREM_CANDIDATE_20260923.zip` with an exact package manifest.
- [ ] Reject path traversal, symlinks, duplicate paths, nested candidate ZIPs, `.git`, and `.lake`.
- [ ] Extract to a fresh directory and rerun source-manifest, certificate-regeneration, and final-theorem checks.
- [ ] Keep the archive below 20 MB where feasible and commit its checksum record.

### Task 5: GitHub CI and audit artifact

- [ ] Add `.github/workflows/final-main-theorem-audit.yml` binding evidence to exact HEAD.
- [ ] Run the full local verification once more and inspect the complete diff.
- [ ] Push the final candidate branch and wait for a clean GitHub Actions run.
- [ ] Download and verify `P21_FINAL_TRUE_AUDIT_EVIDENCE`, including digest, file count, missing, and extra-file checks.
- [ ] Report `FINAL MAIN THEOREM CANDIDATE FOR TRUE AUDIT` only after every gate succeeds.

