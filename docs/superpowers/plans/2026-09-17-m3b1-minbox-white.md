# M3B1 MINBOX / White implementation plan

> Agentic workers: use superpowers:subagent-driven-development with bounded proof ownership and independent review.

Goal: prove exactly `P21.Nonsymmetric.ColorCap.MinimumOneStatement`, with no additional assumptions, and reduce the conditional three-arm frontier to DPE alone.

Architecture: preserve all baseline Lean sources. Add independently checked modules for relative-lattice/simplex geometry, the required White consequence, and the two color arithmetic closures. Assemble only proved interfaces. If closure remains open, deliver the strongest exact reduction under request section 18.

Tech stack: existing pinned Lean 4.34.0-rc1 and mathlib; Python evidence scripts; GitHub Actions.

Spec: `verification/m3b1/REQUEST.md`.

## Global constraints

- Base commit: `258d74ac941796c62bb45cc177f22a7396319413`; branch `m3b1-minbox-white`; no main merge.
- Every existing Lean file is byte-immutable. Existing mathematical statements and old verification suites are not edited.
- No sorry/admit/axiom/unsafe/opaque/native_decide/run_tac. Standard logical dependencies only.
- Actual factorizations use natural coefficients; lattice relations use integers. Minimum applies only after explicit nonnegativity conversion.
- Tail primitivity derives from hcof via the existing Bezout theorem.
- DPE is out of scope. No theorem is claimed from a citation or an assumed White conclusion.

## Tasks and evidence gates

- [x] Create branch/worktree from the exact base and preserve the user specification.
- [x] Verify authoritative PDF/ZIP hashes and read their relevant Appendix B material.
- [x] Search pinned mathlib for White/empty tetrahedra/lattice width APIs and save `MATHLIB_WHITE_SEARCH.md`.
- [x] Prove specialized relative-lattice index/quotient and socle determinant/emptiness consequences, reusing primitive formulas and kernel basis.
- [x] Prove the needed White width/class statement internally, or find a proved alternative route to MINBOX. Record the first precise open statement if unsuccessful.
- [x] Derive both color branches' class and inverse-class companion inequalities and parameter contradictions, including genuine row-order transport.
- [x] Assemble `minimum_one_proved : MinimumOneStatement` and DPE-only wrapper if all inputs close; otherwise exact honest best reduction.
- [x] Independently review new statements and actuality/primitivity boundaries.
- [x] Fresh root and explicit new-module build; all new declarations' axiom reports; debt scanner; exact frozen-source comparison.
- [x] Run unchanged original M1/M2A/M2B/M3A suites in isolated source copies.
- [ ] Package one immutable candidate, exact commit/ZIP gate, push, fresh Linux CI, download and verify artifact, write receipt and final report.

## Execution rulings

The detailed user request already approves implementation, the named branch and CI push. No additional design or publication approval is needed. This is a mathematical proof search, so task plans name the exact desired propositions and kernel checks without inventing proof scripts before they exist. Targeted Lean compilation is the primary proof test; final independent source/axiom/CI gates check the delivered result.

## Progress ledger

2026-09-17: exact base checked out in the new sibling worktree. Baseline root build passed. `RowAtlas.lean` exists and imports the frozen arm/Herzog APIs; the initial absence report was an inspection error and has been corrected.

2026-09-17: all 16 new proof modules compiled. The exact unconditional MINBOX theorem and DPE-only wrapper are proved, including the specialized White arithmetic consequence. Internal mathematical reviews found no blocking defects. Final source-bound fresh verification, isolated old suites, packaging and Linux CI remain in progress.

2026-09-17: fresh root/all old/all 16 new modules passed, 342 new kernel declarations passed axiom inspection, 55 scanner/verification unit tests passed, 233 protected files unchanged. All four isolated historical suites exited zero. Candidate packaging and remote CI follow this local snapshot; the external handoff receipt records final remote identifiers.
