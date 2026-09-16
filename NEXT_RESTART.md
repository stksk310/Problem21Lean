# Restart / independent-review handoff

Current status: **M1 CANDIDATE FOR TRUE AUDIT**.
There are no intentionally open proof obligations inside FOUNDATION + C2.

1. Extract the candidate ZIP to a fresh directory. Review `SOURCE_OF_TRUTH.md`,
   `STATEMENT_MAP.md`, and the pinned dependency manifest.
2. Run `lake exe cache get`, `lake build`, and `python verification/verify.py`.
   Confirm every axiom result is within `propext`, `Classical.choice`, `Quot.sound`.
3. Independently compare the publication PDF §1.1 and §§2.7–2.12 against the printed
   Lean statements in `verification/STATEMENTS.txt`. Check indexed irredundance
   represents the four minimal generators, with multiplicity exactly as stated.
4. Inspect `Factorization.lean` for containment and nonnegative residual proofs;
   inspect `key_return_apery` and `return_coordinate_zero` for same-element provenance.
5. Inspect the maximal/minimal layer bridges and row-selection quantifier scopes.
   Confirm the tail's signed representation is used only for the integer group
   and divisor arguments, followed by the proved natural-closure cast bridge.

Only the user's independent control/audit process can authorize promotion beyond
this candidate status. This package makes no independent-audit outcome claim.

## Intentionally OPEN / not attempted

- Proof of `P21MainStatement` / T1.
- S3 and symmetric-tail closure.
- STD_SYM_GLUE, STD_HERZOG, STD_WHITE.
- Six-arm classification, COLOR-CAP, PATH, TYPE II, CHAIN, CORE-ROOT, CENTRAL.
- Euclidean descent and the 715/3234-term certificate theorems.

These are mission exclusions, not hidden dependencies or postponed M1 proofs.
Do not proceed into them without a new instruction specifying the next milestone.
