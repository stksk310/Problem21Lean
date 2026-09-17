# Independent review: ColorCap and actual terminal extraction

Reviewer: m3_kernel (not the author of ColorCap, ActualMixed, or Extraction).
Date: 2026-09-17. Review is of the shared m3-nonsym-g4 worktree before the parent fresh-build freeze.

## Conclusion

No concrete mathematical correctness defect was found in the reviewed proofs or boundary handling. The result is a **conditional reduction**, not an unconditional proof of COLOR-CAP or G4. The exact two remaining mathematical inputs are `ColorCap.MinimumOneStatement` and `ColorCap.BoxPositiveExitStatement`. Neither is proved by the current subtree. They remain explicit parameters of the final conditional selected-four theorem.

No Lean proof source was modified for this review. This is a source and statement review, not a substitute for the parent fresh build and whole-import axiom audit.

## Scope inspected

Read all eleven ColorCap modules: ActualMinimum, BoxPaths, BoxInput, RelativeLattice, CompanionBounds, WhiteCertificates, DPEOneColor, PositiveMinors, PrefixArithmetic, ThreeArms, Residuals. Read ActualMixed and Extraction, including their actual-membership hypotheses, depth synchronization, endpoint saturation, and cyclic transport. Also inspected the public terminal/value-preservation interfaces and composition in SelectedExtraction; that latter inspection is narrower than the full proof review above.

The source comparison uses section4-readable.md, especially the MINBOX and finite-box discussion around lines 613-645, together with the detailed scope recorded by the ColorCap author. A token scan of ColorCap, ActualMixed, and Extraction found no sorry, axiom declaration, unsafe, opaque, native_decide, or run_tac.

## Exact residual strength

`MinimumOneStatement` quantifies over genuine Generators, Setting, and HerzogCriticalData, either color, a positive natural level k, and integral p with `1 <= p_i < a_i` (or b_i). It assumes an actual socle equality with coefficients p_i-1 and that k is least among **all nonnegative integral actual representations** of that same socle. Its conclusion is k=1. It does not assume three arms, White classes, a lattice index, or a color-cap conclusion. Actual three arms are used by the proved bridge to obtain its hypotheses. It is the needed local MINBOX consequence; the current work must not describe it as a proved White theorem or claim equivalence to every statement of White's classification.

`BoxPositiveExitStatement` quantifies over BoxInput and any finite path starting at its actual initial point x, ending at a state where no firing remains in the box. It requires a firing with all coordinates at least one. It concerns reachable terminal states, not arbitrary positive points. BoxInput carries positivity and exact weighted row identities; it does not contain DPE as a field. Path existence and the positive-exit contradiction are proved independently.

`three_arms_impossible_of_residuals` passes precisely these two hypotheses to actual same-socle data and proves impossibility for both colors. The ColorCap Boolean convention is true=A and false=B; ActualClassification bridges its opposite RowLabel color convention explicitly.

## Proved bridges and boundaries

* ActualMinimum converts integers to natural coefficients only after nonnegativity is established. The attained Nat.find minimum is positive using the genuine fA/fB gap theorem. Arm caps apply to every actual same-socle representation, not only a chosen representation.
* BoxPath stores the in-box requirement on every successful step. The maximal-path proof minimizes nonnegative weight, with each firing decreasing it by positive m. It assumes neither graph connectivity nor an infinite-path exclusion axiom.
* SAME-F is retained at every path stage. A positive exit after t in-box steps represents the original f at level t+2; subtracting the original arm depth leaves nonnegative coefficients. This correctly includes equality at the exiting upper face.
* The B-color construction performs an actual 1/2 coordinate swap and exchanges a/b. Its exit is transported back to the original generators, socle, and arm gaps. It does not introduce an unrelated semigroup.
* Relative-lattice and companion lemmas prove local level and positivity obstructions. Companion bounds and mass certificates retain the necessary class/parameter equations as hypotheses. They do not manufacture a White class or infer an empty tetrahedron from unstated geometry.
* The one-color result, positive minors, selected two-color sink exclusions, and prefix arithmetic have narrower statements than full DPE. Prefix conditions use chronological successful prefixes; finite slot counting retains its needed injectivity hypotheses.

The remaining MINBOX work includes the relative empty-tetrahedron/volume argument and White-class existence and ordering, followed by class-bound assembly. The remaining DPE work includes actual-path residue extraction, reciprocal-prefix/dual-rank steps, the remaining mixed sink certificates, and first-third-color exclusion. Existing helper names must not be presented as completion of these arguments.

## ActualMixed and Extraction

ActualMixed extracts complement coefficients from actual Q rows, derives missing directions from the full Herzog PF result, and transports the fixed orientation with genuine cyclic relabeling. The BA and AB singleton exclusions concern precisely their stated directions. Where distinctness is needed, it follows from the two return directions of an arm versus the one direction of a singleton.

Extraction packages keep four actual rows and their injectivity. PATH derives positivity of the middle coefficient using its singleton endpoint; the generic mixed-pair stage does not silently discard the zero boundary. TYPE II derives the additional lambda <= b0 cap from an actual nonnegative coefficient. CHAIN's public independent-depth wrapper proves the equality of the two matched depths before constructing the synchronized package. Positive chain slacks follow from strict arm ranges.

`singleton_saturation_last` genuinely rotates index 2 to index 0 and sends (P,R,T) to (T,P,R). The Setting's semigroup, F, m, Q membership, and W are preserved. The odd reversal exchanges a/b and fA/fB through the established Relabel API.

The inspected SelectedExtraction interface uses `SelectedTerminal` with an explicit equality between package values and the selected rows' value set. `TerminalInputExists` permits a rotation or reversal followed by rotation of those same rows. `selectedValues_relabel` is definitional equality. The final `nonsymmetric_Q_ge_four_of_colorcap_residuals` assumes cardinality at least four, selects four actual rows, and retains both residual parameters. It does not replace the full Q set by a four-element set or prove unconditional cardinality exclusion.

## Verification context

The separate Relabel/ActualClassification audit completed with exit code 0 and only propext, Classical.choice, and Quot.sound in the reported axiom dependencies (`ACTUAL_CLASSIFICATION_VERIFICATION_LOG.txt`). This review makes no new fresh-build claim for the other author's files. The parent integration build remains the authoritative fresh verification.
