# Matched pair and return levels: work report

Owned new source: `P21/Nonsymmetric/MatchedPair.lean`,
`P21/Nonsymmetric/ReturnLevels.lean`.

## Scope and interfaces

The coordinate convention is fixed `(i,j,k)=(0,1,2)`. Permutations are an
upstream/downstream transport issue; the local statements do not silently
identify different semigroups. All actual-row hypotheses refer to the same
`g`, setting `s`, Frobenius `F`, and Q set.

`matched_pair_sync` takes positive critical data, actual A/B row formulas and
nonnegative natural critical-box complement coefficients. It proves equality
of depths and the two exact complement-coordinate shifts. The proof first
establishes `matched_kernel_box_zero` from the saturated integer kernel basis.

`matched_pair_data` packages the result as `MatchedPairData`, including depth,
nonnegative gapJ/gapK, P/R/T, actual q and complement identities, the exact W
identity and R/T box bounds. `P_gt_a` and `P_gt_b` are proved consequences.
There is no strict positivity assumption on gapJ or gapK.

`minimal_return_exists` independently minimizes the positive m coefficient in
one actual return fiber, using Nat.find. Any actual return has zero n0
coordinate by removing that coordinate from the same vector; a return outside
H has a positive m coefficient.

`frobenius_return_caps` proves both off-direction critical caps for an actual
F+n0 representation, replacing a critical packet and removing the resulting
n0. `four_return_caps` applies this to the same A/B returns and complements.

`unequal_levels_impossible` excludes each strict level ordering. Minimum-level
replacement first forces the required positive correcting coefficient. Only
the completed final representation of F is passed to `four_mem`, after all
four coordinates have been proved nonnegative. gapJ=0 and gapK=0 are retained.

`equal_level_matching` eliminates m and only then applies critical-box
uniqueness to the remaining pure-H relation.

`root_free_level_rigidity` proves all three exact §4.6 formulas with L>0 and
t,u>=0, with no unit-root or later-section hypothesis.

`matched_pair_excludes_A_one` and `matched_pair_excludes_B_two` exclude the two
forbidden extra arms using actual nonnegative Gamma factorizations.
`matched_pair_no_singleton` excludes every singleton direction: directions 1/2
use critical complement bounds and genuine missing-direction H returns;
direction 0 uses the P-fiber and the Apéry property of its actual complement.

## Equivalent pure-H proof refinement

Publication §4.7 separately proves EA/EB outside H by critical relations.
Here the already proved `HerzogCriticalData.fA_gap`/`fB_gap` are used: if
EA=fA-(depth-1)n0 were in H, adding the nonnegative (depth-1) copies of n0
would put fA in H, a contradiction; similarly for B. Those Herzog gap lemmas
are themselves proved from the same positive minimal critical data. This uses
no stronger hypothesis, no m term, and no axiom; it merely reuses a completed
pure-H lemma rather than repeating criticality calculations.

## Verification

`MatchedVerification.lean` inspects exact principal theorem types and all 23
new named declarations. Its output is `MATCHED_VERIFICATION_LOG.txt`.
No remaining local mathematical obligation within the displayed fixed
coordinate §4.5–4.10 package; actual-arm box extraction and cyclic/color
transport are supplied by their own modules.
