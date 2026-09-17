# STD_HERZOG work report

## Status

The nonsymmetric three-generator critical-cycle and exact-PF theorem is proved in Lean:

- `P21.Nonsymmetric.herzog_critical_exists`
- `P21.Nonsymmetric.nonsymmetric_herzog_exists`
- `P21.Nonsymmetric.herzog_classification : HerzogClassificationStatement`

The input is the existing irredundant four-generator `g.Setting`, actual
cofiniteness of `g.H`, and `¬ SymmetricTail g`. The conclusion supplies strictly
positive `a`, `b`, exact `rho = a+b`, the three critical relations, actual least
positive critical multipliers, the two publication PF formulas, their
distinctness, and exact equality with the full integer PF set of the same tail.
No pairwise coprimality is assumed. Fixed indices 0,1,2 suffice; the choice of
`a,b` gives the required positive cycle without permuting the original tail.

## Primitive-generator bridge — completed

Publication §2.2.2's three primitive determinant identities are now proved in
`P21/Nonsymmetric/PrimitiveGenerators.lean`. The theorem
`primitive_generator_formulas` uses only the positive critical data, positive
generators, and actual tail cofiniteness. No pairwise coprimality or determinant
normalization is assumed.

Consecutive cofinite tail elements produce an integer Bezout vector v. The
saturated kernel theorem decomposes each standard basis vector minus n_j*v.
These decompositions give an integer right inverse to the matrix with columns
v,r_j,r_k. Its determinant is a unit; the positive kernel minor and positive
n_0 force determinant +1. The exact minors, and hence all three publication
formulas, follow. `nonsymmetric_herzog_primitive_exists` bundles them with the
same full Herzog witness. This completion supersedes the earlier primitive
bridge scope caveat.
## Pinned-library search

A focused text search of the pinned Mathlib tree for `Herzog` and numerical
semigroup classification found no matching theorem. The proof instead reuses
frozen M2B critical-relation and primitive two-generator infrastructure.

## Proof route

1. Positivity supplies each least critical relation by the frozen
   `criticalRelation_exists` theorem and natural well-ordering.
2. If a critical relation is pure, normalize the two generators by their gcd.
   Their primitive coefficients show that its critical multiplier is at least
   the primitive partner. The signed normal form of the third generator has
   a bounded coefficient. If its other coefficient were negative, rearranging
   gives an actual nonnegative off-direction representation at a strictly
   smaller critical multiplier. Therefore the third generator lies in the
   primitive two-generator semigroup. Frozen `decomposition_glue_data` and
   `glue_data_symmetric_tail` then contradict nonsymmetry.
3. Consequently every off-diagonal critical coefficient is positive. Replacing
   a whole packet of another critical relation would yield a strictly smaller
   actual critical relation, so each off coefficient is below its target
   critical multiplier.
4. Adding pairs of relations gives `rho_i ≤ a_i+b_i`. The sum of all three
   weighted relations is zero and the generators are positive, so equality
   holds in each direction. This constructs `HerzogCriticalData`.
5. Prove the actual Apéry set relative to `n_0` has the L-shaped pair domain
   `0 ≤ y < rho_1`, `0 ≤ z < rho_2`, and `y < b_1 ∨ z < a_2`.
   The forward direction replaces actual critical packets coefficientwise.
   For the reverse direction, cancel a hypothetical factorization of
   `y*n_1+z*n_2-n_0`. Critical minimality first forces both remaining pair
   coefficients positive. Subtracting the mixed critical relation then proves
   those coefficients cover `b_1,a_2`, contrary to the L condition.
6. The two upper corners give the displayed `fA` and `fB`. All generator
   returns have explicit nonnegative factorizations, and a factorization
   induction proves these suffice for the full PF predicate.
7. For arbitrary PF `q`, `q+n_0` lies in that Apéry domain. Its returns at
   `n_1,n_2` force it to one of the two upper corners. Thus the pair exhausts
   PF. Equality of the two corners would give the pure relation
   `a_1*n_1=b_2*n_2` below `rho_1`, so they are distinct.

The PF proof does not need a kernel-basis or global factorization-uniqueness
assumption. All signed rearrangements are converted to actual factorizations
only after explicit coefficient nonnegativity proofs.

## New files owned by this work

- `P21/Nonsymmetric/HerzogData.lean`
- `P21/Nonsymmetric/HerzogClassification.lean`
- `P21/Nonsymmetric/Herzog/PseudoFrobenius.lean`
- `P21/Nonsymmetric/PrimitiveGenerators.lean`

All four compiled through the frozen Lean wrapper. No frozen mathematical
source was edited. No project-specific assumptions or proof escapes were added.
The complete M3 G4 classification is a separate downstream obligation; this
report does not claim it.


