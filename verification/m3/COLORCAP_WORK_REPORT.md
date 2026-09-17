# COLOR-CAP route audit and proof work

## Authoritative source and comparison

Publication text Appendix B begins on printed page 78 (PDF page 79); the
socle matrices and determinant formulas are on printed page 79 (PDF page 80).
`publication.txt`, `appendixB-readable.md`, and `frozen-color-cap.md` agree on
both natural socle matrix orderings, INPUT, the four sink regions, and the
B.17.2 PRE-CROSS-PATCH. The publication includes the reciprocal-prefix proof
and the special zero-th-run treatment. No mathematical source discrepancy
has been found in the portions audited. The readable text's A1/A2 labels
correspond to publication B.1–B.20; they are not alternative hypotheses.

A short search of the pinned Mathlib source found no empty lattice tetrahedron
or White width-one theorem. Whitehead topology and whitespace matches are
irrelevant. Thus a citation cannot close this dependency.

## Proven implementation scope

All code is new, below `P21/Nonsymmetric/ColorCap/`.

- `ActualMinimum.lean`: actual conversion of signed integer coefficients only
  after nonnegativity; coordinate caps from the same actual arm gap; attained
  minimal positive m-level; all three caps retained at that minimum; and the
  same-element positive-exit contradiction. These statements are color-neutral.
- `BoxPaths.lean`: finite counted in-box paths, exact weight loss at every
  firing, SAME-F for the original semigroup and socle element, existence of
  a maximal finite path by minimization of nonnegative weight, and the
  positive-exit contradiction with every coefficient explicitly nonnegative.
- `BoxInput.lean`: exact scalar/matrix INPUT, with no determinant, White,
  sink-exclusion, or positive-exit assumption in its fields; the actual rows,
  initial box membership, and maximal path existence; generic multiplicity
  contradiction from a nonnegative weighted certificate of sufficient mass.
- `RelativeLattice.lean`: the actual subgroup `{z | m divides z dot n}`;
  integral level extraction in its affine translate; smaller positive level
  contradiction from the attained minimum; top-face positive integral point
  contradiction via an actual tail witness.
- `PrefixArithmetic.lean`: RES implies the integer PREFIX separator for every
  successful index, and the symbolic residue antichain consequence. No
  numerical parameter bound or numerical scan is used.

None of these files calls a signed intermediate actual. No file asserts a
White result or DPE as an established theorem.

## Exact remaining mathematical gates

### WHITE/MINBOX

For either natural socle matrix U from Appendix B.1, retain the positive
Herzog parameters and primitive generator formulas, `0 < m < n_i`,
`1 <= p_i <= alpha_i - 1`, and `s - p dot n = k*m`, `k >= 1`.
The actual minimality condition is:

```
for every integer ell with 0 < ell < k and every integer vector u > 0,
  s - u dot n != ell*m.
```

The top-face condition is:

```
for every integer vector u > 0, s != u dot n.
```

Prove `k = 1`. These two displayed conditions are already derived from the
actual minimum and `f notin H` by the lower-companion/top-face lemmas; they
must not be postulated in the final COLOR-CAP theorem. The outstanding route
is relative-lattice saturation/volume, empty tetrahedron, White width-one
(or its precise special consequence), row-partition/permutation bookkeeping,
and the two colors' companion inequalities/multiplicity certificates.

### DPE

The exact unproved dynamics proposition in the current Lean vocabulary is:

```lean
forall (D : P21.Nonsymmetric.ColorCap.BoxInput) (t : Nat)
    (u : P21.Nonsymmetric.ColorCap.Point),
  P21.Nonsymmetric.ColorCap.BoxPath D.upper D.rows t D.x u ->
  (forall i, not (P21.Nonsymmetric.ColorCap.InBox D.upper
    (P21.Nonsymmetric.ColorCap.fire D.rows i u))) ->
  exists i, forall j, 1 <= P21.Nonsymmetric.ColorCap.fire D.rows i u j
```

The endpoint is therefore positive and out of the box. The already proved
`path_exit_contradiction` then closes THREE-ARM for the same original data
once MINBOX supplies the initial level-one equation. What remains for DPE
is the actual successful-crossing prefix derivation, residue injectivity and
slot counts, reciprocal-prefix preservation/rank, one/two-color terminal
certificate exhaustion, and first-third-color exclusion. PREFIX itself is
proved from RES, not assumed as an unexplained named fact.

## Status

COLOR-CAP, STD_WHITE/MINBOX, and DPE are not yet closed. The implemented
lemmas isolate their actual/relative-lattice/path semantics without an
axiomized standard input or a stronger final hypothesis. Full closure is
still the target; these files alone do not justify a full M3 claim.

## Updated checked progress

The source arithmetic has been pushed substantially beyond the initial audit:

- `BoxInput.sink_cover` proves the exact four-region cover by negating actual
  positivity conditions; `initial_positive_firing` excludes every initial sink
  using the publication's explicit row-weight certificates.
- `PositiveMinors.lean` derives both strict corridor minors directly from
  INPUT, proves the {1,2} sink-A and {1,3} sink-B exclusions, and proves that
  the three in-box source regions are pairwise disjoint.
- `DPEOneColor.one_color_sink_impossible` proves all four sink exclusions
  for every nonempty one-color in-box run, with symbolic unbounded N.
- `PrefixArithmetic` now also proves distinctness of each residue coordinate
  and the full finite interval slot bound, including out-of-range terminal
  thresholds via integer `toNat` counts.
- `WhiteCertificates` proves the common failure-cone mass bound and BOTH
  master AP/BP multiplicity contradictions for every k>=2, including the
  modular-inverse identities. No numerical scan or bound on k occurs.
- `CompanionBounds` proves BOTH exact six-failure BA/BB inequalities, derives
  AP/BP with explicitly nonnegative integer slack, and proves the first
  color-A class's preliminary coordinate bounds.
- `RelativeLattice.six_companion_failures` derives ALL six COMP positivity
  failures directly from the same attained actual minimum and class heights;
  the positivity failures are not new mathematical assumptions at this link.
- `ThreeArms` derives socle membership directly from actual PF returns,
  applies the proved Herzog fA/fB gap results to get the minimum for both
  colors, constructs exact level-one BoxInput, and transports the color-B
  odd swap back to the original same-element factorization. Both conditional
  MINBOX+DPE endpoints are kernel checked.

The final integration API is now exactly:

```
P21.Nonsymmetric.ColorCap.MinimumOneStatement
P21.Nonsymmetric.ColorCap.BoxPositiveExitStatement
P21.Nonsymmetric.ColorCap.three_arms_impossible_of_residuals
```

`MinimumOneStatement` quantifies over the same Setting and true Herzog
critical data, either color, a positive minimum k, and p in the corresponding
open a/b arm box. Its conclusion is k=1. It does NOT assume actual arms,
White classes, or an already proved color cap. Actual arms supply all its
hypotheses by the preceding proved bridge.

`BoxPositiveExitStatement` is precisely the maximal finite-path positive
exit proposition displayed above. Neither proposition is asserted as a
theorem. `three_arms_impossible_of_residuals` has these TWO explicitly visible
hypotheses and proves actual three-arm impossibility for BOTH colors.

The remaining MINBOX work is: complete relative empty-tetrahedron/saturation
and White-class existence and arbitrary row ordering, plus inverse-class
preliminary bounds and assembly of the already proved companion/mass links.
The remaining DPE work is: chronological RES extraction from actual paths,
reciprocal-prefix preservation and dual rank, the remaining two-color sink
certificates, and first-third-color exclusion. The one-color branch, the
initial sink, both orientation minors, basic PREFIX arithmetic, and finite
slot counting are already proved and are not remaining external inputs.

This is a proved reduction with two precise open inputs. It is not STD_WHITE,
MINBOX, DPE, THREE-ARM, or unconditional COLOR-CAP closure.
