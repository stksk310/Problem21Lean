# Herzog, geometry and extraction proof-path review

## Scope and result

Internal review of the final statements and proof paths in HerzogData,
HerzogClassification, Herzog/PseudoFrobenius, CriticalBox, Kernel, MatchedPair,
ReturnLevels, SameColor, MixedColor, Saturation, Extraction and ActualMixed.
No material mismatch or hidden stronger mathematical assumption was found in
these reviewed paths. This is an implementation review, not an external audit.

The terminal extraction theorems are conditional on their respective actual
four-row configuration. They do not by themselves prove exhaustive four-row
classification. The separate classifier must establish that configuration.

## Herzog

`nonsymmetric_herzog_exists` assumes the existing `g.Setting`, actual tail
cofiniteness, and `¬ SymmetricTail g`. It constructs all positive a/b data and
least positive critical multipliers. Tail cofiniteness is not smuggled into
nonsymmetry; it is an explicit premise, supplied downstream by the canonical
setting infrastructure. No pairwise-coprimality premise occurs.

The pure-critical branch uses the gcd of the selected pair solely to normalize
that pair. A negative coefficient in the signed normal form of the third
generator is rearranged into an explicitly nonnegative smaller critical
relation. Primitive-pair membership then invokes the frozen gluing-to-symmetry
theorem. This is logically in the permitted direction.

The exact PF theorem concerns `TailPF g`, i.e. the original integer tail and
all nonzero tail elements. The two corners are proved gaps, have actual returns
at all three generators, exhaust PF, and are distinct. `fullData` packages
these proved properties; it is not an existence assumption. The standard
statement proposition is discharged by `herzog_classification`.

## Primitive-generator completion addendum

The earlier primitive-generator caveat has been closed by
`PrimitiveGenerators.lean`. `primitive_generator_formulas` proves all three
exact publication determinant formulas. `nonsymmetric_herzog_primitive_exists`
uses the same full Herzog witness for criticality, PF, and primitive formulas.

The proof constructs a Bezout vector from consecutive actual tail elements,
then applies the already-proved saturated integer kernel to obtain an integer
right inverse for the basis-completion matrix. Determinant multiplicativity
makes its determinant a unit. Positivity of n_0 and the corresponding critical
minor proves the determinant is +1, with no orientation or normalization
assumption. Polynomial cofactor identities then yield all three generators.
The matching theorem-level regressions and axiom checks pass.
## Critical box and integer kernel

Critical-box uniqueness uses differences of two actual natural coefficient
vectors. In three coordinates, a nonzero relation has a side supported in one
direction, which contradicts that direction's actual critical minimality.

The kernel proof first constructs a rational span using a positive minor.
It then subtracts integer floor multiples of the two rows. The resulting vector
is still integral, remains in the actual integer kernel, and is strictly
subcritical in every coordinate. Critical-box rigidity forces this remainder
to zero. Thus integer saturation is proved rather than assumed. The uniqueness
part is supplied by the nonzero minor and is an actual Z-basis theorem.

## Return minima and synchronization

`minimal_return_exists` applies natural well-ordering separately to each
return fiber. A positive m-coordinate is obtained from nonmembership in H;
the returned n_0-coordinate is zero because otherwise removing one n_0 would
represent the same actual PF row in Gamma.

The four caps apply to the same F+n_0 representation obtained by adding the
named complement to its own return. Packet replacement then gives an actual
F representation. No relation containing a nonzero m-coordinate is fed to
critical minimality.

`unequal_levels_impossible` admits gapJ=0 and gapK=0. Its final completed
vectors have all four coefficients proved nonnegative before `four_mem` is
called. Potentially signed intermediate W-expressions are not used as actual
factorizations. Only after the two m-levels have been proved equal does
`equal_level_matching` apply the pure-tail critical-box lemma.

The return gap lemmas use a short equivalent argument: if
f_epsilon-(depth-1)*n_0 were in H, adding the nonnegative removed copies would
put the already-proved PF gap f_epsilon in H. This derives exactly the source
nonmembership with no extra hypothesis.

## Same/mixed color geometry

The same-color two-case theorem and both mixed orientations begin with natural
coefficients in the named actual complements. Kernel coefficients are bounded
using the exact integer basis. Case splits retain zero coefficients.

The auxiliary strict positivity needed for singleton exclusions is derived
from the actual complement antichain. It is not an extra premise on the
geometry. BA-W is completed before being called actual; the regression suite
explicitly verifies that common coefficient R=0 remains valid.

`ActualMixed` obtains coefficient boxes from actual arm rows and transports
all data through the same cyclic relabeling. It adds no coefficient or
distinctness assumptions. If an arm were the singleton row, its two actual
return directions would contradict singleton support; this supplies required
distinctness internally.

## Terminal extraction

The three structures retain the same setting, F, m, W and selected rows.
Each carries actual-Q membership, injectivity of the selected four-row vector,
required missing directions, exact complement identities and coefficient
ranges. No exact cardinality assertion about the whole Q set occurs.

- PATH derives positive R from actual ray incomparability, then saturates both
  endpoint singleton rays via BOX-W and gives all three ladder equalities.
  The qA/qB ladder labels are explicitly positions: qA is the A-arm in direction
  2, while qB is the B-arm in direction 0.
- TYPE II derives lambda <= b_0 by ruling out same-color Case B with the cyclic
  mixed pair. It then proves the singleton complement and exact row formula.
- CHAIN compares the same matched complements and extracts all four positive
  slacks. `chain_exact_input_independent` also derives equality of independently
  supplied matched-arm depths rather than assuming it in the incoming labels.

BOX-W saturation uses the cap on all W factorizations and an attained maximum,
then the integer kernel. It never assumes global factorization uniqueness.

## Verification evidence

`verification/m3/ExtractionRegression.lean` contains theorem-level exact
signature tests for PATH, TYPE II and CHAIN, positive CHAIN slack extraction,
and the R=0 completed BA-W boundary. It compiled successfully. The inspected
Herzog and extraction/geometry declarations depend only on propext,
Classical.choice and Quot.sound. Parent integration remains responsible for a
fresh complete build, all-declaration checks, immutable-source checks and CI.


