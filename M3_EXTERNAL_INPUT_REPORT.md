# Exact remaining external and combinatorial inputs

## STD_HERZOG: proved

`herzog_classification : HerzogClassificationStatement` constructs positive
critical data and exactly two distinct tail PF elements from the actual
setting, tail cofiniteness, and nonsymmetry. Critical coefficients are least
positive multipliers. No pairwise-coprime hypothesis is introduced. The proof
rules out pure critical relations via genuine gluing and symmetry, proves
the positive cycle, then proves the Apéry L-shape and both PF formulas.
`primitive_generator_formulas` additionally proves the three exact publication
generator formulas under tail cofiniteness, using the saturated integer kernel
and a unimodular completion. Pairwise coprimality is never assumed.

## STD_WHITE / narrower MINBOX consequence: OPEN

The chosen narrow remaining proposition is `ColorCap.MinimumOneStatement`
in `P21/Nonsymmetric/ColorCap/Residuals.lean`. It universally quantifies the
actual generators and setting, tail cofiniteness (hence primitive tail lattice),
positive critical data, either socle color,
an attained positive m-level k, a point in that color's open coefficient box,
the actual socle representation and its minimum property; the conclusion is
k = 1. The representation and minimum hypotheses are already derived from
three actual PF arms by `colorA_actual_minimum` / `colorB_actual_minimum`.
The actual classification derives tail cofiniteness from canonical reduction
and an actual selected Q row. It is not an extra premise in the final theorem.
The earlier pre-CI version omitted this required primitive-tail condition;
that version is superseded. See `verification/m3/REVIEW_CORRECTION_MINBOX.md`.

What is still needed for the publication route: rank-three relative-lattice
saturation and tetrahedron volume;
emptiness; White width-one or the exact special consequence; class/partition
and modular inverse bookkeeping; assembly with the proved six companion
failure inequalities and both-color multiplicity certificates. No applicable
White theorem was found in the pinned Mathlib source. A citation alone is not
used as a Lean proof.

## DPE: OPEN

`ColorCap.BoxPositiveExitStatement` in `ColorCap/ThreeArms.lean` states that
every maximal finite in-box path from x for exact `BoxInput` admits a firing
whose coordinates remain positive. `BoxInput` contains the source's positive
parameters and `Cn = m 1`, with 0 < m < n_i. It contains neither a sink
exclusion nor a positive-exit assertion.

Proved groundwork includes actual finite path existence, exact weight loss,
SAME-F, first-state and one-color sink exclusions, positive minors, integer
PREFIX separation, residue injectivity/antichain and slot bounds. Remaining
work includes deriving the complete successful-prefix hypotheses from the
path, reciprocal-rank/omitted-prefix preservation, all two-color terminal
cases B.17–B.18, and first-third-color cases B.19.

## Proved conditional reduction

`three_arms_impossible_of_residuals` has exactly the two above propositions as
visible extra inputs and excludes three actual same-color PF arms in either
color. It keeps the same original semigroup and socle element and turns only
nonnegative completed vectors into memberships. Both inputs are unproved
definitions of Prop. There are no project-specific axioms, claimed White
instances, or fabricated theorem bodies closing them. Any downstream result
using this reduction remains conditional until both are proved.
