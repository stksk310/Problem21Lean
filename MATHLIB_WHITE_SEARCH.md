# Pinned mathlib White theorem search

Search performed 2026-09-17 in `.lake/packages/mathlib/Mathlib`.
The manifest pins mathlib `v4.34.0-rc1`, commit
`de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`.

## Queries and result

The case-insensitive ripgrep query was
`\bwhite\b|empty lattice simplex|lattice width|primitive affine functional|integer simplex|unimodular simplex|empty.{0,30}tetrahedr`.
Its only hit was the CSS string `white-space` in
`Mathlib/Tactic/ClickSuggestions/Util.lean:368`. Searches for `tetrahedr`
found general Euclidean/convex geometry, not integer-lattice emptiness.
Filename searches covered `ZLattice`, `Lattice`, `Simplex`, `Polytope`,
`Polyhedron`, and `FundamentalDomain`.

Relevant supporting APIs, none of which supplies White's conclusion:

- `Algebra/Module/ZLattice/Basic.lean`: integral lattices, basis fundamental
  domains, coordinate floor/ceiling.
- `Algebra/Module/ZLattice/Covolume.lean`: `covolume_eq_det`,
  `covolume_div_covolume_eq_relIndex`.
- `LinearAlgebra/AffineSpace/Simplex/Basic.lean` and
  `Analysis/Convex/StdSimplex.lean`: affine/convex simplices.
- `Data/Int/GCD.lean`: Bezout coefficients and modular inverses.

**W1 result: no sufficient theorem found.** Generic lattice and simplex
infrastructure does not prove that an empty lattice tetrahedron has width one.

## Internal arithmetic route investigated

For cyclic class coordinates, the needed arithmetic implication is:
for `k >= 2`, three residues `0 < a_i < k` satisfying
`sum_i ((j*a_i) % k) = k+j` for every `0 < j < k` have a coordinate equal
to one. This is an all-parameter theorem, not a bounded enumeration.

The primary exposition [Khan and Rogers, arXiv:1610.01981](https://arxiv.org/abs/1610.01981)
gives a proof using increments of integer floor sequences (Proposition 16
and the following argument). Its modular-age identity is Proposition 14.
This reference supplies a proof strategy, not a Lean theorem or an axiom.
The original reference is G. K. White, *Lattice Tetrahedra*, Canadian
Journal of Mathematics 16 (1964), 389–396.

The arithmetic implication is now proved internally as
`P21.Nonsymmetric.White.cyclic_white_proved : CyclicWhiteStatement` in
`P21/Nonsymmetric/White/WidthOneBeatty.lean`. Its individual Lean compilation
completed successfully. The proof uses `WidthOne.lean` for the modular-age,
floor-jump, Beatty-support, and gap lemmas, then proves the support partition
contradiction and handles all six orderings of the three residues. No
citation is accepted as a proof term. The separately formalized geometric
bridge is required to apply this arithmetic theorem to MINBOX.

`P21/Nonsymmetric/White/ClassData.lean` independently proves that nonzero
coordinates in all cyclic classes force gcd one, and constructs the positive
inverse representative and nonnegative quotient by Bezout.
