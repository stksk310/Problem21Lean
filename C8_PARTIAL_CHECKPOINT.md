# C8 partial checkpoint — 2026-09-18

Frozen base: `80b36191937b2e2f0dc251ac6006d63f088e03b2`
Branch: `c8-chain-boundary-window`

## Proved in Lean

- exact integer first-fit sequence and genuine minimum
- FIRST-CAPS
- Xi positivity and actual zero-k OmegaHat
- central signed FK row and genuine upper face
- same-element packet with two actual factorizations and common-source containment
- boundary wall and FI-A/FJ-only window wall
- pure-H EA and Qj kernel coordinates via frozen `integer_kernel_span`
- EA second kernel coefficient `y=1`
- Qj second kernel coefficient `v=1`
- exact EA-ONE / QJ-ONE equations
- determinant identity `(x*Lj-z*Li)*d = x*(Aj+1)+z*delta`
- determinant positivity `x*Lj-z*Li >= 1`

## First open theorem

Publication subsection: §8.5, empty integer triangle / DET1.

The first Lean target represented by:

```lean
theorem empty_triangle
    (O : A.OneData E)
    (hF : s.semigroup.IsFrobenius F)
    (hw : A.chi ≤ K.chain.T) :
    O.EmptyTriangleStatement
```

where `O : A.OneData E`, `EmptyTriangleStatement` says every integer point in
the closed triangle with vertices `(0,0)`, `(x,Li)`, `(z,Lj)` is a vertex, and
`DetOneStatement` is `x*Lj-z*Li=1`.  After `empty_triangle`, the next target is
the internal implication `O.EmptyTriangleStatement → O.DetOneStatement`.

The first missing proof must turn any nonvertex closed-triangle point into an
earlier fitting HRJ point and contradict WINDOW-WALL.  The immediately following
missing step is the lattice-index lemma: if the positive determinant is at least
two, the fundamental parallelogram has a nonzero integer representative and that
point or its reflection supplies such a nonvertex point. These are mathematical
proof gaps, not frozen-interface obstructions. DET1 has not been added as a field
or assumption.

No Section 9 source is imported. No frozen mathematical Lean source was edited.
