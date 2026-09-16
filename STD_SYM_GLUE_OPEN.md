# STD_SYM_GLUE — OPEN

The missing external result is the symmetric three-generator gluing classification
used in publication Section 2.2.1 and Section 3.3. It is not a project axiom.

The exact required direction is recorded, without a proof, as:

```lean
def SymmetricThreeGeneratorGluingStatement : Prop :=
  ∀ (g : Generators), g.Setting → SymmetricTail g → Nonempty (SymmetricGlueData g)
```

`SymmetricTail g` means `∃ f : ℤ, ∀ t : ℤ, t ∉ g.H ↔ f-t ∈ g.H`.
The frozen Setting supplies positive, irredundant generators. With nonnegativity,
the stated symmetry gives cofiniteness and identifies the greatest gap; it is not
an uninterpreted English predicate. No classification is embedded in its definition.

`SymmetricGlueData g` contains a permutation of the actual three tail generators,
integers `d,u,v,w`, `d,u,v ≥ 2`, `Int.gcd u v = 1`, `Int.gcd d w = 1`,
actual nonnegative-coefficient membership `w ∈ ⟨u,v⟩`, and the three equalities
`g.n (perm 0)=d*u`, `g.n (perm 1)=d*v`, `g.n (perm 2)=w`.
There is no pairwise-coprime, uniqueness, or additional positivity hypothesis.
Positivity of w follows from the original Setting.

The pinned-source search is in `MATHLIB_SYM_GLUE_SEARCH.md`. No sufficient theorem
was located. The available Frobenius-number results do not classify symmetric
three-generated semigroups. Formalizing that classification would introduce a
separate presentation/complete-intersection development, so this delivery uses
the user's authorized Gate-0 outcome C.

## What is proved

`P21.Symmetric.symmetric_tail_from_glue_data` proves the complete internal
conclusion `setting.semigroup.type ≤ 4` from the frozen Setting, its Frobenius
element, CAN, and exactly the explicit gluing data above. All stable-core,
RAW4, cross-layer, actual PF, and branch-closure arguments are proved.
The definition `SymmetricThreeGeneratorGluingStatement` is not used as a proved
theorem or as a hypothesis of that internal-closure theorem.

## Minimal remaining obligation and next attack

Prove the displayed external direction, then construct its data and apply the
existing internal closure. A focused route is to formalize the necessary
direction of the symmetric embedding-dimension-three complete-intersection
classification, extract a permuted generator pair with a common divisor,
divide out that divisor, and prove the remaining generator belongs to the
two-generated quotient semigroup. Keep the quotient coefficients nonnegative.
No later nonsymmetric classification or certificate is needed for this bridge.

STD_SYM_GLUE OPEN
FULL S3 OPEN
