import P21.Symmetric.Raw4

open P21.Symmetric

-- Exact 2GI interface, with the full strict-bound parameter range.
example (D : TwoGeneratorData) (A B : ℤ)
    (hA : 0 < A) (hAv : A < D.v) (hB : 0 < B) (hBu : B < D.u) :
    D.translate (A*D.u) ∩ D.translate (B*D.v) =
      D.translate (A*D.u+B*D.v) ∪ D.translate (D.u*D.v) :=
  D.two_generator_intersection hA hAv hB hBu

-- Signed expressions do not confer actual membership.
example (D : TwoGeneratorData) : (-1)*D.u + 0*D.v ∉ D.T := by
  rw [D.normal_form_mem_iff (by omega) D.u_pos]
  norm_num

-- The semantics of generated membership agree with frozen M1.
example (D : TwoGeneratorData) : D.T = P21.generated ![D.u,D.v] :=
  D.T_eq_generated

-- Integer Frobenius semantics, including all negative integer arguments.
example (D : TwoGeneratorData) (t : ℤ) :
    t ∉ D.T ↔ D.u*D.v-D.u-D.v-t ∈ D.T := D.frobenius_symmetry t

example (D : TwoGeneratorData) : D.semigroup.IsFrobenius (D.u*D.v-D.u-D.v) :=
  D.isFrobenius

#print axioms TwoGeneratorData.T_eq_generated
#print axioms TwoGeneratorData.representation_difference
#print axioms TwoGeneratorData.normal_form_existsUnique
#print axioms TwoGeneratorData.normal_form_mem_iff
#print axioms TwoGeneratorData.frobenius_symmetry
#print axioms TwoGeneratorData.subcritical_nonneg
#print axioms TwoGeneratorData.interior_gap
#print axioms TwoGeneratorData.subcritical_gap
#print axioms TwoGeneratorData.two_generator_intersection
#print axioms TwoGeneratorData.isFrobenius

-- Threshold classification retains both strict interior bounds exactly.
example (D : TwoGeneratorData) (p q : ℤ) (hq : 0 ≤ q) (hqu : q < D.u) :
    (∃ a b, idealMin D.T (D.intersectionIdeal (p*D.u+q*D.v)) a ∧
      idealMin D.T (D.intersectionIdeal (p*D.u+q*D.v)) b ∧ a ≠ b) ↔
        0 < q ∧ -D.v < p ∧ p < 0 := D.two_minima_iff hq hqu

-- All four actual rows are derived from type, never accepted as a hypothesis.
example {g : P21.Generators} (G : SymmetricGlueData g) (s : g.Setting) (F : ℤ)
    (hF : s.semigroup.IsFrobenius F) (hcan : s.semigroup.Canonical F g.m)
    (htype : 5 ≤ s.semigroup.type) : Nonempty (Raw4Data G s F) :=
  G.exists_raw4 s hF hcan htype

#print axioms TwoGeneratorData.intersectionIdeal_generators
#print axioms TwoGeneratorData.minimal_ncard_le_two
#print axioms TwoGeneratorData.minimal_pair_eq
#print axioms TwoGeneratorData.two_minima_iff
#print axioms SymmetricGlueData.raw_min_layers
#print axioms SymmetricGlueData.raw_min_ncard_le_four
#print axioms SymmetricGlueData.raw_min_zero_ncard_le_two
#print axioms SymmetricGlueData.surviving_eq_candidates
#print axioms SymmetricGlueData.exists_raw4
