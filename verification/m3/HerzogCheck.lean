import P21.Nonsymmetric.PrimitiveGenerators
#print axioms P21.Nonsymmetric.herzog_critical_exists
#print axioms P21.Nonsymmetric.nonsymmetric_herzog_exists
#print axioms P21.Nonsymmetric.herzog_classification
#print axioms P21.Nonsymmetric.HerzogCriticalData.tailPF_eq_pair
#print axioms P21.Nonsymmetric.HerzogCriticalData.fA_ne_fB
#check P21.Nonsymmetric.nonsymmetric_herzog_exists


namespace P21.Nonsymmetric.HerzogRegression
variable {g : Generators}

/-- All three exact primitive formulas are conclusions; no pairwise-coprime
or determinant-normalization hypothesis is accepted by this regression. -/
example (D : HerzogCriticalData g) (hp : ∀ i, 0 < g.n i)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H) :
    g.n 0 = (D.a 1:ℤ)*D.a 2+(D.a 2:ℤ)*D.b 1+(D.b 1:ℤ)*D.b 2 ∧
    g.n 1 = (D.a 0:ℤ)*D.a 2+(D.a 0:ℤ)*D.b 2+(D.b 0:ℤ)*D.b 2 ∧
    g.n 2 = (D.a 0:ℤ)*D.a 1+(D.a 1:ℤ)*D.b 0+(D.b 0:ℤ)*D.b 1 :=
  primitive_generator_formulas D hp hcof

/-- The primitive formulas belong to the very same constructed full Herzog
data; the existential witnesses are not re-instantiated independently. -/
example (g : Generators) (s : g.Setting)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (hns : ¬ P21.Symmetric.SymmetricTail g) :
    ∃ D : NonsymmetricHerzogData g,
      g.n 0 = (D.a 1:ℤ)*D.a 2+(D.a 2:ℤ)*D.b 1+(D.b 1:ℤ)*D.b 2 ∧
      g.n 1 = (D.a 0:ℤ)*D.a 2+(D.a 0:ℤ)*D.b 2+(D.b 0:ℤ)*D.b 2 ∧
      g.n 2 = (D.a 0:ℤ)*D.a 1+(D.a 1:ℤ)*D.b 0+(D.b 0:ℤ)*D.b 1 :=
  nonsymmetric_herzog_primitive_exists g s hcof hns
end P21.Nonsymmetric.HerzogRegression

#print axioms P21.Nonsymmetric.tail_bezout_vector
#print axioms P21.Nonsymmetric.primitive_generator_minors
#print axioms P21.Nonsymmetric.primitive_generator_formulas
#print axioms P21.Nonsymmetric.nonsymmetric_herzog_primitive_exists
