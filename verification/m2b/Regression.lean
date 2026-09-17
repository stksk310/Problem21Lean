import P21.Symmetric.FullClosure
import P21.Symmetric.Classification.CriticalRelations

namespace P21.Symmetric.M2BRegression

open Classification

/-- Symmetry keeps its original integer-gap meaning. -/
example (g : Generators) : SymmetricTail g ↔
    ∃ f : ℤ, ∀ t : ℤ, t ∉ g.H ↔ f-t ∈ g.H := Iff.rfl

/-- Existence and positive minimal critical coefficients require no canonical hypothesis. -/
example (g : Generators) (s : g.Setting) (i : Fin 3) :
    ∃ R : CriticalRelation g i, 2 ≤ R.coeff := by
  obtain ⟨R⟩ := criticalRelation_exists g (tail_generator_pos s) i
  exact ⟨R, R.ge_two (tail_minimal s)⟩

/-- This exact public type has neither canonical nor supplied gluing assumptions. -/
example : ∀ g : Generators, g.Setting → SymmetricTail g →
    Nonempty (SymmetricGlueData g) := symmetric_three_generator_gluing

/-- All arithmetic fields and actual nonnegative membership come from the proved result. -/
example (g : Generators) (s : g.Setting) (hs : SymmetricTail g) :
    ∃ G : SymmetricGlueData g,
      2 ≤ G.d ∧ 2 ≤ G.two.u ∧ 2 ≤ G.two.v ∧
      Int.gcd G.two.u G.two.v = 1 ∧ Int.gcd G.d G.w = 1 ∧
      (∃ a b : ℤ, 0 ≤ a ∧ 0 ≤ b ∧ G.w = a*G.two.u+b*G.two.v) ∧
      g.n (G.perm 0) = G.d*G.two.u ∧
      g.n (G.perm 1) = G.d*G.two.v ∧ g.n (G.perm 2) = G.w := by
  obtain ⟨G⟩ := symmetric_three_generator_gluing g s hs
  exact ⟨G, G.d_ge_two, G.two.u_ge_two, G.two.v_ge_two, G.two.coprime,
    G.coprime, G.w_mem, G.x_eq, G.y_eq, G.z_eq⟩

/-- Publication-equivalent full S3 input: symmetry, not an explicit gluing assumption. -/
example (g : Generators) (s : g.Setting) (F : ℤ)
    (hF : s.semigroup.IsFrobenius F) (hcan : s.semigroup.Canonical F g.m)
    (hs : SymmetricTail g) : s.semigroup.type ≤ 4 :=
  symmetric_tail_type_le_four g s F hF hcan hs

end P21.Symmetric.M2BRegression
