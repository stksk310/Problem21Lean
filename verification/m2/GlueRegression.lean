import P21.Symmetric.GlueNormalForm
namespace P21.Symmetric.Regression
variable {g : Generators} (D : SymmetricGlueData g) (s : g.Setting)
example (a : ℤ) : ∃! jt : ℤ × ℤ,
    0 ≤ jt.1 ∧ jt.1 < D.d ∧ a = jt.1 * D.w + D.d * jt.2 :=
  D.normal_form_existsUnique a
example {j t : ℤ} (hj : 0 ≤ j) (hjd : j < D.d) :
    j * D.w + D.d * t ∈ g.H ↔ t ∈ D.two.T := D.normal_form_mem_iff hj hjd
example : SymmetricAt g.H ((D.d - 1) * D.w + D.d * D.two.frobenius) := D.symmetry
#print axioms SymmetricGlueData.represented_eq_tail
#print axioms SymmetricGlueData.normal_form_mem_iff
#print axioms SymmetricGlueData.symmetry
#print axioms SymmetricGlueData.isFrobenius
end P21.Symmetric.Regression
