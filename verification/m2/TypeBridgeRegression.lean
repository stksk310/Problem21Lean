import P21.Symmetric.CrossLayer
import P21.External.SymmetricThreeGenerator

open P21 P21.Symmetric

example {g : Generators} (s : g.Setting) {F f : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hcan : s.semigroup.Canonical F g.m)
    (hsym : SymmetricAt g.H f) :
    s.semigroup.type = 1 +
      {c | idealMin g.H (tailIntersection g (f - F - g.m)) c ∧
        c ∈ s.semigroup.Apery g.m}.ncard := type_bridge s hF hcan hsym

example {g : Generators} (s : g.Setting) {F f : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hcan : s.semigroup.Canonical F g.m)
    (hsym : SymmetricAt g.H f) :
    {c | idealMin g.Gamma (shiftedCore g (f - F - g.m)) c} =
      insert g.m {c | idealMin g.H (tailIntersection g (f - F - g.m)) c ∧
        c ∈ s.semigroup.Apery g.m} := exact_bridge s hF hcan hsym

namespace BridgeRegression
def twoThree : TwoGeneratorData := ⟨2, 3, by norm_num, by norm_num, by decide⟩

/-- Both source SPLIT alternatives can hold, so exclusive disjunction is incorrect. -/
example : (8 - twoThree.u - twoThree.v) ∈ twoThree.T ∧
    (8 - 1 - twoThree.u - twoThree.v) ∈ twoThree.T := by
  constructor
  · exact ⟨0, 1, by norm_num, by norm_num, by norm_num [twoThree]⟩
  · exact ⟨1, 0, by norm_num, by norm_num, by norm_num [twoThree]⟩

example : Nonempty (SignedRepresentation ![2, 3] 1) := by
  exact ⟨⟨![-1, 1], by norm_num [value, Fin.sum_univ_succ]⟩⟩

example : ¬ Nonempty (ActualFactorization ![2, 3] 1) := by
  intro h
  have hg := actual_iff_mem.mp h
  have hT : (1 : ℤ) ∈ twoThree.T := by
    rw [twoThree.T_eq_generated]
    exact hg
  have he : (1 : ℤ) = (-1) * twoThree.u + 1 * twoThree.v := by norm_num [twoThree]
  rw [he, twoThree.normal_form_mem_iff (by norm_num) (by norm_num [twoThree])] at hT
  omega

#print axioms type_bridge
#print axioms exact_bridge
#print axioms ActualRawRow.pf
#print axioms ActualRawRow.pf_add_m_mem_tail
#print axioms complete_split
#print axioms SymmetricThreeGeneratorGluingStatement

end BridgeRegression
