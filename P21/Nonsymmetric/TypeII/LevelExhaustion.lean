import P21.Nonsymmetric.TypeII.UniformCap

namespace P21.Nonsymmetric
namespace TypeIIInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

theorem F_from_SJ (T : TypeIIInput s F D) (SJ : ActualReturn g T.qS 1) :
    F = ((SJ.factorization.coeff 0 : ℤ) - 1) * g.m +
      (T.P0 + SJ.factorization.coeff 1) * g.n 0 - g.n 1 +
      (SJ.factorization.coeff 3 : ℤ) * g.n 2 := by
  have hs := T.sj_equation SJ
  have hw := T.qS_add_P0
  simp only [W] at hw
  linear_combination -hw - hs

theorem F_from_SK (T : TypeIIInput s F D) (SK : ActualReturn g T.qS 2) :
    F = ((SK.factorization.coeff 0 : ℤ) - 1) * g.m +
      (T.P0 + SK.factorization.coeff 1) * g.n 0 +
      (SK.factorization.coeff 2 : ℤ) * g.n 1 - g.n 2 := by
  have hs := T.sk_equation SK
  have hw := T.qS_add_P0
  simp only [W] at hw
  linear_combination -hw - hs

theorem equal_level_relation (T : TypeIIInput s F D)
    (SJ : ActualReturn g T.qS 1) (SK : ActualReturn g T.qS 2)
    (heq : SJ.factorization.coeff 0 = SK.factorization.coeff 0) :
    ((SK.factorization.coeff 1 : ℤ) - SJ.factorization.coeff 1) * g.n 0 +
      ((SK.factorization.coeff 2 : ℤ) + 1) * g.n 1 =
      ((SJ.factorization.coeff 3 : ℤ) + 1) * g.n 2 := by
  have hj := T.JR SJ
  have hk := T.KR SK
  rw [heq] at hj
  linear_combination hk - hj

theorem impossible_equal_levels (T : TypeIIInput s F D)
    (hF : s.semigroup.IsFrobenius F)
    (SJ : ActualReturn g T.qS 1) (SK : ActualReturn g T.qS 2)
    (heq : SJ.factorization.coeff 0 = SK.factorization.coeff 0) : False := by
  have hrel := T.equal_level_relation SJ SK heq
  have hC := T.C_cap hF SJ
  have hB := T.B_cap hF SK
  by_cases hDA : (SJ.factorization.coeff 1 : ℤ) ≤ SK.factorization.coeff 1
  · have hcrit := herzog_critical_le_int D
      (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)
      ((SJ.factorization.coeff 3 : ℤ) + 1)
      ((SK.factorization.coeff 1 : ℤ) - SJ.factorization.coeff 1)
      ((SK.factorization.coeff 2 : ℤ) + 1)
      (by omega) (by omega) (by omega) (by linarith [hrel])
    have hr := D.rho_eq 2
    have := D.a_pos 2
    omega
  · have hcrit := herzog_critical_le_int D
      (by decide : (1 : Fin 3) ≠ 0) (by decide : (1 : Fin 3) ≠ 2)
      ((SK.factorization.coeff 2 : ℤ) + 1)
      ((SJ.factorization.coeff 1 : ℤ) - SK.factorization.coeff 1)
      ((SJ.factorization.coeff 3 : ℤ) + 1)
      (by omega) (by omega) (by omega) (by linarith [hrel])
    have hr := D.rho_eq 1
    have := D.b_pos 1
    omega

theorem ABS_L (T : TypeIIInput s F D)
    (SJ : ActualReturn g T.qS 1) (SK : ActualReturn g T.qS 2) :
    F = ((SJ.factorization.coeff 0 : ℤ) - SK.factorization.coeff 0 - 1) * g.m +
      (T.P0 + SJ.factorization.coeff 1 - SK.factorization.coeff 1 - 1) * g.n 0 +
      (T.R - 2 - SK.factorization.coeff 2) * g.n 1 +
      ((SJ.factorization.coeff 3 : ℤ) + T.T0) * g.n 2 := by
  have hf := T.F_from_SJ SJ
  have hk := T.KR SK
  linear_combination hf + hk

theorem impossible_level_left (T : TypeIIInput s F D)
    (hF : s.semigroup.IsFrobenius F)
    (SJ : ActualReturn g T.qS 1) (SK : ActualReturn g T.qS 2)
    (hlt : SK.factorization.coeff 0 < SJ.factorization.coeff 0) : False := by
  have hU := T.uniform_i_cap SJ SK
  have hB := T.B_cap hF SK
  have hcert := T.ABS_L SJ SK
  have hmem := actual_of_coordinates g F
    ((SJ.factorization.coeff 0 : ℤ) - SK.factorization.coeff 0 - 1)
    (T.P0 + SJ.factorization.coeff 1 - SK.factorization.coeff 1 - 1)
    (T.R - 2 - SK.factorization.coeff 2)
    ((SJ.factorization.coeff 3 : ℤ) + T.T0)
    (by omega)
    (by have := T.P0_sub_b0_pos; omega)
    (by have := T.R_eq; have := T.g1_pos; omega)
    (by have := T.T0_sub_b2_pos; omega) hcert
  exact hF.1 hmem

theorem ABS_R (T : TypeIIInput s F D)
    (SJ : ActualReturn g T.qS 1) (SK : ActualReturn g T.qS 2) :
    F = ((SK.factorization.coeff 0 : ℤ) - SJ.factorization.coeff 0 - 1) * g.m +
      (T.P0 + SK.factorization.coeff 1 - SJ.factorization.coeff 1 - 1) * g.n 0 +
      ((SK.factorization.coeff 2 : ℤ) + T.R) * g.n 1 +
      (T.T0 - 2 - SJ.factorization.coeff 3) * g.n 2 := by
  have hf := T.F_from_SK SK
  have hj := T.JR SJ
  linear_combination hf + hj

theorem impossible_level_right (T : TypeIIInput s F D)
    (hF : s.semigroup.IsFrobenius F)
    (SJ : ActualReturn g T.qS 1) (SK : ActualReturn g T.qS 2)
    (hlt : SJ.factorization.coeff 0 < SK.factorization.coeff 0) : False := by
  have hU := T.uniform_i_cap SJ SK
  have hC := T.C_cap hF SJ
  have hcert := T.ABS_R SJ SK
  have hmem := actual_of_coordinates g F
    ((SK.factorization.coeff 0 : ℤ) - SJ.factorization.coeff 0 - 1)
    (T.P0 + SK.factorization.coeff 1 - SJ.factorization.coeff 1 - 1)
    ((SK.factorization.coeff 2 : ℤ) + T.R)
    (T.T0 - 2 - SJ.factorization.coeff 3)
    (by omega)
    (by have := T.P0_sub_b0_pos; omega)
    (by have := T.R_eq; have := T.g1_pos; omega)
    (by have := T.T0_sub_b2_pos; omega) hcert
  exact hF.1 hmem

/-- Exhaustion of the three possible return-level orderings. -/
theorem level_order_impossible (T : TypeIIInput s F D)
    (hF : s.semigroup.IsFrobenius F)
    (SJ : ActualReturn g T.qS 1) (SK : ActualReturn g T.qS 2) : False := by
  rcases lt_trichotomy (SJ.factorization.coeff 0) (SK.factorization.coeff 0) with h | h | h
  · exact T.impossible_level_right hF SJ SK h
  · exact T.impossible_equal_levels hF SJ SK h
  · exact T.impossible_level_left hF SJ SK h

end TypeIIInput
end P21.Nonsymmetric
