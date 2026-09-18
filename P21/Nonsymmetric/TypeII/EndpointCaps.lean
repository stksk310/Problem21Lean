import P21.Nonsymmetric.TypeII.Returns

namespace P21.Nonsymmetric
namespace TypeIIInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

theorem C_certificate (T : TypeIIInput s F D) (SJ : ActualReturn g T.qS 1) :
    F = ((SJ.factorization.coeff 0 : ℤ) - 1) * g.m +
      ((D.b 0 : ℤ) - T.lambda + SJ.factorization.coeff 1) * g.n 0 +
      ((D.rho 1 : ℤ) - 1) * g.n 1 +
      ((SJ.factorization.coeff 3 : ℤ) - D.b 2) * g.n 2 := by
  have hs := T.sj_equation SJ
  have hw := T.qS_add_P0
  have e1 := D.relation_one
  simp only [W] at hw
  have hbase : F = ((SJ.factorization.coeff 0 : ℤ) - 1) * g.m +
      (T.P0 + SJ.factorization.coeff 1) * g.n 0 - g.n 1 +
      (SJ.factorization.coeff 3 : ℤ) * g.n 2 := by
    linear_combination -hw - hs
  have hP : (D.b 0 : ℤ) - T.lambda = T.P0 - D.a 0 := by
    have := T.P0_sub_b0
    omega
  rw [hP]
  linear_combination hbase - e1

theorem B_certificate (T : TypeIIInput s F D) (SK : ActualReturn g T.qS 2) :
    F = ((SK.factorization.coeff 0 : ℤ) - 1) * g.m +
      ((D.a 0 : ℤ) - T.lambda + SK.factorization.coeff 1) * g.n 0 +
      ((SK.factorization.coeff 2 : ℤ) - D.a 1) * g.n 1 +
      ((D.rho 2 : ℤ) - 1) * g.n 2 := by
  have hs := T.sk_equation SK
  have hw := T.qS_add_P0
  have e2 := D.relation_two
  simp only [W] at hw
  have hbase : F = ((SK.factorization.coeff 0 : ℤ) - 1) * g.m +
      (T.P0 + SK.factorization.coeff 1) * g.n 0 +
      (SK.factorization.coeff 2 : ℤ) * g.n 1 - g.n 2 := by
    linear_combination -hw - hs
  have hP : (D.a 0 : ℤ) - T.lambda = T.P0 - D.b 0 := by
    simpa using T.P0_sub_b0.symm
  rw [hP]
  linear_combination hbase - e2

/-- Endpoint C-cap, obtained by an actual factorization of `F` if violated. -/
theorem C_cap (T : TypeIIInput s F D) (hF : s.semigroup.IsFrobenius F)
    (SJ : ActualReturn g T.qS 1) :
    (SJ.factorization.coeff 3 : ℤ) ≤ D.b 2 - 1 := by
  by_contra hn
  have hcert := T.C_certificate SJ
  have hmem := actual_of_coordinates g F
    ((SJ.factorization.coeff 0 : ℤ) - 1)
    ((D.b 0 : ℤ) - T.lambda + SJ.factorization.coeff 1)
    ((D.rho 1 : ℤ) - 1)
    ((SJ.factorization.coeff 3 : ℤ) - D.b 2)
    (by have := SJ.level_pos; omega)
    (by have := T.lambda_range.2.2; omega)
    (by have := D.rho_pos 1; omega)
    (by omega) hcert
  exact hF.1 hmem

/-- Endpoint B-cap, obtained by an actual factorization of `F` if violated. -/
theorem B_cap (T : TypeIIInput s F D) (hF : s.semigroup.IsFrobenius F)
    (SK : ActualReturn g T.qS 2) :
    (SK.factorization.coeff 2 : ℤ) ≤ D.a 1 - 1 := by
  by_contra hn
  have hcert := T.B_certificate SK
  have hmem := actual_of_coordinates g F
    ((SK.factorization.coeff 0 : ℤ) - 1)
    ((D.a 0 : ℤ) - T.lambda + SK.factorization.coeff 1)
    ((SK.factorization.coeff 2 : ℤ) - D.a 1)
    ((D.rho 2 : ℤ) - 1)
    (by have := SK.level_pos; omega)
    (by have := T.lambda_range.2.1; omega)
    (by omega)
    (by have := D.rho_pos 2; omega) hcert
  exact hF.1 hmem

end TypeIIInput
end P21.Nonsymmetric
