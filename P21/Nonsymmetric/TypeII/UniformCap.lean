import P21.Nonsymmetric.TypeII.EndpointCaps

namespace P21.Nonsymmetric
namespace TypeIIInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

theorem fA_from_SJ (T : TypeIIInput s F D) (SJ : ActualReturn g T.qS 1) :
    D.fA = (SJ.factorization.coeff 0 : ℤ) * g.m +
      (SJ.factorization.coeff 1 : ℤ) * g.n 0 +
      (T.mu - 1) * g.n 1 +
      ((SJ.factorization.coeff 3 : ℤ) + T.eta) * g.n 2 := by
  have ha := T.anchor_A
  have hs := T.sj_equation SJ
  linear_combination ha - hs

theorem fA_from_SK (T : TypeIIInput s F D) (SK : ActualReturn g T.qS 2) :
    D.fA = (SK.factorization.coeff 0 : ℤ) * g.m +
      (SK.factorization.coeff 1 : ℤ) * g.n 0 +
      ((SK.factorization.coeff 2 : ℤ) + T.mu) * g.n 1 +
      (T.eta - 1) * g.n 2 := by
  have ha := T.anchor_A
  have hs := T.sk_equation SK
  linear_combination ha - hs

theorem Ak_from_SJ (T : TypeIIInput s F D) (SJ : ActualReturn g T.qS 1) :
    D.fA - T.nu * g.n 2 = (SJ.factorization.coeff 0 : ℤ) * g.m +
      ((SJ.factorization.coeff 1 : ℤ) - D.b 0) * g.n 0 +
      (T.mu - D.a 1 - 1) * g.n 1 +
      ((SJ.factorization.coeff 3 : ℤ) + D.a 2) * g.n 2 := by
  have hf := T.fA_from_SJ SJ
  have e2 := D.relation_two
  have hr2 : (D.rho 2 : ℤ) = D.a 2 + D.b 2 := by exact_mod_cast D.rho_eq 2
  simp only [eta] at hf
  linear_combination hf - e2 + g.n 2 * hr2

theorem Ak_from_SK (T : TypeIIInput s F D) (SK : ActualReturn g T.qS 2) :
    D.fA - T.nu * g.n 2 = (SK.factorization.coeff 0 : ℤ) * g.m +
      ((SK.factorization.coeff 1 : ℤ) - D.b 0) * g.n 0 +
      ((SK.factorization.coeff 2 : ℤ) + T.mu - D.a 1) * g.n 1 +
      ((D.a 2 : ℤ) - 1) * g.n 2 := by
  have hf := T.fA_from_SK SK
  have e2 := D.relation_two
  have hr2 : (D.rho 2 : ℤ) = D.a 2 + D.b 2 := by exact_mod_cast D.rho_eq 2
  simp only [eta] at hf
  linear_combination hf - e2 + g.n 2 * hr2

theorem cap_of_eta_pos (T : TypeIIInput s F D)
    (SJ : ActualReturn g T.qS 1) (SK : ActualReturn g T.qS 2) (heta : 1 ≤ T.eta) :
    (SJ.factorization.coeff 1 : ℤ) ≤ T.lambda - 1 ∧
      (SK.factorization.coeff 1 : ℤ) ≤ T.lambda - 1 := by
  constructor
  · by_contra hn
    have hf := T.fA_from_SJ SJ
    have hq : D.fA - T.lambda * g.n 0 =
        (SJ.factorization.coeff 0 : ℤ) * g.m +
        ((SJ.factorization.coeff 1 : ℤ) - T.lambda) * g.n 0 +
        (T.mu - 1) * g.n 1 +
        ((SJ.factorization.coeff 3 : ℤ) + T.eta) * g.n 2 := by
      linear_combination hf
    have hmem := actual_of_coordinates g (D.fA - T.lambda * g.n 0)
      (SJ.factorization.coeff 0 : ℤ)
      ((SJ.factorization.coeff 1 : ℤ) - T.lambda)
      (T.mu - 1) ((SJ.factorization.coeff 3 : ℤ) + T.eta)
      (by omega) (by omega) (by have := T.mu_range.1; omega) (by omega) hq
    exact (T.actual 1).1.1 hmem
  · by_contra hn
    have hf := T.fA_from_SK SK
    have hq : D.fA - T.lambda * g.n 0 =
        (SK.factorization.coeff 0 : ℤ) * g.m +
        ((SK.factorization.coeff 1 : ℤ) - T.lambda) * g.n 0 +
        ((SK.factorization.coeff 2 : ℤ) + T.mu) * g.n 1 +
        (T.eta - 1) * g.n 2 := by
      linear_combination hf
    have hmem := actual_of_coordinates g (D.fA - T.lambda * g.n 0)
      (SK.factorization.coeff 0 : ℤ)
      ((SK.factorization.coeff 1 : ℤ) - T.lambda)
      ((SK.factorization.coeff 2 : ℤ) + T.mu) (T.eta - 1)
      (by omega) (by omega) (by have := T.mu_range.1; omega) (by omega) hq
    exact (T.actual 1).1.1 hmem

theorem cap_of_theta_pos (T : TypeIIInput s F D)
    (SJ : ActualReturn g T.qS 1) (SK : ActualReturn g T.qS 2) (htheta : 1 ≤ T.theta) :
    (SJ.factorization.coeff 1 : ℤ) ≤ D.b 0 - 1 ∧
      (SK.factorization.coeff 1 : ℤ) ≤ D.b 0 - 1 := by
  have hmu : 1 ≤ T.mu - D.a 1 := by simpa [theta] using htheta
  constructor
  · by_contra hn
    have hq := T.Ak_from_SJ SJ
    have hmem := actual_of_coordinates g (D.fA - T.nu * g.n 2)
      (SJ.factorization.coeff 0 : ℤ)
      ((SJ.factorization.coeff 1 : ℤ) - D.b 0)
      (T.mu - D.a 1 - 1)
      ((SJ.factorization.coeff 3 : ℤ) + D.a 2)
      (by omega) (by omega) (by omega) (by have := D.a_pos 2; omega) hq
    exact (T.actual 3).1.1 hmem
  · by_contra hn
    have hq := T.Ak_from_SK SK
    have hmem := actual_of_coordinates g (D.fA - T.nu * g.n 2)
      (SK.factorization.coeff 0 : ℤ)
      ((SK.factorization.coeff 1 : ℤ) - D.b 0)
      ((SK.factorization.coeff 2 : ℤ) + T.mu - D.a 1)
      ((D.a 2 : ℤ) - 1)
      (by omega) (by omega) (by omega) (by have := D.a_pos 2; omega) hq
    exact (T.actual 3).1.1 hmem

theorem cap_zero_zero (T : TypeIIInput s F D)
    (SJ : ActualReturn g T.qS 1) (SK : ActualReturn g T.qS 2)
    (heta : T.eta = 0) (htheta : T.theta = 0) :
    (SJ.factorization.coeff 1 : ℤ) ≤ D.b 0 - 1 ∧
      (SK.factorization.coeff 1 : ℤ) ≤ D.b 0 - 1 := by
  constructor
  · have hlambda : T.lambda ≤ D.b 0 := T.lambda_range.2.2
    by_contra hn
    have hf := T.fA_from_SJ SJ
    have hq : D.fA - T.lambda * g.n 0 =
        (SJ.factorization.coeff 0 : ℤ) * g.m +
        ((SJ.factorization.coeff 1 : ℤ) - T.lambda) * g.n 0 +
        (T.mu - 1) * g.n 1 +
        (SJ.factorization.coeff 3 : ℤ) * g.n 2 := by
      rw [heta] at hf
      norm_num at hf
      linear_combination hf
    have hmem := actual_of_coordinates g (D.fA - T.lambda * g.n 0)
      (SJ.factorization.coeff 0 : ℤ)
      ((SJ.factorization.coeff 1 : ℤ) - T.lambda)
      (T.mu - 1) (SJ.factorization.coeff 3 : ℤ)
      (by omega) (by omega) (by have := T.mu_range.1; omega) (by omega) hq
    exact (T.actual 1).1.1 hmem
  · have hmu : T.mu - D.a 1 = 0 := by simpa [theta] using htheta
    by_contra hn
    have hq := T.Ak_from_SK SK
    have hmem := actual_of_coordinates g (D.fA - T.nu * g.n 2)
      (SK.factorization.coeff 0 : ℤ)
      ((SK.factorization.coeff 1 : ℤ) - D.b 0)
      ((SK.factorization.coeff 2 : ℤ) + T.mu - D.a 1)
      ((D.a 2 : ℤ) - 1)
      (by omega) (by omega) (by omega) (by have := D.a_pos 2; omega) hq
    exact (T.actual 3).1.1 hmem

theorem impossible_eta_zero_theta_neg (T : TypeIIInput s F D)
    (heta : T.eta = 0) (htheta : T.theta ≤ -1) : False := by
  have hq := T.qS_eq
  have e0 := D.relation_zero
  have hr1 : (D.rho 1 : ℤ) = D.a 1 + D.b 1 := by exact_mod_cast D.rho_eq 1
  have hr2 : (D.rho 2 : ℤ) = D.a 2 + D.b 2 := by exact_mod_cast D.rho_eq 2
  have he : T.qS + g.n 2 = ((D.rho 0 : ℤ) - 1) * g.n 0 +
      ((D.a 1 : ℤ) - T.mu - 1) * g.n 1 + 0 * g.n 2 := by
    simp only [R, T0, eta, theta] at hq heta htheta
    linear_combination hq - e0 + g.n 1 * hr1 + g.n 2 * hr2 - g.n 2 * heta
  have hm := tail_of_coordinates g (T.qS + g.n 2)
    ((D.rho 0 : ℤ) - 1) ((D.a 1 : ℤ) - T.mu - 1) 0
    (by have := D.rho_pos 0; omega) (by simp only [theta] at htheta; omega) (by omega) he
  have hmissing : (2 : Fin 3) ∉ g.SH T.qS := by rw [T.singleton]; decide
  exact hmissing (by simpa [Generators.SH] using hm)

theorem impossible_theta_zero_eta_neg (T : TypeIIInput s F D)
    (htheta : T.theta = 0) (heta : T.eta ≤ -1) : False := by
  have hq := T.qS_eq
  have e0 := D.relation_zero
  have hr1 : (D.rho 1 : ℤ) = D.a 1 + D.b 1 := by exact_mod_cast D.rho_eq 1
  have hr2 : (D.rho 2 : ℤ) = D.a 2 + D.b 2 := by exact_mod_cast D.rho_eq 2
  have he : T.qS + g.n 1 = ((D.rho 0 : ℤ) - 1) * g.n 0 +
      0 * g.n 1 + ((D.b 2 : ℤ) - T.nu - 1) * g.n 2 := by
    simp only [R, T0, eta, theta] at hq heta htheta
    linear_combination hq - e0 + g.n 1 * hr1 + g.n 2 * hr2 - g.n 1 * htheta
  have hm := tail_of_coordinates g (T.qS + g.n 1)
    ((D.rho 0 : ℤ) - 1) 0 ((D.b 2 : ℤ) - T.nu - 1)
    (by have := D.rho_pos 0; omega) (by omega) (by simp only [eta] at heta; omega) he
  have hmissing : (1 : Fin 3) ∉ g.SH T.qS := by rw [T.singleton]; decide
  exact hmissing (by simpa [Generators.SH] using hm)

theorem impossible_eta_theta_neg (T : TypeIIInput s F D)
    (heta : T.eta ≤ -1) (htheta : T.theta ≤ -1) : False := by
  have hq := T.qS_eq
  have e0 := D.relation_zero
  have hr1 : (D.rho 1 : ℤ) = D.a 1 + D.b 1 := by exact_mod_cast D.rho_eq 1
  have hr2 : (D.rho 2 : ℤ) = D.a 2 + D.b 2 := by exact_mod_cast D.rho_eq 2
  have he : T.qS = ((D.rho 0 : ℤ) - 1) * g.n 0 +
      (-T.theta - 1) * g.n 1 + (-T.eta - 1) * g.n 2 := by
    simp only [R, T0, theta, eta] at hq ⊢
    linear_combination hq - e0 + g.n 1 * hr1 + g.n 2 * hr2
  have hm := tail_of_coordinates g T.qS
    ((D.rho 0 : ℤ) - 1) (-T.theta - 1) (-T.eta - 1)
    (by have := D.rho_pos 0; omega) (by omega) (by omega) he
  exact (T.actual 0).1.1 (g.h_subset_gamma hm)

/-- Uniform cap on the two direction-0 coefficients, with all integer sign
regions treated explicitly. -/
theorem uniform_i_cap (T : TypeIIInput s F D)
    (SJ : ActualReturn g T.qS 1) (SK : ActualReturn g T.qS 2) :
    (SJ.factorization.coeff 1 : ℤ) ≤ D.b 0 - 1 ∧
      (SK.factorization.coeff 1 : ℤ) ≤ D.b 0 - 1 := by
  by_cases hepos : 1 ≤ T.eta
  · have h := T.cap_of_eta_pos SJ SK hepos
    have hl := T.lambda_range.2.2
    omega
  · have henon : T.eta ≤ 0 := by omega
    by_cases htpos : 1 ≤ T.theta
    · exact T.cap_of_theta_pos SJ SK htpos
    · have htnon : T.theta ≤ 0 := by omega
      by_cases he0 : T.eta = 0
      · by_cases ht0 : T.theta = 0
        · exact T.cap_zero_zero SJ SK he0 ht0
        · exact (T.impossible_eta_zero_theta_neg he0 (by omega)).elim
      · by_cases ht0 : T.theta = 0
        · exact (T.impossible_theta_zero_eta_neg ht0 (by omega)).elim
        · exact (T.impossible_eta_theta_neg (by omega) (by omega)).elim

end TypeIIInput
end P21.Nonsymmetric
