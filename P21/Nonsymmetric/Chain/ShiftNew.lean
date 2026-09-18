import P21.Nonsymmetric.Chain.ReturnLevels

namespace P21.Nonsymmetric
namespace ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable (K : ChainCore s F D) (E : K.Returns)

/-- SHIFT-NEW: the exact replacement of `h` root copies by one `R_j` packet. -/
theorem shift_new :
    K.h*g.m + K.tau0*g.n 1 =
      ((D.a 0 : ℤ)-K.h*K.d)*g.n 0 +
      ((D.b 2 : ℤ)+K.h*K.Croot)*g.n 2 := by
  have hr := K.root
  have hj := D.relation_one
  simp [tau0]
  linear_combination K.h*hr + hj

/-- The target of SHIFT-NEW is coefficientwise nonnegative; its `n_i`
coefficient is exactly `r+delta`, hence positive. -/
theorem shift_new_coefficients :
    (D.a 0 : ℤ)-K.h*K.d = K.r+K.chain.delta ∧
      0 < (D.a 0 : ℤ)-K.h*K.d ∧
      0 ≤ (D.b 2 : ℤ)+K.h*K.Croot := by
  have Eu := K.euclidean
  have ha := K.chain.a0_exact
  have hdelta := K.chain.scalar_ranges.1
  have hb2 : (1 : ℤ) ≤ D.b 2 := by exact_mod_cast D.b_pos 2
  have hh : 0 ≤ K.h := by have := Eu.h_pos; omega
  have hC : 1 ≤ K.Croot := le_trans K.chain.scalar_ranges.2.2.2 K.C_lower
  have hx : (D.a 0 : ℤ)-K.h*K.d = K.r+K.chain.delta := by
    nlinarith [Eu.lambda_eq]
  constructor
  · exact hx
  constructor
  · rw [hx]
    have hr := Eu.r_range.1
    omega
  · nlinarith [mul_nonneg hh (show 0 ≤ K.Croot by omega)]

private theorem gap_of_four {q l x y z : ℤ} (hq : q ∉ g.Gamma)
    (he : q = l*g.m+x*g.n 0+y*g.n 1+z*g.n 2)
    (hl : 0 ≤ l) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : False := by
  apply hq
  rw [he]
  exact four_mem l x y z hl hx hy hz

/-- Applying SHIFT-NEW inside the named actual `EA` return forces the packet cap. -/
theorem Uj_tau_cap : E.Uj ≤ K.tau0-1 := by
  by_contra hn
  have levels := K.I_levels E
  have nonneg := E.coeff_nonneg
  have coeff := K.shift_new_coefficients
  have he := E.EA_eq
  have hs := K.shift_new
  have hq : K.chain.qA ∉ g.Gamma := K.chain.qA_actual.1.1
  have eq : K.chain.qA = (E.Li-K.h)*g.m +
      ((D.a 0 : ℤ)-K.h*K.d-1)*g.n 0 +
      (E.Uj-K.tau0)*g.n 1 +
      (E.Uk+(D.b 2 : ℤ)+K.h*K.Croot)*g.n 2 := by
    linear_combination he + hs
  exact gap_of_four hq eq (by omega) (by omega) (by omega) (by omega)

/-- Applying SHIFT-NEW inside the named actual `EB` return forces the packet cap. -/
theorem Vj_tau_cap : E.Vj ≤ K.tau0-1 := by
  by_contra hn
  have levels := K.I_levels E
  have nonneg := E.coeff_nonneg
  have coeff := K.shift_new_coefficients
  have he := E.EB_eq
  have hs := K.shift_new
  have hq : K.chain.qB ∉ g.Gamma := K.chain.qB_actual.1.1
  have eq : K.chain.qB = (E.Lb-K.h)*g.m +
      ((D.a 0 : ℤ)-K.h*K.d-1)*g.n 0 +
      (E.Vj-K.tau0)*g.n 1 +
      (E.Vk+(D.b 2 : ℤ)+K.h*K.Croot)*g.n 2 := by
    linear_combination he + hs
  exact gap_of_four hq eq (by omega) (by omega) (by omega) (by omega)

theorem tau_caps : E.Uj ≤ K.tau0-1 ∧ E.Vj ≤ K.tau0-1 :=
  ⟨K.Uj_tau_cap E, K.Vj_tau_cap E⟩

/-- FK-STRONG, valid only in the strict `Croot > alpha` region. -/
theorem FK_strong (hF : s.semigroup.IsFrobenius F) (C : K.Caps E)
    (hJ : K.J0 < 0) (hstrict : K.chain.alpha < K.Croot) :
    0 ≤ E.Bk ∧ E.Bk ≤ K.tau0-K.chain.R-1 ∧
      K.chain.R+1 ≤ K.tau0 := by
  have nonneg := E.coeff_nonneg
  have hBk := nonneg.2.2.2.2.2.2.2
  have level := K.Lk_strict_level E C hJ hstrict
  have Eu := K.euclidean
  have coeff := K.shift_new_coefficients
  have hb2 : (1 : ℤ) ≤ D.b 2 := by exact_mod_cast D.b_pos 2
  have hC : 1 ≤ K.Croot := le_trans K.chain.scalar_ranges.2.2.2 K.C_lower
  have hR : 1 ≤ K.chain.R := by
    rw [K.chain.R_exact]
    have := D.a_pos 1
    have := K.chain.scalar_ranges.2.2.1
    omega
  have hbound : E.Bk+K.chain.R < K.tau0 := by
    by_contra hn
    have he := E.Qk_eq
    have hc := K.chain.cK_exact
    simp [complement, W] at hc
    have hs := K.shift_new
    have base : F+g.n 2 = (E.Lk-1)*g.m +
        (E.Ak+K.chain.beta)*g.n 0 +
        (E.Bk+K.chain.R)*g.n 1 := by
      linear_combination he + hc
    have eq : F = (E.Lk-K.h-1)*g.m +
        (E.Ak+K.chain.beta+(D.a 0 : ℤ)-K.h*K.d)*g.n 0 +
        (E.Bk+K.chain.R-K.tau0)*g.n 1 +
        ((D.b 2 : ℤ)+K.h*K.Croot-1)*g.n 2 := by
      linear_combination base + hs - g.n 2
    have hm := four_mem (g:=g) (E.Lk-K.h-1)
      (E.Ak+K.chain.beta+(D.a 0 : ℤ)-K.h*K.d)
      (E.Bk+K.chain.R-K.tau0)
      ((D.b 2 : ℤ)+K.h*K.Croot-1)
      (by simp [q0] at level; omega)
      (by have := K.chain.scalar_ranges.2.1; omega)
      (by omega)
      (by
        have hh : 0 ≤ K.h := by have := Eu.h_pos; omega
        nlinarith [mul_nonneg hh (show 0 ≤ K.Croot by omega)])
    apply hF.1
    change F ∈ g.Gamma
    rw [eq]
    exact hm
  exact ⟨hBk, by omega, by omega⟩

end ChainCore
end P21.Nonsymmetric
