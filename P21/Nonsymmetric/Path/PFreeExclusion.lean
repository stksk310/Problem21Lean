import P21.Nonsymmetric.Path.PFreeFix

namespace P21.Nonsymmetric
namespace PathInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

namespace PFreeI

theorem left_k_fabs (P : PathInput s F D) (p : PFreeI P)
    (LK : ActualReturn g P.qL 2) :
    F = ((LK.factorization.coeff 0 : ℤ) - 2) * g.m +
      (P.P0 + LK.factorization.coeff 1 - p.D0 P) * g.n 0 +
      ((LK.factorization.coeff 2 : ℤ) + p.E0 D) * g.n 1 +
      (p.F0 D P - 1) * g.n 2 := by
  have hk := left_k_equation P LK
  have hm := p.Mminus P
  have hc := P.cL
  change F + g.m - P.qL = P.P0 * g.n 0 at hc
  linear_combination hc - hk + hm

theorem left_k_level_one (P : PathInput s F D) (hF : s.semigroup.IsFrobenius F)
    (p : PFreeI P) (LK : ActualReturn g P.qL 2) :
    LK.factorization.coeff 0 = 1 := by
  have hF0 := p.F0_pos P hF
  by_contra hn
  have hlvl : 2 ≤ LK.factorization.coeff 0 := by
    have := LK.level_pos
    omega
  have hcert := p.left_k_fabs P LK
  have hcoord : P.P0 + (LK.factorization.coeff 1 : ℤ) - p.D0 P =
      (LK.factorization.coeff 1 : ℤ) + p.Y + 1 := by simp [D0]; ring
  have hmem := gamma_of_coordinates g F
    ((LK.factorization.coeff 0 : ℤ) - 2)
    (P.P0 + LK.factorization.coeff 1 - p.D0 P)
    ((LK.factorization.coeff 2 : ℤ) + p.E0 D)
    (p.F0 D P - 1)
    (by omega) (by rw [hcoord]; omega)
    (by have := D.b_pos 1; simp only [E0]; omega) (by omega) hcert
  exact hF.1 hmem

theorem unit_eq (P : PathInput s F D) (p : PFreeI P)
    (LJ : ActualReturn g P.qL 1) (LK : ActualReturn g P.qL 2)
    (hj : LJ.factorization.coeff 0 = 1) (hk : LK.factorization.coeff 0 = 1) :
    ((LK.factorization.coeff 1 : ℤ) - LJ.factorization.coeff 1) * g.n 0 +
      ((LK.factorization.coeff 2 : ℤ) + 1) * g.n 1 =
      ((LJ.factorization.coeff 3 : ℤ) + 1) * g.n 2 := by
  have ej := left_j_equation P LJ
  have ek := left_k_equation P LK
  rw [hj] at ej
  rw [hk] at ek
  norm_num at ej ek
  linear_combination ek - ej

/-- P5-PIN: the two actual unit returns are pinned to one coefficient point. -/
theorem pin (P : PathInput s F D) (hF : s.semigroup.IsFrobenius F)
    (p : PFreeI P) (LJ : ActualReturn g P.qL 1) (LK : ActualReturn g P.qL 2) :
    (LK.factorization.coeff 1 : ℤ) = LJ.factorization.coeff 1 - D.a 0 ∧
      (LK.factorization.coeff 2 : ℤ) = D.rho 1 - 1 ∧
      (LJ.factorization.coeff 3 : ℤ) = D.b 2 - 1 := by
  have hj := p.left_j_level_one P hF LJ
  have hk := p.left_k_level_one P hF LK
  have caps := p.left_j_caps P hF (p.F0_pos P hF) LJ
  have fix := p.fix_j P hF LJ
  have heq := p.unit_eq P LJ LK hj hk
  have hn0 : 0 < g.n 0 := lt_trans s.m_pos (s.n_gt 0)
  have hn1 : 0 < g.n 1 := lt_trans s.m_pos (s.n_gt 1)
  have hn2 : 0 < g.n 2 := lt_trans s.m_pos (s.n_gt 2)
  have hAupper : (LJ.factorization.coeff 1 : ℤ) < D.rho 0 := by
    have hl := P.lambda_range.1
    rw [fix.2.1]
    simp only [D0, P0]
    omega
  have hDA : (LK.factorization.coeff 1 : ℤ) < LJ.factorization.coeff 1 := by
    by_contra hn
    have hc := herzog_critical_le_int D
      (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)
      ((LJ.factorization.coeff 3 : ℤ) + 1)
      ((LK.factorization.coeff 1 : ℤ) - LJ.factorization.coeff 1)
      ((LK.factorization.coeff 2 : ℤ) + 1)
      (by omega) (by omega) (by omega) (by linarith [heq])
    have hr := D.rho_eq 2
    have := D.a_pos 2
    omega
  have hjcrit := herzog_critical_le_int D
    (by decide : (1 : Fin 3) ≠ 0) (by decide : (1 : Fin 3) ≠ 2)
    ((LK.factorization.coeff 2 : ℤ) + 1)
    ((LJ.factorization.coeff 1 : ℤ) - LK.factorization.coeff 1)
    ((LJ.factorization.coeff 3 : ℤ) + 1)
    (by omega) (by omega) (by omega) (by linarith [heq])
  have hsub : ((LK.factorization.coeff 2 : ℤ) + 1 - D.rho 1) * g.n 1 =
      ((LJ.factorization.coeff 1 : ℤ) - LK.factorization.coeff 1 - D.a 0) * g.n 0 +
      ((LJ.factorization.coeff 3 : ℤ) + 1 - D.b 2) * g.n 2 := by
    linear_combination heq - D.relation_one
  let x : ℤ := LJ.factorization.coeff 1 - LK.factorization.coeff 1 - D.a 0
  by_cases hx : 0 < x
  · have hpure : x * g.n 0 =
        ((LK.factorization.coeff 2 : ℤ) + 1 - D.rho 1) * g.n 1 +
        ((D.b 2 : ℤ) - LJ.factorization.coeff 3 - 1) * g.n 2 := by
      linarith [hsub]
    have hc := herzog_critical_le_int D
      (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)
      x ((LK.factorization.coeff 2 : ℤ) + 1 - D.rho 1)
      ((D.b 2 : ℤ) - LJ.factorization.coeff 3 - 1)
      hx (by omega) (by omega) hpure
    simp only [x] at hc
    omega
  · have hleft : 0 ≤ (LK.factorization.coeff 2 : ℤ) + 1 - D.rho 1 := by omega
    have hx0 : x ≤ 0 := by omega
    have hz : (LJ.factorization.coeff 3 : ℤ) + 1 - D.b 2 ≤ 0 := by omega
    have hxz : x = 0 := by
      dsimp [x] at hx0 ⊢
      by_contra hn
      have hxneg : (LJ.factorization.coeff 1 : ℤ) - LK.factorization.coeff 1 - D.a 0 < 0 := by omega
      have hxp := mul_neg_of_neg_of_pos hxneg hn0
      have hzp := mul_nonpos_of_nonpos_of_nonneg hz hn2.le
      have hlp := mul_nonneg hleft hn1.le
      nlinarith [hsub]
    have hxz' : (LJ.factorization.coeff 1 : ℤ) - LK.factorization.coeff 1 - D.a 0 = 0 := by
      simpa [x] using hxz
    have hyz : (LK.factorization.coeff 2 : ℤ) + 1 - D.rho 1 = 0 := by
      rw [hxz'] at hsub
      by_contra hn
      have hyp : 0 < (LK.factorization.coeff 2 : ℤ) + 1 - D.rho 1 := by omega
      have hlp := mul_pos hyp hn1
      have hrp := mul_nonpos_of_nonpos_of_nonneg hz hn2.le
      nlinarith [hsub]
    have hzz : (LJ.factorization.coeff 3 : ℤ) + 1 - D.b 2 = 0 := by
      rw [hxz', hyz] at hsub
      norm_num at hsub
      rcases hsub with hh | hh
      · exact hh
      · exact False.elim ((ne_of_gt hn2) hh)
    exact ⟨by omega, by omega, by omega⟩

theorem roots (P : PathInput s F D) (hF : s.semigroup.IsFrobenius F)
    (p : PFreeI P) (LJ : ActualReturn g P.qL 1) (LK : ActualReturn g P.qL 2) :
    p.F0 D P = P.alpha ∧ p.C0 P = P.nu ∧
      g.m = p.A0 P * g.n 0 + (p.H0 + 1) * g.n 1 - P.nu * g.n 2 ∧
      g.m = -((LK.factorization.coeff 1 : ℤ) + 1) * g.n 0 -
        (D.rho 1 - P.R) * g.n 1 + P.T * g.n 2 := by
  have fix := p.fix_j P hF LJ
  have pin := p.pin P hF LJ LK
  have hk := p.left_k_level_one P hF LK
  have ek := left_k_equation P LK
  rw [hk] at ek
  norm_num at ek
  have hq := P.qL_eq
  have hF0 : p.F0 D P = P.alpha := by
    have hT := P.T_eq
    have he := fix.2.2
    have hp := pin.2.2
    rw [hp] at he
    simp only [F0]
    omega
  have hC0 : p.C0 P = P.nu := by
    have hsum := p.C0_add_F0 P
    have ha : P.alpha = (D.a 2 : ℤ) - P.nu := rfl
    omega
  have hp := p.Mplus P
  simp only [B0] at hp
  rw [hC0] at hp
  refine ⟨hF0, hC0, hp, ?_⟩
  rw [pin.2.1] at ek
  linear_combination ek + hq

theorem impossible (P : PathInput s F D) (hF : s.semigroup.IsFrobenius F)
    (p : PFreeI P) : False := by
  obtain ⟨LJ⟩ := P.qL_n1_return
  obtain ⟨LK⟩ := P.qL_n2_return
  have pin := p.pin P hF LJ LK
  have roots := p.roots P hF LJ LK
  obtain ⟨RJ⟩ := P.qR_n1_return
  have hr := right_j_equation P RJ
  have hc := P.cR
  change F + g.m - P.qR = P.T * g.n 2 at hc
  by_cases hlevel : 2 ≤ RJ.factorization.coeff 0
  · have hcert : F = ((RJ.factorization.coeff 0 : ℤ) - 2) * g.m +
        ((RJ.factorization.coeff 1 : ℤ) + p.A0 P) * g.n 0 +
        (p.H0 : ℤ) * g.n 1 +
        (P.T + RJ.factorization.coeff 3 - P.nu) * g.n 2 := by
      linear_combination hc - hr + roots.2.2.1
    have hsurplus : 1 ≤ P.T - P.nu := by
      have hK : 0 ≤ (p.K : ℤ) := by omega
      have hF0 := roots.1
      simp only [F0, eta] at hF0
      have ha : P.alpha = (D.a 2 : ℤ) - P.nu := rfl
      have hT := P.T_eq
      omega
    have hmem := gamma_of_coordinates g F
      ((RJ.factorization.coeff 0 : ℤ) - 2)
      ((RJ.factorization.coeff 1 : ℤ) + p.A0 P) p.H0
      (P.T + RJ.factorization.coeff 3 - P.nu)
      (by omega) (by have := p.A0_pos P; omega) (by omega) (by omega) hcert
    exact hF.1 hmem
  · have hrlevel : RJ.factorization.coeff 0 = 1 := by
      have := RJ.level_pos
      omega
    rw [hrlevel] at hr
    norm_num at hr
    have hqactual : (RJ.factorization.coeff 3 : ℤ) ≤ P.nu - 1 := by
      by_contra hn
      have hq : P.qR =
          ((RJ.factorization.coeff 1 : ℤ) + p.A0 P) * g.n 0 +
          (p.H0 : ℤ) * g.n 1 +
          ((RJ.factorization.coeff 3 : ℤ) - P.nu) * g.n 2 := by
        linear_combination -hr + roots.2.2.1
      have hmem := gamma_of_coordinates g P.qR 0
        ((RJ.factorization.coeff 1 : ℤ) + p.A0 P) p.H0
        ((RJ.factorization.coeff 3 : ℤ) - P.nu)
        (by omega) (by have := p.A0_pos P; omega) (by omega) (by omega)
        (by simpa using hq)
      exact (P.actual 3).1.1 hmem
    have hlast : (P.P0 + LK.factorization.coeff 1 + D.a 0 - RJ.factorization.coeff 1) * g.n 0 =
        (P.alpha + RJ.factorization.coeff 3 + 1) * g.n 2 := by
      have hq := P.qR_eq
      have rt := roots.2.2.2
      have hRmu : P.R + (D.rho 1 - P.R) = D.rho 1 := by ring
      have hT := P.T_eq
      linear_combination -hr + rt - hq - D.relation_one + g.n 2 * hT
    have hcoef : 1 ≤ P.alpha + (RJ.factorization.coeff 3 : ℤ) + 1 ∧
        P.alpha + (RJ.factorization.coeff 3 : ℤ) + 1 < D.rho 2 := by
      have ha : P.alpha = (D.a 2 : ℤ) - P.nu := rfl
      have hrho := D.rho_eq 2
      have hrho' : (D.rho 2 : ℤ) = D.a 2 + D.b 2 := by exact_mod_cast hrho
      have := D.b_pos 2
      constructor
      · have := P.alpha_pos
        omega
      · rw [ha]
        omega
    have hleftpos : 0 < P.P0 + (LK.factorization.coeff 1 : ℤ) + D.a 0 -
        RJ.factorization.coeff 1 := by
      by_contra hn
      have hn0 : 0 < g.n 0 := lt_trans s.m_pos (s.n_gt 0)
      have hn2 : 0 < g.n 2 := lt_trans s.m_pos (s.n_gt 2)
      nlinarith [hlast]
    have hcrit := herzog_critical_le_int D
      (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)
      (P.alpha + RJ.factorization.coeff 3 + 1)
      (P.P0 + LK.factorization.coeff 1 + D.a 0 - RJ.factorization.coeff 1) 0
      hcoef.1 hleftpos.le (by omega) (by linarith [hlast])
    omega

end PFreeI
end PathInput
end P21.Nonsymmetric
