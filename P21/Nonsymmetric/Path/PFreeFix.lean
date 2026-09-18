import P21.Nonsymmetric.Path.PFreeAbsorption

namespace P21.Nonsymmetric
namespace PathInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

namespace PFreeI

def Pc (P : PathInput s F D) (p : PFreeI P) (LJ : ActualReturn g P.qL 1) : ℤ :=
  LJ.factorization.coeff 1 + p.A0 P + 1
def Qc (P : PathInput s F D) (p : PFreeI P) : ℤ := P.R - p.H0 - 1
def Kc (P : PathInput s F D) (p : PFreeI P) (LJ : ActualReturn g P.qL 1) : ℤ :=
  2 * P.T - p.K - LJ.factorization.coeff 3 - 2

theorem comparison (P : PathInput s F D) (p : PFreeI P)
    (LJ : ActualReturn g P.qL 1) (hlvl : LJ.factorization.coeff 0 = 1) :
    p.Pc P LJ * g.n 0 = p.Qc P * g.n 1 + p.Kc P LJ * g.n 2 := by
  have hj := left_j_equation P LJ
  have hm := p.Mplus P
  have hq := P.qL_eq
  rw [hlvl] at hj
  norm_num at hj
  simp only [A0, B0, C0] at hm
  simp only [Pc, Qc, Kc, A0, B0, C0]
  linear_combination hj - hm + hq

theorem comparison_bounds (P : PathInput s F D) (p : PFreeI P)
    (LJ : ActualReturn g P.qL 1)
    (hA : (LJ.factorization.coeff 1 : ℤ) ≤ p.D0 P - 1)
    (hC : (LJ.factorization.coeff 3 : ℤ) ≤ D.b 2 - 1) :
    1 ≤ p.Pc P LJ ∧ p.Pc P LJ ≤ D.rho 0 ∧ P.T ≤ p.Kc P LJ := by
  have hAD := p.A0_add_D0 P
  have hK := p.K_lt
  have hT := P.T_eq
  simp only [Pc, Kc]
  constructor
  · have := p.A0_pos P
    omega
  constructor
  · omega
  · have halpha := P.alpha_pos
    omega

/-- P5-FIX-J, obtained only after the level-one pure-H comparison. -/
theorem fix_j (P : PathInput s F D) (hF : s.semigroup.IsFrobenius F)
    (p : PFreeI P) (LJ : ActualReturn g P.qL 1) :
    p.H0 = P.R - D.b 1 - 1 ∧
      (LJ.factorization.coeff 1 : ℤ) = p.D0 P - 1 ∧
      (LJ.factorization.coeff 3 : ℤ) = P.T - p.K - p.eta D P - 2 := by
  have hF0 := p.F0_pos P hF
  have caps := p.left_j_caps P hF hF0 LJ
  have hlvl := p.left_j_level_one P hF LJ
  have heq := p.comparison P LJ hlvl
  have hbds := p.comparison_bounds P LJ caps.2 caps.1
  have hn0 : 0 < g.n 0 := lt_trans s.m_pos (s.n_gt 0)
  have hn1 : 0 < g.n 1 := lt_trans s.m_pos (s.n_gt 1)
  have hn2 : 0 < g.n 2 := lt_trans s.m_pos (s.n_gt 2)
  have hTpos : 0 < P.T := by
    have ht := P.T_eq
    have hb := D.b_pos 2
    have ha := P.alpha_pos
    omega
  have hQK : p.Qc P = D.b 1 ∧ p.Kc P LJ = D.a 2 := by
    by_cases hQ : p.Qc P < 0
    · let rc : ℤ := -p.Qc P
      have hrc : 1 ≤ rc ∧ rc ≤ D.a 1 - 1 := by
        have hR := P.R_pos
        have hH := p.H0_lt
        have hHc : (p.H0 : ℤ) < D.a 1 := by exact_mod_cast hH
        have hQ' : P.R - (p.H0 : ℤ) - 1 < 0 := by simpa [Qc] using hQ
        dsimp [rc, Qc]
        omega
      have hkrel : p.Kc P LJ * g.n 2 = p.Pc P LJ * g.n 0 + rc * g.n 1 := by
        dsimp [rc]
        linarith [heq]
      have hkcrit := herzog_critical_le_int D
        (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)
        (p.Kc P LJ) (p.Pc P LJ) rc
        (by omega)
        (by omega) (by omega) hkrel
      have hsub : (p.Pc P LJ - D.b 0) * g.n 0 =
          ((D.a 1 : ℤ) - rc) * g.n 1 +
          (p.Kc P LJ - D.rho 2) * g.n 2 := by
        linear_combination -hkrel + D.relation_two
      by_cases hP : p.Pc P LJ ≤ D.b 0
      · nlinarith [hsub]
      · have hcrit := herzog_critical_le_int D
          (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)
          (p.Pc P LJ - D.b 0) ((D.a 1 : ℤ) - rc)
          (p.Kc P LJ - D.rho 2)
          (by omega) (by omega) (by omega) hsub
        have hrho := D.rho_eq 0
        have := D.b_pos 0
        omega
    · have hQ0 : 0 ≤ p.Qc P := by omega
      have hcrit := herzog_critical_le_int D
        (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)
        (p.Pc P LJ) (p.Qc P) (p.Kc P LJ)
        (by omega) hQ0 (by omega) heq
      have hPc : p.Pc P LJ = D.rho 0 := by omega
      rw [hPc] at heq
      have hzero : (p.Qc P - D.b 1) * g.n 1 +
          (p.Kc P LJ - D.a 2) * g.n 2 = 0 := by
        linear_combination D.relation_zero - heq
      by_cases hQl : p.Qc P < D.b 1
      · have hpure : ((D.b 1 : ℤ) - p.Qc P) * g.n 1 =
            (p.Kc P LJ - D.a 2) * g.n 2 := by linarith [hzero]
        have hkcoef : 0 < p.Kc P LJ - D.a 2 := by
          nlinarith [hpure]
        have hc := herzog_critical_le_int D
          (by decide : (1 : Fin 3) ≠ 0) (by decide : (1 : Fin 3) ≠ 2)
          ((D.b 1 : ℤ) - p.Qc P) 0 (p.Kc P LJ - D.a 2)
          (by omega) (by omega) hkcoef.le (by simpa using hpure)
        have hrho := D.rho_eq 1
        have := D.a_pos 1
        omega
      · by_cases hQg : D.b 1 < p.Qc P
        · have hpure : (p.Qc P - D.b 1) * g.n 1 =
              ((D.a 2 : ℤ) - p.Kc P LJ) * g.n 2 := by linarith [hzero]
          have hcoef : 0 < (D.a 2 : ℤ) - p.Kc P LJ := by
            nlinarith [hpure]
          have hc := herzog_critical_le_int D
            (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)
            ((D.a 2 : ℤ) - p.Kc P LJ) 0 (p.Qc P - D.b 1)
            hcoef (by omega) (by omega) (by linarith [hpure])
          have hrho := D.rho_eq 2
          have := D.b_pos 2
          omega
        · have hQeq : p.Qc P = D.b 1 := by omega
          have hKeq : p.Kc P LJ = D.a 2 := by
            rw [hQeq] at hzero
            norm_num at hzero
            rcases hzero with hk | hk
            · omega
            · exact False.elim ((ne_of_gt hn2) hk)
          exact ⟨hQeq, hKeq⟩
  have hAD := p.A0_add_D0 P
  have hT := P.T_eq
  have hPc : p.Pc P LJ = D.rho 0 := by
    have heq' := heq
    rw [hQK.1, hQK.2] at heq'
    have hz : (p.Pc P LJ - D.rho 0) * g.n 0 = 0 := by
      linear_combination heq' - D.relation_zero
    nlinarith
  simp only [Qc, Kc, eta] at hQK ⊢
  simp only [Pc] at hPc
  constructor
  · omega
  constructor
  · omega
  · have halpha : P.alpha = (D.a 2 : ℤ) - P.nu := rfl
    have heta : P.T - D.a 2 = -p.eta D P := by
      simp only [eta]
      omega
    omega

end PFreeI
end PathInput
end P21.Nonsymmetric
