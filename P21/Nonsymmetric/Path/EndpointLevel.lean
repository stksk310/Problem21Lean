import P21.Nonsymmetric.Path.RootNormalization

namespace P21.Nonsymmetric
namespace PathInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

namespace NormalizedRoot

theorem lj_equation (P : PathInput s F D) (LJ : ActualReturn g P.qL 1) :
    (LJ.factorization.coeff 0 : ℤ) * g.m +
      (LJ.factorization.coeff 1 : ℤ) * g.n 0 +
      (LJ.factorization.coeff 3 : ℤ) * g.n 2 = P.qL + g.n 1 := by
  have h := LJ.factorization.equation
  have hc : LJ.factorization.coeff =
      Fin.cons (LJ.factorization.coeff 0) (fun j => LJ.factorization.coeff j.succ) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [hc, g.value_cons] at h
  simp [value, Fin.sum_univ_succ] at h
  have hz : LJ.factorization.coeff 2 = 0 := by simpa using LJ.direction_zero
  rw [hz] at h
  simp at h
  linarith

theorem C_cert (P : PathInput s F D) (N : NormalizedRoot P)
    (LJ : ActualReturn g P.qL 1) :
    F = ((LJ.factorization.coeff 0 : ℤ) - 1) * g.m +
      (P.beta + LJ.factorization.coeff 1) * g.n 0 +
      ((D.rho 1 : ℤ) - 1) * g.n 1 +
      ((LJ.factorization.coeff 3 : ℤ) - D.b 2) * g.n 2 := by
  have hLJ := lj_equation P LJ
  have hc := P.cL
  change F + g.m - P.qL = P.P0 * g.n 0 at hc
  have hP := P.P0_eq
  linear_combination hc - hLJ + g.n 0 * hP - D.relation_one

theorem C_cap (P : PathInput s F D) (hF : s.semigroup.IsFrobenius F)
    (N : NormalizedRoot P) (LJ : ActualReturn g P.qL 1) :
    (LJ.factorization.coeff 3 : ℤ) ≤ D.b 2 - 1 := by
  by_contra hn
  have hcert := N.C_cert P LJ
  have hmem := gamma_of_coordinates g F
    ((LJ.factorization.coeff 0 : ℤ) - 1)
    (P.beta + LJ.factorization.coeff 1)
    ((D.rho 1 : ℤ) - 1)
    ((LJ.factorization.coeff 3 : ℤ) - D.b 2)
    (by have := LJ.level_pos; omega)
    (by have := P.beta_pos; omega)
    (by have := D.rho_pos 1; omega)
    (by omega) hcert
  exact hF.1 hmem

theorem qL_cert_of_level_one (P : PathInput s F D) (N : NormalizedRoot P)
    (LJ : ActualReturn g P.qL 1) (hlevel : LJ.factorization.coeff 0 = 1) :
    P.qL = ((LJ.factorization.coeff 1 : ℤ) - N.d) * g.n 0 +
      (N.S - 1) * g.n 1 +
      ((LJ.factorization.coeff 3 : ℤ) + N.K + P.alpha) * g.n 2 := by
  have hLJ := lj_equation P LJ
  have hr := N.equation
  have he := N.e_eq
  rw [hlevel] at hLJ
  norm_num at hLJ
  linear_combination -hLJ + hr + g.n 2 * he

/-- P5.3.5: every genuine missing-j return has level at least two. -/
theorem endpoint_level_two (P : PathInput s F D)
    (hF : s.semigroup.IsFrobenius F) (N : NormalizedRoot P)
    (LJ : ActualReturn g P.qL 1) : 2 ≤ LJ.factorization.coeff 0 := by
  have hC := N.C_cap P hF LJ
  by_contra hn
  have hlevel : LJ.factorization.coeff 0 = 1 := by
    have := LJ.level_pos
    omega
  have hqcert := N.qL_cert_of_level_one P LJ hlevel
  have hA : (LJ.factorization.coeff 1 : ℤ) ≤ N.d - 1 := by
    by_contra hAn
    have hmem := gamma_of_coordinates g P.qL 0
      ((LJ.factorization.coeff 1 : ℤ) - N.d) (N.S - 1)
      ((LJ.factorization.coeff 3 : ℤ) + N.K + P.alpha)
      (by omega) (by omega) (by have := N.S_pos; omega)
      (by have := N.K_lower; have := P.alpha_pos; omega)
      (by simpa using hqcert)
    exact (P.actual 0).1.1 hmem
  let V : ℤ := LJ.factorization.coeff 3 + N.K - D.b 2 + 1
  have hpure : V * g.n 2 =
      (N.d - LJ.factorization.coeff 1 - 1) * g.n 0 +
      (P.R - N.S) * g.n 1 := by
    have hq := P.qL_eq
    have hT := P.T_eq
    dsimp [V]
    linear_combination hq - hqcert + g.n 2 * hT
  have hVpos : 0 < V := by
    have := N.K_lower
    omega
  have hVupper : V ≤ N.K := by omega
  have hright : 0 ≤ P.R - N.S := by have := N.S_lt; omega
  have hcrit := herzog_critical_le_int D (by decide : (2 : Fin 3) ≠ 0)
    (by decide : (2 : Fin 3) ≠ 1) V
    (N.d - LJ.factorization.coeff 1 - 1) (P.R - N.S)
    hVpos (by omega) hright hpure
  have hKupper := N.K_upper
  omega

theorem F_absorption (P : PathInput s F D) (N : NormalizedRoot P)
    (LJ : ActualReturn g P.qL 1) :
    F = ((LJ.factorization.coeff 0 : ℤ) - 2) * g.m +
      (P.P0 + LJ.factorization.coeff 1 - N.d) * g.n 0 +
      (N.S - 1) * g.n 1 +
      ((LJ.factorization.coeff 3 : ℤ) + N.K + P.alpha) * g.n 2 := by
  have hLJ := lj_equation P LJ
  have hc := P.cL
  change F + g.m - P.qL = P.P0 * g.n 0 at hc
  have hr := N.equation
  have he := N.e_eq
  linear_combination hc - hLJ + hr + g.n 2 * he

/-- A normalized left root is impossible by the exact one-step F absorption. -/
theorem impossible (P : PathInput s F D) (hF : s.semigroup.IsFrobenius F)
    (N : NormalizedRoot P) : False := by
  obtain ⟨LJ⟩ := P.qL_n1_return
  have hlvl := N.endpoint_level_two P hF LJ
  have hcert := N.F_absorption P LJ
  have hP := P.P0_eq
  have hmem := gamma_of_coordinates g F
    ((LJ.factorization.coeff 0 : ℤ) - 2)
    (P.P0 + LJ.factorization.coeff 1 - N.d)
    (N.S - 1)
    ((LJ.factorization.coeff 3 : ℤ) + N.K + P.alpha)
    (by omega)
    (by have := N.d_le; have := P.beta_pos; omega)
    (by have := N.S_pos; omega)
    (by have := N.K_lower; have := P.alpha_pos; omega)
    hcert
  exact hF.1 hmem

end NormalizedRoot

theorem WeakRoot.impossible (P : PathInput s F D)
    (hF : s.semigroup.IsFrobenius F) (w : WeakRoot P) : False := by
  obtain ⟨LK⟩ := P.qL_n2_return
  obtain ⟨N⟩ := w.normalize P hF LK
  exact N.impossible P hF

end PathInput
end P21.Nonsymmetric
