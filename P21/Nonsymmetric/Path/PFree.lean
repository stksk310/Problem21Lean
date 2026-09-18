import P21.Nonsymmetric.Path.Seam

namespace P21.Nonsymmetric
namespace PathInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

/-- The actual left-oriented PFREE kernel. -/
structure PFreeI (P : PathInput s F D) where
  Y : ℕ
  H0 : ℕ
  K : ℕ
  Y_lt : Y < P.beta.toNat
  K_lt : K < P.alpha.toNat
  H0_lt : H0 < D.a 1
  equationA : P.qA + g.m =
    value g.n ![Y + D.a 0 + P.lambda.toNat, H0, K]
  equationB : P.qB + g.m =
    value g.n ![Y, H0 + D.b 1, K + P.nu.toNat]

theorem pfree_of_middle_lt (P : PathInput s F D)
    (N : NoPairNormalization P) (hmiddle : N.atA.coeff 1 < N.atB.coeff 1) :
    Nonempty (PFreeI P) := by
  let e : ℤ := N.atB.coeff 1 - N.atA.coeff 1
  have he : 0 < e := by dsimp [e]; omega
  have helt : e < D.rho 1 := by
    dsimp [e]
    have := N.B_j_lt
    omega
  have hbetaCast : (P.beta.toNat : ℤ) = P.beta :=
    Int.toNat_of_nonneg (by have := P.beta_pos; omega)
  have halphaCast : (P.alpha.toNat : ℤ) = P.alpha :=
    Int.toNat_of_nonneg (by have := P.alpha_pos; omega)
  have hlambdaCast : (P.lambda.toNat : ℤ) = P.lambda :=
    Int.toNat_of_nonneg (by have := P.lambda_range.1; omega)
  have hnuCast : (P.nu.toNat : ℤ) = P.nu :=
    Int.toNat_of_nonneg (by have := P.nu_range.1; omega)
  have hr0 : (D.rho 0 : ℤ) = D.a 0 + D.b 0 := by exact_mod_cast D.rho_eq 0
  have hr1 : (D.rho 1 : ℤ) = D.a 1 + D.b 1 := by exact_mod_cast D.rho_eq 1
  have hbetaDef : P.beta = (D.b 0 : ℤ) - P.lambda := rfl
  have halphaDef : P.alpha = (D.a 2 : ℤ) - P.nu := rfl
  have haUpper : N.Ac P - D.rho 0 < D.rho 0 := by
    have hi := N.A_i_lt
    have hb := N.B_i_lt
    have hbr := P.lambda_range.1
    have hbpos := D.b_pos 0
    simp only [NoPairNormalization.Ac]
    omega
  have hvUpper : N.Bc P - D.a 2 < D.rho 2 := by
    have hk := N.B_k_lt
    have hT := P.T_eq
    have hTr := P.nu_range.1
    have hr2 : (D.rho 2 : ℤ) = D.a 2 + D.b 2 := by exact_mod_cast D.rho_eq 2
    simp only [NoPairNormalization.Bc]
    omega
  have hrel : N.Ac P * g.n 0 = e * g.n 1 + N.Bc P * g.n 2 := by
    have h := N.central_relation P
    dsimp [e]
    linear_combination h
  obtain ⟨hAc, heq, hBc⟩ := path_seam_rigidity D
    (fun i => lt_trans s.m_pos (s.n_gt i)) (N.Ac P) e (N.Bc P)
    (N.Ac_pos P) he (N.Bc_pos P) helt haUpper hvUpper hrel
  have hAi : N.atA.coeff 0 = N.atB.coeff 0 + D.a 0 + P.lambda.toNat := by
    simp only [NoPairNormalization.Ac] at hAc
    omega
  have hBj : N.atB.coeff 1 = N.atA.coeff 1 + D.b 1 := by
    dsimp [e] at heq
    omega
  have hBk : N.atB.coeff 2 = N.atA.coeff 2 + P.nu.toNat := by
    simp only [NoPairNormalization.Bc] at hBc
    have heAlpha : P.alpha = (D.a 2 : ℤ) - P.nu := rfl
    omega
  have hH : N.atA.coeff 1 < D.a 1 := by
    have := N.B_j_lt
    omega
  refine ⟨{
    Y := N.atB.coeff 0
    H0 := N.atA.coeff 1
    K := N.atA.coeff 2
    Y_lt := N.B_i_lt
    K_lt := N.A_k_lt
    H0_lt := hH
    equationA := ?_
    equationB := ?_ }⟩
  · have hc : (![N.atB.coeff 0 + D.a 0 + P.lambda.toNat,
        N.atA.coeff 1, N.atA.coeff 2] : Fin 3 → ℕ) = N.atA.coeff := by
      funext i
      fin_cases i <;> simp [hAi]
    rw [hc]
    exact N.atA.equation.symm
  · have hc : (![N.atB.coeff 0, N.atA.coeff 1 + D.b 1,
        N.atA.coeff 2 + P.nu.toNat] : Fin 3 → ℕ) = N.atB.coeff := by
      funext i
      fin_cases i <;> simp [hBj, hBk]
    rw [hc]
    exact N.atB.equation.symm

end PathInput
end P21.Nonsymmetric
