import P21.Nonsymmetric.Extraction

namespace P21.Nonsymmetric
namespace PathInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    (P : PathInput s F D)

/-- Publication slack `β = b₀ - λ`. -/
def beta : ℤ := D.b 0 - P.lambda

/-- Publication slack `α = a₂ - ν`. -/
def alpha : ℤ := D.a 2 - P.nu

/-- Publication coordinate `P = ρ₀ - λ`; named `P0` to avoid collision
with the PATH structure. -/
def P0 : ℤ := D.rho 0 - P.lambda

/-- Publication coordinate `T = ρ₂ - ν`. -/
def T : ℤ := D.rho 2 - P.nu

theorem beta_pos : 1 ≤ P.beta := by
  have := P.lambda_range
  simp only [beta]
  omega

theorem alpha_pos : 1 ≤ P.alpha := by
  have := P.nu_range
  simp only [alpha]
  omega

theorem P0_eq : P.P0 = D.a 0 + P.beta := by
  have hr : (D.rho 0 : ℤ) = D.a 0 + D.b 0 := by
    exact_mod_cast D.rho_eq 0
  simp only [P0, beta]
  omega

theorem T_eq : P.T = D.b 2 + P.alpha := by
  have hr : (D.rho 2 : ℤ) = D.a 2 + D.b 2 := by
    exact_mod_cast D.rho_eq 2
  simp only [T, alpha]
  omega

theorem R_pos : 1 ≤ P.R := P.R_range.1

theorem R_lt : P.R < D.rho 1 := P.R_range.2

theorem qL_eq :
    P.qL = -g.n 0 + (P.R - 1) * g.n 1 + (P.T - 1) * g.n 2 := by
  have hcL := P.cL
  have hW := P.boxW
  simp only [complement, W] at hcL
  simp only [W, T] at hW ⊢
  linear_combination hW - hcL

theorem qA_eq :
    P.qA = (D.a 0 - 1) * g.n 0 - g.n 1 + (P.T - 1) * g.n 2 := by
  have hcA := P.cA
  have hW := P.boxW
  simp only [complement, W] at hcA
  have hP := P.P0_eq
  simp only [W, P0, beta, T] at hW hcA hP ⊢
  linear_combination hW - hcA + g.n 0 * hP

theorem qB_eq :
    P.qB = (P.P0 - 1) * g.n 0 - g.n 1 + (D.b 2 - 1) * g.n 2 := by
  have hcB := P.cB
  have hW := P.boxW
  simp only [complement, W] at hcB
  have hT := P.T_eq
  simp only [W, P0, alpha, T] at hW hcB hT ⊢
  linear_combination hW - hcB + g.n 2 * hT

theorem qR_eq :
    P.qR = (P.P0 - 1) * g.n 0 + (P.R - 1) * g.n 1 - g.n 2 := by
  have hcR := P.cR
  have hW := P.boxW
  simp only [complement, W] at hcR
  simp only [W, P0] at hW hcR ⊢
  linear_combination hW - hcR

end PathInput
end P21.Nonsymmetric
