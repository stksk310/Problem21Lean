import P21.Nonsymmetric.Extraction

namespace P21.Nonsymmetric
namespace TypeIIInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    (T : TypeIIInput s F D)

/-- Convert a coefficientwise nonnegative four-generator identity into
genuine membership.  This local helper keeps signed identities separate. -/
theorem actual_of_coordinates (g : Generators) (x k a b c : ℤ)
    (hk : 0 ≤ k) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (he : x = k * g.m + a * g.n 0 + b * g.n 1 + c * g.n 2) :
    x ∈ g.Gamma := by
  refine ⟨![k.toNat, a.toNat, b.toNat, c.toNat], ?_⟩
  simpa [Generators.all, value, Fin.sum_univ_succ,
    Int.toNat_of_nonneg hk, Int.toNat_of_nonneg ha,
    Int.toNat_of_nonneg hb, Int.toNat_of_nonneg hc, add_assoc] using he.symm

/-- Three-generator counterpart used for the excluded sign regions. -/
theorem tail_of_coordinates (g : Generators) (x a b c : ℤ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (he : x = a * g.n 0 + b * g.n 1 + c * g.n 2) : x ∈ g.H := by
  refine ⟨![a.toNat, b.toNat, c.toNat], ?_⟩
  simpa [Generators.H, value, Fin.sum_univ_succ,
    Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb,
    Int.toNat_of_nonneg hc, add_assoc] using he.symm

/-- Publication coordinate `P₀ = ρ₀ - λ`. -/
def P0 : ℤ := D.rho 0 - T.lambda

/-- Publication coordinate `R = ρ₁ - μ`. -/
def R : ℤ := D.rho 1 - T.mu

/-- Publication coordinate `T₀ = ρ₂ - ν`. -/
def T0 : ℤ := D.rho 2 - T.nu

/-- Publication slack `g₁ = b₁ - μ`. -/
def g1 : ℤ := D.b 1 - T.mu

theorem R_eq : T.R = D.a 1 + T.g1 := by
  have hr : (D.rho 1 : ℤ) = D.a 1 + D.b 1 := by exact_mod_cast D.rho_eq 1
  simp only [R, g1]
  omega

theorem g1_pos : 1 ≤ T.g1 := by
  have := T.mu_range.2
  simp only [g1]
  omega

theorem P0_sub_b0 : T.P0 - D.b 0 = D.a 0 - T.lambda := by
  have hr : (D.rho 0 : ℤ) = D.a 0 + D.b 0 := by exact_mod_cast D.rho_eq 0
  simp only [P0]
  omega

theorem P0_sub_b0_pos : 1 ≤ T.P0 - D.b 0 := by
  rw [T.P0_sub_b0]
  have := T.lambda_range.2.1
  omega

theorem T0_sub_b2 : T.T0 - D.b 2 = D.a 2 - T.nu := by
  have hr : (D.rho 2 : ℤ) = D.a 2 + D.b 2 := by exact_mod_cast D.rho_eq 2
  simp only [T0]
  omega

theorem T0_sub_b2_pos : 1 ≤ T.T0 - D.b 2 := by
  rw [T.T0_sub_b2]
  have := T.nu_range.2
  omega

theorem qS_eq :
    T.qS = -g.n 0 + (T.R - 1) * g.n 1 + (T.T0 - 1) * g.n 2 := by
  simpa [R, T0] using T.singleton_row

theorem qS_add_P0 : T.qS + T.P0 * g.n 0 = W F g.m := by
  have hc : W F g.m - T.qS = T.P0 * g.n 0 := by
    simpa [complement, P0] using T.cS
  linarith

/-- `η = ν - b₂`. -/
def eta : ℤ := T.nu - D.b 2

/-- `θ = μ - a₁`. -/
def theta : ℤ := T.mu - D.a 1

theorem anchor_A : D.fA - T.qS = T.mu * g.n 1 + T.eta * g.n 2 := by
  have hq := T.qS_eq
  have hr1 : (D.rho 1 : ℤ) = D.a 1 + D.b 1 := by exact_mod_cast D.rho_eq 1
  have hr2 : (D.rho 2 : ℤ) = D.a 2 + D.b 2 := by exact_mod_cast D.rho_eq 2
  have e0 := D.relation_zero
  simp only [R, T0] at hq
  simp only [eta, HerzogCriticalData.fA]
  linear_combination -hq + e0 - g.n 1 * hr1 - g.n 2 * hr2

theorem anchor_B : D.fB - T.qS = T.theta * g.n 1 + T.nu * g.n 2 := by
  have hq := T.qS_eq
  have hr1 : (D.rho 1 : ℤ) = D.a 1 + D.b 1 := by exact_mod_cast D.rho_eq 1
  have hr2 : (D.rho 2 : ℤ) = D.a 2 + D.b 2 := by exact_mod_cast D.rho_eq 2
  have e0 := D.relation_zero
  simp only [R, T0] at hq
  simp only [theta, HerzogCriticalData.fB]
  linear_combination -hq + e0 - g.n 1 * hr1 - g.n 2 * hr2

end TypeIIInput
end P21.Nonsymmetric
