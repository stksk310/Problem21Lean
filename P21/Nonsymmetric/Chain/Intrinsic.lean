import P21.Nonsymmetric.Chain.Slopes

namespace P21.Nonsymmetric
namespace ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

def h (K : ChainCore s F D) : ℤ := K.chain.lambda / K.d
def q0 (K : ChainCore s F D) : ℤ := K.h + 1
def r (K : ChainCore s F D) : ℤ := K.chain.lambda % K.d
def e0 (K : ChainCore s F D) : ℤ := K.q0 * K.d - K.chain.lambda

def J0 (K : ChainCore s F D) : ℤ :=
  D.rho 1 + K.chain.gapJ - 1 - K.q0 * K.S
def K0 (K : ChainCore s F D) : ℤ :=
  D.rho 2 + K.chain.alpha - 1 - K.q0 * K.Croot

structure Euclidean (K : ChainCore s F D) : Prop where
  lambda_eq : K.chain.lambda = K.h * K.d + K.r
  r_range : 0 ≤ K.r ∧ K.r < K.d
  h_pos : 1 ≤ K.h
  q0_pos : 2 ≤ K.q0
  e0_eq : K.e0 = K.d - K.r
  e0_range : 1 ≤ K.e0 ∧ K.e0 ≤ K.d

theorem euclidean (K : ChainCore s F D) : K.Euclidean := by
  have hd1 := K.d_range.1
  have hd : 0 < K.d := by omega
  have hd0 : K.d ≠ 0 := ne_of_gt hd
  have hr0 : 0 ≤ K.r := by
    exact Int.emod_nonneg _ hd0
  have hrd : K.r < K.d := Int.emod_lt_of_pos _ hd
  have heq0 := Int.ediv_mul_add_emod K.chain.lambda K.d
  have heq : K.chain.lambda = K.h * K.d + K.r := by
    simpa [h, r, add_comm] using heq0.symm
  have hh : 1 ≤ K.h := by
    rw [h, Int.le_ediv_iff_mul_le hd]
    simpa using K.d_range.2
  have hq : 2 ≤ K.q0 := by simp [q0]; omega
  have he : K.e0 = K.d - K.r := by
    simp only [e0, q0]
    nlinarith [heq]
  have helo : 1 ≤ K.e0 := by rw [he]; omega
  have hehi : K.e0 ≤ K.d := by rw [he]; omega
  exact ⟨heq, ⟨hr0, hrd⟩, hh, hq, he, ⟨helo, hehi⟩⟩

def v (K : ChainCore s F D) (x y : ℤ) : Fin 4 → ℤ :=
  ![x - 1,
    K.chain.P - 1 + x*K.d - y*D.rho 0,
    K.chain.R - 1 - x*K.S + y*D.b 1,
    K.chain.T - 1 - x*K.Croot + y*D.a 2]

theorem completed_F (K : ChainCore s F D) (x y : ℤ) :
    F = (K.v x y 0) * g.m + (K.v x y 1) * g.n 0 +
      (K.v x y 2) * g.n 1 + (K.v x y 3) * g.n 2 := by
  have hw := K.chain.W_exact
  simp only [W] at hw
  have hr := D.relation_zero
  simp [v]
  linear_combination hw - x * K.root + y * hr

def Successful (K : ChainCore s F D) (x y : ℤ) : Prop :=
  ∀ i, 0 ≤ K.v x y i

theorem successful_x_pos (K : ChainCore s F D) {x y : ℤ}
    (H : K.Successful x y) : 1 ≤ x := by
  have := H 0
  simpa [Successful, v] using this

theorem nonpositive_y_reduces (K : ChainCore s F D) {x y : ℤ}
    (H : K.Successful x y) (hy : y ≤ 0) : K.Successful 1 0 := by
  have hx := K.successful_x_pos H
  have hs : 0 ≤ K.S := by have := K.S_strong; have := K.chain.scalar_ranges.2.2.1; omega
  have hc : 0 ≤ K.Croot := by have := K.C_lower; have := K.chain.scalar_ranges.2.2.2; omega
  have hb1 : (0 : ℤ) ≤ D.b 1 := by exact_mod_cast (D.b 1).zero_le
  have ha2 : (0 : ℤ) ≤ D.a 2 := by exact_mod_cast (D.a 2).zero_le
  intro i
  fin_cases i
  · simp [v]
  · simp [v]
    have hp : 1 ≤ K.chain.P := by
      rw [K.chain.P_eq_a_beta]
      have := D.a_pos 0; have := K.chain.scalar_ranges.2.1; omega
    have hd := K.d_range.1
    omega
  · have hh := H 2
    simp [v] at hh ⊢
    nlinarith
  · have hh := H 3
    simp [v] at hh ⊢
    nlinarith

theorem positive_y_i_fit (K : ChainCore s F D) {x y : ℤ}
    (H : K.Successful x y) (hy : 1 ≤ y) :
    K.chain.lambda + 1 + (y-1) * D.rho 0 ≤ x * K.d := by
  have hi := H 1
  have hp : K.chain.P = (D.rho 0 : ℤ) - K.chain.lambda := by simp [ChainInput.P]
  simp [v, hp] at hi
  nlinarith

theorem rho_gap_identity (K : ChainCore s F D) :
    (D.rho 0 : ℤ) - K.q0*K.d - K.q0 =
      (K.q0-2)*(K.d-1) + 2*K.r + K.chain.delta + K.chain.beta - 2 := by
  have E := K.euclidean
  have hr0 : (D.rho 0 : ℤ) = D.a 0 + D.b 0 := by exact_mod_cast D.rho_eq 0
  have ha := K.chain.a0_exact
  have hb := K.chain.b0_exact
  simp only [q0] at ⊢
  nlinarith [hr0, ha, hb, E.lambda_eq]

theorem rho_gap_nonneg (K : ChainCore s F D) :
    0 ≤ (D.rho 0 : ℤ) - K.q0*K.d - K.q0 := by
  rw [K.rho_gap_identity]
  have E := K.euclidean
  have hs := K.chain.scalar_ranges
  have hq := E.q0_pos
  have hd := K.d_range.1
  have hr := E.r_range.1
  have hdelta := hs.1
  have hbeta := hs.2.1
  have hmul := mul_nonneg (show 0 ≤ K.q0-2 by omega)
    (show 0 ≤ K.d-1 by omega)
  nlinarith [hmul]

theorem successful_ge_q0 (K : ChainCore s F D) {x y : ℤ}
    (H : K.Successful x y) (hy : 1 ≤ y) : y*K.q0 ≤ x := by
  have hfit := K.positive_y_i_fit H hy
  have hg := K.rho_gap_nonneg
  have E := K.euclidean
  have hq := E.q0_pos
  by_contra hn
  have hx : x ≤ y*K.q0-1 := by omega
  have hd : 1 ≤ K.d := K.d_range.1
  have hqd : K.q0*K.d + K.q0 ≤ D.rho 0 := by omega
  have hxd := mul_le_mul_of_nonneg_right hx (show 0 ≤ K.d by omega)
  have hyr := mul_le_mul_of_nonneg_left hqd (show 0 ≤ y-1 by omega)
  have hbound : K.chain.lambda + 1 + (y-1) * (D.rho 0 : ℤ) ≤
      (y*K.q0-1)*K.d := le_trans hfit hxd
  have hsmall : K.chain.lambda + 1 + (y-1)*(K.q0*K.d+K.q0) ≤
      (y*K.q0-1)*K.d := by nlinarith
  have hid : (y*K.q0-1)*K.d -
      (K.chain.lambda+1+(y-1)*(K.q0*K.d+K.q0)) =
      -K.r-1-(y-1)*K.q0 := by
    rw [E.lambda_eq]
    simp only [q0]
    ring
  have hp := mul_nonneg (show 0 ≤ y-1 by omega) (show 0 ≤ K.q0 by omega)
  have hr := E.r_range.1
  nlinarith

theorem second_coordinates (K : ChainCore s F D) :
    K.v K.q0 1 = ![K.q0-1, K.e0-1, K.J0, K.K0] := by
  have hr1 : (D.rho 1 : ℤ) = D.a 1 + D.b 1 := by exact_mod_cast D.rho_eq 1
  have hr2 : (D.rho 2 : ℤ) = D.a 2 + D.b 2 := by exact_mod_cast D.rho_eq 2
  funext i
  fin_cases i
  · simp [v]
  · simp [v, e0, ChainInput.P]
    ring
  · simp [v, J0, K.chain.R_exact]
    omega
  · simp [v, K0, K.chain.T_exact]
    omega

theorem second_deficient (K : ChainCore s F D)
    (hF : s.semigroup.IsFrobenius F) : K.J0 < 0 ∨ K.K0 < 0 := by
  by_contra hn
  push_neg at hn
  have E := K.euclidean
  have hq := E.q0_pos
  have he := E.e0_range.1
  have hv : K.Successful K.q0 1 := by
    intro i
    rw [K.second_coordinates]
    fin_cases i
    · simp; omega
    · simp; omega
    · simpa using hn.1
    · simpa using hn.2
  have hm := four_mem (g := g) (K.v K.q0 1 0) (K.v K.q0 1 1)
    (K.v K.q0 1 2) (K.v K.q0 1 3)
    (hv 0) (hv 1) (hv 2) (hv 3)
  apply hF.1
  change F ∈ g.Gamma
  convert hm using 1
  simpa using K.completed_F K.q0 1

end ChainCore
end P21.Nonsymmetric
