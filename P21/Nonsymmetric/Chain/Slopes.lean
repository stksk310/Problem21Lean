import P21.Nonsymmetric.Chain.Caps

namespace P21.Nonsymmetric
namespace ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

structure Slopes (K : ChainCore s F D) : Prop where
  j_identity : (D.rho 1 : ℤ) * g.m =
    (K.S * D.a 0 - K.d * D.rho 1) * g.n 0 +
    (K.S * D.b 2 + K.Croot * D.rho 1) * g.n 2
  k_identity : (D.rho 2 : ℤ) * g.m =
    (K.Croot * D.b 0 - K.d * D.rho 2) * g.n 0 +
    (K.S * D.rho 2 + K.Croot * D.a 1) * g.n 1
  j_pos : 0 < K.d * D.rho 1 - K.S * D.a 0
  k_pos : 0 < K.d * D.rho 2 - K.Croot * D.b 0
  S_lt : K.S < D.rho 1
  C_lt : K.Croot < D.rho 2

theorem slopes (K : ChainCore s F D) : K.Slopes := by
  have hj : (D.rho 1 : ℤ) * g.m =
      (K.S * D.a 0 - K.d * D.rho 1) * g.n 0 +
      (K.S * D.b 2 + K.Croot * D.rho 1) * g.n 2 := by
    linear_combination (D.rho 1 : ℤ) * K.root + K.S * D.relation_one
  have hk : (D.rho 2 : ℤ) * g.m =
      (K.Croot * D.b 0 - K.d * D.rho 2) * g.n 0 +
      (K.S * D.rho 2 + K.Croot * D.a 1) * g.n 1 := by
    linear_combination (D.rho 2 : ℤ) * K.root + K.Croot * D.relation_two
  have hp : ∀ i, 0 < g.n i := fun i => lt_trans s.m_pos (s.n_gt i)
  have hr1 : (0 : ℤ) < D.rho 1 := by exact_mod_cast D.rho_pos 1
  have hr2 : (0 : ℤ) < D.rho 2 := by exact_mod_cast D.rho_pos 2
  have ha0 : (0 : ℤ) < D.a 0 := by exact_mod_cast D.a_pos 0
  have hb0 : (0 : ℤ) < D.b 0 := by exact_mod_cast D.b_pos 0
  have ha1 : (0 : ℤ) < D.a 1 := by exact_mod_cast D.a_pos 1
  have hb2 : (0 : ℤ) < D.b 2 := by exact_mod_cast D.b_pos 2
  have hs : 1 ≤ K.S := by
    have h := K.S_strong
    have hg := K.chain.scalar_ranges.2.2.1
    omega
  have hc : 1 ≤ K.Croot := by
    exact le_trans K.chain.scalar_ranges.2.2.2 K.C_lower
  have hjp : 0 < K.d * D.rho 1 - K.S * D.a 0 := by
    by_contra hn
    have hA : 0 ≤ K.S * D.a 0 - K.d * D.rho 1 := by omega
    have hB : (D.rho 1 : ℤ) ≤ K.S * D.b 2 + K.Croot * D.rho 1 := by
      nlinarith
    have hAterm := mul_nonneg hA (hp 0).le
    have hBterm : (D.rho 1 : ℤ) * g.n 2 ≤
        (K.S * D.b 2 + K.Croot * D.rho 1) * g.n 2 :=
      (mul_le_mul_of_nonneg_right hB (hp 2).le)
    have hm := s.n_gt 2
    nlinarith [hj]
  have hkp : 0 < K.d * D.rho 2 - K.Croot * D.b 0 := by
    by_contra hn
    have hA : 0 ≤ K.Croot * D.b 0 - K.d * D.rho 2 := by omega
    have hB : (D.rho 2 : ℤ) ≤ K.S * D.rho 2 + K.Croot * D.a 1 := by
      nlinarith
    have hAterm := mul_nonneg hA (hp 0).le
    have hBterm : (D.rho 2 : ℤ) * g.n 1 ≤
        (K.S * D.rho 2 + K.Croot * D.a 1) * g.n 1 :=
      mul_le_mul_of_nonneg_right hB (hp 1).le
    have hm := s.n_gt 1
    nlinarith [hk]
  have hS : K.S < D.rho 1 := by
    have hd := K.d_range.2
    have hl := K.chain.lambda_range.2.1
    by_contra hn
    have : (D.rho 1 : ℤ) ≤ K.S := by omega
    nlinarith [mul_pos (show 0 < (D.rho 1 : ℤ) from hr1) (show 0 < (D.a 0 : ℤ) - K.d by omega)]
  have hC : K.Croot < D.rho 2 := by
    have hd := K.d_range.2
    have hl := K.chain.lambda_range.2.2
    by_contra hn
    have : (D.rho 2 : ℤ) ≤ K.Croot := by omega
    nlinarith [mul_pos (show 0 < (D.rho 2 : ℤ) from hr2) (show 0 < (D.b 0 : ℤ) - K.d by omega)]
  exact ⟨hj, hk, hjp, hkp, hS, hC⟩

end ChainCore
end P21.Nonsymmetric
