import P21.Nonsymmetric.Chain.Returns

namespace P21.Nonsymmetric
namespace ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable (K : ChainCore s F D) (E : K.Returns)

theorem FI_A :
    F + g.n 0 = (E.Li - 1) * g.m + (E.Uj + K.chain.gapJ) * g.n 1 +
      (E.Uk + K.chain.T) * g.n 2 := by
  have he := E.EA_eq
  have hc := K.chain.cA_exact
  simp [complement, W] at hc
  linear_combination he + hc

theorem FI_B :
    F + g.n 0 = (E.Lb - 1) * g.m + (E.Vj + K.chain.R) * g.n 1 +
      (E.Vk + K.chain.alpha) * g.n 2 := by
  have he := E.EB_eq
  have hc := K.chain.cB_exact
  simp [complement, W] at hc
  linear_combination he + hc

theorem FJ :
    F + g.n 1 = (E.Lj - 1) * g.m + (E.Aj + K.chain.delta) * g.n 0 +
      (E.Cj + K.chain.T) * g.n 2 := by
  have he := E.Qj_eq
  have hc := K.chain.cJ_exact
  simp [complement, W] at hc
  linear_combination he + hc

private theorem gap_of_four {q l x y z : ℤ} (hq : q ∉ g.Gamma)
    (he : q = l*g.m + x*g.n 0 + y*g.n 1 + z*g.n 2)
    (hl : 0 ≤ l) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : False := by
  apply hq
  rw [he]
  exact four_mem l x y z hl hx hy hz

private theorem frobenius_of_four (hF : s.semigroup.IsFrobenius F)
    {l x y z : ℤ}
    (he : F = l*g.m + x*g.n 0 + y*g.n 1 + z*g.n 2)
    (hl : 0 ≤ l) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : False := by
  apply hF.1
  change F ∈ g.Gamma
  rw [he]
  exact four_mem l x y z hl hx hy hz

/-- All packet and ROOT caps of §7.9–7.10. -/
structure Caps : Prop where
  Uj_FI : E.Uj + K.chain.gapJ < D.rho 1
  Uk_FI : E.Uk + K.chain.T < D.rho 2
  Vj_FI : E.Vj + K.chain.R < D.rho 1
  Vk_FI : E.Vk + K.chain.alpha < D.rho 2
  Cj_FJ : E.Cj + K.chain.T < D.rho 2
  Aj_cap : E.Aj ≤ K.d - 1
  Ak_cap : E.Ak ≤ K.d - 1
  Uj_root : E.Uj + K.S < D.rho 1
  Uk_root : E.Uk + K.Croot < D.rho 2
  Vj_root : E.Vj + K.S < D.rho 1
  Vk_root : E.Vk + K.Croot < D.rho 2

theorem caps (hF : s.semigroup.IsFrobenius F) : K.Caps E := by
  have hn := E.coeff_nonneg
  have hL := E.levels_pos
  have hscalar := K.chain.scalar_ranges
  have ha0 : (1 : ℤ) ≤ D.a 0 := by exact_mod_cast D.a_pos 0
  have hb0 : (1 : ℤ) ≤ D.b 0 := by exact_mod_cast D.b_pos 0
  have ha1 : (1 : ℤ) ≤ D.a 1 := by exact_mod_cast D.a_pos 1
  have hb2 : (1 : ℤ) ≤ D.b 2 := by exact_mod_cast D.b_pos 2
  have hs0 := K.S_strong
  have hs : 1 ≤ K.S := by omega
  have hc : 1 ≤ K.Croot := le_trans hscalar.2.2.2 K.C_lower
  have hd := K.d_range
  have hR : 1 ≤ K.chain.R := by
    rw [K.chain.R_exact]; have := D.a_pos 1; omega
  have hT : 1 ≤ K.chain.T := by
    rw [K.chain.T_exact]; have := D.b_pos 2; omega
  have hqA : K.chain.qA ∉ g.Gamma := K.chain.qA_actual.1.1
  have hqB : K.chain.qB ∉ g.Gamma := K.chain.qB_actual.1.1
  have hqJ : K.chain.qJ ∉ g.Gamma := K.chain.qJ_actual.1.1
  have hqK : K.chain.qK ∉ g.Gamma := K.chain.qK_actual.1.1
  have ufi : E.Uj + K.chain.gapJ < D.rho 1 := by
    by_contra hh
    have he := K.FI_A E
    have hr := D.relation_one
    have hf : F = (E.Li-1)*g.m + (D.a 0-1)*g.n 0 +
        (E.Uj+K.chain.gapJ-D.rho 1)*g.n 1 +
        (E.Uk+K.chain.T+D.b 2)*g.n 2 := by
      linear_combination he + hr - g.n 0
    exact frobenius_of_four hF hf (by omega) (by omega) (by omega) (by omega)
  have ukfi : E.Uk + K.chain.T < D.rho 2 := by
    by_contra hh
    have he := K.FI_A E
    have hr := D.relation_two
    have hf : F = (E.Li-1)*g.m + (D.b 0-1)*g.n 0 +
        (E.Uj+K.chain.gapJ+D.a 1)*g.n 1 +
        (E.Uk+K.chain.T-D.rho 2)*g.n 2 := by
      linear_combination he + hr - g.n 0
    exact frobenius_of_four hF hf (by omega) (by omega) (by omega) (by omega)
  have vfi : E.Vj + K.chain.R < D.rho 1 := by
    by_contra hh
    have he := K.FI_B E
    have hr := D.relation_one
    have hf : F = (E.Lb-1)*g.m + (D.a 0-1)*g.n 0 +
        (E.Vj+K.chain.R-D.rho 1)*g.n 1 +
        (E.Vk+K.chain.alpha+D.b 2)*g.n 2 := by
      linear_combination he + hr - g.n 0
    exact frobenius_of_four hF hf (by omega) (by omega) (by omega) (by omega)
  have vkfi : E.Vk + K.chain.alpha < D.rho 2 := by
    by_contra hh
    have he := K.FI_B E
    have hr := D.relation_two
    have hf : F = (E.Lb-1)*g.m + (D.b 0-1)*g.n 0 +
        (E.Vj+K.chain.R+D.a 1)*g.n 1 +
        (E.Vk+K.chain.alpha-D.rho 2)*g.n 2 := by
      linear_combination he + hr - g.n 0
    exact frobenius_of_four hF hf (by omega) (by omega) (by omega) (by omega)
  have cjcap : E.Cj + K.chain.T < D.rho 2 := by
    by_contra hh
    have he := K.FJ E
    have hr := D.relation_two
    have hf : F = (E.Lj-1)*g.m + (E.Aj+K.chain.delta+D.b 0)*g.n 0 +
        (D.a 1-1)*g.n 1 + (E.Cj+K.chain.T-D.rho 2)*g.n 2 := by
      linear_combination he + hr - g.n 1
    exact frobenius_of_four hF hf (by omega) (by omega) (by omega) (by omega)
  have ajcap : E.Aj ≤ K.d-1 := by
    by_contra hh
    have he := E.Qj_eq
    have hf : K.chain.qJ = (E.Lj-1)*g.m + (E.Aj-K.d)*g.n 0 +
        (K.S-1)*g.n 1 + (E.Cj+K.Croot)*g.n 2 := by
      linear_combination he + K.root - g.n 1
    exact gap_of_four hqJ hf (by omega) (by omega) (by omega) (by omega)
  have akcap : E.Ak ≤ K.d-1 := by
    by_contra hh
    have he := E.Qk_eq
    have hf : K.chain.qK = (E.Lk-1)*g.m + (E.Ak-K.d)*g.n 0 +
        (E.Bk+K.S)*g.n 1 + (K.Croot-1)*g.n 2 := by
      linear_combination he + K.root - g.n 2
    exact gap_of_four hqK hf (by omega) (by omega) (by omega) (by omega)
  have rootUj : E.Uj + K.S < D.rho 1 := by
    by_contra hh
    have he := E.EA_eq
    have hr := D.relation_one
    have hf : K.chain.qA = (E.Li-1)*g.m + (D.a 0-K.d-1)*g.n 0 +
        (E.Uj+K.S-D.rho 1)*g.n 1 + (E.Uk+K.Croot+D.b 2)*g.n 2 := by
      linear_combination he + K.root + hr
    exact gap_of_four hqA hf (by omega)
      (by have := K.chain.lambda_range.2.1; omega) (by omega) (by omega)
  have rootUk : E.Uk + K.Croot < D.rho 2 := by
    by_contra hh
    have he := E.EA_eq
    have hr := D.relation_two
    have hf : K.chain.qA = (E.Li-1)*g.m + (D.b 0-K.d-1)*g.n 0 +
        (E.Uj+K.S+D.a 1)*g.n 1 + (E.Uk+K.Croot-D.rho 2)*g.n 2 := by
      linear_combination he + K.root + hr
    exact gap_of_four hqA hf (by omega)
      (by have := K.chain.lambda_range.2.2; omega) (by omega) (by omega)
  have rootVj : E.Vj + K.S < D.rho 1 := by
    by_contra hh
    have he := E.EB_eq
    have hr := D.relation_one
    have hf : K.chain.qB = (E.Lb-1)*g.m + (D.a 0-K.d-1)*g.n 0 +
        (E.Vj+K.S-D.rho 1)*g.n 1 + (E.Vk+K.Croot+D.b 2)*g.n 2 := by
      linear_combination he + K.root + hr
    exact gap_of_four hqB hf (by omega)
      (by have := K.chain.lambda_range.2.1; omega) (by omega) (by omega)
  have rootVk : E.Vk + K.Croot < D.rho 2 := by
    by_contra hh
    have he := E.EB_eq
    have hr := D.relation_two
    have hf : K.chain.qB = (E.Lb-1)*g.m + (D.b 0-K.d-1)*g.n 0 +
        (E.Vj+K.S+D.a 1)*g.n 1 + (E.Vk+K.Croot-D.rho 2)*g.n 2 := by
      linear_combination he + K.root + hr
    exact gap_of_four hqB hf (by omega)
      (by have := K.chain.lambda_range.2.2; omega) (by omega) (by omega)
  exact ⟨ufi, ukfi, vfi, vkfi, cjcap, ajcap, akcap,
    rootUj, rootUk, rootVj, rootVk⟩

end ChainCore
end P21.Nonsymmetric
