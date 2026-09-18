import P21.Nonsymmetric.Chain.Intrinsic

namespace P21.Nonsymmetric
namespace ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

theorem hS_lt_rho (K : ChainCore s F D) : K.h * K.S < D.rho 1 := by
  have E := K.euclidean
  have L := K.slopes
  have hhd : K.h*K.d ≤ K.chain.lambda := by nlinarith [E.lambda_eq, E.r_range.1]
  have hda : K.chain.lambda < D.a 0 := K.chain.lambda_range.2.1
  have ha : (0 : ℤ) < D.a 0 := by exact_mod_cast D.a_pos 0
  have hr : (0 : ℤ) < D.rho 1 := by exact_mod_cast D.rho_pos 1
  have hhp := E.h_pos
  have hh : 0 < K.h := by omega
  have hsl : K.S * D.a 0 < K.d * D.rho 1 := by nlinarith [L.j_pos]
  have hmul := mul_lt_mul_of_pos_left hsl hh
  have hbound := mul_le_mul_of_nonneg_right hhd hr.le
  have hstrict := mul_lt_mul_of_pos_right hda hr
  by_contra hn
  have hrev : (D.rho 1 : ℤ) ≤ K.h*K.S := by omega
  have hrev' := mul_le_mul_of_nonneg_right hrev ha.le
  nlinarith

theorem hC_lt_rho (K : ChainCore s F D) : K.h * K.Croot < D.rho 2 := by
  have E := K.euclidean
  have L := K.slopes
  have hhd : K.h*K.d ≤ K.chain.lambda := by nlinarith [E.lambda_eq, E.r_range.1]
  have hdb : K.chain.lambda < D.b 0 := K.chain.lambda_range.2.2
  have hb : (0 : ℤ) < D.b 0 := by exact_mod_cast D.b_pos 0
  have hr : (0 : ℤ) < D.rho 2 := by exact_mod_cast D.rho_pos 2
  have hhp := E.h_pos
  have hh : 0 < K.h := by omega
  have hsl : K.Croot * D.b 0 < K.d * D.rho 2 := by nlinarith [L.k_pos]
  have hmul := mul_lt_mul_of_pos_left hsl hh
  have hbound := mul_le_mul_of_nonneg_right hhd hr.le
  have hstrict := mul_lt_mul_of_pos_right hdb hr
  by_contra hn
  have hrev : (D.rho 2 : ℤ) ≤ K.h*K.Croot := by omega
  have hrev' := mul_le_mul_of_nonneg_right hrev hb.le
  nlinarith

theorem QM (K : ChainCore s F D) :
    K.q0 * g.m = ((D.rho 0 : ℤ)-K.q0*K.d)*g.n 0 +
      (K.q0*K.S-D.b 1)*g.n 1 + (K.q0*K.Croot-D.a 2)*g.n 2 := by
  linear_combination K.q0 * K.root - D.relation_zero

theorem J0_forces_k_fit (K : ChainCore s F D) (hJ : K.J0 < 0) :
    K.q0*K.Croot ≤ (D.a 2 : ℤ)-1 := by
  by_contra hn
  have E := K.euclidean
  have hg := K.rho_gap_nonneg
  have hq := E.q0_pos
  have hR : K.chain.R = D.a 1 + K.chain.gapJ := K.chain.R_exact
  have hr1 : (D.rho 1 : ℤ) = D.a 1 + D.b 1 := by exact_mod_cast D.rho_eq 1
  have hi : K.q0 ≤ (D.rho 0 : ℤ)-K.q0*K.d := by omega
  have hj : 1 ≤ K.q0*K.S-D.b 1 := by
    simp [J0] at hJ
    have ha : (1 : ℤ) ≤ D.a 1 := by exact_mod_cast D.a_pos 1
    have hg := K.chain.scalar_ranges.2.2.1
    nlinarith [hr1]
  have hk : 0 ≤ K.q0*K.Croot-D.a 2 := by omega
  have hp : ∀ i, 0 < g.n i := fun i => lt_trans s.m_pos (s.n_gt i)
  have hiTerm := mul_le_mul_of_nonneg_right hi (hp 0).le
  have hjTerm := mul_pos hj (hp 1)
  have hkTerm := mul_nonneg hk (hp 2).le
  have hm := s.n_gt 0
  have eq := K.QM
  nlinarith

theorem K0_forces_j_fit (K : ChainCore s F D) (hK : K.K0 < 0) :
    K.q0*K.S ≤ (D.b 1 : ℤ)-1 := by
  by_contra hn
  have E := K.euclidean
  have hg := K.rho_gap_nonneg
  have hq := E.q0_pos
  have hT : K.chain.T = D.b 2 + K.chain.alpha := K.chain.T_exact
  have hr2 : (D.rho 2 : ℤ) = D.a 2 + D.b 2 := by exact_mod_cast D.rho_eq 2
  have hi : K.q0 ≤ (D.rho 0 : ℤ)-K.q0*K.d := by omega
  have hj : 0 ≤ K.q0*K.S-D.b 1 := by omega
  have hk : 1 ≤ K.q0*K.Croot-D.a 2 := by
    simp [K0] at hK
    have hb : (1 : ℤ) ≤ D.b 2 := by exact_mod_cast D.b_pos 2
    have ha := K.chain.scalar_ranges.2.2.2
    nlinarith [hr2]
  have hp : ∀ i, 0 < g.n i := fun i => lt_trans s.m_pos (s.n_gt i)
  have hiTerm := mul_le_mul_of_nonneg_right hi (hp 0).le
  have hjTerm := mul_nonneg hj (hp 1).le
  have hkTerm := mul_pos hk (hp 2)
  have hm := s.n_gt 0
  have eq := K.QM
  nlinarith

theorem deficiencies_exclusive (K : ChainCore s F D) :
    ¬ (K.J0 < 0 ∧ K.K0 < 0) := by
  rintro ⟨hJ,hK⟩
  have hC := K.J0_forces_k_fit hJ
  simp [K0] at hK
  have hr2 : (D.rho 2 : ℤ) = D.a 2 + D.b 2 := by exact_mod_cast D.rho_eq 2
  have hb := D.b_pos 2
  have ha := K.chain.scalar_ranges.2.2.2
  omega

theorem K0_strict_root (K : ChainCore s F D) (hK : K.K0 < 0) :
    K.chain.alpha + 1 ≤ K.Croot := by
  have hhc := K.hC_lt_rho
  have E := K.euclidean
  have hHC : K.h*K.Croot ≤ (D.rho 2 : ℤ)-1 := by omega
  have hneg : 1 ≤ -K.K0 := by omega
  have hupper : -K.K0 ≤ K.Croot-K.chain.alpha := by
    simp [K0, q0]
    nlinarith
  omega

def reverseCore (K : ChainCore s F D) (h : K.chain.alpha + 1 ≤ K.Croot) :
    ChainCore (relabelSetting s reversePerm) F (reverseHerzog D) where
  chain := K.chain.reverseChain
  d := K.d
  S := K.Croot
  Croot := K.S
  root := by simpa [relabel, reversePerm, add_comm, add_left_comm, add_assoc] using K.root
  d_range := by simpa using K.d_range
  S_strong := by simpa using h
  C_lower := by
    have hS := K.S_strong
    have hs : K.chain.gapJ ≤ K.S := by omega
    simpa using hs

@[simp] theorem reverseCore_h (K : ChainCore s F D)
    (h : K.chain.alpha+1 ≤ K.Croot) : (K.reverseCore h).h = K.h := rfl
@[simp] theorem reverseCore_q0 (K : ChainCore s F D)
    (h : K.chain.alpha+1 ≤ K.Croot) : (K.reverseCore h).q0 = K.q0 := rfl
@[simp] theorem reverseCore_J0 (K : ChainCore s F D)
    (h : K.chain.alpha+1 ≤ K.Croot) : (K.reverseCore h).J0 = K.K0 := rfl

inductive IntrinsicOrientation (K : ChainCore s F D) : Type
  | direct (hJ : K.J0 < 0)
  | reversed (h : K.chain.alpha+1 ≤ K.Croot)
      (hJ : (K.reverseCore h).J0 < 0)

def orientIntrinsic (K : ChainCore s F D) (hF : s.semigroup.IsFrobenius F) :
    K.IntrinsicOrientation := by
  by_cases hJ : K.J0 < 0
  · exact .direct hJ
  · have hK : K.K0 < 0 := (K.second_deficient hF).resolve_left hJ
    let hs := K.K0_strict_root hK
    exact .reversed hs (by simpa using hK)

end ChainCore
end P21.Nonsymmetric
