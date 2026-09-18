import P21.Nonsymmetric.Chain.C9.DSetup

set_option maxHeartbeats 1200000

namespace P21.Nonsymmetric.ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns}
variable {hF : s.semigroup.IsFrobenius F}

theorem nZeta_increment (RD : A.RegionD E hF) (hJ : K.J0<0) (zeta : ℤ) :
    K.nZeta (zeta+1)-K.nZeta zeta=K.h ∨
      K.nZeta (zeta+1)-K.nZeta zeta=K.h+1 := by
  let dn := K.nZeta (zeta+1)-K.nZeta zeta
  have hi0 := (K.IZeta_bounds zeta).1
  have hi1 := (K.IZeta_bounds zeta).2
  have hj0 := (K.IZeta_bounds (zeta+1)).1
  have hj1 := (K.IZeta_bounds (zeta+1)).2
  have hai := RD.ai_eq
  have hd := K.d_range.1
  have hb := (RD.b_range hJ).1
  have hbd := (RD.b_range hJ).2.2
  have heq : K.IZeta (zeta+1)-K.IZeta zeta=dn*K.d-(D.a 0 : ℤ) := by
    simp only [IZeta, dn]
    ring
  have hlow : K.h≤dn := by
    by_contra hn
    have hm : dn≤K.h-1 := by omega
    have hmul := mul_le_mul_of_nonneg_right hm (show 0≤K.d by omega)
    rw [hai] at heq
    nlinarith
  have hupp : dn≤K.h+1 := by
    by_contra hn
    have hm : K.h+2≤dn := by omega
    have hmul := mul_le_mul_of_nonneg_right hm (show 0≤K.d by omega)
    rw [hai] at heq
    nlinarith
  dsimp [dn] at hlow hupp ⊢
  omega

namespace FirstFit.RegionD

theorem zhat_ge_two (RD : A.RegionD E hF) (hJ : K.J0<0) : 2≤A.zhat := by
  have hz := A.zhat_range.1
  by_contra hn
  have heq : A.zhat=1 := by omega
  have hfit := A.J_nonneg
  rw [A.J_eq, heq] at hfit
  have hj1 : K.JZeta 1 = K.J0 := by
    simp [JZeta, J0, K.nZeta_one]
    ring
  rw [hj1] at hfit
  omega

theorem last_increment (RD : A.RegionD E hF) (hJ : K.J0<0) :
    K.nZeta A.zhat-K.nZeta (A.zhat-1)=K.h := by
  have hz := RD.zhat_ge_two hJ
  have halt := K.nZeta_increment RD hJ (A.zhat-1)
  have hpred := A.predecessor (by omega)
  have hfit := A.J_nonneg
  have htau := (RD.tau_range hJ).2
  have hg := K.chain.scalar_ranges.2.2.1
  rcases halt with hh | hh
  · simpa only [sub_add_cancel] using hh
  · have hh' : K.nZeta A.zhat-K.nZeta (A.zhat-1)=K.h+1 := by
      simpa only [sub_add_cancel] using hh
    have hdiff : K.JZeta A.zhat-K.JZeta (A.zhat-1)=K.Dtau-K.S := by
      simp only [JZeta, ChainCore.Dtau]
      linear_combination -K.S*hh'
    rw [A.J_eq] at hfit
    nlinarith

theorem sharp_caps (RD : A.RegionD E hF) (hJ : K.J0<0) :
    0≤A.J ∧ A.J≤K.Dtau-1 ∧ 0≤A.I ∧ A.I≤K.d-K.Db-1 := by
  have hz := RD.zhat_ge_two hJ
  have hinc := RD.last_increment hJ
  have hpred := A.predecessor (by omega)
  have hJdiff : A.J-K.JZeta (A.zhat-1)=K.Dtau := by
    rw [A.J_eq]
    simp only [JZeta, ChainCore.Dtau]
    linear_combination -K.S*hinc
  have hIdiff : A.I-K.IZeta (A.zhat-1)=-K.Db := by
    rw [A.I_eq]
    simp only [IZeta]
    have hai := RD.ai_eq
    have hb : K.Db=K.r+K.chain.delta := rfl
    rw [hb]
    linear_combination K.d*hinc-hai-hb
  have hprevI := (K.IZeta_bounds (A.zhat-1)).2
  exact ⟨A.J_nonneg,by omega,A.I_bounds.1,by omega⟩

theorem I_e0_cap (RD : A.RegionD E hF) (hJ : K.J0<0) :
    A.I≤K.e0-K.chain.delta-1 := by
  have h := (RD.sharp_caps hJ).2.2.2
  have Eu := K.euclidean
  rw [Eu.e0_eq]
  simp only [ChainCore.Db] at h ⊢
  omega

theorem NV_identity (RD : A.RegionD E hF) :
    A.N*K.DV=(D.rho 1 : ℤ)*(A.I-K.chain.delta+1)+
      (D.a 0 : ℤ)*(A.J-K.chain.gapJ+1) := by
  rw [A.N_eq, A.I_eq, A.J_eq]
  simp only [IZeta, JZeta, ChainCore.DV]
  ring

theorem zV_identity (RD : A.RegionD E hF) :
    A.zhat*K.DV=K.S*(A.I-K.chain.delta+1)+
      K.d*(A.J-K.chain.gapJ+1) := by
  rw [A.I_eq, A.J_eq]
  simp only [IZeta, JZeta, ChainCore.DV]
  ring

theorem first_bounds (RD : A.RegionD E hF) (hJ : K.J0<0) :
    A.N*K.DV≤K.h*K.DV+(K.d-K.chain.delta)*(D.rho 1 : ℤ)-
      (D.a 0 : ℤ)*K.chain.gapJ ∧
    (A.zhat-1)*K.DV≤K.S*(K.d-K.chain.delta)-K.d*K.chain.gapJ := by
  have hc := RD.sharp_caps hJ
  have hai : (0:ℤ)<D.a 0 := by exact_mod_cast D.a_pos 0
  have hrj : (0:ℤ)<D.rho 1 := by exact_mod_cast D.rho_pos 1
  have hNV := RD.NV_identity
  have hzV := RD.zV_identity
  have hIpart : A.I-K.chain.delta+1≤K.d-K.Db-K.chain.delta := by omega
  have hJpart : A.J-K.chain.gapJ+1≤K.Dtau-K.chain.gapJ := by omega
  have hIterm := mul_le_mul_of_nonneg_left hIpart (le_of_lt hrj)
  have hJterm := mul_le_mul_of_nonneg_left hJpart (le_of_lt hai)
  have hSI := mul_le_mul_of_nonneg_left hIpart (show 0≤K.S by
    have := K.S_strong; have := K.chain.scalar_ranges.2.2.1; omega)
  have hdJ := mul_le_mul_of_nonneg_left hJpart (show 0≤K.d by
    have := K.d_range.1
    omega)
  constructor
  · have hupper : A.N*K.DV≤
        (D.rho 1 : ℤ)*(K.d-K.Db-K.chain.delta)+
          (D.a 0 : ℤ)*(K.Dtau-K.chain.gapJ) := by
      nlinarith
    have hid :
        (D.rho 1 : ℤ)*(K.d-K.Db-K.chain.delta)+
            (D.a 0 : ℤ)*(K.Dtau-K.chain.gapJ) =
          K.h*K.DV+(K.d-K.chain.delta)*(D.rho 1 : ℤ)-
            (D.a 0 : ℤ)*K.chain.gapJ := by
      rw [RD.ai_eq, RD.rhoj_eq, RD.V_eq]
      ring
    rw [hid] at hupper
    exact hupper
  · have hupper : A.zhat*K.DV≤
        K.S*(K.d-K.Db-K.chain.delta)+
          K.d*(K.Dtau-K.chain.gapJ) := by
      nlinarith
    have hid :
        K.S*(K.d-K.Db-K.chain.delta)+K.d*(K.Dtau-K.chain.gapJ)-K.DV =
          K.S*(K.d-K.chain.delta)-K.d*K.chain.gapJ := by
      rw [RD.V_eq]
      simp only [ChainCore.Db]
      ring
    nlinarith

end FirstFit.RegionD
end P21.Nonsymmetric.ChainCore
