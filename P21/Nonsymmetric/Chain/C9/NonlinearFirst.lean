import P21.Nonsymmetric.Chain.C9.HighQ

set_option maxHeartbeats 1200000

namespace P21.Nonsymmetric.ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns}
variable {hF : s.semigroup.IsFrobenius F}

def Dkappa (K : ChainCore s F D) : ℤ :=
  (K.d+K.chain.delta-1)/K.Db

def Drprime (K : ChainCore s F D) : ℤ :=
  K.d-K.Dkappa*K.Db

def DA1 (K : ChainCore s F D) : ℤ :=
  ((K.Dkappa+1)*K.Db+K.chain.beta)*K.S+
    (K.chain.beta-K.Drprime)*K.Dtau+(D.a 0 : ℤ)*K.chain.R

def DB1 (K : ChainCore s F D) : ℤ :=
  (K.Dkappa*K.Db+K.chain.beta)*K.S+K.d*K.chain.R

def DES (K : ChainCore s F D) : ℤ :=
  (4*K.Dkappa+2)*K.Db+4*K.chain.beta+K.chain.delta-K.Drprime

def DEtau (K : ChainCore s F D) : ℤ :=
  -K.Db+3*K.chain.beta+K.chain.delta-4*K.Drprime

def DEc (K : ChainCore s F D) : ℤ :=
  (D.a 1 : ℤ)*((4*K.Dkappa+3)*K.Db+4*K.Drprime)+
  K.chain.gapJ*((5*K.Dkappa+4)*K.Db+5*K.Drprime)

namespace FirstFit.RegionD

theorem small_nZeta (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hh : K.h=1) {v : ℤ} (hv : 1≤v) (hvk : v≤K.Dkappa) :
    K.nZeta v=v+1 := by
  have hb := (RD.b_range hJ).1
  have hd := K.d_range.1
  have hmul := Int.ediv_mul_le (K.d+K.chain.delta-1) (show K.Db≠0 by omega)
  have hvb : v*K.Db≤K.d+K.chain.delta-1 := by
    have hm := mul_le_mul_of_nonneg_right hvk (show 0≤K.Db by omega)
    simpa only [Dkappa] using le_trans hm hmul
  have hlow : 0≤v*K.Db-K.chain.delta := by
    have hDb : K.Db=K.r+K.chain.delta := rfl
    have hr := K.euclidean.r_range.1
    rw [hDb]
    nlinarith [mul_nonneg (show 0≤v-1 by omega)
      (show 0≤K.r+K.chain.delta by omega)]
  have hai := RD.ai_eq
  have hquot : (v*(D.a 0 : ℤ)-K.chain.delta)/K.d=v := by
    rw [Int.ediv_eq_iff_of_pos (show 0<K.d by omega)]
    constructor
    · rw [hai, hh]
      nlinarith
    · rw [hai, hh]
      nlinarith
  simp only [nZeta, hquot]

theorem kappa_pos (RD : A.RegionD E hF) (hJ : K.J0<0) : 1≤K.Dkappa := by
  have hb := (RD.b_range hJ).1
  rw [Dkappa, Int.le_ediv_iff_mul_le (show 0<K.Db by omega)]
  have hdelta := K.chain.scalar_ranges.1
  have hbd := (RD.b_range hJ).2.2
  omega

theorem kappa_lt_zhat (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hh : K.h=1) (hnonlin : A.zhat+2≤A.N) : K.Dkappa<A.zhat := by
  by_contra hn
  have hz := A.zhat_range.1
  have heq := RD.small_nZeta hJ hh hz (by omega)
  rw [A.N_eq, heq] at hnonlin
  omega

theorem prefix_shortage (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hh : K.h=1) (hnonlin : A.zhat+2≤A.N) :
    K.Dkappa*K.Dtau+K.chain.gapJ≤K.S := by
  have hk := RD.kappa_pos hJ
  have hkz := RD.kappa_lt_zhat hJ hh hnonlin
  have hjk : K.JZeta K.Dkappa<0 := by
    by_contra hn
    have hm := A.minimal K.Dkappa hk (by omega)
    omega
  have hn := RD.small_nZeta hJ hh hk le_rfl
  have hrho := RD.rhoj_eq
  simp only [JZeta] at hjk
  rw [hn, hrho, hh] at hjk
  nlinarith

theorem small_r (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hh : K.h=1) (hnonlin : A.zhat+2≤A.N) :
    1≤K.Drprime ∧ K.Drprime≤K.Db-K.chain.delta := by
  have hb := (RD.b_range hJ).1
  have hk := RD.kappa_pos hJ
  have hprefix := RD.prefix_shortage hJ hh hnonlin
  have hv := RD.V_pos
  have hveq := RD.V_eq
  have ht := (RD.tau_range hJ).1
  have hg := K.chain.scalar_ranges.2.2.1
  have hrpos : 0<K.Drprime := by
    simp only [Drprime] at ⊢
    by_contra hn
    have hst : 0≤K.S-K.Dkappa*K.Dtau := by omega
    have hp := mul_nonneg (show 0≤K.Db by omega) hst
    rw [hveq] at hv
    nlinarith
  have hupper : K.d+K.chain.delta-1<(K.Dkappa+1)*K.Db := by
    apply (Int.ediv_lt_iff_lt_mul (show 0<K.Db by omega)).1
    simp only [Dkappa]
    omega
  rw [show (K.Dkappa+1)*K.Db=K.Dkappa*K.Db+K.Db by ring] at hupper
  constructor
  · omega
  · simp only [Drprime]
    omega

private theorem nZeta_le_of_candidate {zeta n : ℤ}
    (hI : 0≤K.chain.delta-1+n*K.d-zeta*(D.a 0 : ℤ)) :
    K.nZeta zeta≤n := by
  have hd := K.d_range.1
  have hq : (zeta*(D.a 0 : ℤ)-K.chain.delta)/K.d<n := by
    rw [Int.ediv_lt_iff_lt_mul (show 0<K.d by omega)]
    nlinarith
  simp only [nZeta]
  omega

theorem nonlinear_I_cap (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hh : K.h=1) (hnonlin : A.zhat+2≤A.N) :
    0≤A.I ∧ A.I≤K.Drprime-1 := by
  refine ⟨A.I_bounds.1, ?_⟩
  by_contra hn
  have hk := RD.kappa_pos hJ
  have hkz := RD.kappa_lt_zhat hJ hh hnonlin
  have hprefix := RD.prefix_shortage hJ hh hnonlin
  let zp : ℤ := A.zhat-K.Dkappa
  let np : ℤ := A.N-K.Dkappa-1
  let ip : ℤ := K.chain.delta-1+np*K.d-zp*(D.a 0 : ℤ)
  let jp : ℤ := K.chain.gapJ-1+zp*(D.rho 1 : ℤ)-np*K.S
  have hai := RD.ai_eq
  have hrho := RD.rhoj_eq
  have hip : ip=A.I-K.Drprime := by
    dsimp [ip, np, zp, Drprime]
    rw [A.I_eq]
    simp only [IZeta]
    rw [A.N_eq, hai, hh]
    ring
  have hjp : jp=A.J+K.S-K.Dkappa*K.Dtau := by
    dsimp [jp, np, zp]
    rw [A.J_eq]
    simp only [JZeta]
    rw [A.N_eq, hrho, hh]
    ring
  have hip0 : (0 : ℤ) ≤ ip := by
    rw [hip]
    omega
  have hjp0 : (0 : ℤ) ≤ jp := by
    have hgap0 : 0≤K.chain.gapJ := by
      have := K.chain.scalar_ranges.2.2.1
      omega
    have hkt : K.Dkappa*K.Dtau≤K.Dkappa*K.Dtau+K.chain.gapJ :=
      le_add_of_nonneg_right hgap0
    have hrest : 0≤K.S-K.Dkappa*K.Dtau :=
      sub_nonneg.mpr (le_trans hkt hprefix)
    have hsum : 0≤A.J+(K.S-K.Dkappa*K.Dtau) :=
      add_nonneg A.J_nonneg hrest
    rw [hjp]
    nlinarith
  have hnle : K.nZeta zp≤np := nZeta_le_of_candidate hip0
  have hS : 0≤K.S := by
    have := K.S_strong
    have := K.chain.scalar_ranges.2.2.1
    omega
  have hjfit : 0≤K.JZeta zp := by
    have hdiff : K.JZeta zp=jp+(np-K.nZeta zp)*K.S := by
      dsimp [jp]
      simp only [JZeta]
      ring
    rw [hdiff]
    exact add_nonneg hjp0 (mul_nonneg (by omega) hS)
  have hzppos : 1≤zp := by dsimp [zp]; omega
  have hmin := A.minimal zp hzppos hjfit
  dsimp [zp] at hmin
  omega

theorem nonlinear_lower_bounds (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hh : K.h=1) (hnonlin : A.zhat+2≤A.N) :
    K.DA1≤K.DAmul A ∧ K.DB1≤K.DBmul A := by
  have hc := RD.nonlinear_I_cap hJ hh hnonlin
  have hjc := (RD.sharp_caps hJ).2.1
  have hrj : (0:ℤ)<D.rho 1 := by exact_mod_cast D.rho_pos 1
  have hai : (0:ℤ)<D.a 0 := by exact_mod_cast D.a_pos 0
  have hS : 0≤K.S := by
    have := K.S_strong
    have := K.chain.scalar_ranges.2.2.1
    omega
  have hd : 0≤K.d := by have := K.d_range.1; omega
  have hIp : A.I-K.chain.delta+1≤K.Drprime-K.chain.delta := by omega
  have hJp : A.J-K.chain.gapJ+1≤K.Dtau-K.chain.gapJ := by omega
  have hri := mul_le_mul_of_nonneg_left hIp (le_of_lt hrj)
  have haj := mul_le_mul_of_nonneg_left hJp (le_of_lt hai)
  have hsi := mul_le_mul_of_nonneg_left hIp hS
  have hdj := mul_le_mul_of_nonneg_left hJp hd
  have hNV := RD.NV_identity
  have hzV := RD.zV_identity
  have hAraw : K.DKcal-(D.rho 1 : ℤ)*(K.Drprime-K.chain.delta)-
      (D.a 0 : ℤ)*(K.Dtau-K.chain.gapJ)≤K.DAmul A := by
    simp only [DAmul]
    nlinarith
  have hBraw : K.DDj-(K.S*(K.Drprime-K.chain.delta)+
      K.d*(K.Dtau-K.chain.gapJ)-K.DV)≤K.DBmul A := by
    simp only [DBmul]
    nlinarith
  have hAeq : K.DKcal-(D.rho 1 : ℤ)*(K.Drprime-K.chain.delta)-
      (D.a 0 : ℤ)*(K.Dtau-K.chain.gapJ)=K.DA1 := by
    have hbi := RD.bi_eq
    have haieq := RD.ai_eq
    have hrho := RD.rhoj_eq
    have hR := K.chain.R_exact
    simp only [DKcal, DA1]
    rw [hbi, haieq, hrho, hR, hh]
    simp only [ChainCore.Db, ChainCore.Dc, Drprime]
    ring
  have hBeq : K.DDj-(K.S*(K.Drprime-K.chain.delta)+
      K.d*(K.Dtau-K.chain.gapJ)-K.DV)=K.DB1 := by
    have hbi := RD.bi_eq
    have hV := RD.V_eq
    have hR := K.chain.R_exact
    simp only [ChainCore.DDj, DB1]
    rw [hbi, hV, hR, hh]
    simp only [ChainCore.Db, ChainCore.Dc, Drprime]
    ring
  exact ⟨by rw [←hAeq]; exact hAraw, by rw [←hBeq]; exact hBraw⟩

theorem nonlinear_A1_B1_pos (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hh : K.h=1) (hnonlin : A.zhat+2≤A.N) : 0<K.DA1 ∧ 0<K.DB1 := by
  have hk := RD.kappa_pos hJ
  have hrp := RD.small_r hJ hh hnonlin
  have hprefix := RD.prefix_shortage hJ hh hnonlin
  have ht := (RD.tau_range hJ).1
  have hb := (RD.b_range hJ).1
  have hs := K.chain.scalar_ranges
  have hcoeff : 0<(K.Dkappa+1)*K.Db+K.chain.beta := by
    nlinarith [mul_pos (show 0<K.Dkappa+1 by omega) (show 0<K.Db by omega)]
  have hsum : 0<(K.Dkappa+1)*K.Db+2*K.chain.beta-K.Drprime := by
    have hbd : K.Drprime+K.chain.delta≤K.Db := by omega
    have hkb := mul_pos (show 0<K.Dkappa by omega) (show 0<K.Db by omega)
    nlinarith
  have hst : 0<K.S-K.Dtau := by
    have hu := (RD.tau_range hJ).2
    omega
  have hai : (0:ℤ)<D.a 0 := by exact_mod_cast D.a_pos 0
  have hR : 0<K.chain.R := by
    rw [K.chain.R_exact]
    have haj : (0:ℤ)<D.a 1 := by exact_mod_cast D.a_pos 1
    omega
  constructor
  · simp only [DA1]
    have h1 := mul_pos hst hcoeff
    have h2 := mul_pos (show 0<K.Dtau by omega) hsum
    have h3 := mul_pos hai hR
    nlinarith
  · simp only [DB1]
    have hcb : 0<K.Dkappa*K.Db+K.chain.beta := by
      nlinarith [mul_pos (show 0<K.Dkappa by omega) (show 0<K.Db by omega)]
    have hSpos : 0<K.S := by
      have := K.S_strong
      have := hs.2.2.1
      omega
    have hdpos : 0<K.d := by have := K.d_range.1; omega
    nlinarith [mul_pos hcb hSpos, mul_pos hdpos hR]

theorem nonlinear_bracket_expansion (RD : A.RegionD E hF) (hh : K.h=1) :
    4*K.DA1+K.DB1+K.DV-K.DKcal=
      K.S*K.DES+K.Dtau*K.DEtau+K.DEc := by
  have hbi := RD.bi_eq
  have hai := RD.ai_eq
  have hrho := RD.rhoj_eq
  have hV := RD.V_eq
  have hR := K.chain.R_exact
  simp only [DA1, DB1, DES, DEtau, DEc, DKcal]
  rw [hbi, hai, hrho, hV, hR, hh]
  simp only [ChainCore.Db, ChainCore.Dc, Drprime]
  ring

theorem nonlinear_bracket_pos (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hh : K.h=1) (hnonlin : A.zhat+2≤A.N) :
    0<4*K.DA1+K.DB1+K.DV-K.DKcal := by
  have hk := RD.kappa_pos hJ
  have hrp := RD.small_r hJ hh hnonlin
  have hprefix := RD.prefix_shortage hJ hh hnonlin
  have ht := (RD.tau_range hJ).1
  have hs := K.chain.scalar_ranges
  have hb := (RD.b_range hJ).1
  have hbd : K.Drprime+K.chain.delta≤K.Db := by omega
  have hES : 0<K.DES := by
    simp only [DES]
    have hm := mul_pos (show 0<4*K.Dkappa+2 by omega) (show 0<K.Db by omega)
    nlinarith
  let lower : ℤ :=
    (K.Dkappa-1)*(4*K.Dkappa+5)*K.Drprime+
    K.Dkappa*(4*K.Dkappa+3)*K.chain.delta+
    (4*K.Dkappa+3)*K.chain.beta
  have hcoef : 0≤4*K.Dkappa^2+2*K.Dkappa-1 := by nlinarith
  have hdiff : K.Dkappa*K.DES+K.DEtau-lower=
      (4*K.Dkappa^2+2*K.Dkappa-1)*
        (K.Db-K.Drprime-K.chain.delta) := by
    dsimp [lower]
    simp only [DES, DEtau]
    ring
  have hlower : 0<lower := by
    dsimp [lower]
    have h1 := mul_nonneg
      (mul_nonneg (show 0≤K.Dkappa-1 by omega) (show 0≤4*K.Dkappa+5 by omega))
      (show 0≤K.Drprime by omega)
    have h2 := mul_pos
      (mul_pos (show 0<K.Dkappa by omega) (show 0<4*K.Dkappa+3 by omega))
      (show 0<K.chain.delta by omega)
    have h3 := mul_pos (show 0<4*K.Dkappa+3 by omega)
      (show 0<K.chain.beta by omega)
    nlinarith
  have hsum : 0<K.Dkappa*K.DES+K.DEtau := by
    have hm := mul_nonneg hcoef (show 0≤K.Db-K.Drprime-K.chain.delta by omega)
    nlinarith
  have hSkt : 0<K.S-K.Dkappa*K.Dtau := by
    have hg := hs.2.2.1
    omega
  have hEc : 0<K.DEc := by
    simp only [DEc]
    have haj : (0:ℤ)<D.a 1 := by exact_mod_cast D.a_pos 1
    have hl : 0<(4*K.Dkappa+3)*K.Db+4*K.Drprime := by
      nlinarith [mul_pos (show 0<4*K.Dkappa+3 by omega) (show 0<K.Db by omega)]
    have hr : 0<(5*K.Dkappa+4)*K.Db+5*K.Drprime := by
      nlinarith [mul_pos (show 0<5*K.Dkappa+4 by omega) (show 0<K.Db by omega)]
    nlinarith [mul_pos haj hl, mul_pos (show 0<K.chain.gapJ by omega) hr]
  rw [RD.nonlinear_bracket_expansion hh]
  nlinarith [mul_pos hSkt hES, mul_pos (show 0<K.Dtau by omega) hsum]

theorem nonlinear_first_impossible (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) (hh : K.h=1)
    (hnonlin : A.zhat+2≤A.N) : False := by
  have hl := RD.nonlinear_lower_bounds hJ hh hnonlin
  have hp := RD.nonlinear_A1_B1_pos hJ hh hnonlin
  have hA : 0<K.DAmul A := lt_of_lt_of_le hp.1 hl.1
  have hB : 0<K.DBmul A := lt_of_lt_of_le hp.2 hl.2
  have hbr0 := RD.nonlinear_bracket_pos hJ hh hnonlin
  have hbr : 0<4*K.DAmul A+K.DBmul A+K.DV-K.DKcal := by nlinarith
  have hcfs := RD.master_coefficients
  have hV := RD.V_pos
  have h1 := mul_nonneg hcfs.1 (le_of_lt hA)
  have h2 := mul_nonneg hcfs.2.1 (show 0≤K.DAmul A+K.DBmul A by omega)
  have h3 := mul_nonneg hcfs.2.2.1 (show 0≤2*K.DAmul A+K.DV by omega)
  have h4 := mul_nonneg hcfs.2.2.2 (le_of_lt hV)
  have hm := RD.multiplicity_master
  apply RD.multiplicity_contradiction hc
  nlinarith

theorem N_ge_zhat_add_one (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hh : K.h=1) : A.zhat+1≤A.N := by
  have hz := A.zhat_range.1
  have hb := (RD.b_range hJ).1
  have hai := RD.ai_eq
  rw [A.N_eq]
  simp only [nZeta]
  have hq : A.zhat≤
      (A.zhat*(D.a 0 : ℤ)-K.chain.delta)/K.d := by
    rw [Int.le_ediv_iff_mul_le (show 0<K.d by have := K.d_range.1; omega)]
    rw [hai, hh]
    have hDb : K.Db=K.r+K.chain.delta := rfl
    rw [hDb]
    have hr := K.euclidean.r_range.1
    nlinarith [mul_nonneg (show 0≤A.zhat-1 by omega)
      (show 0≤K.r+K.chain.delta by omega)]
  omega

theorem linear_first_survivor (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) : K.h=1 ∧ A.N=A.zhat+1 := by
  have hh := RD.h_eq_one_of_regionD hJ hc
  have hl := RD.N_ge_zhat_add_one hJ hh
  refine ⟨hh, ?_⟩
  by_contra hn
  exact RD.nonlinear_first_impossible hJ hc hh (by omega)

end FirstFit.RegionD
end P21.Nonsymmetric.ChainCore
