import P21.Nonsymmetric.Chain.C9.MultiplicityMaster

set_option maxHeartbeats 1200000

namespace P21.Nonsymmetric.ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns}
variable {hF : s.semigroup.IsFrobenius F}

def DA0 (K : ChainCore s F D) : ℤ :=
  K.DKcal-K.h*K.DV-(K.d-K.chain.delta)*(D.rho 1 : ℤ)+
    (D.a 0 : ℤ)*K.chain.gapJ

def DB0 (K : ChainCore s F D) : ℤ :=
  K.d*K.chain.R+K.S*(K.chain.P-K.d)

def DAS (K : ChainCore s F D) : ℤ :=
  K.h*((K.h-1)*K.d+K.chain.beta+2*K.chain.delta+2*K.r)

def DAtau (K : ChainCore s F D) : ℤ :=
  K.chain.beta-K.d+K.chain.delta+K.r

def DHS (K : ChainCore s F D) : ℤ :=
  (3*K.h^2-3*K.h-1)*K.d+(3*K.h+1)*K.chain.beta+
    8*K.h*K.chain.delta+7*K.h*K.r

def DHtau (K : ChainCore s F D) : ℤ :=
  3*K.chain.beta-(K.h+3)*K.d+4*K.chain.delta+3*K.r

def DHc (K : ChainCore s F D) : ℤ :=
  (D.a 1 : ℤ)*((3*K.h+1)*K.d+3*(K.chain.delta+K.r))+
  K.chain.gapJ*((4*K.h+1)*K.d+4*(K.chain.delta+K.r))

namespace FirstFit.RegionD

theorem high_lower_bounds (RD : A.RegionD E hF) (hJ : K.J0<0) :
    K.DA0≤K.DAmul A ∧ K.DB0≤K.DBmul A := by
  have hf := RD.first_bounds hJ
  constructor
  · simp only [DA0, DAmul]
    nlinarith
  · have hDj := K.chain.R_exact
    have hP := K.chain.P_eq_b_delta
    have hbi := RD.bi_eq
    simp only [DB0, DBmul, ChainCore.DDj]
    rw [hDj, hP, hbi]
    nlinarith

theorem B0_pos (RD : A.RegionD E hF) (hh : 2≤K.h) : 0<K.DB0 := by
  have Eu := K.euclidean
  have hs := K.chain.scalar_ranges
  have hdelta := hs.1
  have hbeta := hs.2.1
  have hr := Eu.r_range.1
  have hS := K.S_strong
  have hd := K.d_range.1
  have hR : 1≤K.chain.R := by
    rw [K.chain.R_exact]
    have ha : (1:ℤ)≤D.a 1 := by exact_mod_cast D.a_pos 1
    omega
  have hp := K.chain.P_exact'
  have hpd : 0<K.chain.P-K.d := by
    rw [hp, Eu.lambda_eq]
    have hm := mul_pos (show 0<K.h-1 by omega) (show 0<K.d by omega)
    calc
      0 < (K.h-1)*K.d+K.r+K.chain.delta+K.chain.beta := by omega
      _ = K.h*K.d+K.r+K.chain.delta+K.chain.beta-K.d := by ring
  simp only [DB0]
  nlinarith [mul_pos (show 0<K.d by omega) (show 0<K.chain.R by omega),
    mul_pos (show 0<K.S by omega) hpd]

theorem A0_expansion (RD : A.RegionD E hF) :
    K.DA0=K.S*K.DAS+K.Dtau*K.DAtau+(D.a 0 : ℤ)*K.chain.R := by
  have hbi := RD.bi_eq
  have hai := RD.ai_eq
  have hrho := RD.rhoj_eq
  have hV := RD.V_eq
  have hR := K.chain.R_exact
  have Eu := K.euclidean
  simp only [DA0, DKcal, DAS, DAtau]
  rw [hbi, hai, hrho, hV, hR]
  simp only [ChainCore.Db, ChainCore.Dc]
  ring

theorem AS_plus_Atau (RD : A.RegionD E hF) :
    K.DAS+K.DAtau=(K.h*(K.h-1)-1)*K.d+
      (K.h+1)*K.chain.beta+(2*K.h+1)*(K.chain.delta+K.r) := by
  simp only [DAS, DAtau]
  ring

theorem A0_pos (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hh : 2≤K.h) : 0<K.DA0 := by
  have ht := RD.tau_range hJ
  have hst : 0<K.S-K.Dtau := by
    have hg := K.chain.scalar_ranges.2.2.1
    omega
  have hs := K.chain.scalar_ranges
  have hd := K.d_range.1
  have hr := K.euclidean.r_range.1
  have hAS : 0<K.DAS := by
    simp only [DAS]
    have hin : 0<(K.h-1)*K.d+K.chain.beta+2*K.chain.delta+2*K.r := by
      nlinarith [mul_pos (show 0<K.h-1 by omega) (show 0<K.d by omega)]
    nlinarith [mul_pos (show 0<K.h by omega) hin]
  have hsum : 0<K.DAS+K.DAtau := by
    rw [RD.AS_plus_Atau]
    have hcoef : 0≤K.h*(K.h-1)-1 := by nlinarith
    have hm := mul_nonneg hcoef (show 0≤K.d by omega)
    nlinarith [mul_pos (show 0<K.h+1 by omega) (show 0<K.chain.beta by omega),
      mul_pos (show 0<2*K.h+1 by omega)
        (show 0<K.chain.delta+K.r by omega)]
  have hai : (0:ℤ)<D.a 0 := by exact_mod_cast D.a_pos 0
  have hR : 0<K.chain.R := by
    rw [K.chain.R_exact]
    have haj : (0:ℤ)<D.a 1 := by exact_mod_cast D.a_pos 1
    omega
  rw [RD.A0_expansion]
  have h1 := mul_pos hst hAS
  have h2 := mul_pos (show 0<K.Dtau by omega) hsum
  have h3 := mul_pos hai hR
  nlinarith

theorem high_bracket_expansion (RD : A.RegionD E hF) :
    4*K.DA0+K.DB0+K.DV-K.DKcal=
      K.S*K.DHS+K.Dtau*K.DHtau+K.DHc := by
  have hbi := RD.bi_eq
  have hai := RD.ai_eq
  have hrho := RD.rhoj_eq
  have hV := RD.V_eq
  have hR := K.chain.R_exact
  have hP := K.chain.P_exact'
  have Eu := K.euclidean
  simp only [DA0, DB0, DKcal, DHS, DHtau, DHc]
  rw [hbi, hai, hrho, hV, hR, hP, Eu.lambda_eq]
  simp only [ChainCore.Db, ChainCore.Dc]
  ring

theorem HS_plus_Htau (RD : A.RegionD E hF) :
    K.DHS+K.DHtau=(K.h-2)*(3*K.h+2)*K.d+
      (3*K.h+4)*K.chain.beta+(8*K.h+4)*K.chain.delta+
      (7*K.h+3)*K.r := by
  simp only [DHS, DHtau]
  ring

theorem high_bracket_pos (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hh : 2≤K.h) : 0<4*K.DA0+K.DB0+K.DV-K.DKcal := by
  have hs := K.chain.scalar_ranges
  have hd := K.d_range.1
  have hr := K.euclidean.r_range.1
  have ht := RD.tau_range hJ
  have hst : 0<K.S-K.Dtau := by omega
  have hHS : 0<K.DHS := by
    simp only [DHS]
    have hc : 1≤3*K.h^2-3*K.h-1 := by nlinarith
    have h1 := mul_pos (show 0<3*K.h^2-3*K.h-1 by omega) (show 0<K.d by omega)
    have h2 := mul_pos (show 0<3*K.h+1 by omega) (show 0<K.chain.beta by omega)
    have h3 := mul_pos (show 0<8*K.h by omega) (show 0<K.chain.delta by omega)
    have h4 := mul_nonneg (show 0≤7*K.h by omega) (show 0≤K.r by omega)
    nlinarith
  have hsum : 0<K.DHS+K.DHtau := by
    rw [RD.HS_plus_Htau]
    have h1 := mul_nonneg
      (mul_nonneg (show 0≤K.h-2 by omega) (show 0≤3*K.h+2 by omega))
      (show 0≤K.d by omega)
    have h2 := mul_pos (show 0<3*K.h+4 by omega) (show 0<K.chain.beta by omega)
    have h3 := mul_pos (show 0<8*K.h+4 by omega) (show 0<K.chain.delta by omega)
    have h4 := mul_nonneg (show 0≤7*K.h+3 by omega) (show 0≤K.r by omega)
    nlinarith
  have hHc : 0<K.DHc := by
    simp only [DHc]
    have haj : (0:ℤ)<D.a 1 := by exact_mod_cast D.a_pos 1
    have hleft : 0<(3*K.h+1)*K.d+3*(K.chain.delta+K.r) := by
      nlinarith [mul_pos (show 0<3*K.h+1 by omega) (show 0<K.d by omega)]
    have hright : 0<(4*K.h+1)*K.d+4*(K.chain.delta+K.r) := by
      nlinarith [mul_pos (show 0<4*K.h+1 by omega) (show 0<K.d by omega)]
    nlinarith [mul_pos haj hleft,
      mul_pos (show 0<K.chain.gapJ by omega) hright]
  rw [RD.high_bracket_expansion]
  nlinarith [mul_pos hst hHS,
    mul_pos (show 0<K.Dtau by omega) hsum]

theorem high_q_impossible (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) (hh : 2≤K.h) : False := by
  have hl := RD.high_lower_bounds hJ
  have ha0 := RD.A0_pos hJ hh
  have hb0 := RD.B0_pos hh
  have hA : 0<K.DAmul A := lt_of_lt_of_le ha0 hl.1
  have hB : 0<K.DBmul A := lt_of_lt_of_le hb0 hl.2
  have hbr0 := RD.high_bracket_pos hJ hh
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

theorem h_eq_one_of_regionD (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) : K.h=1 := by
  have hh := K.euclidean.h_pos
  by_contra hn
  exact RD.high_q_impossible hJ hc (by omega)

end FirstFit.RegionD
end P21.Nonsymmetric.ChainCore
