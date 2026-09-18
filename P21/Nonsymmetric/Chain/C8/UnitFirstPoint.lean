import P21.Nonsymmetric.Chain.C8.UnitParameters

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} (O : A.OneData E)

theorem unit_nZeta (U : O.UnitParam) {zeta : ℤ}
    (hz1 : 1≤zeta) (hzz : zeta≤O.z+1) : K.nZeta zeta=zeta+1 := by
  have hd : 0<K.d := K.d_range.1
  have ha : 0<a E := a_pos (K:=K) (E:=E)
  have hdelta : 0<K.chain.delta := by have := K.chain.scalar_ranges.1; omega
  have hrem0 : 0≤(zeta-1)*K.chain.delta := mul_nonneg (by omega) (by omega)
  have hremd : (zeta-1)*K.chain.delta<K.d := by
    rw [U.d_eq]
    nlinarith [mul_nonneg (show 0≤O.z-(zeta-1) by omega) (show 0≤K.chain.delta by omega)]
  simp only [ChainCore.nZeta]
  rw [U.ai_eq]
  have heq : zeta*(K.d+K.chain.delta)-K.chain.delta=
      zeta*K.d+(zeta-1)*K.chain.delta := by ring
  rw [heq]
  have hq : (zeta*K.d+(zeta-1)*K.chain.delta)/K.d=zeta := by
    rw [Int.ediv_eq_iff_of_pos hd]
    constructor <;> nlinarith
  omega

theorem unit_JZeta (U : O.UnitParam) {zeta : ℤ}
    (hz1 : 1≤zeta) (hzz : zeta≤O.z+1) :
    K.JZeta zeta=(zeta-O.z)*Q E-1 := by
  rw [ChainCore.JZeta, O.unit_nZeta U hz1 hzz, U.rhoj_eq, U.S_eq]
  ring

/-- Exact first-fit point and UNIT-ETA bounds. -/
structure UnitFirstPoint (O : A.OneData E) : Prop where
  zhat_eq : A.zhat=O.z+1
  N_eq : A.N=O.z+2
  I_eq : A.I=a E-1
  J_eq : A.J=Q E-1
  Xi_eq : A.Xi=K.Croot-K.chain.alpha-O.eta+1
  chi_eq : A.chi=O.eta
  eta_pos : 1≤O.eta
  eta_C : O.eta≤K.Croot-K.chain.alpha
  eta_T : O.eta≤K.chain.T

theorem unit_first_point (U : O.UnitParam) : O.UnitFirstPoint := by
  have hzpos := O.z_pos
  have hQ := Q_pos (K:=K) (E:=E)
  have hfit : 0≤K.JZeta (O.z+1) := by
    rw [O.unit_JZeta U (by omega) le_rfl]
    nlinarith
  have hzle : A.zhat≤O.z+1 := A.minimal _ (by omega) hfit
  have hzrange := A.zhat_range.1
  have hzeq : A.zhat=O.z+1 := by
    by_contra hn
    have hzupper : A.zhat≤O.z := by omega
    have hJform := O.unit_JZeta U hzrange (by omega)
    have hJfit := A.J_nonneg
    rw [A.J_eq, hJform] at hJfit
    have hprod : (A.zhat-O.z)*Q E≤0 :=
      mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
    omega
  have hN : A.N=O.z+2 := by
    rw [A.N_eq, hzeq, O.unit_nZeta U (by omega) le_rfl]
    ring
  have hI : A.I=a E-1 := by
    rw [A.I_eq, hzeq]
    simp only [ChainCore.IZeta, O.unit_nZeta U (by omega) le_rfl]
    rw [U.ai_eq, U.d_eq]
    ring
  have hJ : A.J=Q E-1 := by
    rw [A.J_eq, hzeq, O.unit_JZeta U (by omega) le_rfl]
    ring
  have hXi : A.Xi=K.Croot-K.chain.alpha-O.eta+1 := by
    simp only [FirstFit.Xi]
    rw [hN, hzeq, U.rhok_eq, K.chain.T_exact]
    ring
  have hchi : A.chi=O.eta := by
    simp [FirstFit.chi, hXi]
  have heta0 : 1≤O.eta := by
    have := E.coeff_nonneg.2.2.2.2.2.1
    simp [eta]
    omega
  have hetaC : O.eta≤K.Croot-K.chain.alpha := by
    have hH := U.H0_nonneg
    rw [U.H0_eq] at hH
    omega
  have hetaT : O.eta≤K.chain.T := by rw [← hchi]; exact U.window
  exact ⟨hzeq,hN,hI,hJ,hXi,hchi,heta0,hetaC,hetaT⟩

theorem unit_compact (U : O.UnitParam) :
    K.Delta0=(O.z-1)*Q E+1 ∧ K.tau0=Q E := by
  have hq := U.q0_eq
  have hh : K.h=1 := by simp [ChainCore.q0] at hq; omega
  constructor
  · simp [ChainCore.Delta0, U.q0_eq, U.S_eq, U.rhoj_eq]
    ring
  · simp [ChainCore.tau0, hh, U.S_eq, U.rhoj_eq]
    ring

end P21.Nonsymmetric.ChainCore.FirstFit.OneData
