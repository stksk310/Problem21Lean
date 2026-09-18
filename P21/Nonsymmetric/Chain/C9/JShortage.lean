import P21.Nonsymmetric.Chain.C9.IFit

namespace P21.Nonsymmetric.ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns}
variable {hF : s.semigroup.IsFrobenius F}

def DLDelta1 (K : ChainCore s F D) (A : K.FirstFit) : ℤ :=
  K.DLupsilon A+1-K.DLtheta A

namespace FirstFit.RegionD

theorem repeated_packet_F_row (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) :
    F=(K.DLf A+1)*(DLk A+1)*g.m+
      (K.d+K.chain.beta-1-(K.DLf A+1)*K.DLBpkt A)*g.n 0+
      (K.DLtheta A-K.DLupsilon A-1)*g.n 1+
      (A.chi-K.DLw A-1)*g.n 2 := by
  have hu := RD.omegaD_eq
  have hp := RD.d_linear_packet hJ hc
  rcases RD.linear_parameters hJ hc with
    ⟨hk, hups, ha, hS, hrj, hrk, hai, hbi, hd, hI, hJform, hB⟩
  have rem := RD.linear_remainder_parameters hJ hc
  have hC := rem.2.2.2.1
  have hQ : K.DLQ=K.DLf A*K.DLEpar A+K.DLtheta A := by
    simp only [DLtheta]
    ring
  have hE : K.DLEpar A=K.chain.R+K.DLupsilon A := rfl
  have hj : K.chain.R+(D.rho 1 : ℤ)-K.S-1-
      (K.DLf A+1)*K.DLEpar A=K.DLtheta A-K.DLupsilon A-1 := by
    rw [hrj, hS, hQ, hE]
    ring
  have hkcoord : (K.DLf A+1)*A.chi-
      (K.Croot-K.chain.alpha+1)=A.chi-K.DLw A-1 := by
    rw [hC]
    ring
  rw [←hj, ←hkcoord]
  linear_combination hu + (K.DLf A+1)*hp

theorem repeated_packet_coefficients_except_j (RD : A.RegionD E hF)
    (hJ : K.J0<0) (hc : s.semigroup.Canonical F g.m) :
    0<(K.DLf A+1)*(DLk A+1) ∧
    0≤K.d+K.chain.beta-1-(K.DLf A+1)*K.DLBpkt A ∧
    0≤A.chi-K.DLw A-1 := by
  have rem := RD.linear_remainder_parameters hJ hc
  have hk := (RD.linear_parameters hJ hc).1
  have hfit := RD.linear_i_fit_source hJ hc
  exact ⟨by nlinarith,by omega,by omega⟩

theorem theta_upper (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) :
    K.DLtheta A≤K.DLupsilon A := by
  by_contra hn
  have htheta : K.DLupsilon A+1≤K.DLtheta A := by omega
  have heq := RD.repeated_packet_F_row hJ hc
  have hcoeff := RD.repeated_packet_coefficients_except_j hJ hc
  apply hF.1
  change F∈g.Gamma
  rw [heq]
  exact four_mem _ _ _ _ hcoeff.1.le hcoeff.2.1 (by omega) hcoeff.2.2

theorem theta_range (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) :
    1≤K.DLtheta A ∧ K.DLtheta A≤K.DLupsilon A := by
  exact ⟨(RD.linear_remainder_parameters hJ hc).2.2.2.2.1,
    RD.theta_upper hJ hc⟩

theorem Delta1_pos (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) : 1≤K.DLDelta1 A := by
  have ht := RD.theta_range hJ hc
  simp only [DLDelta1]
  omega

theorem zero_j_upper (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) :
    F+K.DLDelta1 A*g.n 1=
      (K.DLf A+1)*(DLk A+1)*g.m+
      (K.d+K.chain.beta-1-(K.DLf A+1)*K.DLBpkt A)*g.n 0+
      (A.chi-K.DLw A-1)*g.n 2 := by
  have heq := RD.repeated_packet_F_row hJ hc
  simp only [DLDelta1]
  linear_combination heq

theorem zero_j_upper_coefficients (RD : A.RegionD E hF)
    (hJ : K.J0<0) (hc : s.semigroup.Canonical F g.m) :
    0<(K.DLf A+1)*(DLk A+1) ∧
    0≤K.d+K.chain.beta-1-(K.DLf A+1)*K.DLBpkt A ∧
    0≤A.chi-K.DLw A-1 :=
  RD.repeated_packet_coefficients_except_j hJ hc

end FirstFit.RegionD
end P21.Nonsymmetric.ChainCore
