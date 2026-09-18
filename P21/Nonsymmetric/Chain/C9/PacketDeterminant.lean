import P21.Nonsymmetric.Chain.C9.LinearFirst

namespace P21.Nonsymmetric.ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns}
variable {hF : s.semigroup.IsFrobenius F}

def DDp (K : ChainCore s F D) (A : K.FirstFit) : ℤ :=
  K.DLQ*A.chi-K.DLEpar A*(K.Croot+(D.b 2 : ℤ))

def DMb (K : ChainCore s F D) (A : K.FirstFit) : ℤ :=
  K.Croot*(K.DLQ*(DLk A)*(DLk A+1)+(D.a 1 : ℤ)*(DLk A+1)+
      K.DLG A*(2*DLk A+1))+
    (D.b 2 : ℤ)*(K.DLQ*(DLk A)^2+(D.a 1 : ℤ)*DLk A+
      2*K.DLG A*DLk A)+A.chi*K.DLG A

def DMc (K : ChainCore s F D) (A : K.FirstFit) : ℤ :=
  K.Croot*(K.DLQ*(DLk A+1)+K.DLG A)+
    (D.b 2 : ℤ)*(K.DLQ*DLk A+K.DLG A)

namespace FirstFit.RegionD

theorem d_discriminant_identity (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) :
    K.Dmhat-K.DIcal=
      -(K.DLa A+DLk A+1)*K.DDp A+
      (K.Db-1)*K.DMb A+(K.Dc-1)*K.DMc A := by
  rcases RD.linear_parameters hJ hc with
    ⟨hk, hu, ha, hS, hrj, hrk, hai, hbi, hd, hI, hJform, hB⟩
  have hR := K.chain.R_exact
  have hE : K.DLEpar A=(D.a 1 : ℤ)+K.DLG A := by
    simp only [DLEpar, DLG, DLupsilon]
    rw [hR]
    ring
  simp only [Dmhat, DIcal, DJcal, DKcal, DDp, DMb, DMc]
  rw [hS, hrj, hrk, hai, hbi, hd, hE]
  ring

theorem d_discriminant_positive (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) : 0<K.DDp A := by
  by_contra hn
  have hDp : K.DDp A≤0 := by omega
  rcases RD.linear_parameters hJ hc with
    ⟨hk, hu, ha, hS, hrj, hrk, hai, hbi, hd, hI, hJform, hB⟩
  have hQ := (RD.tau_range hJ).1
  have hC := K.C_lower
  have hchi := RD.chi_pos
  have hb2 : (1:ℤ)≤D.b 2 := by exact_mod_cast D.b_pos 2
  have haj : (1:ℤ)≤D.a 1 := by exact_mod_cast D.a_pos 1
  have hg := K.chain.scalar_ranges.2.2.1
  have hR := K.chain.scalar_ranges.2.2.1
  have hG : 0≤K.DLG A := by simp only [DLG]; omega
  have hQ0 : 0≤K.DLQ := by simp only [DLQ]; omega
  have hC0 : 0≤K.Croot := by
    have halpha := K.chain.scalar_ranges.2.2.2
    omega
  have hk0 : 0≤DLk A := by omega
  have hchi0 : 0≤A.chi := by omega
  have haj0 : (0:ℤ)≤D.a 1 := by omega
  have hb20 : (0:ℤ)≤D.b 2 := by omega
  have hMb : 0≤K.DMb A := by
    simp only [DMb]
    positivity
  have hMc : 0≤K.DMc A := by
    simp only [DMc]
    positivity
  have hb : 1≤K.Db := by
    simp only [ChainCore.Db]
    have hr := K.euclidean.r_range.1
    have hd := K.chain.scalar_ranges.1
    omega
  have hc' : 1≤K.Dc := by
    simp only [ChainCore.Dc]
    have hr := K.euclidean.r_range.1
    have hb := K.chain.scalar_ranges.2.1
    omega
  have hr0 := K.euclidean.r_range.1
  have hfac : 0≤K.DLa A+DLk A+1 := by nlinarith
  have hid := RD.d_discriminant_identity hJ hc
  have hdiff : 0≤K.Dmhat-K.DIcal := by
    rw [hid]
    nlinarith [mul_nonneg hfac (neg_nonneg.mpr hDp),
      mul_nonneg (by omega : 0≤K.Db-1) hMb,
      mul_nonneg (by omega : 0≤K.Dc-1) hMc]
  have hcomp : K.DIcal≤K.Dmhat := by omega
  obtain ⟨sigma,hsigma,hni,hnj,hnk,hm⟩ := K.d_cross_product_scale hF hc
  have hs := mul_le_mul_of_nonneg_left hcomp hsigma.le
  rw [←hni, ←hm] at hs
  exact (not_le_of_gt (s.n_gt 0)) hs

end FirstFit.RegionD
end P21.Nonsymmetric.ChainCore
