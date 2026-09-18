import P21.Nonsymmetric.Chain.C9.LinearCertificate

namespace P21.Nonsymmetric.ChainCore.FirstFit.RegionD

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns}
variable {hF : s.semigroup.IsFrobenius F}

theorem linear_i_fit (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) :
    K.DLastar A+1≤K.DLa A := by
  by_contra hn
  have hle : K.DLa A≤K.DLastar A := by omega
  have hdiff := RD.phi_difference hJ hc (K.DLa A) (K.DLastar A)
  have hDp := RD.d_discriminant_positive hJ hc
  have hC : 0<K.Croot := by
    have hCl := K.C_lower
    have ha := K.chain.scalar_ranges.2.2.2
    omega
  have hk := (RD.linear_parameters hJ hc).1
  have hbk : (0:ℤ)<D.b 2 := by exact_mod_cast D.b_pos 2
  have hchi := RD.chi_pos
  have hrhok : 0<
      (DLk A+1)*K.Croot+DLk A*(D.b 2 : ℤ)+A.chi := by
    nlinarith [mul_pos (show 0<DLk A+1 by omega) hC,
      mul_nonneg (show 0≤DLk A by omega) hbk.le]
  have hcoef : -K.DDp A-
      ((DLk A+1)*K.Croot+DLk A*(D.b 2 : ℤ)+A.chi)-(D.b 2 : ℤ)<0 := by
    omega
  have hmono : K.DLPhiAt A (K.DLastar A)≤K.DLPhiAt A (K.DLa A) := by
    have hp : 0≤(K.DLa A-K.DLastar A)*
        (-K.DDp A-
          ((DLk A+1)*K.Croot+DLk A*(D.b 2 : ℤ)+A.chi)-(D.b 2 : ℤ)) :=
      mul_nonneg_of_nonpos_of_nonpos (by omega) hcoef.le
    nlinarith
  have hthreshold := RD.threshold_phi_positive hJ hc
  have hactual : 0<K.DLPhiAt A (K.DLa A) := lt_of_lt_of_le hthreshold hmono
  have hphi := RD.phi_actual hJ hc
  have hmj : K.DJcal<K.Dmhat := by nlinarith
  obtain ⟨sigma,hsigma,hni,hnj,hnk,hm⟩ := K.d_cross_product_scale hF hc
  have hs := mul_lt_mul_of_pos_left hmj hsigma
  rw [←hnj, ←hm] at hs
  exact (not_lt_of_ge (s.n_gt 1).le) hs

theorem linear_i_fit_source (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) :
    (K.DLf A+1)*K.DLBpkt A-K.chain.beta+1≤K.d := by
  have hfit := RD.linear_i_fit hJ hc
  rcases RD.linear_parameters hJ hc with
    ⟨hk, hu, ha, hS, hrj, hrk, hai, hbi, hd, hI, hJform, hB⟩
  simp only [DLastar, DLBpkt] at hfit ⊢
  simp only [ChainCore.Dc] at hfit ⊢
  nlinarith

end P21.Nonsymmetric.ChainCore.FirstFit.RegionD
