import P21.Nonsymmetric.Chain.C9.LinearRemainder
import P21.Nonsymmetric.Chain.C9.GeneratedLinearCertificate

namespace P21.Nonsymmetric.ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns}
variable {hF : s.semigroup.IsFrobenius F}

open C9.LinearCertificateData

def DLIcalAt (K : ChainCore s F D) (A : K.FirstFit) : ℤ :=
  ((DLk A+1)*K.DLQ+K.DLG A)*
      ((DLk A+1)*K.Croot+DLk A*(D.b 2 : ℤ)+A.chi)-
    (D.a 1 : ℤ)*(D.b 2 : ℤ)

def DLJcalAt (K : ChainCore s F D) (A : K.FirstFit) (a : ℤ) : ℤ :=
  (a+(DLk A+1)*K.Db)*
      ((DLk A+1)*K.Croot+DLk A*(D.b 2 : ℤ)+A.chi)+
    (a+DLk A*K.Db+K.Dc)*(D.b 2 : ℤ)

def DLKcalAt (K : ChainCore s F D) (A : K.FirstFit) (a : ℤ) : ℤ :=
  (a+DLk A*K.Db+K.Dc)*((DLk A+1)*K.DLQ+K.DLG A)+
    (a+(DLk A+1)*K.Db)*(D.a 1 : ℤ)

def DLPhiAt (K : ChainCore s F D) (A : K.FirstFit) (a : ℤ) : ℤ :=
  -(a+DLk A*K.Db)*K.DLIcalAt A+
    (DLk A*K.DLQ+K.DLG A)*K.DLJcalAt A a+
    K.Croot*K.DLKcalAt A a-K.DLJcalAt A a

def DLcertificateVariables (K : ChainCore s F D) (A : K.FirstFit) : Variables where
  f := K.DLf A-1
  r := K.r
  delta := K.chain.delta-1
  beta := K.chain.beta-1
  g := K.chain.gapJ-1
  u := K.DLupsilon A
  alpha := K.chain.alpha-1
  w := K.DLw A
  theta := K.DLtheta A-1
  eps := K.DLepsilon A
  k := DLk A-1
  a_j := (D.a 1 : ℤ)-1
  b_k := (D.b 2 : ℤ)-1

namespace FirstFit.RegionD

theorem certificate_variables_nonnegative (RD : A.RegionD E hF)
    (hJ : K.J0<0) (hc : s.semigroup.Canonical F g.m) :
    0≤(K.DLcertificateVariables A).f ∧
    0≤(K.DLcertificateVariables A).r ∧
    0≤(K.DLcertificateVariables A).delta ∧
    0≤(K.DLcertificateVariables A).beta ∧
    0≤(K.DLcertificateVariables A).g ∧
    0≤(K.DLcertificateVariables A).u ∧
    0≤(K.DLcertificateVariables A).alpha ∧
    0≤(K.DLcertificateVariables A).w ∧
    0≤(K.DLcertificateVariables A).theta ∧
    0≤(K.DLcertificateVariables A).eps ∧
    0≤(K.DLcertificateVariables A).k ∧
    0≤(K.DLcertificateVariables A).a_j ∧
    0≤(K.DLcertificateVariables A).b_k := by
  have hp := RD.linear_remainder_parameters hJ hc
  have hk := (RD.linear_parameters hJ hc).1
  have hr := K.euclidean.r_range.1
  have hs := K.chain.scalar_ranges
  have haj : (1:ℤ)≤D.a 1 := by exact_mod_cast D.a_pos 1
  have hbk : (1:ℤ)≤D.b 2 := by exact_mod_cast D.b_pos 2
  simp only [DLcertificateVariables]
  exact ⟨by omega,by omega,by omega,by omega,by omega,
    (RD.linear_parameters hJ hc).2.1,by omega,hp.2.1,
    by omega,hp.2.2.2.2.2.2,by omega,by omega,by omega⟩

theorem phi_actual (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) :
    K.DLPhiAt A (K.DLa A)=K.Dmhat-K.DJcal := by
  rcases RD.linear_parameters hJ hc with
    ⟨hk, hu, ha, hS, hrj, hrk, hai, hbi, hd, hI, hJform, hB⟩
  simp only [DLPhiAt, DLIcalAt, DLJcalAt, DLKcalAt,
    Dmhat, DIcal, DJcal, DKcal]
  rw [hrj, hrk, hai, hbi, hS, hd]
  ring

theorem phi_difference (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) (x y : ℤ) :
    K.DLPhiAt A x-K.DLPhiAt A y=
      (x-y)*(-K.DDp A-
        ((DLk A+1)*K.Croot+DLk A*(D.b 2 : ℤ)+A.chi)-(D.b 2 : ℤ)) := by
  simp only [DLPhiAt, DLIcalAt, DLJcalAt, DLKcalAt, DDp]
  have hE : K.DLEpar A=(D.a 1 : ℤ)+K.DLG A := by
    simp only [DLEpar, DLG, DLupsilon]
    rw [K.chain.R_exact]
    ring
  rw [hE]
  ring

theorem threshold_certificate_identity (RD : A.RegionD E hF)
    (hJ : K.J0<0) (hc : s.semigroup.Canonical F g.m) :
    K.DLPhiAt A (K.DLastar A)=
      polynomial (K.DLcertificateVariables A) := by
  have hp := RD.linear_remainder_parameters hJ hc
  have hC := hp.2.2.2.1
  have hQ : K.DLQ=K.DLf A*K.DLEpar A+K.DLtheta A := by
    simp only [DLtheta]
    ring
  have hE : K.DLEpar A=(D.a 1 : ℤ)+K.DLG A := by
    simp only [DLEpar, DLG, DLupsilon]
    rw [K.chain.R_exact]
    ring
  have hchi : A.chi=(D.b 2 : ℤ)+K.chain.alpha+1+K.DLepsilon A := by
    simp only [DLepsilon]
    ring
  simp only [DLPhiAt, DLIcalAt, DLJcalAt, DLKcalAt,
    DLastar, DLBpkt, DLcertificateVariables,
    polynomial, terms, evalTerm,
    terms0, terms1, terms2, terms3, terms4, terms5, terms6, terms7,
    List.map_append, List.sum_append, List.map_cons, List.sum_cons,
    List.map_nil, List.sum_nil]
  rw [hC, hQ, hE, hchi]
  simp only [DLG, ChainCore.Db, ChainCore.Dc]
  ring

theorem threshold_phi_positive (RD : A.RegionD E hF)
    (hJ : K.J0<0) (hc : s.semigroup.Canonical F g.m) :
    0<K.DLPhiAt A (K.DLastar A) := by
  rw [RD.threshold_certificate_identity hJ hc]
  rcases RD.certificate_variables_nonnegative hJ hc with
    ⟨hf,hr,hd,hb,hg,hu,hal,hw,ht,he,hk,haj,hbk⟩
  exact polynomial_pos _ hf hr hd hb hg hu hal hw ht he hk haj hbk

end FirstFit.RegionD
end P21.Nonsymmetric.ChainCore
