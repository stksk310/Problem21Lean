import P21.Nonsymmetric.Chain.C8.UnitFirstPoint

set_option maxHeartbeats 1200000

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} (O : A.OneData E)

def Du (O : A.OneData E) : ℤ :=
  Q E*O.eta-K.chain.R*(K.Croot+(D.b 2 : ℤ))

def Ma (O : A.OneData E) : ℤ :=
  K.chain.R*(K.Croot+(D.b 2 : ℤ))-Q E*O.eta

def Mdelta (O : A.OneData E) : ℤ :=
  K.Croot*(Q E*O.z*(O.z+1)+(D.a 1 : ℤ)*(O.z+1)+
      K.chain.gapJ*(2*O.z+1))+
    (D.b 2 : ℤ)*(Q E*O.z^2+(D.a 1 : ℤ)*O.z+2*K.chain.gapJ*O.z)+
    O.eta*K.chain.gapJ

def Mbeta (O : A.OneData E) : ℤ :=
  K.Croot*(Q E*(O.z+1)+K.chain.gapJ)+
    (D.b 2 : ℤ)*(Q E*O.z+K.chain.gapJ)

theorem Ma_eq_neg_Du : O.Ma=-O.Du := by simp [Ma, Du]

theorem unit_Mcoeff_pos (U : O.UnitParam) (FP : O.UnitFirstPoint) :
    0<O.Mdelta ∧ 0<O.Mbeta := by
  have hC : 0<K.Croot := by have := U.strict; have := K.chain.scalar_ranges.2.2.2; omega
  have hQ := Q_pos (K:=K) (E:=E)
  have hz := O.z_pos
  have haj : (0:ℤ)<D.a 1 := by exact_mod_cast D.a_pos 1
  have hg : 0<K.chain.gapJ := by have := K.chain.scalar_ranges.2.2.1; omega
  have hbk : (0:ℤ)<D.b 2 := by exact_mod_cast D.b_pos 2
  have heta : 0<O.eta := by have := FP.eta_pos; omega
  simp only [Mdelta, Mbeta]
  constructor
  · have h1 : 0<Q E*O.z*(O.z+1) := by positivity
    have h2 : 0<(D.a 1 : ℤ)*(O.z+1) := by positivity
    have h3 : 0<K.chain.gapJ*(2*O.z+1) := by positivity
    have h4 : 0<Q E*O.z^2 := by positivity
    have h5 : 0<(D.a 1 : ℤ)*O.z := by positivity
    have h6 : 0<2*K.chain.gapJ*O.z := by positivity
    have h7 : 0<O.eta*K.chain.gapJ := by positivity
    nlinarith [mul_pos hC (by nlinarith), mul_pos hbk (by nlinarith)]
  · have h1 : 0<Q E*(O.z+1) := by positivity
    have h2 : 0<Q E*O.z := by positivity
    nlinarith [mul_pos hC (by nlinarith), mul_pos hbk (by nlinarith)]

theorem unit_mhat (U : O.UnitParam) :
    O.mhat=a E*O.Ma+K.chain.delta*O.Mdelta+K.chain.beta*O.Mbeta := by
  have hR := K.chain.R_exact
  simp only [mhat, Ical, Jcal, Kcal, Ma, Mdelta, Mbeta]
  rw [U.ai_eq, U.bi_eq, U.rhoj_eq, U.rhok_eq, U.d_eq, U.S_eq, hR]
  ring

theorem unit_mhat_sub_Ical (U : O.UnitParam) :
    O.mhat-O.Ical=(a E+O.z+1)*O.Ma+
      (K.chain.delta-1)*O.Mdelta+(K.chain.beta-1)*O.Mbeta := by
  have hm := O.unit_mhat U
  have hR := K.chain.R_exact
  simp only [mhat, Ical, Jcal, Kcal, Ma, Mdelta, Mbeta] at hm ⊢
  rw [U.ai_eq, U.bi_eq, U.rhoj_eq, U.rhok_eq, U.d_eq, U.S_eq, hR] at hm ⊢
  nlinarith [hm]

theorem unit_Du_pos (U : O.UnitParam) (FP : O.UnitFirstPoint)
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m) :
    0<O.Du := by
  by_contra hn
  have hMa : 0≤O.Ma := by rw [O.Ma_eq_neg_Du]; omega
  have hM := O.unit_Mcoeff_pos U FP
  have ha : 0<a E := a_pos (K:=K) (E:=E)
  have hz := O.z_pos
  have hd := K.chain.scalar_ranges.1
  have hb := K.chain.scalar_ranges.2.1
  have hid := O.unit_mhat_sub_Ical U
  have h0 : 0≤(a E+O.z+1)*O.Ma := mul_nonneg (by omega) hMa
  have h1 : 0≤(K.chain.delta-1)*O.Mdelta := mul_nonneg (by omega) (le_of_lt hM.1)
  have h2 : 0≤(K.chain.beta-1)*O.Mbeta := mul_nonneg (by omega) (le_of_lt hM.2)
  have hcomp : O.Ical≤O.mhat := by nlinarith
  obtain ⟨sigma,hsigma,hni,hnj,hnk,hm⟩ := O.cross_product_scale hF hc
  have hs := mul_le_mul_of_nonneg_left hcomp (le_of_lt hsigma)
  have hmge : g.n 0≤g.m := by rw [hni, hm]; exact hs
  exact (not_le_of_gt (s.n_gt 0)) hmge

theorem unit_Q_gt_R (U : O.UnitParam) (FP : O.UnitFirstPoint)
    (hDu : 0<O.Du) : K.chain.R<Q E := by
  have hR : 1≤K.chain.R := by
    rw [K.chain.R_exact]
    have haj : (1:ℤ)≤D.a 1 := by exact_mod_cast D.a_pos 1
    have hg := K.chain.scalar_ranges.2.2.1
    omega
  have heta : O.eta<K.Croot+(D.b 2 : ℤ) := by
    have ha := K.chain.scalar_ranges.2.2.2
    have hb : (1:ℤ)≤D.b 2 := by exact_mod_cast D.b_pos 2
    have hetaC := FP.eta_C
    omega
  by_contra hn
  have hQ := Q_pos (K:=K) (E:=E)
  have h1 := mul_le_mul_of_nonneg_right (show Q E≤K.chain.R by omega)
    (show 0≤O.eta by have := FP.eta_pos; omega)
  have h2 := mul_lt_mul_of_pos_left heta (show 0<K.chain.R by omega)
  simp only [Du] at hDu
  nlinarith

theorem unit_Uj_ge_aj (U : O.UnitParam) (hQR : K.chain.R<Q E) :
    (D.a 1 : ℤ)≤E.Uj := by
  have hR := K.chain.R_exact
  rw [U.Uj_eq]
  rw [hR] at hQR
  have hg := K.chain.scalar_ranges.2.2.1
  omega

end P21.Nonsymmetric.ChainCore.FirstFit.OneData
