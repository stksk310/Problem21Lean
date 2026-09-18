import P21.Nonsymmetric.Chain.C9.RegionUSetup

set_option maxHeartbeats 1200000

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} {O : A.OneData E}

def astar (O : A.OneData E) : ℤ := O.t*O.b0+K.chain.beta

/-- The scale-free multiplicity difference after replacing the return parameter
`a = A_j+1` by an integer variable while keeping the critical `a_j` fixed. -/
def phiUAt (O : A.OneData E) (x : ℤ) : ℤ :=
  let d := x+O.z*K.chain.delta
  let ai := d+K.chain.delta
  let bi := d+K.chain.beta
  let rj := K.chain.gapJ+(O.z+1)*Q E
  let rk := (O.z+1)*K.Croot+O.eta+O.z*(D.b 2 : ℤ)
  let ii := rj*rk-(D.a 1 : ℤ)*D.b 2
  let jj := ai*rk+bi*(D.b 2 : ℤ)
  let kk := bi*rj+ai*(D.a 1 : ℤ)
  (-d)*ii+(K.chain.gapJ+O.z*Q E)*jj+K.Croot*kk-jj

def Xdelta (O : A.OneData E) : ℤ :=
  K.chain.alpha*(O.t*O.z+O.z+1)+
  O.eta*(O.t^2*O.z^2+O.t^2*O.z+2*O.t*O.z^2+2*O.t*O.z+O.t+O.z^2+O.z)+
  O.rU*(O.t*O.z^2+2*O.t*O.z+O.z^2+2*O.z+1)+
  O.wU*(O.t*O.z^2+O.t*O.z+O.z^2+O.z)

def Ydelta (O : A.OneData E) : ℤ :=
  K.chain.alpha*(O.t*O.z+O.z+1)+
  O.eta*(O.t^2*O.z^2+O.t^2*O.z+2*O.t*O.z^2+3*O.t*O.z+O.t+O.z^2+2*O.z+1)+
  O.rU*(O.t*O.z^2+2*O.t*O.z+O.z^2+3*O.z+1)+
  O.wU*(O.t*O.z^2+O.t*O.z+O.z^2+2*O.z)

def Xbeta (O : A.OneData E) : ℤ :=
  K.chain.alpha*(O.t+1)+
  O.eta*(O.t^2*O.z+O.t^2+2*O.t*O.z+O.t+O.z)+
  O.rU*(O.t*O.z+2*O.t+O.z+2)+O.wU*(O.t*O.z+O.t+O.z+1)

def Ybeta (O : A.OneData E) : ℤ :=
  K.chain.alpha*(O.t+1)+
  O.eta*(O.t^2*O.z+O.t^2+2*O.t*O.z+2*O.t+O.z+1)+
  O.rU*(O.t*O.z+2*O.t+O.z+3)+O.wU*(O.t*O.z+O.t+O.z+2)

def Zdelta (O : A.OneData E) : ℤ :=
  O.z*(K.chain.alpha+O.eta*(O.t+1)*O.z+O.rU*(O.z+1)+O.wU*O.z)

def Zbeta (O : A.OneData E) : ℤ :=
  K.chain.alpha+O.eta*((O.t+1)*O.z-1)+O.rU*(O.z+1)+O.wU*O.z

def Pdelta (O : A.OneData E) : ℤ :=
  K.chain.alpha*(2*O.t*O.z+3*O.z+1)+
  O.eta*(O.t^2*O.z^2+O.t^2*O.z+3*O.t*O.z^2+O.t*O.z+O.t+2*O.z^2)+
  O.rU*(O.t*O.z^2+3*O.t*O.z+2*O.z^2+4*O.z+1)+
  O.wU*O.z*(O.t*O.z+O.t+2*O.z+1)

def Pbeta (O : A.OneData E) : ℤ :=
  2*K.chain.alpha*(O.t+2)+
  O.eta*(O.t^2*O.z+O.t^2+3*O.t*O.z+2*O.z-3)+
  O.rU*(O.t*O.z+3*O.t+2*O.z+5)+
  O.wU*(O.t*O.z+O.t+2*O.z+1)

namespace RegionU

theorem phi_actual (U : O.RegionU) : O.mhat-O.Jcal=O.phiUAt (a E) := by
  have u := U.unit
  simp only [phiUAt, OneData.mhat, OneData.Ical, OneData.Jcal, OneData.Kcal]
  rw [u.ai_eq, u.bi_eq, u.rhoj_eq, u.rhok_eq, u.d_eq, u.S_eq]

theorem phi_difference (U : O.RegionU) (x y : ℤ) :
    O.phiUAt x-O.phiUAt y=
      (x-y)*(-O.Du-((O.z+1)*K.Croot+O.eta+O.z*(D.b 2 : ℤ))-(D.b 2 : ℤ)) := by
  have hR := K.chain.R_exact
  simp only [phiUAt, OneData.Du]
  rw [hR]
  ring

theorem phi_step_neg (U : O.RegionU) (x : ℤ) : O.phiUAt (x+1)<O.phiUAt x := by
  have hd := U.Du_pos
  have hrk : 0<(O.z+1)*K.Croot+O.eta+O.z*(D.b 2 : ℤ) := by
    have hz := O.z_pos
    have hC : 0<K.Croot := by
      have := U.unit.strict
      have ha := K.chain.scalar_ranges.2.2.2
      omega
    have he := U.firstPoint.eta_pos
    have hb : (0:ℤ)<D.b 2 := by exact_mod_cast D.b_pos 2
    positivity
  have hb : (0:ℤ)<D.b 2 := by exact_mod_cast D.b_pos 2
  have h := U.phi_difference (x+1) x
  nlinarith

theorem coefficient_polynomials (U : O.RegionU) :
    0≤O.Xdelta ∧ 0≤O.Ydelta ∧ 0≤O.Zdelta ∧
    0≤O.Xbeta ∧ 0≤O.Ybeta ∧ 0≤O.Zbeta := by
  have ht := U.t_pos
  have hz := O.z_pos
  have ha := K.chain.scalar_ranges.2.2.2
  have he := U.firstPoint.eta_pos
  have hr := U.rU_nonneg
  have hw := U.wU_nonneg
  have htz : 0≤(O.t+1)*O.z-1 := by
    nlinarith [mul_pos (show 0<O.t by omega) (show 0<O.z by omega)]
  simp only [Xdelta, Ydelta, Zdelta, Xbeta, Ybeta, Zbeta]
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  · positivity

theorem dangerous_beta (U : O.RegionU) :
    4≤O.t^2*O.z+O.t^2+3*O.t*O.z+2*O.z-3 := by
  have ht := U.t_pos
  have hz := O.z_pos
  nlinarith [mul_pos (show 0<O.t by omega) (show 0<O.z by omega),
    sq_nonneg (O.t-1), mul_nonneg (by omega : 0≤O.t-1) (by omega : 0≤O.z-1)]

theorem leading_polynomials_pos (U : O.RegionU) : 0<O.Pdelta ∧ 0<O.Pbeta := by
  have ht := U.t_pos
  have hz := O.z_pos
  have ha := K.chain.scalar_ranges.2.2.2
  have he := U.firstPoint.eta_pos
  have hr := U.rU_nonneg
  have hw := U.wU_nonneg
  have hd := U.dangerous_beta
  simp only [Pdelta, Pbeta]
  constructor <;> positivity

theorem pos_decomp (U : O.RegionU) :
    O.phiUAt O.astar=
      K.chain.delta*(O.Pdelta+((D.a 1 : ℤ)-1)*O.Xdelta+
        (K.chain.gapJ-1)*O.Ydelta+O.qprime*O.Zdelta)+
      K.chain.beta*(O.Pbeta+((D.a 1 : ℤ)-1)*O.Xbeta+
        (K.chain.gapJ-1)*O.Ybeta+O.qprime*O.Zbeta) := by
  have hC := U.C_decomp
  have hT := K.chain.T_exact
  have hbk : (D.b 2 : ℤ)=O.eta-K.chain.alpha+O.wU := by
    simp only [wU]
    rw [hT]
    ring
  have hQ : Q E=(O.t+1)*((D.a 1 : ℤ)+K.chain.gapJ)+1+O.qprime := by
    simp only [qprime]
    ring
  simp only [phiUAt, astar, b0, Pdelta, Pbeta, Xdelta, Ydelta, Zdelta,
    Xbeta, Ybeta, Zbeta]
  rw [hC, hbk, hQ]
  ring

theorem phi_astar_pos (U : O.RegionU) : 0<O.phiUAt O.astar := by
  rw [U.pos_decomp]
  have hc := U.coefficient_polynomials
  have hp := U.leading_polynomials_pos
  have hq := U.qprime_nonneg
  have hadj : (0:ℤ)≤D.a 1-1 := by
    have h : (1:ℤ)≤D.a 1 := by exact_mod_cast D.a_pos 1
    omega
  have hg := K.chain.scalar_ranges.2.2.1
  have hs := K.chain.scalar_ranges
  rcases hc with ⟨hxd,hyd,hzd,hxb,hyb,hzb⟩
  rcases hp with ⟨hpd,hpb⟩
  have hg0 : 0≤K.chain.gapJ-1 := by omega
  have hBd : 0<O.Pdelta+((D.a 1 : ℤ)-1)*O.Xdelta+
      (K.chain.gapJ-1)*O.Ydelta+O.qprime*O.Zdelta := by positivity
  have hBb : 0<O.Pbeta+((D.a 1 : ℤ)-1)*O.Xbeta+
      (K.chain.gapJ-1)*O.Ybeta+O.qprime*O.Zbeta := by positivity
  exact add_pos (mul_pos (by omega) hBd) (mul_pos (by omega) hBb)

theorem i_fit (U : O.RegionU) (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) :
    O.astar+1≤a E := by
  by_contra hn
  have hale : a E≤O.astar := by omega
  have hcoef :
      -O.Du-((O.z+1)*K.Croot+O.eta+O.z*(D.b 2 : ℤ))-(D.b 2 : ℤ)<0 := by
    have hd := U.Du_pos
    have hz := O.z_pos
    have hC : 0<K.Croot := by
      have := U.unit.strict
      have ha := K.chain.scalar_ranges.2.2.2
      omega
    have he := U.firstPoint.eta_pos
    have hb : (0:ℤ)<D.b 2 := by exact_mod_cast D.b_pos 2
    nlinarith [mul_nonneg (by omega : 0≤O.z) (by omega : 0≤(D.b 2 : ℤ))]
  have hdiff := U.phi_difference (a E) O.astar
  have hprod : 0≤(a E-O.astar)*
      (-O.Du-((O.z+1)*K.Croot+O.eta+O.z*(D.b 2 : ℤ))-(D.b 2 : ℤ)) :=
    mul_nonneg_of_nonpos_of_nonpos (by omega) (le_of_lt hcoef)
  have hphi : O.phiUAt O.astar≤O.phiUAt (a E) := by nlinarith
  have hpos := U.phi_astar_pos
  have hactual := U.phi_actual
  have hcomp : O.Jcal<O.mhat := by nlinarith
  obtain ⟨sigma,hsigma,hni,hnj,hnk,hm⟩ := O.cross_product_scale hF hc
  have hscaled := mul_lt_mul_of_pos_left hcomp hsigma
  have hmgt : g.n 1<g.m := by rw [hnj, hm]; exact hscaled
  exact (not_lt_of_ge (s.n_gt 1).le) hmgt

end RegionU
end P21.Nonsymmetric.ChainCore.FirstFit.OneData
