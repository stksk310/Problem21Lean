import P21.Nonsymmetric.Chain.C9.RegionUCapacity

set_option maxHeartbeats 1200000

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData.RegionU

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} {O : A.OneData E}

/-- U-PACKET, retained as a genuine equality with positive coefficients. -/
theorem packet_eq (U : O.RegionU) :
    O.b0*g.n 0+K.chain.R*g.n 1=(O.z+1)*g.m+O.eta*g.n 2 := by
  have u := U.unit
  have hR := K.chain.R_exact
  have hr := K.root
  have h1 := D.relation_one
  have h2 := D.relation_two
  rw [u.d_eq, u.S_eq] at hr
  rw [u.rhoj_eq, u.ai_eq, u.d_eq] at h1
  rw [u.rhok_eq, u.bi_eq, u.d_eq] at h2
  simp only [OneData.b0]
  rw [hR]
  linear_combination
    -(O.z+1)*hr - h2 - O.z*h1

theorem packet_coefficients (U : O.RegionU) :
    0≤O.b0 ∧ 0≤K.chain.R ∧ 0≤O.z+1 ∧ 0≤O.eta := by
  have hR : 0<K.chain.R := by
    rw [K.chain.R_exact]
    have haj : (0:ℤ)<D.a 1 := by exact_mod_cast D.a_pos 1
    have hg := K.chain.scalar_ranges.2.2.1
    omega
  exact ⟨le_of_lt U.b0_pos,le_of_lt hR,by have := O.z_pos; omega,
    by have := U.firstPoint.eta_pos; omega⟩

/-- The exact signed equality for the named upper element. -/
theorem upper_eq (U : O.RegionU) :
    K.chain.qK+(O.Hu+1)*g.n 2=
      (O.z+2)*g.m+(a E-K.chain.beta-1)*g.n 0+
        (Q E-K.chain.R-1)*g.n 1 := by
  have u := U.unit
  have hq := K.chain.qK_exact
  have hT := K.chain.T_exact
  have hR := K.chain.R_exact
  have hHu : O.Hu=K.Croot-K.chain.alpha-O.eta := rfl
  have hp := U.packet_eq
  have hr := K.root
  have h1 := D.relation_one
  rw [u.d_eq, u.S_eq] at hr
  rw [u.rhoj_eq, u.ai_eq, u.d_eq] at h1
  rw [hq, hT, hR, hHu, u.ai_eq, u.d_eq]
  rw [hR] at hp
  simp only [OneData.b0] at hp ⊢
  linear_combination hp - hr - h1

theorem upper_actual (U : O.RegionU) :
    K.chain.qK+(O.Hu+1)*g.n 2∈g.Gamma := by
  have hsucc : K.chain.qK+g.n 2∈g.Gamma :=
    K.chain.qK_actual.1.2 (g.n 2) (g.n_mem 2)
      (by have := s.n_gt 2; have := s.m_pos; omega)
  have hHu := U.Hu_nonneg
  have hcast : ((O.Hu.toNat : ℕ) : ℤ)=O.Hu := Int.toNat_of_nonneg hHu
  have hmultiple : O.Hu*g.n 2∈g.Gamma := by
    rw [← hcast]
    simpa [nsmul_eq_mul] using g.Gamma.nsmul_mem (g.n_mem 2) O.Hu.toNat
  have hadd := g.Gamma.add_mem hsucc hmultiple
  convert hadd using 1 <;> ring

theorem upper_source_nonnegative (U : O.RegionU)
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m) :
    0≤O.z+2 ∧ 0≤a E-K.chain.beta-1 ∧ 0≤Q E-K.chain.R-1 := by
  have hi := U.i_fit hF hc
  have hj := U.j_fit
  have ht := U.t_pos
  have hb := U.b0_pos
  have hR : 0<K.chain.R := by
    rw [K.chain.R_exact]
    have haj : (0:ℤ)<D.a 1 := by exact_mod_cast D.a_pos 1
    have hg := K.chain.scalar_ranges.2.2.1
    omega
  have hz := O.z_pos
  simp only [OneData.astar] at hi
  constructor
  · omega
  constructor
  · nlinarith [mul_pos ht hb]
  · nlinarith [mul_pos ht hR]

/-- Coefficientwise replacement of exactly `t` U-packets inside the same
named upper element. -/
theorem replaced_upper (U : O.RegionU) :
    K.chain.qK+(O.Hu+1)*g.n 2=
      (O.z+2+O.t*(O.z+1))*g.m+
      (a E-K.chain.beta-1-O.t*O.b0)*g.n 0+
      (Q E-(O.t+1)*K.chain.R-1)*g.n 1+
      (O.t*O.eta)*g.n 2 := by
  have hu := U.upper_eq
  have hp := U.packet_eq
  linear_combination hu + O.t*hp

theorem final_eq (U : O.RegionU) :
    K.chain.qK=
      (O.z+2+O.t*(O.z+1))*g.m+
      (a E-K.chain.beta-1-O.t*O.b0)*g.n 0+
      (Q E-(O.t+1)*K.chain.R-1)*g.n 1+
      (O.eta-O.rU-1)*g.n 2 := by
  have hr := U.replaced_upper
  have hh := U.Hu_decomp
  rw [hh] at hr
  linear_combination hr

theorem final_coefficients (U : O.RegionU)
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m) :
    0≤O.z+2+O.t*(O.z+1) ∧
    0≤a E-K.chain.beta-1-O.t*O.b0 ∧
    0≤Q E-(O.t+1)*K.chain.R-1 ∧
    0≤O.eta-O.rU-1 := by
  have hi := U.i_fit hF hc
  have hj := U.j_fit
  have ht := U.t_pos
  have hz := O.z_pos
  have hr := U.rU_lt_eta
  simp only [OneData.astar] at hi
  constructor
  · nlinarith [mul_nonneg (by omega : 0≤O.t) (by omega : 0≤O.z+1)]
  constructor <;> omega

theorem impossible (U : O.RegionU)
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m) : False := by
  have heq := U.final_eq
  have hn := U.final_coefficients hF hc
  apply K.chain.qK_actual.1.1
  rw [heq]
  exact four_mem _ _ _ _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2

end P21.Nonsymmetric.ChainCore.FirstFit.OneData.RegionU
