import P21.Nonsymmetric.Chain.C8.Handoff

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} {O : A.OneData E}

def Hu (O : A.OneData E) : ℤ := K.Croot-K.chain.alpha-O.eta
def t (O : A.OneData E) : ℤ := O.Hu/O.eta+1
def rU (O : A.OneData E) : ℤ := O.Hu-(O.t-1)*O.eta
def b0 (O : A.OneData E) : ℤ := O.z*K.chain.delta+K.chain.beta
def wU (O : A.OneData E) : ℤ := K.chain.T-O.eta
def qprime (O : A.OneData E) : ℤ :=
  Q E-(O.t+1)*((D.a 1 : ℤ)+K.chain.gapJ)-1

namespace RegionU

theorem Hu_nonneg (U : O.RegionU) : 0≤O.Hu := by
  simp only [Hu]
  have h := U.firstPoint.eta_C
  omega

theorem t_pos (U : O.RegionU) : 1≤O.t := by
  simp only [t]
  have he := U.firstPoint.eta_pos
  have hh := U.Hu_nonneg
  have hd : 0≤O.Hu/O.eta := Int.ediv_nonneg hh (by omega)
  omega

theorem rU_eq_emod (U : O.RegionU) : O.rU=O.Hu%O.eta := by
  have h := Int.ediv_mul_add_emod O.Hu O.eta
  simp only [rU, t]
  nlinarith

theorem rU_nonneg (U : O.RegionU) : 0≤O.rU := by
  rw [U.rU_eq_emod]
  exact Int.emod_nonneg _ (by have := U.firstPoint.eta_pos; omega)

theorem rU_lt_eta (U : O.RegionU) : O.rU<O.eta := by
  rw [U.rU_eq_emod]
  exact Int.emod_lt_of_pos _ (by exact U.firstPoint.eta_pos)

theorem Hu_decomp (U : O.RegionU) : O.Hu=(O.t-1)*O.eta+O.rU := by
  simp only [rU]
  ring

theorem C_decomp (U : O.RegionU) :
    K.Croot=K.chain.alpha+O.t*O.eta+O.rU := by
  have h := U.Hu_decomp
  simp only [Hu] at h
  linarith

theorem b0_pos (U : O.RegionU) : 0<O.b0 := by
  have hz := O.z_pos
  have hs := K.chain.scalar_ranges
  simp only [b0]
  nlinarith [mul_pos hz (show 0<K.chain.delta by omega)]

theorem wU_nonneg (U : O.RegionU) : 0≤O.wU := by
  simp only [wU]
  have h := U.firstPoint.eta_T
  omega

theorem C_add_bk_ge (U : O.RegionU) :
    (O.t+1)*O.eta≤K.Croot+(D.b 2 : ℤ) := by
  have hC := U.C_decomp
  have hw := U.wU_nonneg
  have hT := K.chain.T_exact
  simp only [wU] at hw
  rw [hT] at hw
  calc
    (O.t+1)*O.eta = O.t*O.eta+O.eta := by ring
    _ ≤ O.t*O.eta+((D.b 2 : ℤ)+K.chain.alpha) := by omega
    _ ≤ K.Croot+(D.b 2 : ℤ) := by rw [hC]; have := U.rU_nonneg; omega

theorem j_fit (U : O.RegionU) :
    (O.t+1)*K.chain.R+1≤Q E := by
  have hR : 0<K.chain.R := by
    rw [K.chain.R_exact]
    have haj : (0:ℤ)<D.a 1 := by exact_mod_cast D.a_pos 1
    have hg := K.chain.scalar_ranges.2.2.1
    omega
  have heta := U.firstPoint.eta_pos
  have hcap := U.C_add_bk_ge
  have hmul := mul_le_mul_of_nonneg_left hcap (le_of_lt hR)
  have hDu := U.Du_pos
  simp only [OneData.Du] at hDu
  have hDu' : K.chain.R*(K.Croot+(D.b 2 : ℤ))<Q E*O.eta := by nlinarith
  have hstrict : K.chain.R*((O.t+1)*O.eta)<Q E*O.eta :=
    lt_of_le_of_lt hmul hDu'
  have hcancel : K.chain.R*(O.t+1)<Q E := by
    have hfact : (K.chain.R*(O.t+1))*O.eta<Q E*O.eta := by
      nlinarith [hstrict]
    exact (Int.mul_lt_mul_right (show 0<O.eta by omega)).mp hfact
  nlinarith [hcancel]

theorem qprime_nonneg (U : O.RegionU) : 0≤O.qprime := by
  have hj := U.j_fit
  have hR := K.chain.R_exact
  simp only [qprime]
  rw [hR] at hj
  omega

end RegionU
end P21.Nonsymmetric.ChainCore.FirstFit.OneData
