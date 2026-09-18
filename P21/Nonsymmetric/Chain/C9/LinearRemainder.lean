import P21.Nonsymmetric.Chain.C9.PacketDeterminant

namespace P21.Nonsymmetric.ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns}
variable {hF : s.semigroup.IsFrobenius F}

def DLf (K : ChainCore s F D) (A : K.FirstFit) : ℤ :=
  (K.Croot-K.chain.alpha)/A.chi
def DLw (K : ChainCore s F D) (A : K.FirstFit) : ℤ :=
  K.Croot-K.chain.alpha-K.DLf A*A.chi
def DLtheta (K : ChainCore s F D) (A : K.FirstFit) : ℤ :=
  K.DLQ-K.DLf A*K.DLEpar A
def DLepsilon (K : ChainCore s F D) (A : K.FirstFit) : ℤ :=
  A.chi-((D.b 2 : ℤ)+K.chain.alpha+1)
def DLastar (K : ChainCore s F D) (A : K.FirstFit) : ℤ :=
  K.DLf A*K.DLBpkt A+K.r

namespace FirstFit.RegionD

theorem linear_remainder_parameters (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) :
    1≤K.DLf A ∧ 0≤K.DLw A ∧ K.DLw A<A.chi ∧
    K.Croot=K.chain.alpha+K.DLf A*A.chi+K.DLw A ∧
    1≤K.DLtheta A ∧
    K.DLtheta A*A.chi>K.DLEpar A*(K.chain.T+K.DLw A) ∧
    0≤K.DLepsilon A := by
  have hchi := RD.chi_pos
  have hchiU := RD.chi_upper
  have hf : 1≤K.DLf A := by
    simp only [DLf]
    rw [Int.le_ediv_iff_mul_le (show 0<A.chi by omega)]
    simpa using hchiU
  have hwemod : K.DLw A=(K.Croot-K.chain.alpha)%A.chi := by
    have h := Int.ediv_mul_add_emod (K.Croot-K.chain.alpha) A.chi
    simp only [DLw, DLf]
    nlinarith
  have hw0 : 0≤K.DLw A := by
    rw [hwemod]
    exact Int.emod_nonneg _ (by omega)
  have hwchi : K.DLw A<A.chi := by
    rw [hwemod]
    exact Int.emod_lt_of_pos _ (by omega)
  have hC : K.Croot=K.chain.alpha+K.DLf A*A.chi+K.DLw A := by
    simp only [DLw]
    ring
  have hT := K.chain.T_exact
  have hCb : K.Croot+(D.b 2 : ℤ)=
      K.DLf A*A.chi+(K.chain.T+K.DLw A) := by
    rw [hC, hT]
    ring
  have hDp := RD.d_discriminant_positive hJ hc
  have hslope : K.DLtheta A*A.chi>
      K.DLEpar A*(K.chain.T+K.DLw A) := by
    simp only [DDp] at hDp
    simp only [DLtheta]
    rw [hCb] at hDp
    nlinarith
  have hE : 0<K.DLEpar A := by
    simp only [DLEpar]
    have hR : 0<K.chain.R := by
      rw [K.chain.R_exact]
      have haj : (0:ℤ)<D.a 1 := by exact_mod_cast D.a_pos 1
      have hg := K.chain.scalar_ranges.2.2.1
      omega
    have hu := (RD.linear_parameters hJ hc).2.1
    omega
  have hTw : 0<K.chain.T+K.DLw A := by
    rw [hT]
    have hb : (1:ℤ)≤D.b 2 := by exact_mod_cast D.b_pos 2
    have ha := K.chain.scalar_ranges.2.2.2
    omega
  have htheta : 1≤K.DLtheta A := by
    have hp : 0<K.DLtheta A*A.chi :=
      lt_of_lt_of_le (mul_pos hE hTw) hslope.le
    nlinarith
  have heps : 0≤K.DLepsilon A := by
    simp only [DLepsilon]
    have hgt := RD.chi_gt
    rw [hT] at hgt
    omega
  exact ⟨hf,hw0,hwchi,hC,htheta,hslope,heps⟩

end FirstFit.RegionD
end P21.Nonsymmetric.ChainCore
