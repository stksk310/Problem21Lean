import P21.Nonsymmetric.Chain.C9.DFirstCaps
import P21.Nonsymmetric.PrimitiveGenerators
import P21.Tail

namespace P21.Nonsymmetric.ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns}
variable {hF : s.semigroup.IsFrobenius F}

/-- Section 9 cross-product coordinates, defined without `OneData`. -/
def DIcal (K : ChainCore s F D) : ℤ :=
  (D.rho 1 : ℤ)*D.rho 2-(D.a 1 : ℤ)*D.b 2

def DJcal (K : ChainCore s F D) : ℤ :=
  (D.a 0 : ℤ)*D.rho 2+(D.b 0 : ℤ)*D.b 2

def DKcal (K : ChainCore s F D) : ℤ :=
  (D.b 0 : ℤ)*D.rho 1+(D.a 0 : ℤ)*D.a 1

def Dmhat (K : ChainCore s F D) : ℤ :=
  -K.d*K.DIcal+K.S*K.DJcal+K.Croot*K.DKcal

def DAmul (K : ChainCore s F D) (A : K.FirstFit) : ℤ :=
  K.DKcal-A.N*K.DV

def DBmul (K : ChainCore s F D) (A : K.FirstFit) : ℤ :=
  K.DDj-(A.zhat-1)*K.DV

/-- The primitive-generator scale is obtained from the frozen global theorem;
it is not a Region-D assumption. -/
theorem d_cross_product_scale (K : ChainCore s F D)
    (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) :
    ∃ sigma : ℤ, 0 < sigma ∧
      g.n 0=sigma*K.DIcal ∧ g.n 1=sigma*K.DJcal ∧
      g.n 2=sigma*K.DKcal ∧ g.m=sigma*K.Dmhat := by
  have hQ : (s.semigroup.Q F).Nonempty :=
    ⟨K.chain.qJ, K.chain.actual 0⟩
  have hcof := s.tail_cofinite hF hc hQ
  have hp : ∀ i, 0 < g.n i := fun i => lt_trans s.m_pos (s.n_gt i)
  obtain ⟨hi,hj,hk⟩ := primitive_generator_minors D hp hcof
  refine ⟨1, by norm_num, ?_, ?_, ?_, ?_⟩
  · simpa [DIcal] using hi
  · simpa [DJcal] using hj
  · simpa [DKcal, add_comm] using hk
  · simp only [one_mul, Dmhat, DIcal, DJcal, DKcal]
    linear_combination K.root-hi*K.d+hj*K.S+hk*K.Croot

namespace FirstFit.RegionD

theorem rhok_first (RD : A.RegionD E hF) :
    (D.rho 2 : ℤ)=A.N*K.Croot+(A.zhat-1)*(D.b 2 : ℤ)-
      K.chain.alpha+1-A.Xi := by
  have hT := K.chain.T_exact
  simp only [FirstFit.Xi]
  rw [hT]
  ring

theorem multiplicity_identity (RD : A.RegionD E hF) :
    K.Dmhat=K.Croot*(K.DAmul A)+(D.b 2 : ℤ)*(K.DBmul A)+
      (K.chain.alpha-1+A.Xi)*K.DV := by
  have hrk := RD.rhok_first
  simp only [Dmhat, DIcal, DJcal, DKcal, DAmul, DBmul,
    ChainCore.DDj, ChainCore.DV]
  rw [hrk]
  ring

theorem multiplicity_master (RD : A.RegionD E hF) :
    K.Dmhat-K.DKcal=
      (K.Croot-(D.b 2 : ℤ)-2*K.chain.alpha-1)*(K.DAmul A)+
      ((D.b 2 : ℤ)-1)*(K.DAmul A+K.DBmul A)+
      (K.chain.alpha-1)*(2*(K.DAmul A)+K.DV)+
      (A.Xi-1)*K.DV+
      (4*(K.DAmul A)+K.DBmul A+K.DV-K.DKcal) := by
  rw [RD.multiplicity_identity]
  ring

theorem master_coefficients (RD : A.RegionD E hF) :
    0≤K.Croot-(D.b 2 : ℤ)-2*K.chain.alpha-1 ∧
    0≤(D.b 2 : ℤ)-1 ∧ 0≤K.chain.alpha-1 ∧ 0≤A.Xi-1 := by
  have hb : (1:ℤ)≤D.b 2 := by exact_mod_cast D.b_pos 2
  have ha := K.chain.scalar_ranges.2.2.2
  have hdeep := RD.C_deep
  have hXi := RD.Xi_pos
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem multiplicity_contradiction (RD : A.RegionD E hF)
    (hc : s.semigroup.Canonical F g.m) (hm : K.DKcal<K.Dmhat) : False := by
  obtain ⟨sigma,hsigma,_,_,hnk,hmroot⟩ := K.d_cross_product_scale hF hc
  have hs := mul_lt_mul_of_pos_left hm hsigma
  rw [←hnk, ←hmroot] at hs
  have hnkgt := s.n_gt (2 : Fin 3)
  omega

end FirstFit.RegionD
end P21.Nonsymmetric.ChainCore
