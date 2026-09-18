import P21.Nonsymmetric.Chain.C8.StrictRegions

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} (O : A.OneData E)

def eta (O : A.OneData E) : ℤ := E.Cj+1

/-- Exact UNIT-PARAM package for the sole strict survivor inside the window. -/
structure UnitParam (O : A.OneData E) : Prop where
  strict : K.chain.alpha<K.Croot
  window : A.chi≤K.chain.T
  Li_one : E.Li=1
  lambda_eq : K.chain.lambda=K.d
  q0_eq : K.q0=2
  x_one : O.x=1
  Lj_eq : E.Lj=O.z+1
  d_eq : K.d=a E+O.z*K.chain.delta
  S_eq : K.S=K.chain.gapJ+O.z*Q E
  ai_eq : (D.a 0 : ℤ)=K.d+K.chain.delta
  bi_eq : (D.b 0 : ℤ)=K.d+K.chain.beta
  rhoj_eq : (D.rho 1 : ℤ)=K.chain.gapJ+(O.z+1)*Q E
  Aj_eq : E.Aj=a E-1
  rhok_eq : (D.rho 2 : ℤ)=(O.z+1)*K.Croot+O.eta+O.z*(D.b 2 : ℤ)
  Uj_eq : E.Uj=Q E-1
  Uk_eq : E.Uk=(D.a 2 : ℤ)-K.Croot-1
  H0_eq : O.H0=K.Croot-K.chain.alpha-O.eta
  H0_nonneg : 0≤O.H0

theorem unit_param (O : A.OneData E) (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) (hstrict : K.chain.alpha<K.Croot)
    (hw : A.chi≤K.chain.T) : O.UnitParam := by
  have hempty := O.empty_triangle hF hw
  have hdet : O.DetOneStatement := O.det_one hempty
  have P : O.ParamData := O.param_data hdet
  have C : O.CeilingData := O.ceiling_data hF
  have hLi : E.Li=1 := by
    have hp := E.levels_pos.1
    by_contra hn
    exact O.strict_window hF hc hstrict hw (by omega)
  have hlevel := K.Li_level E
  have hlam : K.chain.lambda=K.d := by
    rw [hLi, one_mul] at hlevel
    exact le_antisymm hlevel K.d_range.2
  have hq0 : K.q0=2 := by
    have hdpos := K.d_range.1
    have hd0 : K.d≠0 := by omega
    simp [ChainCore.q0, ChainCore.h, hlam, Int.ediv_self hd0]
  rcases O.level_split hdet P with hreg | hunit
  · omega
  · have hx := hunit.2.1
    have hLj := hunit.2.2
    have hd : K.d=a E+O.z*K.chain.delta := by rw [P.d_eq, hx]; ring
    have hS : K.S=K.chain.gapJ+O.z*Q E := by rw [P.S_eq, hx]; ring
    have hai : (D.a 0 : ℤ)=K.d+K.chain.delta := by
      rw [P.ai_eq, hLi, hLj, hd]
      ring
    have hbi : (D.b 0 : ℤ)=K.d+K.chain.beta := by
      rw [P.bi_eq, hLi, hLj, hd]
      ring
    have hrj : (D.rho 1 : ℤ)=K.chain.gapJ+(O.z+1)*Q E := by
      rw [P.rhoj_eq, hLi, hLj]
      ring
    have hAj : E.Aj=a E-1 := by simp [a]
    have hrk : (D.rho 2 : ℤ)=(O.z+1)*K.Croot+O.eta+O.z*(D.b 2 : ℤ) := by
      have h := O.qj_k
      rw [hLj] at h
      simp only [eta]
      nlinarith
    have hUj : E.Uj=Q E-1 := by simp [Q]
    have hUk : E.Uk=(D.a 2 : ℤ)-K.Croot-1 := by
      have h := O.ea_k
      have hr2 : (D.rho 2 : ℤ)=D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
      rw [hLi, hx] at h
      nlinarith
    have hH : O.H0=K.Croot-K.chain.alpha-O.eta := by
      simp [H0, eta, hLi, hx]
      ring
    exact ⟨hstrict,hw,hLi,hlam,hq0,hx,hLj,hd,hS,hai,hbi,hrj,hAj,
      hrk,hUj,hUk,hH,C.H0_nonneg⟩

end P21.Nonsymmetric.ChainCore.FirstFit.OneData
