import P21.Nonsymmetric.Chain.C8.KCeiling

set_option maxHeartbeats 800000

namespace P21.Nonsymmetric.ChainCore.FirstFit

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} (A : K.FirstFit)

private theorem boundary_nZeta_le {zeta n : ℤ}
    (hI : 0 ≤ K.chain.delta-1+n*K.d-zeta*(D.a 0 : ℤ)) : K.nZeta zeta ≤ n := by
  have hd : 0 < K.d := by have := K.d_range.1; omega
  have hlt : zeta*(D.a 0 : ℤ)-K.chain.delta < n*K.d := by omega
  have hq := (Int.ediv_lt_iff_lt_mul hd).2 hlt
  simp [nZeta]
  omega

private theorem boundary_nZeta_mono {p r : ℤ} (h : p ≤ r) : K.nZeta p ≤ K.nZeta r := by
  rcases h.eq_or_lt with rfl | hlt
  · rfl
  · exact (K.nZeta_strict hlt).le

/-- Pure-H kernel coordinates for the actual boundary EB return. -/
structure EBKernel (E : K.Returns) where
  anchor : A.zhat=A.zhat
  x : ℤ
  y : ℤ
  coordinates : ∀ i,
    (![K.chain.P+E.Lb*K.d, -1-E.Lb*K.S-E.Vj,
      (D.b 2 : ℤ)-1-E.Lb*K.Croot-E.Vk] : Fin 3 → ℤ) i =
      x*kernelRowJ D i+y*kernelRowK D i
  x_pos : 1 ≤ x
  y_pos : 1 ≤ y

noncomputable def ebKernel (E : K.Returns) : A.EBKernel E := by
  let v : Fin 3 → ℤ := ![K.chain.P+E.Lb*K.d, -1-E.Lb*K.S-E.Vj,
    (D.b 2 : ℤ)-1-E.Lb*K.Croot-E.Vk]
  have hv : integerValue g v=0 := by
    have hp := K.EB_pure E
    simp [integerValue, v, Fin.sum_univ_succ]
    linear_combination hp
  let hex := integer_kernel_span (fun i => lt_trans s.m_pos (s.n_gt i)) D v hv
  let x := Classical.choose hex
  let hex' := Classical.choose_spec hex
  let y := Classical.choose hex'
  have hxy := Classical.choose_spec hex'
  change ∀ i, v i=x*kernelRowJ D i+y*kernelRowK D i at hxy
  have hn := E.coeff_nonneg
  have hL := E.levels_pos.2.1
  have hd := K.d_range.1
  have hP : 1 ≤ K.chain.P := by
    rw [K.chain.P_eq_a_beta]
    have ha : (1:ℤ) ≤ D.a 0 := by exact_mod_cast D.a_pos 0
    have hb := K.chain.scalar_ranges.2.1
    omega
  have hleft0 : 0 < K.chain.P+E.Lb*K.d := by
    nlinarith [mul_pos (show 0<E.Lb by omega) (show 0<K.d by omega)]
  have hleft1 : -1-E.Lb*K.S-E.Vj < 0 := by
    have hS : 1 ≤ K.S := by have := K.S_strong; have := K.chain.scalar_ranges.2.2.1; omega
    nlinarith [mul_pos (show 0<E.Lb by omega) (show 0<K.S by omega)]
  have hy : 1 ≤ y := by
    by_contra hh
    have h0 := hxy 0
    have h2 := hxy 2
    simp [v, kernelRowJ, kernelRowK] at h0 h2
    have hy0 : y ≤ 0 := by omega
    have hx : 1 ≤ x := by
      by_contra hx
      have hxa := mul_nonpos_of_nonpos_of_nonneg (show x≤0 by omega)
        (show 0≤(D.a 0:ℤ) by have := D.a_pos 0; omega)
      have hyb := mul_nonpos_of_nonpos_of_nonneg hy0
        (show 0≤(D.b 0:ℤ) by have := D.b_pos 0; omega)
      nlinarith
    have hxb : (D.b 2 : ℤ) ≤ x*(D.b 2 : ℤ) := by
      have hb2 : (1:ℤ)≤D.b 2 := by exact_mod_cast D.b_pos 2
      nlinarith [mul_nonneg (show 0≤x-1 by omega) (show 0≤(D.b 2:ℤ) by omega)]
    have hyn : 0≤-(y*(D.rho 2 : ℤ)) := by
      have := mul_nonpos_of_nonpos_of_nonneg hy0
        (show 0≤(D.rho 2:ℤ) by have := D.rho_pos 2; omega)
      omega
    have hc : 1≤K.Croot := le_trans K.chain.scalar_ranges.2.2.2 K.C_lower
    have hvk := hn.2.2.2.1
    have hLC : 0<E.Lb*K.Croot := mul_pos (by omega) (by omega)
    nlinarith
  have hx : 1 ≤ x := by
    by_contra hh
    have h1 := hxy 1
    simp [v, kernelRowJ, kernelRowK] at h1
    have hx0 : x≤0 := by omega
    have hxr : 0≤-(x*(D.rho 1 : ℤ)) := by
      have := mul_nonpos_of_nonpos_of_nonneg hx0
        (show 0≤(D.rho 1:ℤ) by have := D.rho_pos 1; omega)
      omega
    have hya : 0<y*(D.a 1 : ℤ) := by
      have ha1 : (0:ℤ)<D.a 1 := by exact_mod_cast D.a_pos 1
      exact mul_pos (by omega) ha1
    nlinarith
  exact ⟨rfl,x,y,hxy,hx,hy⟩

namespace EBKernel
variable {A} {E : K.Returns} (H : A.EBKernel E)

theorem d_eq : E.Lb*K.d=H.x*(D.a 0 : ℤ)+(H.y-1)*(D.b 0 : ℤ)-K.chain.delta := by
  have h := H.coordinates 0
  have hp := K.chain.P_eq_b_delta
  simp [kernelRowJ, kernelRowK] at h
  linear_combination h-hp

theorem S_eq : E.Lb*K.S=H.x*(D.rho 1 : ℤ)-H.y*(D.a 1 : ℤ)-E.Vj-1 := by
  have h := H.coordinates 1
  simp [kernelRowJ, kernelRowK] at h
  linear_combination -h

theorem k_eq : (D.rho 2 : ℤ)-E.Vk-1=
    E.Lb*K.Croot+(H.x-1)*(D.b 2 : ℤ)-(H.y-1)*(D.rho 2 : ℤ) := by
  have h := H.coordinates 2
  simp [kernelRowJ, kernelRowK] at h
  linear_combination h

theorem y_eq_one (hF : s.semigroup.IsFrobenius F) (hb : K.Croot=K.chain.alpha) : H.y=1 := by
  have hy1 := H.y_pos
  by_contra hy
  have hy2 : 2 ≤ H.y := by omega
  have hI : 0 ≤ K.chain.delta-1+E.Lb*K.d-H.x*(D.a 0 : ℤ) := by
    rw [H.d_eq]
    have hb0 : (1:ℤ)≤D.b 0 := by exact_mod_cast D.b_pos 0
    nlinarith
  have hJ : 0 ≤ K.chain.gapJ-1+H.x*(D.rho 1 : ℤ)-E.Lb*K.S := by
    rw [H.S_eq]
    have ha1 : (1:ℤ)≤D.a 1 := by exact_mod_cast D.a_pos 1
    have hg := K.chain.scalar_ranges.2.2.1
    have hv := E.coeff_nonneg.2.2.1
    nlinarith
  have hnle : K.nZeta H.x≤E.Lb := boundary_nZeta_le (K:=K) hI
  have hjfit : 0≤K.JZeta H.x := by
    simp [JZeta]
    have hS : 0≤K.S := by have := K.S_strong; have := K.chain.scalar_ranges.2.2.1; omega
    nlinarith [mul_nonneg (show 0≤E.Lb-K.nZeta H.x by omega) hS]
  have hzle : A.zhat≤H.x := A.minimal H.x H.x_pos hjfit
  have hNle : A.N≤E.Lb := by
    rw [A.N_eq]
    exact le_trans (boundary_nZeta_mono (K:=K) hzle) hnle
  have wall := A.boundaryWall E hF hb
  omega

end EBKernel

end P21.Nonsymmetric.ChainCore.FirstFit

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} (O : A.OneData E)

/-- Exact boundary synchronization, retaining the genuine EB kernel witness. -/
structure BoundarySyncData (B : A.EBKernel E) : Prop where
  y_one : B.y=1
  Lb_eq : E.Lb=E.Li
  x_eq : B.x=O.x
  Uj_sync : E.Uj=E.Vj+(D.a 1 : ℤ)
  Vk_sync : E.Vk=E.Uk+(D.b 2 : ℤ)
  Q_ge_two : 2≤Q E

theorem boundary_eb_one (hF : s.semigroup.IsFrobenius F)
    (hb : K.Croot=K.chain.alpha) :
    ∃ B : A.EBKernel E, B.y=1 := by
  let B := A.ebKernel E
  exact ⟨B, B.y_eq_one hF hb⟩

/-- The level-one branch is impossible on `Croot=alpha` because `H0=-Cj-1`. -/
theorem boundary_regular (hb : K.Croot=K.chain.alpha) (C : O.CeilingData)
    (S : O.LevelSplit) :
    E.Li≥O.x+1 ∧ O.x+1≥2 ∧ E.Lj>O.z ∧ O.z≥1 := by
  rcases S with hreg | hunit
  · exact hreg
  · have hH := C.H0_nonneg
    have hCj := E.coeff_nonneg.2.2.2.2.2.1
    simp [H0, hb, hunit.1, hunit.2] at hH
    omega

end P21.Nonsymmetric.ChainCore.FirstFit.OneData
