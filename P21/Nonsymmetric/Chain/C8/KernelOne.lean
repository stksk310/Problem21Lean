import P21.Nonsymmetric.Chain.C8.Packet
import P21.Nonsymmetric.Kernel

namespace P21.Nonsymmetric
namespace ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

namespace FirstFit
variable {K : ChainCore s F D} (A : K.FirstFit)

private theorem nZeta_le_of_I_nonneg {zeta n : ℤ}
    (hI : 0 ≤ K.chain.delta-1+n*K.d-zeta*(D.a 0 : ℤ)) :
    K.nZeta zeta ≤ n := by
  have hd0 := K.d_range.1
  have hd : 0 < K.d := by omega
  have hlt : zeta*(D.a 0 : ℤ)-K.chain.delta < n*K.d := by omega
  have hq := (Int.ediv_lt_iff_lt_mul hd).2 hlt
  simp [nZeta]
  omega

private theorem nZeta_mono {zeta eta : ℤ} (h : zeta ≤ eta) :
    K.nZeta zeta ≤ K.nZeta eta := by
  rcases h.eq_or_lt with rfl | hlt
  · rfl
  · exact (K.nZeta_strict hlt).le

/-- Pure-H kernel coordinates for the actual missing-i return. -/
structure EAKernel (E : K.Returns) where
  anchor : A.zhat = A.zhat
  x : ℤ
  y : ℤ
  coordinates : ∀ i,
    (![K.chain.P+E.Li*K.d,
      (D.a 1 : ℤ)-1-E.Li*K.S-E.Uj,
      -E.Li*K.Croot-E.Uk-1] : Fin 3 → ℤ) i =
      x*kernelRowJ D i+y*kernelRowK D i
  x_pos : 1 ≤ x
  y_pos : 1 ≤ y

noncomputable def eaKernel (E : K.Returns) : A.EAKernel E := by
  let v : Fin 3 → ℤ := ![K.chain.P+E.Li*K.d,
    (D.a 1 : ℤ)-1-E.Li*K.S-E.Uj, -E.Li*K.Croot-E.Uk-1]
  have hv : integerValue g v = 0 := by
    have hp := K.EA_pure E
    simp [integerValue, v, Fin.sum_univ_succ]
    linear_combination hp
  let hex := integer_kernel_span (fun i => lt_trans s.m_pos (s.n_gt i)) D v hv
  let x := Classical.choose hex
  let hex' := Classical.choose_spec hex
  let y := Classical.choose hex'
  have hxy := Classical.choose_spec hex'
  change ∀ i, v i = x*kernelRowJ D i+y*kernelRowK D i at hxy
  have hn := E.coeff_nonneg
  have hL := E.levels_pos.1
  have hd := K.d_range.1
  have hP : 1 ≤ K.chain.P := by
    rw [K.chain.P_eq_a_beta]
    have ha : (1:ℤ) ≤ D.a 0 := by exact_mod_cast D.a_pos 0
    have hb := K.chain.scalar_ranges.2.1
    omega
  have hbk : (1:ℤ) ≤ D.b 2 := by exact_mod_cast D.b_pos 2
  have ha0 : (1:ℤ) ≤ D.a 0 := by exact_mod_cast D.a_pos 0
  have hb0 : (1:ℤ) ≤ D.b 0 := by exact_mod_cast D.b_pos 0
  have hrk : (1:ℤ) ≤ D.rho 2 := by exact_mod_cast D.rho_pos 2
  have haj : (1:ℤ) ≤ D.a 1 := by exact_mod_cast D.a_pos 1
  have hrj : (1:ℤ) ≤ D.rho 1 := by exact_mod_cast D.rho_pos 1
  have hc : 1 ≤ K.Croot := le_trans K.chain.scalar_ranges.2.2.2 K.C_lower
  have hleft0 : 0 < K.chain.P+E.Li*K.d := by
    nlinarith [mul_pos (show 0 < E.Li by omega) (show 0 < K.d by omega)]
  have hleft2 : -E.Li*K.Croot-E.Uk-1 < 0 := by
    nlinarith [mul_pos (show 0 < E.Li by omega) (show 0 < K.Croot by omega)]
  have hy : 1 ≤ y := by
    by_contra hh
    have h0 := hxy 0
    have h2 := hxy 2
    simp [v, kernelRowJ, kernelRowK] at h0 h2
    have hy0 : y ≤ 0 := by omega
    have hx : 1 ≤ x := by
      by_contra hx
      have hxa : x*(D.a 0 : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
      have hyb : y*(D.b 0 : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hy0 (by omega)
      nlinarith
    have hxp : 0 < x*(D.b 2 : ℤ) := mul_pos (by omega) (by omega)
    have hyn : 0 ≤ -(y*(D.rho 2 : ℤ)) := by
      have := mul_nonpos_of_nonpos_of_nonneg hy0 (show 0 ≤ (D.rho 2 : ℤ) by omega)
      omega
    nlinarith
  have hx : 1 ≤ x := by
    by_contra hh
    have h1 := hxy 1
    simp [v, kernelRowJ, kernelRowK] at h1
    have hS : 1 ≤ K.S := by have := K.S_strong; have := K.chain.scalar_ranges.2.2.1; omega
    have hlhs : (D.a 1 : ℤ)-1-E.Li*K.S-E.Uj < (D.a 1 : ℤ) := by
      nlinarith [mul_pos (show 0 < E.Li by omega) (show 0 < K.S by omega)]
    have hx0 : x ≤ 0 := by omega
    have hxterm : 0 ≤ -(x*(D.rho 1 : ℤ)) := by
      have := mul_nonpos_of_nonpos_of_nonneg hx0 (show 0 ≤ (D.rho 1 : ℤ) by omega)
      omega
    have hyterm : (D.a 1 : ℤ) ≤ y*(D.a 1 : ℤ) := by
      nlinarith [mul_nonneg (show 0 ≤ y-1 by omega) (show 0 ≤ (D.a 1 : ℤ) by omega)]
    nlinarith
  exact ⟨rfl,x,y,hxy,hx,hy⟩

namespace EAKernel
variable {A} {E : K.Returns} (H : A.EAKernel E)

 theorem d_eq : E.Li*K.d = H.x*(D.a 0 : ℤ)+(H.y-1)*(D.b 0 : ℤ)-K.chain.delta := by
  have h := H.coordinates 0
  have hp := K.chain.P_eq_b_delta
  simp [kernelRowJ, kernelRowK] at h
  linear_combination h - hp

 theorem S_eq : E.Li*K.S = H.x*(D.rho 1 : ℤ)-(H.y-1)*(D.a 1 : ℤ)-(E.Uj+1) := by
  have h := H.coordinates 1
  simp [kernelRowJ, kernelRowK] at h
  linear_combination -h

 theorem epsilon_eq : (D.rho 2 : ℤ)-E.Uk-1 =
    E.Li*K.Croot+H.x*(D.b 2 : ℤ)-(H.y-1)*(D.rho 2 : ℤ) := by
  have h := H.coordinates 2
  simp [kernelRowJ, kernelRowK] at h
  linear_combination h

 theorem y_eq_one (hF : s.semigroup.IsFrobenius F) (hw : A.chi ≤ K.chain.T) : H.y=1 := by
  have hy1 := H.y_pos
  by_contra hy
  have hy2 : 2 ≤ H.y := by omega
  have hbi : (1:ℤ) ≤ D.b 0 := by exact_mod_cast D.b_pos 0
  have haj : (1:ℤ) ≤ D.a 1 := by exact_mod_cast D.a_pos 1
  have hI : 0 ≤ K.chain.delta-1+E.Li*K.d-H.x*(D.a 0 : ℤ) := by
    rw [H.d_eq]
    nlinarith
  have hJ : 0 ≤ K.chain.gapJ-1+H.x*(D.rho 1 : ℤ)-E.Li*K.S := by
    rw [H.S_eq]
    have hg := K.chain.scalar_ranges.2.2.1
    have hn := E.coeff_nonneg.1
    nlinarith
  have hnle : K.nZeta H.x ≤ E.Li := nZeta_le_of_I_nonneg (K:=K) hI
  have hjfit : 0 ≤ K.JZeta H.x := by
    simp [JZeta]
    have hS : 0 ≤ K.S := by have := K.S_strong; have := K.chain.scalar_ranges.2.2.1; omega
    nlinarith [mul_nonneg (show 0 ≤ E.Li-K.nZeta H.x by omega) hS]
  have hzle : A.zhat ≤ H.x := A.minimal H.x H.x_pos hjfit
  have hNle : A.N ≤ E.Li := by
    rw [A.N_eq]
    exact le_trans (nZeta_mono (K:=K) hzle) hnle
  have wall := A.windowWall E hF hw
  omega

end EAKernel

/-- Pure-H kernel coordinates for the actual missing-j return. -/
structure QJKernel (E : K.Returns) where
  anchor : A.zhat = A.zhat
  z : ℤ
  v : ℤ
  coordinates : ∀ i,
    (![E.Lj*K.d+(D.b 0 : ℤ)-1-E.Aj,
      K.chain.R-E.Lj*K.S,
      -E.Lj*K.Croot-E.Cj-1] : Fin 3 → ℤ) i =
      z*kernelRowJ D i+v*kernelRowK D i
  z_pos : 1 ≤ z
  v_pos : 1 ≤ v

noncomputable def qjKernel (E : K.Returns) (C : K.Caps E) : A.QJKernel E := by
  let w : Fin 3 → ℤ := ![E.Lj*K.d+(D.b 0 : ℤ)-1-E.Aj,
    K.chain.R-E.Lj*K.S, -E.Lj*K.Croot-E.Cj-1]
  have hw0 : integerValue g w = 0 := by
    have hp := K.Qj_pure E
    simp [integerValue, w, Fin.sum_univ_succ]
    linear_combination hp
  let hex := integer_kernel_span (fun i => lt_trans s.m_pos (s.n_gt i)) D w hw0
  let z := Classical.choose hex
  let hex' := Classical.choose_spec hex
  let v := Classical.choose hex'
  have hzv := Classical.choose_spec hex'
  change ∀ i, w i = z*kernelRowJ D i+v*kernelRowK D i at hzv
  have hn := E.coeff_nonneg
  have hL := E.levels_pos.2.2.1
  have hd := K.d_range.1
  have hC : 1 ≤ K.Croot := le_trans K.chain.scalar_ranges.2.2.2 K.C_lower
  have hb0 : (1:ℤ) ≤ D.b 0 := by exact_mod_cast D.b_pos 0
  have hai : (1:ℤ) ≤ D.a 0 := by exact_mod_cast D.a_pos 0
  have haj : (1:ℤ) ≤ D.a 1 := by exact_mod_cast D.a_pos 1
  have hbj : (1:ℤ) ≤ D.b 2 := by exact_mod_cast D.b_pos 2
  have hrj : (1:ℤ) ≤ D.rho 1 := by exact_mod_cast D.rho_pos 1
  have hrk : (1:ℤ) ≤ D.rho 2 := by exact_mod_cast D.rho_pos 2
  have hcoord0 : 1 ≤ E.Lj*K.d+(D.b 0 : ℤ)-1-E.Aj := by
    have hajcap := C.Aj_cap
    have hmul : K.d ≤ E.Lj*K.d := by
      simpa using mul_le_mul_of_nonneg_right hL (show 0 ≤ K.d by omega)
    omega
  have hcoord2 : -E.Lj*K.Croot-E.Cj-1 < 0 := by
    nlinarith [mul_pos (show 0 < E.Lj by omega) (show 0 < K.Croot by omega)]
  have hz : 1 ≤ z := by
    by_contra hh
    have h0 := hzv 0
    have h1 := hzv 1
    have h2 := hzv 2
    simp [w, kernelRowJ, kernelRowK] at h0 h1 h2
    have hz0 : z ≤ 0 := by omega
    have hv : 1 ≤ v := by
      by_contra hv
      have hza : z*(D.a 0 : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hz0 (by omega)
      have hvb : v*(D.b 0 : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
      nlinarith
    have hzterm : 0 ≤ -(z*(D.rho 1 : ℤ)) := by
      have := mul_nonpos_of_nonpos_of_nonneg hz0 (show 0 ≤ (D.rho 1 : ℤ) by omega)
      omega
    have hvterm : (D.a 1 : ℤ) ≤ v*(D.a 1 : ℤ) := by
      nlinarith [mul_nonneg (show 0 ≤ v-1 by omega) (show 0 ≤ (D.a 1 : ℤ) by omega)]
    have hS : 1 ≤ K.S := by have := K.S_strong; have := K.chain.scalar_ranges.2.2.1; omega
    have hR := K.chain.R_exact
    have hg := K.chain.scalar_ranges.2.2.1
    have hmulS : K.S ≤ E.Lj*K.S := by
      simpa using mul_le_mul_of_nonneg_right hL (show 0 ≤ K.S by omega)
    have hgS : K.chain.gapJ+1 ≤ E.Lj*K.S := le_trans K.S_strong hmulS
    have hlhs : K.chain.R-E.Lj*K.S < (D.a 1 : ℤ) := by
      calc
        K.chain.R-E.Lj*K.S = (D.a 1 : ℤ)+K.chain.gapJ-E.Lj*K.S := by rw [hR]
        _ ≤ (D.a 1 : ℤ)-1 := by omega
        _ < (D.a 1 : ℤ) := by omega
    nlinarith
  have hv : 1 ≤ v := by
    by_contra hh
    have h0 := hzv 0
    have h2 := hzv 2
    simp [w, kernelRowJ, kernelRowK] at h0 h2
    have hv0 : v ≤ 0 := by omega
    have hz : 1 ≤ z := by
      by_contra hz
      have hza : z*(D.a 0 : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
      have hvb : v*(D.b 0 : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hv0 (by omega)
      nlinarith
    have hzpos : 0 < z*(D.b 2 : ℤ) := mul_pos (by omega) (by omega)
    have hvneg : 0 ≤ -(v*(D.rho 2 : ℤ)) := by
      have := mul_nonpos_of_nonpos_of_nonneg hv0 (show 0 ≤ (D.rho 2 : ℤ) by omega)
      omega
    nlinarith [mul_pos (show 0 < E.Lj by omega) (show 0 < K.Croot by omega)]
  exact ⟨rfl,z,v,hzv,hz,hv⟩

namespace QJKernel
variable {A} {E : K.Returns} (H : A.QJKernel E)

 theorem d_eq : E.Lj*K.d = H.z*(D.a 0 : ℤ)+(E.Aj+1)+(H.v-1)*(D.b 0 : ℤ) := by
  have h := H.coordinates 0
  simp [kernelRowJ, kernelRowK] at h
  linear_combination h

 theorem S_eq : E.Lj*K.S = H.z*(D.rho 1 : ℤ)+K.chain.gapJ-(H.v-1)*(D.a 1 : ℤ) := by
  have h := H.coordinates 1
  have hR := K.chain.R_exact
  simp [kernelRowJ, kernelRowK] at h
  linear_combination -h + hR

 theorem rho_eq : (D.rho 2 : ℤ) = E.Lj*K.Croot+E.Cj+1+
    H.z*(D.b 2 : ℤ)-(H.v-1)*(D.rho 2 : ℤ) := by
  have h := H.coordinates 2
  simp [kernelRowJ, kernelRowK] at h
  linear_combination h

 theorem v_eq_one (hF : s.semigroup.IsFrobenius F) (hw : A.chi ≤ K.chain.T) : H.v=1 := by
  have hv1 := H.v_pos
  by_contra hv
  have hv2 : 2 ≤ H.v := by omega
  have hbi : (1:ℤ) ≤ D.b 0 := by exact_mod_cast D.b_pos 0
  have haj : (1:ℤ) ≤ D.a 1 := by exact_mod_cast D.a_pos 1
  have hI : 0 ≤ K.chain.delta-1+E.Lj*K.d-H.z*(D.a 0 : ℤ) := by
    rw [H.d_eq]
    have hn := E.coeff_nonneg.2.2.2.2.1
    have hdelta := K.chain.scalar_ranges.1
    nlinarith
  have hJ : 0 ≤ K.chain.gapJ-1+H.z*(D.rho 1 : ℤ)-E.Lj*K.S := by
    rw [H.S_eq]
    nlinarith
  have hnle : K.nZeta H.z ≤ E.Lj := nZeta_le_of_I_nonneg (K:=K) hI
  have hjfit : 0 ≤ K.JZeta H.z := by
    simp [JZeta]
    have hS : 0 ≤ K.S := by have := K.S_strong; have := K.chain.scalar_ranges.2.2.1; omega
    nlinarith [mul_nonneg (show 0 ≤ E.Lj-K.nZeta H.z by omega) hS]
  have hzle : A.zhat ≤ H.z := A.minimal H.z H.z_pos hjfit
  have hNle : A.N ≤ E.Lj := by
    rw [A.N_eq]
    exact le_trans (nZeta_mono (K:=K) hzle) hnle
  have wall := A.windowWall E hF hw
  omega

end QJKernel

/-- The two exact `ONE` packages used by the determinant argument. -/
structure OneRelations (E : K.Returns) where
  ea : A.EAKernel E
  qj : A.QJKernel E
  ea_y_one : ea.y=1
  qj_v_one : qj.v=1

noncomputable def oneRelations (E : K.Returns) (hF : s.semigroup.IsFrobenius F)
    (hw : A.chi ≤ K.chain.T) : A.OneRelations E := by
  let ea := A.eaKernel E
  let qj := A.qjKernel E (K.caps E hF)
  exact ⟨ea,qj,ea.y_eq_one hF hw,qj.v_eq_one hF hw⟩

end FirstFit
end ChainCore
end P21.Nonsymmetric
