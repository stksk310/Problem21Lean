import P21.Nonsymmetric.Chain.Compact

namespace P21.Nonsymmetric
namespace ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable (K : ChainCore s F D) (E : K.Returns)

theorem EA_pure :
    (K.chain.P+E.Li*K.d)*g.n 0 =
      (E.Li*K.S+E.Uj-D.a 1+1)*g.n 1 +
      (E.Li*K.Croot+E.Uk+1)*g.n 2 := by
  have he := E.EA_eq
  have hq := K.chain.qA_exact
  linear_combination he - hq + E.Li * K.root

theorem EB_pure :
    (K.chain.P+E.Lb*K.d)*g.n 0 =
      (E.Lb*K.S+E.Vj+1)*g.n 1 +
      (E.Lb*K.Croot+E.Vk-D.b 2+1)*g.n 2 := by
  have he := E.EB_eq
  have hq := K.chain.qB_exact
  linear_combination he - hq + E.Lb * K.root

private theorem critical0 {c y z : ℤ} (hc : 0 < c) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (he : c*g.n 0 = y*g.n 1+z*g.n 2) : (D.rho 0 : ℤ) ≤ c :=
  herzog_critical_le_int D (by decide) (by decide) c y z hc hy hz he

private theorem critical1 {c x z : ℤ} (hc : 0 < c) (hx : 0 ≤ x) (hz : 0 ≤ z)
    (he : c*g.n 1 = x*g.n 0+z*g.n 2) : (D.rho 1 : ℤ) ≤ c :=
  herzog_critical_le_int D (by decide) (by decide) c x z hc hx hz he

private theorem critical2 {c x y : ℤ} (hc : 0 < c) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (he : c*g.n 2 = x*g.n 0+y*g.n 1) : (D.rho 2 : ℤ) ≤ c :=
  herzog_critical_le_int D (by decide) (by decide) c x y hc hx hy he

theorem Li_level : K.chain.lambda ≤ E.Li*K.d := by
  by_contra hn
  have pure := K.EA_pure E
  have nonneg := E.coeff_nonneg
  have levels := E.levels_pos
  have hLi := levels.1
  have hUj := nonneg.1
  have hUk := nonneg.2.1
  have hs : 1 ≤ K.S := by have := K.S_strong; have := K.chain.scalar_ranges.2.2.1; omega
  have hc : 1 ≤ K.Croot := le_trans K.chain.scalar_ranges.2.2.2 K.C_lower
  have hp : K.chain.P = (D.rho 0 : ℤ)-K.chain.lambda := by simp [ChainInput.P]
  have hLid : 0 < E.Li*K.d := mul_pos hLi K.d_range.1
  have cle : K.chain.P+E.Li*K.d < D.rho 0 := by omega
  have cpos : 0 < K.chain.P+E.Li*K.d := by
    rw [K.chain.P_eq_a_beta]
    have ha0 : (1 : ℤ) ≤ D.a 0 := by exact_mod_cast D.a_pos 0
    have hb := K.chain.scalar_ranges.2.1
    nlinarith
  by_cases hj : 0 ≤ E.Li*K.S+E.Uj-D.a 1+1
  · have hk : 0 ≤ E.Li*K.Croot+E.Uk+1 := by nlinarith
    have := critical0 (D:=D) cpos hj hk pure
    omega
  · have hjn : 0 < D.a 1-1-E.Li*K.S-E.Uj := by omega
    have hkpos : 0 < E.Li*K.Croot+E.Uk+1 := by nlinarith
    have rev : (E.Li*K.Croot+E.Uk+1)*g.n 2 =
        (K.chain.P+E.Li*K.d)*g.n 0 +
        (D.a 1-1-E.Li*K.S-E.Uj)*g.n 1 := by linarith [pure]
    have hkcrit := critical2 (D:=D) hkpos (by omega) hjn.le rev
    have hr := D.relation_two
    have pure2 : (K.chain.delta+E.Li*K.d)*g.n 0 =
        (E.Li*K.S+E.Uj+1)*g.n 1 +
        (E.Li*K.Croot+E.Uk+1-D.rho 2)*g.n 2 := by
      have hpb := K.chain.P_eq_b_delta
      linear_combination pure + hr - g.n 0 * hpb
    have c2pos : 0 < K.chain.delta+E.Li*K.d := by
      have := K.chain.scalar_ranges.1; nlinarith
    have c2lt : K.chain.delta+E.Li*K.d < D.rho 0 := by
      have ha := K.chain.a0_exact
      have hr0 : (D.rho 0 : ℤ)=D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
      have hb := D.b_pos 0
      omega
    have hcrit := critical0 (D:=D) c2pos (by nlinarith) (by omega) pure2
    omega

theorem Lb_level : K.chain.lambda ≤ E.Lb*K.d := by
  by_contra hn
  have pure := K.EB_pure E
  have nonneg := E.coeff_nonneg
  have levels := E.levels_pos
  have hLb := levels.2.1
  have hVj := nonneg.2.2.1
  have hVk := nonneg.2.2.2.1
  have hs : 1 ≤ K.S := by have := K.S_strong; have := K.chain.scalar_ranges.2.2.1; omega
  have hc : 1 ≤ K.Croot := le_trans K.chain.scalar_ranges.2.2.2 K.C_lower
  have hLbd : 0 < E.Lb*K.d := mul_pos hLb K.d_range.1
  have cle : K.chain.P+E.Lb*K.d < D.rho 0 := by simp [ChainInput.P]; omega
  have cpos : 0 < K.chain.P+E.Lb*K.d := by
    rw [K.chain.P_eq_a_beta]
    have ha0 : (1 : ℤ) ≤ D.a 0 := by exact_mod_cast D.a_pos 0
    have hb := K.chain.scalar_ranges.2.1
    nlinarith
  by_cases hk : 0 ≤ E.Lb*K.Croot+E.Vk-D.b 2+1
  · have hj : 0 ≤ E.Lb*K.S+E.Vj+1 := by nlinarith
    have := critical0 (D:=D) cpos hj hk pure
    omega
  · have hkn : 0 < D.b 2-1-E.Lb*K.Croot-E.Vk := by omega
    have hjpos : 0 < E.Lb*K.S+E.Vj+1 := by nlinarith
    have rev : (E.Lb*K.S+E.Vj+1)*g.n 1 =
        (K.chain.P+E.Lb*K.d)*g.n 0 +
        (D.b 2-1-E.Lb*K.Croot-E.Vk)*g.n 2 := by linarith [pure]
    have hjcrit := critical1 (D:=D) hjpos (by omega) hkn.le rev
    have hr := D.relation_one
    have pure2 : (K.chain.beta+E.Lb*K.d)*g.n 0 =
        (E.Lb*K.S+E.Vj+1-D.rho 1)*g.n 1 +
        (E.Lb*K.Croot+E.Vk+1)*g.n 2 := by
      have hpa := K.chain.P_eq_a_beta
      linear_combination pure + hr - g.n 0 * hpa
    have c2pos : 0 < K.chain.beta+E.Lb*K.d := by
      have := K.chain.scalar_ranges.2.1; nlinarith
    have c2lt : K.chain.beta+E.Lb*K.d < D.rho 0 := by
      have hb := K.chain.b0_exact
      have hr0 : (D.rho 0 : ℤ)=D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
      have ha := D.a_pos 0
      omega
    have hcrit := critical0 (D:=D) c2pos (by omega) (by nlinarith) pure2
    omega

theorem I_levels (K : ChainCore s F D) (E : K.Returns) :
    K.h ≤ E.Li ∧ K.h ≤ E.Lb := by
  have A := K.Li_level E
  have B := K.Lb_level E
  have Eu := K.euclidean
  have hd := K.d_range.1
  constructor
  · by_contra hn
    have hm := mul_le_mul_of_nonneg_right (show E.Li ≤ K.h-1 by omega)
      (show 0 ≤ K.d by omega)
    nlinarith [Eu.lambda_eq, Eu.r_range.1]
  · by_contra hn
    have hm := mul_le_mul_of_nonneg_right (show E.Lb ≤ K.h-1 by omega)
      (show 0 ≤ K.d by omega)
    nlinarith [Eu.lambda_eq, Eu.r_range.1]

theorem Qj_pure :
    (D.b 0-1-E.Aj+E.Lj*K.d)*g.n 0 + (K.chain.R-E.Lj*K.S)*g.n 1 =
      (E.Cj+E.Lj*K.Croot+1)*g.n 2 := by
  have he := E.Qj_eq
  have hq := K.chain.qJ_exact
  linear_combination he - hq + E.Lj*K.root

theorem Lj_level (C : K.Caps E) : K.q0 ≤ E.Lj := by
  by_contra hn
  have Eu := K.euclidean
  have pure := K.Qj_pure E
  have nonneg := E.coeff_nonneg
  have levels := E.levels_pos
  have hLj := levels.2.2.1
  have hAj := nonneg.2.2.2.2.1
  have hCj := nonneg.2.2.2.2.2.1
  have hS : 1 ≤ K.S := by have hh := K.S_strong; have hg := K.chain.scalar_ranges.2.2.1; omega
  have hC : 1 ≤ K.Croot := le_trans K.chain.scalar_ranges.2.2.2 K.C_lower
  have hd := K.d_range.1
  have hLjH : E.Lj ≤ K.h := by
    simp [q0] at hn
    omega
  have hLjd_pos : 0 < E.Lj*K.d := mul_pos hLj K.d_range.1
  have hld : E.Lj*K.d ≤ K.chain.lambda := by
    have hmul := mul_le_mul_of_nonneg_right hLjH
      (show 0 ≤ K.d by omega)
    have hhd : K.h*K.d ≤ K.chain.lambda := by nlinarith [Eu.lambda_eq, Eu.r_range.1]
    exact le_trans hmul hhd
  have ci_pos : 0 < (D.b 0 : ℤ)-1-E.Aj+E.Lj*K.d := by
    have hb := K.chain.b0_exact
    have := K.chain.scalar_ranges.2.1
    nlinarith [C.Aj_cap]
  have ci_lt : (D.b 0 : ℤ)-1-E.Aj+E.Lj*K.d < D.rho 0 := by
    have hr0 : (D.rho 0 : ℤ)=D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
    have hl := K.chain.lambda_range.2.1
    omega
  by_cases hj : K.chain.R-E.Lj*K.S ≤ 0
  · have eq0 : ((D.b 0 : ℤ)-1-E.Aj+E.Lj*K.d)*g.n 0 =
        (E.Lj*K.S-K.chain.R)*g.n 1 +
        (E.Cj+E.Lj*K.Croot+1)*g.n 2 := by linarith [pure]
    have hcrit := critical0 (D:=D) ci_pos (by omega) (by nlinarith) eq0
    omega
  · have hjp : 0 < K.chain.R-E.Lj*K.S := by omega
    have ckpos : 0 < E.Cj+E.Lj*K.Croot+1 := by nlinarith
    have hkcrit := critical2 (D:=D) (c:=E.Cj+E.Lj*K.Croot+1)
      (x:=(D.b 0 : ℤ)-1-E.Aj+E.Lj*K.d)
      (y:=K.chain.R-E.Lj*K.S) ckpos (by omega) hjp.le pure.symm
    have hr := D.relation_two
    have pure2 : (E.Lj*K.d-E.Aj-1)*g.n 0 +
        (K.chain.gapJ-E.Lj*K.S)*g.n 1 =
        (E.Cj+E.Lj*K.Croot+1-D.rho 2)*g.n 2 := by
      have hR := K.chain.R_exact
      linear_combination pure + hr - g.n 1 * hR
    have hjneg : K.chain.gapJ-E.Lj*K.S < 0 := by
      have hs := K.S_strong
      nlinarith
    by_cases hi : E.Lj*K.d-E.Aj-1 ≤ 0
    · have hp := fun i => lt_trans s.m_pos (s.n_gt i)
      have hz : 0 ≤ E.Cj+E.Lj*K.Croot+1-D.rho 2 := by omega
      have hneg : (K.chain.gapJ-E.Lj*K.S)*g.n 1 < 0 :=
        mul_neg_of_neg_of_pos hjneg (hp 1)
      have hnonpos := mul_nonpos_of_nonpos_of_nonneg hi (hp 0).le
      have hnonneg := mul_nonneg hz (hp 2).le
      linarith [pure2]
    · have hiP : 0 < E.Lj*K.d-E.Aj-1 := by omega
      have eq0 : (E.Lj*K.d-E.Aj-1)*g.n 0 =
          (E.Lj*K.S-K.chain.gapJ)*g.n 1 +
          (E.Cj+E.Lj*K.Croot+1-D.rho 2)*g.n 2 := by linarith [pure2]
      have hcrit := critical0 (D:=D) hiP (by omega) (by omega) eq0
      have hilt : E.Lj*K.d-E.Aj-1 < D.rho 0 := by omega
      omega

theorem Lj_rigidity (C : K.Caps E) (hJ : K.J0 < 0) (hEq : E.Lj = K.q0) :
    K.Delta0 = 1 ∧ E.Aj = K.A0 ∧ E.Cj = K.C0 := by
  have hret := E.Qj_eq
  have hcompact := K.compact_return_equation hJ
  rw [hEq] at hret
  have hz : (E.Aj-K.A0)*g.n 0 + (K.Delta0-1)*g.n 1 +
      (E.Cj-K.C0)*g.n 2 = 0 := by
    linear_combination hcompact - hret
  have CD := K.compact_data hJ
  have Eu := K.euclidean
  have EN := E.coeff_nonneg
  have hAj0 := EN.2.2.2.2.1
  have hCj0 := EN.2.2.2.2.2.1
  have hAjU := C.Aj_cap
  have hA0 := CD.A_nonneg
  have hA0U : K.A0 ≤ K.d-1 := by
    simp [A0]
    have he := Eu.e0_range.2
    have hdlt := K.chain.scalar_ranges.1
    omega
  have hdR : K.d < D.rho 0 := by
    have hd := K.d_range.2
    have hl := K.chain.lambda_range.2.1
    have hr0 : (D.rho 0 : ℤ)=D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
    have hb := D.b_pos 0
    omega
  have hDelP := CD.Delta_pos
  have hDel0 : 0 ≤ K.Delta0-1 := by omega
  have hDelR : K.Delta0-1 < D.rho 1 := by
    have hu := CD.Delta_upper
    have hslt := K.slopes.S_lt
    have hg := K.chain.scalar_ranges.2.2.1
    omega
  have hC0 := CD.C_nonneg
  have hC0R : K.C0 < D.rho 2 := by
    simp [C0]
    have hr2 : (D.rho 2 : ℤ)=D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
    have hb := D.b_pos 2
    have hq := Eu.q0_pos
    have hc : 1 ≤ K.Croot := le_trans K.chain.scalar_ranges.2.2.2 K.C_lower
    have hp : 0 < K.q0*K.Croot := mul_pos (by omega) (by omega)
    omega
  have hCjR : E.Cj < D.rho 2 := by
    have hh := C.Cj_FJ
    have hT : 1 ≤ K.chain.T := by
      rw [K.chain.T_exact]; have hb := D.b_pos 2; have ha := K.chain.scalar_ranges.2.2.2; omega
    omega
  let w : Fin 3 → ℤ := ![E.Aj-K.A0, K.Delta0-1, E.Cj-K.C0]
  have hlo : ∀ i, -((D.critical i).coeff : ℤ) < w i := by
    intro i; fin_cases i <;> simp [w, D.coeff_rho]
    · omega
    · omega
    · omega
  have hhi : ∀ i, w i < ((D.critical i).coeff : ℤ) := by
    intro i; fin_cases i <;> simp [w, D.coeff_rho]
    · omega
    · omega
    · omega
  have hw : integerValue g w = 0 := by
    simpa [w, integerValue, Fin.sum_univ_succ, add_assoc] using hz
  have zero := critical_kernel_box_zero (fun i => lt_trans s.m_pos (s.n_gt i))
    D.critical w hw hlo hhi
  have z0 := congrFun zero 0
  have z1 := congrFun zero 1
  have z2 := congrFun zero 2
  simp [w] at z0 z1 z2
  exact ⟨by omega, by omega, by omega⟩

theorem Qk_pure :
    (D.a 0-1-E.Ak+E.Lk*K.d)*g.n 0 +
      (K.chain.T-E.Lk*K.Croot)*g.n 2 =
      (E.Bk+E.Lk*K.S+1)*g.n 1 := by
  have he := E.Qk_eq
  have hq := K.chain.qK_exact
  linear_combination he - hq + E.Lk*K.root

theorem K_pure :
    (E.Lk*K.d-E.Ak-1)*g.n 0 =
      (E.Bk+E.Lk*K.S+1-D.rho 1)*g.n 1 +
      (E.Lk*K.Croot-K.chain.alpha)*g.n 2 := by
  have pure := K.Qk_pure E
  have hr := D.relation_one
  have hT := K.chain.T_exact
  linear_combination pure + hr - g.n 2 * hT

set_option maxHeartbeats 800000 in
theorem Lk_strict_level (C : K.Caps E) (hJ : K.J0 < 0)
    (hstrict : K.chain.alpha < K.Croot) : K.q0+1 ≤ E.Lk := by
  have Eu := K.euclidean
  have EN := E.coeff_nonneg
  have EL := E.levels_pos
  have hLk := EL.2.2.2
  have hAk := EN.2.2.2.2.2.2.1
  have hBk := EN.2.2.2.2.2.2.2
  have hd := K.d_range.1
  have hS : 1 ≤ K.S := by have hh := K.S_strong; have hg := K.chain.scalar_ranges.2.2.1; omega
  have hC : 1 ≤ K.Croot := le_trans K.chain.scalar_ranges.2.2.2 K.C_lower
  have hbase : K.q0 ≤ E.Lk := by
    by_contra hn
    have hLh : E.Lk ≤ K.h := by simp [q0] at hn; omega
    have hld : E.Lk*K.d ≤ K.chain.lambda := by
      have hm := mul_le_mul_of_nonneg_right hLh (show 0 ≤ K.d by omega)
      have hh : K.h*K.d ≤ K.chain.lambda := by nlinarith [Eu.lambda_eq, Eu.r_range.1]
      exact le_trans hm hh
    have pure := K.Qk_pure E
    have ciP : 0 < (D.a 0 : ℤ)-1-E.Ak+E.Lk*K.d := by
      have ha0 : (1 : ℤ) ≤ D.a 0 := by exact_mod_cast D.a_pos 0
      have hmul : K.d ≤ E.Lk*K.d := by
        nlinarith [mul_nonneg (show 0 ≤ E.Lk-1 by omega) (show 0 ≤ K.d by omega)]
      have hcap := C.Ak_cap
      omega
    have ciL : (D.a 0 : ℤ)-1-E.Ak+E.Lk*K.d < D.rho 0 := by
      have hr0 : (D.rho 0 : ℤ)=D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
      have hl := K.chain.lambda_range.2.2
      omega
    by_cases hk : K.chain.T-E.Lk*K.Croot ≤ 0
    · have eq0 : ((D.a 0 : ℤ)-1-E.Ak+E.Lk*K.d)*g.n 0 =
          (E.Bk+E.Lk*K.S+1)*g.n 1 +
          (E.Lk*K.Croot-K.chain.T)*g.n 2 := by linarith [pure]
      have hcrit := critical0 (D:=D) ciP (by nlinarith) (by omega) eq0
      omega
    · have kp := K.K_pure E
      have hkP : 0 < K.chain.T-E.Lk*K.Croot := by omega
      have rhsP : 0 < E.Bk+E.Lk*K.S+1 := by nlinarith
      have jcrit := critical1 (D:=D)
        (c:=E.Bk+E.Lk*K.S+1)
        (x:=(D.a 0 : ℤ)-1-E.Ak+E.Lk*K.d)
        (z:=K.chain.T-E.Lk*K.Croot)
        rhsP ciP.le hkP.le pure.symm
      have hkcoef : 0 < E.Lk*K.Croot-K.chain.alpha := by
        have hp := mul_pos hLk (show 0 < K.Croot by omega)
        nlinarith
      by_cases hi : E.Lk*K.d-E.Ak-1 ≤ 0
      · have hp := fun i => lt_trans s.m_pos (s.n_gt i)
        have hjcoef : 0 ≤ E.Bk+E.Lk*K.S+1-D.rho 1 := by omega
        have h0 := mul_nonpos_of_nonpos_of_nonneg hi (hp 0).le
        have h1 := mul_nonneg hjcoef (hp 1).le
        have h2 := mul_pos hkcoef (hp 2)
        nlinarith [kp]
      · have hiP : 0 < E.Lk*K.d-E.Ak-1 := by omega
        have hcrit := critical0 (D:=D) hiP (by omega) hkcoef.le kp
        have hiL : E.Lk*K.d-E.Ak-1 < D.rho 0 := by omega
        omega
  by_contra hn
  have hEq : E.Lk = K.q0 := by omega
  have kp := K.K_pure E
  rw [hEq] at kp
  have hqS : (D.rho 1 : ℤ) < K.q0*K.S := by
    simp [J0] at hJ
    have hg := K.chain.scalar_ranges.2.2.1
    omega
  have hj : 0 ≤ E.Bk+K.q0*K.S+1-D.rho 1 := by omega
  have hk : 0 < K.q0*K.Croot-K.chain.alpha := by
    have hp := mul_pos (show 0 < K.q0 by omega) (show 0 < K.Croot by omega)
    nlinarith
  have hi : 0 < K.q0*K.d-E.Ak-1 := by
    have hp := fun i => lt_trans s.m_pos (s.n_gt i)
    by_contra hh
    have h0 := mul_nonpos_of_nonpos_of_nonneg (show K.q0*K.d-E.Ak-1 ≤ 0 by omega) (hp 0).le
    have h1 := mul_nonneg hj (hp 1).le
    have h2 := mul_pos hk (hp 2)
    nlinarith [kp]
  have hcrit := critical0 (D:=D) hi hj hk.le kp
  have gap := K.rho_gap_nonneg
  omega

theorem FK_completed (hJ : K.J0 < 0) :
    F = (E.Lk-K.q0-1)*g.m +
      (E.Ak+K.chain.beta+K.chain.delta-K.e0)*g.n 0 +
      (E.Bk+K.chain.R+K.q0*K.S-D.rho 1)*g.n 1 +
      (K.q0*K.Croot+D.b 2-1)*g.n 2 := by
  have he := E.Qk_eq
  have hc := K.chain.cK_exact
  simp [complement, W] at hc
  have hr := D.relation_one
  have ha := K.chain.a0_exact
  have base : F+g.n 2 = (E.Lk-1)*g.m +
      (E.Ak+K.chain.beta)*g.n 0 +
      (E.Bk+K.chain.R)*g.n 1 := by
    linear_combination he + hc
  simp [e0]
  linear_combination base + K.q0*K.root + hr - g.n 2 + g.n 0*ha

theorem sum_notch (hF : s.semigroup.IsFrobenius F) (C : K.Caps E)
    (hJ : K.J0 < 0) (hstrict : K.chain.alpha < K.Croot) :
    E.Ak+K.chain.beta+K.chain.delta ≤ K.e0-1 ∧
      K.chain.beta+K.chain.delta+1 ≤ K.e0 := by
  have level := K.Lk_strict_level E C hJ hstrict
  have EN := E.coeff_nonneg
  have hAk := EN.2.2.2.2.2.2.1
  have hBk := EN.2.2.2.2.2.2.2
  have hR : 1 ≤ K.chain.R := by rw [K.chain.R_exact]; have := D.a_pos 1; have := K.chain.scalar_ranges.2.2.1; omega
  have hqS : (D.rho 1 : ℤ) < K.q0*K.S := by
    simp [J0] at hJ
    have hg := K.chain.scalar_ranges.2.2.1
    omega
  have hC : 1 ≤ K.Croot := le_trans K.chain.scalar_ranges.2.2.2 K.C_lower
  have hb2 : (1 : ℤ) ≤ D.b 2 := by exact_mod_cast D.b_pos 2
  have hq : 1 ≤ K.q0 := by have := K.euclidean.q0_pos; omega
  have hqC : 1 ≤ K.q0*K.Croot := by
    nlinarith [mul_pos (show 0 < K.q0 by omega) (show 0 < K.Croot by omega)]
  have hf := K.FK_completed E hJ
  have hi : E.Ak+K.chain.beta+K.chain.delta-K.e0 < 0 := by
    by_contra hn
    have hm := four_mem (g:=g) (E.Lk-K.q0-1)
      (E.Ak+K.chain.beta+K.chain.delta-K.e0)
      (E.Bk+K.chain.R+K.q0*K.S-D.rho 1)
      (K.q0*K.Croot+D.b 2-1)
      (by omega) (by omega) (by omega)
      (by omega)
    apply hF.1
    change F ∈ g.Gamma
    rw [hf]
    exact hm
  constructor
  · omega
  · omega

end ChainCore
end P21.Nonsymmetric
