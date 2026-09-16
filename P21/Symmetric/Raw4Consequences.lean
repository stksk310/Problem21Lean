import P21.Symmetric.Raw4
import P21.Symmetric.Reduction
import P21.Symmetric.BranchIActual

namespace P21.Symmetric.BranchIRealization

/-- The source's auxiliary E is positive, although the hit contradiction is stronger. -/
theorem difference_pos {g : Generators} {B : BranchIData} {G : SymmetricGlueData g}
    {F f : ℤ} (R : BranchIRealization B G F f) (setting : g.Setting) : 0 < B.w-B.L := by
  have hw : 0 < B.w := by rw [← R.w_eq]; exact G.w_pos setting
  have hm := setting.n_gt (G.perm 2)
  rw [G.z_eq, R.m_eq, R.w_eq] at hm
  have hd : 0 < B.d := by have := B.d_ge_two; omega
  have hk : 0 < B.d-(B.κ+1) := by have := B.κ_le; have := B.s_pos; omega
  have hprod := mul_pos hk hw
  nlinarith

end P21.Symmetric.BranchIRealization

namespace P21.Symmetric.Raw4Data
variable {g : Generators} {G : SymmetricGlueData g} {setting : g.Setting} {F : ℤ}
variable (R : Raw4Data G setting F)

theorem row_x : ActualRawRow setting F G.frobenius (R.A * (G.d * G.two.u)) :=
  R.rows _ (by simp)
theorem row_y : ActualRawRow setting F G.frobenius (R.B * (G.d * G.two.v)) :=
  R.rows _ (by simp)
theorem row_px : ActualRawRow setting F G.frobenius ((G.d-R.s)*G.w+R.Ap*(G.d*G.two.u)) :=
  R.rows _ (by simp)
theorem row_py : ActualRawRow setting F G.frobenius ((G.d-R.s)*G.w+R.Bp*(G.d*G.two.v)) :=
  R.rows _ (by simp)

theorem A_lt : R.A < G.two.v := by have := R.D_pos; have := R.sumAD; omega
theorem B_lt : R.B < G.two.u := by have := R.C_pos; have := R.sumBC; omega
theorem Ap_lt : R.Ap < G.two.v := by have := R.Dp_pos; have := R.sumApDp; omega
theorem Bp_lt : R.Bp < G.two.u := by have := R.Cp_pos; have := R.sumBpCp; omega

theorem rho_formula : R.rho = G.two.u*G.two.v-R.A*G.two.u-R.B*G.two.v := by
  linear_combination R.rho_eq + G.two.v * R.sumBC
theorem rhop_formula : R.rho+G.w = G.two.u*G.two.v-R.Ap*G.two.u-R.Bp*G.two.v := by
  linear_combination R.rhop_eq + G.two.v * R.sumBpCp
theorem rho_y : R.rho = -R.B*G.two.v+R.D*G.two.u := by
  linear_combination R.rho_formula - G.two.u * R.sumAD
theorem rhop_y : R.rho+G.w = -R.Bp*G.two.v+R.Dp*G.two.u := by
  linear_combination R.rhop_formula - G.two.u * R.sumApDp

theorem Ap_lt_A : R.Ap < R.A := by
  exact cross_layer_drop g.H _ G.w_mem_tail
    (G.d_mul_mem_tail ⟨1,0,by norm_num,by norm_num,by ring⟩)
    (G.w_pos setting) (mul_pos G.d_pos G.two.u_pos)
    (by have := R.hslt; omega) R.row_x.1.1 R.row_px.1
theorem Bp_lt_B : R.Bp < R.B := by
  exact cross_layer_drop g.H _ G.w_mem_tail
    (G.d_mul_mem_tail ⟨0,1,by norm_num,by norm_num,by ring⟩)
    (G.w_pos setting) (mul_pos G.d_pos G.two.v_pos)
    (by have := R.hslt; omega) R.row_y.1.1 R.row_py.1

theorem w_formula : G.w = (R.A-R.Ap)*G.two.u+(R.B-R.Bp)*G.two.v :=
  cross_layer_identity G.two R.rho_formula R.rhop_formula

theorem split (hF : setting.semigroup.IsFrobenius F)
    (hcan : setting.semigroup.Canonical F g.m) {e μ : ℤ}
    (hm : g.m = e*G.w+G.d*μ) :
    (μ+((G.d-1-R.s+e)/G.d)*G.w)-G.two.u-G.two.v ∈ G.two.T ∨
    (μ+((G.d-1-R.s+e)/G.d)*G.w)-R.rho-G.two.u-G.two.v ∈ G.two.T :=
  complete_split G.two R.A_pos R.A_lt R.B_pos R.B_lt R.rho_formula
    (G.qm_x_coordinate setting hF hcan R.row_x R.rdef R.rho_formula hm)
    (G.qm_y_coordinate setting hF hcan R.row_y R.rdef R.rho_formula hm)

theorem branchI_excluded (hF : setting.semigroup.IsFrobenius F)
    (hcan : setting.semigroup.Canonical F g.m) {e μ : ℤ}
    (he : 0 ≤ e) (hed : e < G.d) (hm : g.m = e*G.w+G.d*μ) :
    (μ+((G.d-1-R.s+e)/G.d)*G.w)-G.two.u-G.two.v ∉ G.two.T := by
  intro hI
  let k := (G.d-1-R.s+e)/G.d
  have hk : k = 1 := by
    rcases G.carry_binary R.hspos R.hslt he hed with hk | hk
    · have hμ : μ ∈ G.two.T := by
        have h := G.two.T.add_mem hI
          (show G.two.u+G.two.v ∈ G.two.T from ⟨1,1,by norm_num,by norm_num,by ring⟩)
        simpa [hk] using h
      exact False.elim (G.multiplicity_coordinate_gap setting he hed hm hμ)
    · exact hk
  have hes : R.s+1 ≤ e := (G.carry_one_iff R.hspos R.hslt he hed).mp hk
  obtain ⟨p,q,hp,hq,hpq⟩ := hI
  let B : BranchIData := {
    base := G.two, d := G.d, s := R.s, κ := G.d-e,
    a := R.Ap, b := R.Bp, α := R.A-R.Ap, β := R.B-R.Bp,
    p₀ := p, q₀ := q,
    d_ge_two := G.d_ge_two, s_pos := R.hspos, s_lt := R.hslt,
    κ_pos := by omega, κ_le := by omega,
    a_pos := R.Ap_pos, b_pos := R.Bp_pos,
    α_pos := by have := R.Ap_lt_A; omega,
    β_pos := by have := R.Bp_lt_B; omega,
    aα_lt := by simpa using R.A_lt,
    bβ_lt := by simpa using R.B_lt,
    p₀_nonneg := hp, q₀_nonneg := hq }
  have hw : G.w = B.w := R.w_formula
  have hL : B.L = μ + G.w := by
    change (p+1)*G.two.u+(q+1)*G.two.v = μ+G.w
    change μ+k*G.w-G.two.u-G.two.v = p*G.two.u+q*G.two.v at hpq
    rw [hk] at hpq
    linear_combination -hpq
  have hρ : B.ρ = R.rho := by
    change G.two.u*G.two.v-B.w-R.Ap*G.two.u-R.Bp*G.two.v = R.rho
    rw [← hw]
    linear_combination -R.rhop_formula
  have hreal : BranchIRealization B G F G.frobenius := {
    two_eq := rfl, d_eq := rfl, w_eq := hw,
    m_eq := by rw [hL, ← hw]; change g.m=G.d*(μ+G.w)-(G.d-e)*G.w; linear_combination hm,
    r_eq := by rw [hρ, ← hw]; exact R.rdef }
  apply hreal.impossible setting hF hcan G.symmetry
  · convert R.row_x using 1
    dsimp [B]
    ring
  · convert R.row_y using 1
    dsimp [B]
    ring

end P21.Symmetric.Raw4Data
