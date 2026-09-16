import P21.Symmetric.BranchII
import P21.Symmetric.Raw4
import P21.Symmetric.RawRows
import P21.Symmetric.Raw4Consequences

/-! All Branch II arithmetic premises below are connected to the same actual RAW4
rows. In particular FS and the complementary gaps are derived, not assumed. -/
namespace P21.Symmetric.BranchIIActual
open BranchII
variable {g : Generators} {G : SymmetricGlueData g} {setting : g.Setting} {F : ℤ}
variable (R : Raw4Data G setting F)

theorem row_x : ActualRawRow setting F G.frobenius (R.A*(G.d*G.two.u)) :=
  R.rows _ (by simp)
theorem row_y : ActualRawRow setting F G.frobenius (R.B*(G.d*G.two.v)) :=
  R.rows _ (by simp)
theorem row_px : ActualRawRow setting F G.frobenius
    ((G.d-R.s)*G.w+R.Ap*(G.d*G.two.u)) := R.rows _ (by simp)
theorem row_py : ActualRawRow setting F G.frobenius
    ((G.d-R.s)*G.w+R.Bp*(G.d*G.two.v)) := R.rows _ (by simp)

theorem rho_uv : R.rho = G.two.u*G.two.v-R.A*G.two.u-R.B*G.two.v := by
  linear_combination R.rho_eq+G.two.v*R.sumBC

theorem rho_primed_uv :
    R.rho = G.two.u*G.two.v-G.w-R.Ap*G.two.u-R.Bp*G.two.v := by
  linear_combination R.rhop_eq+G.two.v*R.sumBpCp

include setting in
theorem m_lt_w : g.m < G.w := by simpa [G.z_eq] using setting.n_gt (G.perm 2)

theorem actual_fs (hF : setting.semigroup.IsFrobenius F)
    {e theta : ℤ} (hm : g.m=e*G.w+G.d*theta) (n : ℤ) (hn : 1 ≤ n) :
    tau G.d R.s e G.w R.rho theta n ∈ G.two.T := by
  have hfs := stable_walk setting hF G.symmetry n.toNat (by omega)
  have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
  rw [hncast,stable_coordinate_identity R.rdef hm] at hfs
  exact (G.normal_form_mem_iff (layer_bounds G.d_pos).1 (layer_bounds G.d_pos).2).1 hfs

theorem actual_complement_gap {e theta : ℤ} (hm : g.m=e*G.w+G.d*theta)
    (n : ℤ) (hn : 1 ≤ n) : BranchII.complement G.d e G.w R.B G.two.v theta n ∉ G.two.T := by
  intro ht
  have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
  have hgap := (row_y R).sub_multiple_gap n.toNat (by omega)
  rw [hncast,complement_coordinate_identity hm] at hgap
  exact hgap ((G.normal_form_mem_iff
    (complementLayer_bounds G.d_pos).1 (complementLayer_bounds G.d_pos).2).2 ht)

/-- The zero-index x-row predecessor is an actual H-element, with positive C. -/
theorem x_minus_y_mem :
    R.A*(G.d*G.two.u)+(G.frobenius-F-g.m)-g.n (G.perm 1) ∈ g.H := by
  rw [G.y_eq]
  have he : R.A*(G.d*G.two.u)+(G.frobenius-F-g.m)-G.d*G.two.v =
      R.s*G.w+G.d*((R.C-1)*G.two.v) := by
    rw [R.rdef]
    linear_combination G.d*R.rho_eq
  rw [he]
  apply (G.normal_form_mem_iff R.hspos.le R.hslt).2
  exact ⟨0,R.C-1,by norm_num,by have := R.C_pos; omega,by ring⟩

/-- k0=1 reduces to the independently excluded Branch I using the two actual
primed-row backward gaps. The auxiliary positivity is derived from r>0 and m<w. -/
theorem k1_excluded (hF : setting.semigroup.IsFrobenius F)
    (hcan : setting.semigroup.Canonical F g.m)
    {e mu theta t₀ : ℤ} (_he0 : 0 ≤ e) (hed : e < G.d)
    (hem : g.m=e*G.w+G.d*mu) (htheta : theta=mu+G.w)
    (hse : R.s+1 ≤ e) (hbranch : theta=R.rho+G.two.u+G.two.v+t₀)
    (hnotI : theta-G.two.u-G.two.v ∉ G.two.T) : False := by
  have hm : g.m=G.d*theta-(G.d-e)*G.w := by
    linear_combination hem-G.d*htheta
  have hr : 0 < R.s*G.w+G.d*R.rho := by
    rw [← R.rdef]
    exact stable_shift_pos setting hF G.symmetry
  have haux := k1_aux_pos G.d_pos (G.w_pos setting)
    (show G.d-e+R.s+1 ≤ G.d by omega) hr
    (show G.d*theta-(G.d-e)*G.w < G.w by rw [← hm]; exact m_lt_w (setting := setting))
  have hg : 0 < G.w-G.two.u-G.two.v-t₀ := by omega
  have hmu : mu = R.rho+G.two.u+G.two.v+t₀-G.w := by omega
  have hk0 : 0 ≤ G.d-e := by omega
  have hkd : G.d-e < G.d := by have := R.hspos; omega
  have hx : R.Ap*G.two.u+(G.w-G.two.u-G.two.v-t₀) ∉ G.two.T := by
    intro ht
    apply (row_px R).backward_gap hF hcan G.symmetry
    have he : (G.d-R.s)*G.w+R.Ap*(G.d*G.two.u)+(G.frobenius-F-g.m)-g.m =
        (G.d-e)*G.w+G.d*(R.Ap*G.two.u+(G.w-G.two.u-G.two.v-t₀)) := by
      rw [R.rdef,hem,hmu]
      ring
    rw [he]
    exact (G.normal_form_mem_iff hk0 hkd).2 ht
  have hy : R.Bp*G.two.v+(G.w-G.two.u-G.two.v-t₀) ∉ G.two.T := by
    intro ht
    apply (row_py R).backward_gap hF hcan G.symmetry
    have he : (G.d-R.s)*G.w+R.Bp*(G.d*G.two.v)+(G.frobenius-F-g.m)-g.m =
        (G.d-e)*G.w+G.d*(R.Bp*G.two.v+(G.w-G.two.u-G.two.v-t₀)) := by
      rw [R.rdef,hem,hmu]
      ring
    rw [he]
    exact (G.normal_form_mem_iff hk0 hkd).2 ht
  exact hnotI (k1_reduces_to_branchI G.two R.Ap_pos
    (by have := R.sumApDp; have := R.Dp_pos; omega) R.Bp_pos
    (by have := R.sumBpCp; have := R.Cp_pos; omega)
    (rho_primed_uv R) hbranch hg hx hy)

/-- All k0=0 subcases are eliminated using the same actual x/y rows. -/
theorem k0_excluded (hF : setting.semigroup.IsFrobenius F)
    (hcan : setting.semigroup.Canonical F g.m)
    {e theta t₀ : ℤ} (he0 : 0 ≤ e) (hed : e < G.d)
    (hm : g.m=e*G.w+G.d*theta)
    (hbranch : theta=R.rho+G.two.u+G.two.v+t₀) (ht₀ : t₀ ∈ G.two.T) : False := by
  have hgap : theta ∉ G.two.T := by
    intro ht
    apply m_not_mem_tail setting
    rw [hm]
    exact (G.normal_form_mem_iff he0 hed).2 ht
  by_cases hezero : e = 0
  · have hm' : g.m=G.d*theta := by simpa [hezero] using hm
    have hmu : theta < G.two.u := by
      have h := setting.n_gt (G.perm 0)
      rw [G.x_eq,hm'] at h
      nlinarith [G.d_pos]
    have hmv : theta < G.two.v := by
      have h := setting.n_gt (G.perm 1)
      rw [G.y_eq,hm'] at h
      nlinarith [G.d_pos]
    have hf := actual_fs R hF hm 1 (by omega)
    have hc : carry G.d R.s e 1 = 0 := by
      dsimp [carry]
      rw [hezero]
      simp only [mul_zero,add_zero]
      exact div_eq_of_bounds G.d_pos (by have := R.hspos; omega) (by simpa using R.hslt)
    dsimp [tau] at hf
    rw [hc] at hf
    apply k0_e0_impossible G.two hbranch ht₀ hmu hmv
    simpa using hf
  · have he : 0 < e := by omega
    have hL : 0 < G.two.u+G.two.v+t₀ := by
      have := G.two.nonneg ht₀
      have := G.two.u_pos
      have := G.two.v_pos
      omega
    have phase := crosscore_phase G.d_pos R.hspos.le R.hslt he hed (G.w_pos setting) hL
      (show theta=R.rho+(G.two.u+G.two.v+t₀) by omega)
      (show e*G.w+G.d*theta<G.w by rw [← hm]; exact m_lt_w (setting := setting))
      (G.two.nonneg (actual_fs R hF hm 1 (by omega)))
    obtain ⟨p,q,hp,hq,htrep⟩ := ht₀
    have hcoef := k0_theta_coefficients G.two hp hq (rho_uv R)
      (show theta=R.rho+G.two.u+G.two.v+(p*G.two.u+q*G.two.v) by rw [← htrep]; exact hbranch)
      hgap (by have := R.sumAD; have := R.D_pos; omega)
      (by have := R.sumBC; have := R.C_pos; omega)
    have hshift : ∀ n : ℤ, 1 ≤ n → tau G.d R.s e G.w R.rho theta n+R.A*G.two.u-G.two.v ∈ G.two.T := by
      intro n hn
      exact crosscore_shift_mem G.two G.d_pos R.hspos.le R.hslt he hed phase.2.1 phase.2.2.2.2
        R.A_pos.le R.sumAD (show R.A-1-p ≤ R.A-1 by omega)
        (show 0 < G.two.u-(R.B-1-q) by have := R.sumBC; have := R.C_pos; omega)
        (show G.two.u-(R.B-1-q) < G.two.u by omega) hcoef.2.2.1 (rho_uv R)
        (actual_fs R hF hm) (actual_complement_gap R hm) n hn
    apply (row_x R).predecessor_not_stable hF hcan G.symmetry (G.perm 1)
    intro n
    cases n with
    | zero => simpa using x_minus_y_mem R
    | succ n =>
      have ht := hshift (n+1) (by omega)
      have hb := layer_bounds (s := R.s) (e := e) (n := (n+1:ℕ)) G.d_pos
      have hh := (G.normal_form_mem_iff hb.1 hb.2).2 ht
      rw [G.y_eq]
      convert hh using 1; push_cast; dsimp [layer,tau]; rw [R.rdef,hm]; ring

end P21.Symmetric.BranchIIActual



namespace P21.Symmetric.Raw4Data
variable {g : Generators} {G : SymmetricGlueData g} {setting : g.Setting} {F : ℤ}

/-- The complete Branch II exclusion, with all gaps and stable points supplied
by actual RAW4 data, and k0=1 reduced to the independent Branch I theorem. -/
theorem branchII_excluded (R : Raw4Data G setting F)
    (hF : setting.semigroup.IsFrobenius F) (hcan : setting.semigroup.Canonical F g.m)
    {e μ : ℤ} (he : 0 ≤ e) (hed : e < G.d) (hm : g.m=e*G.w+G.d*μ) :
    (μ+((G.d-1-R.s+e)/G.d)*G.w)-R.rho-G.two.u-G.two.v ∉ G.two.T := by
  intro hII
  rcases G.carry_binary R.hspos R.hslt he hed with hk | hk
  · have ht : μ-R.rho-G.two.u-G.two.v ∈ G.two.T := by simpa [hk] using hII
    exact BranchIIActual.k0_excluded R hF hcan he hed hm
      (show μ=R.rho+G.two.u+G.two.v+(μ-R.rho-G.two.u-G.two.v) by ring) ht
  · have ht : μ+G.w-R.rho-G.two.u-G.two.v ∈ G.two.T := by simpa [hk] using hII
    have hnotI : μ+G.w-G.two.u-G.two.v ∉ G.two.T := by
      simpa [hk] using R.branchI_excluded hF hcan he hed hm
    exact BranchIIActual.k1_excluded R hF hcan he hed hm rfl
      ((G.carry_one_iff R.hspos R.hslt he hed).mp hk)
      (show μ+G.w=R.rho+G.two.u+G.two.v+(μ+G.w-R.rho-G.two.u-G.two.v) by ring) hnotI

end P21.Symmetric.Raw4Data
