import P21.Symmetric.CrossLayer

namespace P21.Symmetric
namespace SymmetricGlueData
variable {g : Generators} (G : SymmetricGlueData g)

theorem layer_mem_iff (j t : ℤ) :
    j * G.w + G.d * t ∈ g.H ↔ t + (j / G.d) * G.w ∈ G.two.T := by
  have he : j * G.w + G.d * t =
      (j % G.d) * G.w + G.d * (t + (j / G.d) * G.w) := by
    have h := Int.ediv_mul_add_emod j G.d
    linear_combination -G.w * h
  rw [he]
  exact G.normal_form_mem_iff (Int.emod_nonneg _ (ne_of_gt G.d_pos))
    (Int.emod_lt_of_pos _ G.d_pos)

theorem multiplicity_bounds (s : g.Setting) :
    0 < g.m ∧ g.m < G.d * G.two.u ∧ g.m < G.d * G.two.v ∧ g.m < G.w := by
  exact ⟨s.m_pos, by simpa [G.x_eq] using s.n_gt (G.perm 0),
    by simpa [G.y_eq] using s.n_gt (G.perm 1),
    by simpa [G.z_eq] using s.n_gt (G.perm 2)⟩

theorem multiplicity_coordinate_gap (s : g.Setting) {e μ : ℤ}
    (he : 0 ≤ e) (hed : e < G.d) (hm : g.m = e * G.w + G.d * μ) :
    μ ∉ G.two.T := by
  intro hμ
  apply m_not_mem_tail s
  rw [hm]
  exact (G.normal_form_mem_iff he hed).mpr hμ

theorem carry_binary {s e : ℤ} (hs : 0 < s) (hsd : s < G.d)
    (he : 0 ≤ e) (hed : e < G.d) :
    (G.d - 1 - s + e) / G.d = 0 ∨ (G.d - 1 - s + e) / G.d = 1 := by
  have hdiv := Int.ediv_mul_add_emod (G.d - 1 - s + e) G.d
  have hr := Int.emod_nonneg (G.d - 1 - s + e) (ne_of_gt G.d_pos)
  have hrlt := Int.emod_lt_of_pos (G.d - 1 - s + e) G.d_pos
  have hklo : 0 ≤ (G.d - 1 - s + e) / G.d :=
    Int.ediv_nonneg (by omega) G.d_pos.le
  have hkhi : (G.d - 1 - s + e) / G.d ≤ 1 := by
    by_contra hn
    have hn' : 2 ≤ (G.d - 1 - s + e) / G.d := by omega
    have := mul_le_mul_of_nonneg_right hn' G.d_pos.le
    nlinarith
  omega

theorem carry_one_iff {s e : ℤ} (hs : 0 < s) (hsd : s < G.d)
    (he : 0 ≤ e) (hed : e < G.d) :
    (G.d - 1 - s + e) / G.d = 1 ↔ s + 1 ≤ e := by
  have hdiv := Int.ediv_mul_add_emod (G.d - 1 - s + e) G.d
  have hr := Int.emod_nonneg (G.d - 1 - s + e) (ne_of_gt G.d_pos)
  have hrlt := Int.emod_lt_of_pos (G.d - 1 - s + e) G.d_pos
  constructor
  · intro hk
    rw [hk] at hdiv
    omega
  · intro hle
    rcases G.carry_binary hs hsd he hed with hk | hk
    · rw [hk] at hdiv
      omega
    · exact hk

/-- QM of the x-row transported into the unique bounded-layer coordinates. -/
theorem qm_x_coordinate (s₀ : g.Setting) {F s ρ A B e μ : ℤ}
    (hF : s₀.semigroup.IsFrobenius F) (hcan : s₀.semigroup.Canonical F g.m)
    (hrow : ActualRawRow s₀ F G.frobenius (A * (G.d * G.two.u)))
    (hr : G.frobenius - F - g.m = s * G.w + G.d * ρ)
    (hρ : ρ = G.two.u * G.two.v - A * G.two.u - B * G.two.v)
    (hm : g.m = e * G.w + G.d * μ) :
    (μ + ((G.d - 1 - s + e) / G.d) * G.w) + (B - 1) * G.two.v - G.two.u ∈ G.two.T := by
  have h := hrow.pf_add_m_mem_tail hF hcan G.symmetry
  have he : F + g.m - A * (G.d * G.two.u) + g.m =
      (G.d - 1 - s + e) * G.w + G.d * (μ + (B - 1) * G.two.v - G.two.u) := by
    dsimp [frobenius, TwoGeneratorData.frobenius] at hr
    linear_combination -hr - G.d * hρ + hm
  rw [he, G.layer_mem_iff] at h
  convert h using 1; ring

theorem qm_y_coordinate (s₀ : g.Setting) {F s ρ A B e μ : ℤ}
    (hF : s₀.semigroup.IsFrobenius F) (hcan : s₀.semigroup.Canonical F g.m)
    (hrow : ActualRawRow s₀ F G.frobenius (B * (G.d * G.two.v)))
    (hr : G.frobenius - F - g.m = s * G.w + G.d * ρ)
    (hρ : ρ = G.two.u * G.two.v - A * G.two.u - B * G.two.v)
    (hm : g.m = e * G.w + G.d * μ) :
    (μ + ((G.d - 1 - s + e) / G.d) * G.w) + (A - 1) * G.two.u - G.two.v ∈ G.two.T := by
  have h := hrow.pf_add_m_mem_tail hF hcan G.symmetry
  have he : F + g.m - B * (G.d * G.two.v) + g.m =
      (G.d - 1 - s + e) * G.w + G.d * (μ + (A - 1) * G.two.u - G.two.v) := by
    dsimp [frobenius, TwoGeneratorData.frobenius] at hr
    linear_combination -hr - G.d * hρ + hm
  rw [he, G.layer_mem_iff] at h
  convert h using 1; ring

end SymmetricGlueData
end P21.Symmetric
