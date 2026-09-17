import P21.Symmetric.Classification.SymmetricRigidity
import P21.Symmetric.Classification.GcdDecomposition

namespace P21.Symmetric.Classification

/-- An element below an Apéry element in the semigroup order is still Apéry. -/
theorem apery_gap_of_sub_mem (H : AddSubmonoid ℤ) {top x t : ℤ}
    (hgap : top - x ∉ H) (hsub : top - t ∈ H) : t - x ∉ H := by
  intro hm
  apply hgap
  convert H.add_mem hsub hm using 1; ring

/-- Distinct nonnegative representations by a primitive pair contain its
least common multiple in the semigroup order. -/
theorem two_representations_sub_lcm_mem (H : AddSubmonoid ℤ) (D : TwoGeneratorData)
    {d top a b c e : ℤ} (hd : 0 < d)
    (hu : d * D.u ∈ H) (hv : d * D.v ∈ H)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hab : top = a * (d * D.u) + b * (d * D.v))
    (hce : top = c * (d * D.u) + e * (d * D.v))
    (hne : a ≠ c ∨ b ≠ e) : top - d * D.u * D.v ∈ H := by
  have hrel : a * D.u + b * D.v = c * D.u + e * D.v := by
    have hmul : d * (a * D.u + b * D.v) = d * (c * D.u + e * D.v) := by
      linear_combination hce - hab
    exact mul_left_cancel₀ (ne_of_gt hd) hmul
  obtain ⟨k, hak, hbk⟩ := D.representation_difference hrel
  have hk : k ≠ 0 := by
    intro hk
    simp only [hk, zero_mul, neg_zero, sub_eq_zero] at hak hbk
    exact hne.elim (fun h => h hak) (fun h => h hbk)
  rcases lt_or_gt_of_ne hk with hk | hk
  · have hk' : k ≤ -1 := by omega
    have hcv : 0 ≤ c - D.v := by nlinarith [D.v_pos]
    have hm := H.add_mem (nonneg_mul_mem H hcv hu) (nonneg_mul_mem H he hv)
    convert hm using 1
    linear_combination hce
  · have hk' : 1 ≤ k := by omega
    have hav : 0 ≤ a - D.v := by nlinarith [D.v_pos]
    have hm := H.add_mem (nonneg_mul_mem H hav hu) (nonneg_mul_mem H hb hv)
    convert hm using 1
    linear_combination hab

/-- Two distinct pair factorizations at an Apéry point force the primitive
least common multiple itself to be Apéry. -/
theorem two_representations_lcm_apery (H : AddSubmonoid ℤ) (D : TwoGeneratorData)
    {d top x a b c e : ℤ} (hd : 0 < d)
    (hu : d * D.u ∈ H) (hv : d * D.v ∈ H)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hab : top = a * (d * D.u) + b * (d * D.v))
    (hce : top = c * (d * D.u) + e * (d * D.v))
    (hne : a ≠ c ∨ b ≠ e) (hgap : top - x ∉ H) :
    d * D.u * D.v ∈ H ∧ d * D.u * D.v - x ∉ H := by
  constructor
  · convert nonneg_mul_mem H D.v_pos.le hu using 1; ring
  · exact apery_gap_of_sub_mem H hgap
      (two_representations_sub_lcm_mem H D hd hu hv ha hb hc he hab hce hne)

/-- The multiple-factorization branch supplies actual nonnegative primitive
membership, with no symmetry assumption beyond the supplied Apéry gap. -/
theorem primitive_mem_of_two_representations (H : AddSubmonoid ℤ) (D : TwoGeneratorData)
    {d top x a b c e : ℤ} (hd : 0 < d) (hx : x ∈ H)
    (hu : d * D.u ∈ H) (hv : d * D.v ∈ H)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hab : top = a * (d * D.u) + b * (d * D.v))
    (hce : top = c * (d * D.u) + e * (d * D.v))
    (hne : a ≠ c ∨ b ≠ e) (hgap : top - x ∉ H) : x ∈ D.T := by
  exact primitive_mem_of_lcm_gap H D (by omega) hx hu hv
    (two_representations_lcm_apery H D hd hu hv ha hb hc he hab hce hne hgap).2

/-- Two different pair representations of the Frobenius translate close the
multiple-factorization branch, including all gluing lower bounds. -/
theorem two_top_representations_glue_data (g : Generators) (s : g.Setting)
    (hcommon : ∀ d : ℤ, (∀ i, d ∣ g.n i) → d ∣ 1)
    (p : Equiv.Perm (Fin 3)) {f a b c e : ℤ} (hf : f ∉ g.H)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hab : f + g.n (p 2) = a * g.n (p 0) + b * g.n (p 1))
    (hce : f + g.n (p 2) = c * g.n (p 0) + e * g.n (p 1))
    (hne : a ≠ c ∨ b ≠ e) : Nonempty (SymmetricGlueData g) := by
  obtain ⟨D, _, _, hx, hy⟩ := primitive_pair_data g s p
  let d : ℤ := Int.gcd (g.n (p 0)) (g.n (p 1))
  have hd : 0 < d := by
    have hpos : 0 < g.n (p 0) := lt_trans s.m_pos (s.n_gt _)
    change 0 < (Int.gcd (g.n (p 0)) (g.n (p 1)) : ℤ)
    exact_mod_cast Int.gcd_pos_of_ne_zero_left (g.n (p 1)) (ne_of_gt hpos)
  have hu : d * D.u ∈ g.H := by rw [← hx]; exact generator_mem g.n _
  have hv : d * D.v ∈ g.H := by rw [← hy]; exact generator_mem g.n _
  have hxmem : g.n (p 2) ∈ g.H := generator_mem g.n _
  have hab' : f + g.n (p 2) = a * (d * D.u) + b * (d * D.v) :=
    hab.trans (congrArg₂ (fun u v : ℤ => a*u+b*v) hx hy)
  have hce' : f + g.n (p 2) = c * (d * D.u) + e * (d * D.v) :=
    hce.trans (congrArg₂ (fun u v : ℤ => c*u+e*v) hx hy)
  have hmem := primitive_mem_of_two_representations g.H D hd hxmem hu hv
    ha hb hc he hab' hce' hne (by simpa using hf)
  exact decomposition_glue_data g s hcommon p d D.u D.v hd hx hy D.coprime hmem

end P21.Symmetric.Classification


