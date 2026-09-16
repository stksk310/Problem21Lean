import P21.Selection

namespace P21

def W (F m : ℤ) : ℤ := F + m
def complement (F m q : ℤ) : ℤ := W F m - q

/-- Threshold cofiniteness is equivalent to finiteness of the nonnegative gaps.
The full integer gap set is intentionally NOT claimed to be finite. -/
theorem cofinite_iff_finite_nonnegative_gaps (G : AddSubmonoid ℤ) :
    (∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ G) ↔ {x : ℤ | 0 ≤ x ∧ x ∉ G}.Finite := by
  constructor
  · rintro ⟨B, hB⟩
    exact (Set.finite_Ico 0 B).subset fun x hx =>
      ⟨hx.1, lt_of_not_ge (fun h => hx.2 (hB x h))⟩
  · intro h
    obtain ⟨B, hB⟩ := h.bddAbove
    refine ⟨max 0 (B + 1), fun x hx => ?_⟩
    by_contra hg
    have hx0 : 0 ≤ x := le_trans (le_max_left _ _) hx
    have hle := hB (show x ∈ {x : ℤ | 0 ≤ x ∧ x ∉ G} from ⟨hx0, hg⟩)
    have := le_trans (le_max_right 0 (B + 1)) hx
    omega

namespace NumericalSemigroup
variable (S : NumericalSemigroup)

theorem all_pf_finite : S.PF.Finite := by
  obtain ⟨F, hF⟩ := S.exists_frobenius
  obtain ⟨B, hB⟩ := S.cofinite
  have hm := hB (max 1 B) (le_max_right _ _)
  exact S.pf_finite hF hm (by have := le_max_left 1 B; omega)

theorem q_finite (F : ℤ) : (S.Q F).Finite := S.all_pf_finite.subset Set.sdiff_subset

theorem a0_lower_in_semigroup {F m x y : ℤ} (hF : S.IsFrobenius F)
    (hx : x ∈ S.carrier) (hy : y ∈ S.A0 F m) (hxy : S.Le x y) : x ∈ S.A0 F m :=
  S.a0_lower hF (S.apery_lower hx hy.1 hxy) hy hxy

theorem minimal_a1_card_eq_type_sub_one {F m : ℤ} (hF : S.IsFrobenius F)
    (hm : m ∈ S.carrier) (hmpos : 0 < m)
    (hmin : ∀ x ∈ S.carrier, x ≠ 0 → m ≤ x) (hc : S.Canonical F m) :
    {w | S.Minimal (S.A1 F m) w}.ncard = S.type - 1 := by
  obtain ⟨h1, h2⟩ := S.minimal_a1_card hF hm hmpos hmin hc
  omega

end NumericalSemigroup
end P21
