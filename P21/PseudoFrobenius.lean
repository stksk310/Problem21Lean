import P21.Basic

namespace P21.NumericalSemigroup
variable (S : NumericalSemigroup)

/-- The exact finite translated gap set used in publication §2.8. -/
theorem translated_gaps_finite {F x : ℤ} (hF : S.IsFrobenius F) :
    {q : ℤ | q ∉ S.carrier ∧ q - x ∈ S.carrier}.Finite := by
  apply (Set.finite_Icc x F).subset
  intro q hq
  exact ⟨by have := S.nonneg _ hq.2; omega, hF.2 hq.1⟩

theorem gap_below_pf {F x : ℤ} (hF : S.IsFrobenius F) (hx : x ∉ S.carrier) :
    ∃ q ∈ S.PF, q - x ∈ S.carrier := by
  let T : Set ℤ := {q | q ∉ S.carrier ∧ q - x ∈ S.carrier}
  have hf : T.Finite := S.translated_gaps_finite hF
  have hn : T.Nonempty := ⟨x, hx, by simp⟩
  obtain ⟨q, hq, hmax⟩ := Set.exists_max_image T id hf hn
  refine ⟨q, ⟨hq.1, ?_⟩, hq.2⟩
  intro s hs hs0
  by_contra hgap
  have hmem : q + s ∈ T := ⟨hgap, by
    convert S.carrier.add_mem hq.2 hs using 1; ring⟩
  have hle : q + s ≤ q := hmax _ hmem
  have := S.nonneg _ hs
  omega

/-- C2.1. Nonnegative-gap statement, proved by the publication maximum argument. -/
theorem canonical_all_nonnegative_gaps {F m x : ℤ} (hF : S.IsFrobenius F)
    (hc : S.Canonical F m) (_hx0 : 0 ≤ x) (hx : x ∉ S.carrier) :
    F + m - x ∈ S.carrier := by
  obtain ⟨q, hq, hqx⟩ := S.gap_below_pf hF hx
  convert S.carrier.add_mem (hc q hq) hqx using 1; ring

end P21.NumericalSemigroup
