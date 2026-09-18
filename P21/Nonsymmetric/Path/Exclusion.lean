import P21.Nonsymmetric.Path.PFreeExclusion

namespace P21.Nonsymmetric
namespace PathInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

/-- Publication P5.7: PAIR and both transported PFREE orientations exhaust
the actual central returns, and each alternative is impossible. -/
theorem impossible (P : PathInput s F D)
    (hF : s.semigroup.IsFrobenius F) : False := by
  rcases P.pair_or_pfree_or_dual with hp | hp | hp
  · obtain ⟨p⟩ := hp
    exact p.impossible P hF
  · obtain ⟨p⟩ := hp
    exact p.impossible P hF
  · obtain ⟨p⟩ := hp
    have hF' : (relabelSetting s pathReversePerm).semigroup.IsFrobenius F := by
      rw [relabel_semigroup]
      exact hF
    exact p.impossible P.reverse hF'

end PathInput
end P21.Nonsymmetric
