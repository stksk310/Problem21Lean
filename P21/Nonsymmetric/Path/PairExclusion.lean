import P21.Nonsymmetric.Path.EndpointLevel

namespace P21.Nonsymmetric
namespace PathInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

/-- P5.2--P5.3: a genuine PAIR is impossible in either orientation. -/
theorem Pair.impossible (P : PathInput s F D)
    (hF : s.semigroup.IsFrobenius F) (p : Pair P) : False := by
  rcases p.weak_root_or_dual P with hw | hw
  · obtain ⟨w⟩ := hw
    exact w.impossible P hF
  · obtain ⟨w⟩ := hw
    have hF' : (relabelSetting s pathReversePerm).semigroup.IsFrobenius F := by
      rw [relabel_semigroup]
      exact hF
    exact w.impossible P.reverse hF'

end PathInput
end P21.Nonsymmetric
