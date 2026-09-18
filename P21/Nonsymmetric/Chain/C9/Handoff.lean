import P21.Nonsymmetric.Chain.C9.EuclideanSeed
import P21.Nonsymmetric.Chain.C9.RegionUExclusion

namespace P21.Nonsymmetric

namespace ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

/-- Exact Section 9 output.  The orientation hypothesis is the established
`J0 < 0` branch used throughout the strict Region-D development. -/
theorem c9_handoff (K : ChainCore s F D) (A : K.FirstFit) (E : K.Returns)
    (hJ : K.J0 < 0) (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) :
    Nonempty (EuclideanSeed s F D) := by
  rcases A.c8_handoff E hF hc with hU | hD
  · rcases hU with ⟨O, U⟩
    exact (U.impossible hF hc).elim
  · rcases hD with ⟨RD⟩
    exact ⟨RD.toEuclideanSeed hJ hc⟩

end ChainCore
end P21.Nonsymmetric
