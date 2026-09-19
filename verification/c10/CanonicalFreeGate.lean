import P21.Nonsymmetric.Chain.C10.Projection

namespace P21.Nonsymmetric

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

/-- Regression gate: the C10 abstract API asks only for the projected state. -/
def canonicalFreeAbstractTarget (X : EuclideanState s F D) : Prop :=
  F ∈ g.Gamma

example (seed : EuclideanSeed s F D) : EuclideanState s F D :=
  seed.toState

example (X : EuclideanState s F D) : F ∉ g.Gamma := X.F_gap

#check EuclideanState.Ical
#check EuclideanState.Jcal
#check EuclideanState.Kcal
#check EuclideanState.Dp
#check EuclideanState.I0
#check EuclideanState.J0
#check EuclideanState.M0
#check EuclideanState.K0
#check EuclideanState.mhat
#check EuclideanState.Phi
#check EuclideanState.measureZ
#check EuclideanState.measureNat

end P21.Nonsymmetric
