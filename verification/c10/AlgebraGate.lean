import P21.Nonsymmetric.Chain.C10.Elimination

namespace P21.Nonsymmetric
namespace EuclideanState

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

example (X : EuclideanState s F D) : 0 < X.Ical := X.ical_pos
example (X : EuclideanState s F D) : 0 < X.Jcal := X.jcal_pos
example (X : EuclideanState s F D) : 0 < X.Kcal := X.kcal_pos

example (X : EuclideanState s F D) : 0 < X.sigma := X.sigma_pos
example (X : EuclideanState s F D) : (g.n 0 : ℚ) = X.sigma * X.Ical := X.ni_scale
example (X : EuclideanState s F D) : (g.n 1 : ℚ) = X.sigma * X.Jcal := X.nj_scale
example (X : EuclideanState s F D) : (g.n 2 : ℚ) = X.sigma * X.Kcal := X.nk_scale

example (X : EuclideanState s F D) : X.v + 1 ≤ X.p ∧ X.t ≤ X.q := X.matrix_order
example (X : EuclideanState s F D) : X.M0 = (D.rho 1 : ℤ) + D.a 1 := X.M0_eq
example (X : EuclideanState s F D) : X.K0 = (D.rho 2 : ℤ) + D.b 2 := X.K0_eq
example (X : EuclideanState s F D) :
    X.I0 * g.n 0 = X.M0 * g.m + X.Dp * g.n 2 := X.packet_elimination
example (X : EuclideanState s F D) :
    X.Acoef * X.M - X.Bcoef * X.L = X.delta - X.beta := X.source_determinant
example (X : EuclideanState s F D) :
    X.I0 * X.K0 - X.M0 * X.J0 = -X.Dp * (X.delta - X.beta) :=
  X.packet_source_determinant
example (X : EuclideanState s F D) :
    X.I0 * X.Ical - X.Dp * X.Kcal = X.M0 * X.mhat := X.mhat_numerator
example (X : EuclideanState s F D) : (g.m : ℚ) = X.sigma * X.mhat := X.mhat_scale

end EuclideanState
end P21.Nonsymmetric
