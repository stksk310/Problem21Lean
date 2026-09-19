import P21.Nonsymmetric.Chain.C10.ColorExchange

namespace P21.Nonsymmetric
namespace EuclideanState

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

example (X : EuclideanState s F D) : X.Epar = X.e * X.theta + X.rhoRem := X.E_division
example (X : EuclideanState s F D) : 0 ≤ X.rhoRem ∧ X.rhoRem < X.theta := X.rhoRem_range
example (X : EuclideanState s F D) (h : ¬ X.Terminal) : X.nu = X.e + 1 := X.nu_eq_e_add_one h
example (X : EuclideanState s F D) (h : ¬ X.Terminal) :
    X.R ≤ X.rhoRem ∧ X.rhoRem < X.theta := X.rhoRem_bounds h
example (X : EuclideanState s F D) (h : ¬ X.Terminal) :
    1 ≤ X.kappa ∧ X.kappa ≤ X.w := ⟨X.kappa_pos, X.kappa_le_w h⟩
example (X : EuclideanState s F D) :
    (X.Bcoef + X.e * X.Acoef) * g.n 0 + X.rhoRem * g.n 1 =
      (X.M + X.e * X.L) * g.m + X.kappa * g.n 2 := X.new_packet

example (X : EuclideanState s F D) (h : ¬ X.Terminal) :
    EuclideanState (relabelSetting s reversePerm) F (reverseHerzog D) := X.step h

example (X : EuclideanState s F D) (h : ¬ X.Terminal) :
    (X.step h).measureNat < X.measureNat := X.step_measureNat_lt h

end EuclideanState
end P21.Nonsymmetric
