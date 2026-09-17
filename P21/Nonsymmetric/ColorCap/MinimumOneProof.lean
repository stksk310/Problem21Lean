import P21.Nonsymmetric.ColorCap.MinimumOne.CyclicReduction
import P21.Nonsymmetric.White.WidthOneBeatty

namespace P21.Nonsymmetric.ColorCap

/-- The exact frozen MINBOX proposition, with no additional mathematical input.
The specialized arithmetic White theorem is proved internally. -/
theorem minimum_one_proved : MinimumOneStatement :=
  MinimumOne.minimum_one_of_cyclic_white White.cyclic_white_proved

/-- MINBOX is discharged; the only remaining ColorCap input is DPE. -/
theorem three_arms_impossible_of_dpe
    (hdpe : BoxPositiveExitStatement)
    (g : Generators) (s : g.Setting)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (D : HerzogCriticalData g) (colorA : Bool)
    (depth : Point) (hdepth : ∀ i, 1 ≤ depth i)
    (hcap : ∀ i, depth i < (if colorA then (D.a i : ℤ) else (D.b i : ℤ)))
    (harms : ∀ i, (if colorA then D.fA else D.fB)-depth i*g.n i ∈ s.semigroup.PF) :
    False :=
  three_arms_impossible_of_residuals minimum_one_proved hdpe g s hcof D colorA depth hdepth hcap harms

end P21.Nonsymmetric.ColorCap
