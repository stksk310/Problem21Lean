import P21.Nonsymmetric.ColorCap.MinimumOneProof
import P21.Nonsymmetric.ColorCap.MinimumOne.EmptyTetrahedron

open P21 P21.Nonsymmetric P21.Nonsymmetric.ColorCap

-- Exact frozen target: no extra class, coprimality, emptiness, or arm hypothesis.
example : MinimumOneStatement := minimum_one_proved

-- The elementary White consequence is an actual theorem, not a residual input.
example : White.CyclicWhiteStatement := White.cyclic_white_proved

-- Both colors, all three directions, and the existing tail-cofinite hypothesis.
example (hdpe : BoxPositiveExitStatement) (g : Generators) (s : g.Setting)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (D : HerzogCriticalData g) (colorA : Bool)
    (depth : Point) (hdepth : ∀ i, 1 ≤ depth i)
    (hcap : ∀ i, depth i < (if colorA then (D.a i : ℤ) else (D.b i : ℤ)))
    (harms : ∀ i, (if colorA then D.fA else D.fB)-depth i*g.n i ∈ s.semigroup.PF) : False :=
  three_arms_impossible_of_dpe hdpe g s hcof D colorA depth hdepth hcap harms

#print axioms minimum_one_proved
#print axioms three_arms_impossible_of_dpe
#print axioms White.cyclic_white_proved
#print MinimumOneStatement
#print BoxPositiveExitStatement
