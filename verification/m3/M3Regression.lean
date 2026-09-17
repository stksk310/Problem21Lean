import P21.Nonsymmetric.Herzog.PseudoFrobenius
import P21.Nonsymmetric.CriticalBox
import P21.Nonsymmetric.Kernel
import P21.Nonsymmetric.Singletons
import P21.Nonsymmetric.ColorCap.Residuals
import P21.Nonsymmetric.FourRowCombinatorics

open P21 P21.Nonsymmetric

example : HerzogClassificationStatement := herzog_classification

example (g : Generators) (s : g.Setting) (F : ℤ)
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (q : Fin 3 → ℤ) (hq : ∀ i, q i ∈ s.semigroup.Q F)
    (hs : ∀ i, IsSingleton g (q i) i) : (s.semigroup.Q F).ncard = 3 :=
  three_singletons_force_Q_three s hF hc q hq hs

example (g : Generators) (hp : ∀ i, 0 < g.n i)
    (critical : ∀ i, P21.Symmetric.Classification.CriticalRelation g i)
    (x y : Fin 3 → ℕ) (hx : ∀ i, x i < (critical i).coeff)
    (hy : ∀ i, y i < (critical i).coeff) (he : value g.n x = value g.n y) : x = y :=
  critical_box_unique hp critical hx hy he

example (t : Finset RowLabel) (hc : RowLabel.Compatible t) : RowLabel.Terminal t :=
  RowLabel.four_labels_classification t hc

-- Conditional means both remaining obligations are explicit arguments.
example (hm : ColorCap.MinimumOneStatement) (hd : ColorCap.BoxPositiveExitStatement)
    (g : Generators) (s : g.Setting)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (D : HerzogCriticalData g) (colorA : Bool)
    (depth : ColorCap.Point) (hdepth : ∀ i, 1 ≤ depth i)
    (hcap : ∀ i, depth i < (if colorA then (D.a i : ℤ) else (D.b i : ℤ)))
    (harms : ∀ i, (if colorA then D.fA else D.fB)-depth i*g.n i ∈ s.semigroup.PF) : False :=
  ColorCap.three_arms_impossible_of_residuals hm hd g s hcof D colorA depth hdepth hcap harms
