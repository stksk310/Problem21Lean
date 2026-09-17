import P21.Nonsymmetric.ColorCap.ThreeArms
import P21.Nonsymmetric.ColorCap.RelativeLattice
import P21.Nonsymmetric.ColorCap.CompanionBounds
import P21.Nonsymmetric.ColorCap.DPEOneColor
import P21.Nonsymmetric.ColorCap.PositiveMinors
import P21.Nonsymmetric.ColorCap.PrefixArithmetic

namespace P21.Nonsymmetric.ColorCap

/-- Precise remaining MINBOX obligation. Tail cofiniteness supplies the primitive
lattice normalization required by the source. The least actual level is supplied
by a proved minimum theorem; no k=1 assertion is a field of data. -/
def MinimumOneStatement : Prop :=
  ∀ (g : Generators) (_s : g.Setting)
    (_hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (D : HerzogCriticalData g) (colorA : Bool)
    (k : ℕ) (p : Point),
    0 < k →
    (∀ i, 1 ≤ p i ∧ p i < (if colorA then (D.a i : ℤ) else (D.b i : ℤ))) →
    (if colorA then D.fA else D.fB) = (k : ℤ)*g.m+∑ i, (p i-1)*g.n i →
    (∀ k' : ℕ, ∀ x' : Fin 3 → ℕ,
      (if colorA then D.fA else D.fB) = (k' : ℤ)*g.m+value g.n x' → k ≤ k') →
    k = 1

/-- Fully proved reduction: exactly MINBOX and DPE remain for actual three-arm exclusion.
The source semigroup, socle element, and all actual PF arms remain unchanged. -/
theorem three_arms_impossible_of_residuals
    (hminimum : MinimumOneStatement) (hdpe : BoxPositiveExitStatement)
    (g : Generators) (s : g.Setting)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (D : HerzogCriticalData g) (colorA : Bool)
    (depth : Point) (hdepth : ∀ i, 1 ≤ depth i)
    (hcap : ∀ i, depth i < (if colorA then (D.a i : ℤ) else (D.b i : ℤ)))
    (harms : ∀ i, (if colorA then D.fA else D.fB)-depth i*g.n i ∈ s.semigroup.PF) : False := by
  cases colorA
  · simp only [Bool.false_eq_true, ↓reduceIte] at hcap harms
    obtain ⟨k,p,hk,hp,he,hmin⟩ := colorB_actual_minimum g s D depth hdepth harms
    have hk1 := hminimum g s hcof D false k p hk
      (fun i => ⟨(hp i).1,lt_of_le_of_lt (hp i).2 (hcap i)⟩) he hmin
    subst k
    simp only [Nat.cast_one,one_mul] at he
    exact colorB_three_arm_contradiction_of_minbox hdpe g s D depth p hp hcap he harms
  · simp only [↓reduceIte] at hcap harms
    obtain ⟨k,p,hk,hp,he,hmin⟩ := colorA_actual_minimum g s D depth hdepth harms
    have hk1 := hminimum g s hcof D true k p hk
      (fun i => ⟨(hp i).1,lt_of_le_of_lt (hp i).2 (hcap i)⟩) he hmin
    subst k
    simp only [Nat.cast_one,one_mul] at he
    exact colorA_three_arm_contradiction_of_minbox hdpe g s D depth p hp hcap he harms

end P21.Nonsymmetric.ColorCap

