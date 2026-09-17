import P21.Nonsymmetric.ColorCap.CompanionBounds
import P21.Nonsymmetric.ColorCap.RelativeLattice

namespace P21.Nonsymmetric.ColorCap.MinimumOne

def rowsA (a b : Point) : Fin 3 → Point :=
  ![![0,a 1+b 1,a 2], ![a 0,0,a 2+b 2], ![a 0+b 0,a 1,0]]

def rowsB (a b : Point) : Fin 3 → Point :=
  ![![0,b 1,a 2+b 2], ![a 0+b 0,0,b 2], ![b 0,a 1+b 1,0]]

/-- Exact integral inverse-class representative; no existence is asserted here. -/
def inverseClass (R : Fin 3 → Point) (z : Point) (q ell : ℤ) : Point :=
  fun i => q*z i-ell*(R 1 i-R 2 i)

theorem inverseClass_identity (R : Fin 3 → Point) (p z : Point)
    (k r q ell : ℤ) (hinv : r*q=1+ell*k)
    (hz : ∀ i, k*z i=R 0 i+r*(R 1 i-R 2 i)-p i) :
    ∀ i, k*inverseClass R z q ell i=q*R 0 i+(R 1 i-R 2 i)-q*p i := by
  intro i
  dsimp [inverseClass]
  linear_combination q * hz i + (R 1 i-R 2 i)*hinv

theorem class_weight (n p z : Point) (R : Fin 3 → Point) (s m k r : ℤ)
    (hk : k ≠ 0) (hp : weight n p=s-k*m) (hR : ∀ i, weight n (R i)=s)
    (hz : ∀ i, k*z i=R 0 i+r*(R 1 i-R 2 i)-p i) : weight n z=m := by
  have h0 := hz 0; have h1 := hz 1; have h2 := hz 2
  have hR0 := hR 0; have hR1 := hR 1; have hR2 := hR 2
  simp [weight, Fin.sum_univ_succ] at *
  apply (mul_left_cancel₀ hk)
  linear_combination n 0*h0+n 1*h1+n 2*h2+hR0+r*hR1-r*hR2-hp

theorem inverseClass_weight (n z : Point) (R : Fin 3 → Point) (s m q ell : ℤ)
    (hR : ∀ i, weight n (R i)=s) (hz : weight n z=m) :
    weight n (inverseClass R z q ell)=q*m := by
  have hR1 := hR 1; have hR2 := hR 2
  simp [weight, Fin.sum_univ_succ] at *
  dsimp [inverseClass]
  linear_combination q*hz-ell*hR1+ell*hR2

end P21.Nonsymmetric.ColorCap.MinimumOne

