import P21.Nonsymmetric.ColorCap.MinimumOne.CyclicInput
import P21.Nonsymmetric.ColorCap.MinimumOne.RotationClosure
import P21.Nonsymmetric.White.ClassReconstruction
import P21.Nonsymmetric.White.ClassData

namespace P21.Nonsymmetric.ColorCap.MinimumOne

open White

/-- Exact reduction to the elementary arithmetic White theorem. Every lattice,
AGE, inverse, integral class, row-order and color step is derived internally.
This is explicitly conditional until CyclicWhiteStatement itself is proved. -/
theorem minimum_one_of_cyclic_white (hwhite : CyclicWhiteStatement) :
    MinimumOneStatement := by
  intro g s hcof D c k p hk hp he hmin
  by_contra hk1
  have hk2 : 2 ≤ k := by omega
  obtain ⟨v,a,ha,hage,heq⟩ := exists_cyclic_age g s hcof D c k p hk2
    (fun i => (hp i).1) he hmin
  obtain ⟨i,hi⟩ := hwhite k a (by omega) ha hage
  have hcop : Int.gcd (a (next i)) (k : ℤ) = 1 :=
    gcd_eq_one_of_nonzero_classes k (a (next i)) (by omega)
      (fun j hj hjk => cyclicAge_nonzero k a (by omega) hage j hj hjk (next i))
  obtain ⟨q,ell,hq,hqk,_,hinv⟩ := exists_positive_inverse k (a (next i))
    (by omega) (ha (next i)).1 hcop
  obtain ⟨z,hz⟩ := integral_class_of_unit_coordinate k (socleRows D c) p v a
    (cyclicAge_sum k a (by omega) ha hage) heq i hi
  exact rotated_integral_class_contradiction g s D c k p i (a (next i)) q ell z
    hp he hmin (by omega) (by have := (ha (next i)).1; omega)
    (ha (next i)).2 hq hqk hinv hz

end P21.Nonsymmetric.ColorCap.MinimumOne
