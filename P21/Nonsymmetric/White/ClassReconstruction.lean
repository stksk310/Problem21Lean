import P21.Nonsymmetric.White.CyclicClasses
import P21.Nonsymmetric.HerzogCoordinates

namespace P21.Nonsymmetric.White

open ColorCap

/-- A unit coordinate and AGE reconstruct the integral source vector Z. Row
order is the genuine cyclic order; no arbitrary row permutation is hidden. -/
theorem integral_class_of_unit_coordinate (k : ℤ) (R : Fin 3 → Point)
    (p v a : Point)
    (hsum : ∑ i,a i = k+1)
    (he : ∀ l, k*v l = ∑ i,a i*(R i l-p l))
    (i : Fin 3) (hi : a i = 1) :
    ∃ z : Point, ∀ l, k*z l =
      R i l+a (next i)*(R (next i) l-R (prev i) l)-p l := by
  refine ⟨fun l => v l-(R (prev i) l-p l),?_⟩
  intro l
  have hc : a (prev i) = k-a (next i) := by
    fin_cases i <;> simp [next,prev,Fin.sum_univ_succ] at hi hsum ⊢ <;> omega
  have hh := he l
  fin_cases i <;> simp [next,prev] at hi hc ⊢ <;>
    simp [Fin.sum_univ_succ,hi,hc] at hh <;> linear_combination hh

end P21.Nonsymmetric.White
