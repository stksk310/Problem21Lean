import P21.Nonsymmetric.ColorCap.RelativeLattice
import Mathlib.Data.Int.GCD

namespace P21.Nonsymmetric.White

/-- Nonzero residues in every nonzero cyclic class force coprimality. -/
theorem gcd_eq_one_of_nonzero_classes (k r : ℤ) (hk : 1 < k)
    (hclasses : ∀ j : ℤ, 0 < j → j < k → (j * r) % k ≠ 0) :
    Int.gcd r k = 1 := by
  have hgpos : 0 < (Int.gcd r k : ℤ) := by
    exact_mod_cast Int.gcd_pos_of_ne_zero_right r (by omega : k ≠ 0)
  obtain ⟨u, hu⟩ := Int.gcd_dvd_left r k
  obtain ⟨v, hv⟩ := Int.gcd_dvd_right r k
  by_contra hne
  have hg : 2 ≤ (Int.gcd r k : ℤ) := by exact_mod_cast (by omega : 2 ≤ Int.gcd r k)
  have hvpos : 0 < v := by nlinarith
  have hvlt : v < k := by nlinarith
  apply hclasses v hvpos hvlt
  apply Int.emod_eq_zero_of_dvd
  refine ⟨u, ?_⟩
  linear_combination v * hu - u * hv

/-- The positive inverse representative and its nonnegative quotient are
constructed from Bezout; they are not part of any input certificate. -/
theorem exists_positive_inverse (k r : ℤ) (hk : 1 < k) (hr : 0 < r)
    (hcop : Int.gcd r k = 1) :
    ∃ q ell : ℤ, 1 ≤ q ∧ q < k ∧ 0 ≤ ell ∧ r * q = 1 + ell * k := by
  let q := Int.gcdA r k % k
  have hk0 : k ≠ 0 := by omega
  have hq0 : 0 ≤ q := Int.emod_nonneg _ hk0
  have hqk : q < k := Int.emod_lt_of_pos _ (by omega)
  have hbez := Int.gcd_eq_gcd_ab r k
  rw [hcop] at hbez
  have hmod : (r * q) % k = 1 := by
    have hh := congrArg (fun x : ℤ => x % k) hbez
    simpa [q, Int.add_emod, Int.mul_emod, Int.emod_eq_of_lt (by omega : 0 ≤ (1 : ℤ)) hk] using hh.symm
  have hqpos : 1 ≤ q := by
    by_contra h
    have : q = 0 := by omega
    simp [this] at hmod
  refine ⟨q, (r * q) / k, hqpos, hqk, ?_, ?_⟩
  · exact Int.ediv_nonneg (by positivity) (by omega)
  · have hh := Int.emod_add_mul_ediv (r * q) k
    rw [hmod] at hh
    nlinarith

end P21.Nonsymmetric.White
