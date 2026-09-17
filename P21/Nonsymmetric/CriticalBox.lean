import P21.Symmetric.Classification.CriticalRelations

namespace P21.Nonsymmetric

open Symmetric.Classification

/-- The integer evaluation map for the three tail generators. -/
def integerValue (g : Generators) (v : Fin 3 → ℤ) : ℤ :=
  ∑ i, v i * g.n i

/-- A kernel vector with only one positive coordinate has a critical-sized
positive coordinate. This is exactly minimality, with negative coordinates
converted into a genuine nonnegative off-direction factorization. -/
theorem critical_le_of_single_positive {g : Generators}
    (critical : ∀ i, CriticalRelation g i) (v : Fin 3 → ℤ)
    (hv : integerValue g v = 0) (i : Fin 3) (hi : 0 < v i)
    (hother : ∀ j, j ≠ i → v j ≤ 0) :
    ((critical i).coeff : ℤ) ≤ v i := by
  classical
  let a : Fin 3 → ℕ := fun j => if j = i then 0 else (-v j).toNat
  have ha : a i = 0 := by simp [a]
  have ha' : ∀ j, (a j : ℤ) = (if j = i then v i else 0) - v j := by
    intro j
    by_cases hji : j = i
    · subst j; simp [a]
    · simp [a, hji, Int.toNat_of_nonneg (neg_nonneg.mpr (hother j hji))]
  have he : ((v i).toNat : ℤ) * g.n i = value g.n a := by
    rw [Int.toNat_of_nonneg hi.le]
    simp only [value, ha', sub_mul, Finset.sum_sub_distrib]
    simpa [integerValue, hv] using (show v i * g.n i = v i * g.n i - integerValue g v by omega)
  have hc := (critical i).minimal (v i).toNat
    (by omega) a ha he
  have hc' : ((critical i).coeff : ℤ) ≤ ((v i).toNat : ℤ) := by exact_mod_cast hc
  simpa [Int.toNat_of_nonneg hi.le] using hc'

/-- A nonzero integer relation cannot be strictly inside the critical box. -/
theorem critical_kernel_box_zero {g : Generators} (hpos : ∀ i, 0 < g.n i)
    (critical : ∀ i, CriticalRelation g i) (v : Fin 3 → ℤ)
    (hv : integerValue g v = 0)
    (hlo : ∀ i, -((critical i).coeff : ℤ) < v i)
    (hhi : ∀ i, v i < ((critical i).coeff : ℤ)) : v = 0 := by
  have single (w : Fin 3 → ℤ) (hw : integerValue g w = 0)
      (hbound : ∀ i, w i < ((critical i).coeff : ℤ))
      (i : Fin 3) (hi : 0 < w i) (ho : ∀ j, j ≠ i → w j ≤ 0) : False := by
    have := critical_le_of_single_positive critical w hw i hi ho
    have := hbound i
    omega
  have hn : integerValue g (fun i => -v i) = 0 := by
    simpa [integerValue, neg_mul, Finset.sum_neg_distrib] using congrArg Neg.neg hv
  have hnb : ∀ i, -v i < ((critical i).coeff : ℤ) := by intro i; have := hlo i; omega
  have he : v 0 * g.n 0 + v 1 * g.n 1 + v 2 * g.n 2 = 0 := by
    simpa [integerValue, Fin.sum_univ_succ, add_assoc] using hv
  have hp0 := hpos 0
  have hp1 := hpos 1
  have hp2 := hpos 2
  have hs : ∀ i, 0 < v i → (∀ j, j ≠ i → v j ≤ 0) → False := single v hv hhi
  have ht : ∀ i, v i < 0 → (∀ j, j ≠ i → 0 ≤ v j) → False := by
    intro i hi ho
    apply single (fun j => -v j) hn hnb i (by omega)
    intro j hj
    exact neg_nonpos.mpr (ho j hj)
  have hzero : v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 := by
    by_cases h0 : 0 < v 0 <;> by_cases h1 : 0 < v 1 <;> by_cases h2 : 0 < v 2
    · nlinarith [mul_pos h0 hp0, mul_pos h1 hp1, mul_pos h2 hp2]
    · by_cases h2' : v 2 < 0
      · exact False.elim (ht 2 h2' (by intro j hj; fin_cases j <;> simp_all <;> omega))
      · nlinarith [mul_pos h0 hp0, mul_pos h1 hp1]
    · by_cases h1' : v 1 < 0
      · exact False.elim (ht 1 h1' (by intro j hj; fin_cases j <;> simp_all <;> omega))
      · nlinarith [mul_pos h0 hp0, mul_pos h2 hp2]
    · exact False.elim (hs 0 h0 (by intro j hj; fin_cases j <;> simp_all <;> omega))
    · by_cases h0' : v 0 < 0
      · exact False.elim (ht 0 h0' (by intro j hj; fin_cases j <;> simp_all <;> omega))
      · nlinarith [mul_pos h1 hp1, mul_pos h2 hp2]
    · exact False.elim (hs 1 h1 (by intro j hj; fin_cases j <;> simp_all <;> omega))
    · exact False.elim (hs 2 h2 (by intro j hj; fin_cases j <;> simp_all <;> omega))
    · have hz0 : v 0 ≤ 0 := by omega
      have hz1 : v 1 ≤ 0 := by omega
      have hz2 : v 2 ≤ 0 := by omega
      have hm0 := mul_nonpos_of_nonpos_of_nonneg hz0 hp0.le
      have hm1 := mul_nonpos_of_nonpos_of_nonneg hz1 hp1.le
      have hm2 := mul_nonpos_of_nonpos_of_nonneg hz2 hp2.le
      constructor
      · nlinarith
      constructor <;> nlinarith
  funext i
  fin_cases i <;> simp_all

/-- Two factorizations in the three-direction critical box coincide. No
nonsymmetry, connectivity, or global uniqueness assumption is used. -/
theorem critical_box_unique {g : Generators} (hpos : ∀ i, 0 < g.n i)
    (critical : ∀ i, CriticalRelation g i) {x y : Fin 3 → ℕ}
    (hx : ∀ i, x i < (critical i).coeff)
    (hy : ∀ i, y i < (critical i).coeff)
    (he : value g.n x = value g.n y) : x = y := by
  have hz := critical_kernel_box_zero hpos critical
    (fun i => (x i : ℤ) - y i)
    (by simpa [integerValue, value, sub_mul, Finset.sum_sub_distrib] using sub_eq_zero.mpr he)
    (by intro i; have := hx i; have := hy i; omega)
    (by intro i; have := hx i; have := hy i; omega)
  funext i
  have := congrFun hz i
  simp only [Pi.zero_apply] at this
  omega

end P21.Nonsymmetric

