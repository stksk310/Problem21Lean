import P21.Nonsymmetric.ColorCap.RelativeLattice

namespace P21.Nonsymmetric.White

open ColorCap

def combination (R : Fin 3 → Point) (t : Point) : Point :=
  fun j => ∑ i, t i * R i j

theorem weight_combination (n : Point) (R : Fin 3 → Point) (t : Point) :
    weight n (combination R t) = ∑ i, t i * weight n (R i) := by
  simp [weight, combination, Fin.sum_univ_succ]
  ring

theorem weight_scale (n v : Point) (k : ℤ) :
    weight n (fun i => k * v i) = k * weight n v := by
  simp [weight, Fin.sum_univ_succ]
  ring

def classResidues (k : ℤ) (t : Point) (j : ℤ) : Point :=
  fun i => (j * t i) % k

def classRepresentative (R : Fin 3 → Point) (p z t : Point) (k j : ℤ) : Point :=
  fun l => j * z l - ∑ i, (j * t i / k) * (R i l - p l)

theorem classRepresentative_equation (R : Fin 3 → Point) (p z t : Point) (k j : ℤ)
    (he : ∀ l, k * z l = ∑ i, t i * (R i l - p l)) :
    ∀ l, k * classRepresentative R p z t k j l =
      ∑ i, classResidues k t j i * (R i l - p l) := by
  intro l
  have h0 := Int.emod_add_ediv_mul (j*t 0) k
  have h1 := Int.emod_add_ediv_mul (j*t 1) k
  have h2 := Int.emod_add_ediv_mul (j*t 2) k
  have h := he l
  simp [classRepresentative, classResidues, Fin.sum_univ_succ] at h ⊢
  linear_combination j*h - (R 0 l-p l)*h0 - (R 1 l-p l)*h1 - (R 2 l-p l)*h2

theorem classResidues_sum (k j : ℤ) (t : Point) (ht : ∑ i, t i = 1) :
    ∑ i, classResidues k t j i = j-k*(∑ i, j*t i/k) := by
  have h0 := Int.emod_add_ediv_mul (j*t 0) k
  have h1 := Int.emod_add_ediv_mul (j*t 1) k
  have h2 := Int.emod_add_ediv_mul (j*t 2) k
  simp [classResidues, Fin.sum_univ_succ] at ht ⊢
  linear_combination h0+h1+h2+j*ht

/-- Small residue mass would produce a positive integral companion at a smaller
actual level. This statement uses actual natural factorizations through the
frozen minimum lemma, rather than applying minimum to signed coefficients. -/
theorem small_mass_impossible (g : Generators) (hm : 0 < g.m)
    (f s : ℤ) (k : ℕ) (hk : 0 < k) (p v a : Point) (R : Fin 3 → Point)
    (hs : f + ∑ i, g.n i = s)
    (hp : ∀ i, 1 ≤ p i) (hR : ∀ i l, 0 ≤ R i l)
    (hpw : weight g.n p = s-(k : ℤ)*g.m)
    (hRw : ∀ i, weight g.n (R i) = s)
    (ha : ∀ i, 0 ≤ a i)
    (he : ∀ l, (k : ℤ)*v l = ∑ i, a i*(R i l-p l))
    (hmin : ∀ k' : ℕ, ∀ x : Fin 3 → ℕ,
      f = (k' : ℤ)*g.m+value g.n x → k ≤ k')
    (hlo : 0 < ∑ i, a i) (hhi : ∑ i, a i < k) : False := by
  have hkz : (0 : ℤ) < k := by exact_mod_cast hk
  have hw := congrArg (weight g.n) (funext he)
  change weight g.n (fun l => (k : ℤ)*v l) =
    weight g.n (combination (fun i => R i-p) a) at hw
  rw [weight_scale, weight_combination] at hw
  simp only [weight_sub, hRw, hpw] at hw
  have hvw : weight g.n v = (∑ i, a i)*g.m := by
    apply mul_left_cancel₀ (ne_of_gt hkz)
    calc
      (k : ℤ)*weight g.n v = ∑ i, a i*(s-(s-(k : ℤ)*g.m)) := hw
      _ = (k : ℤ)*((∑ i, a i)*g.m) := by simp [Fin.sum_univ_succ]; ring
  have hpos : ∀ l, 0 < (p+v) l := by
    intro l
    have hnonneg : 0 ≤ ∑ i, a i*R i l :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (hR i l))
    have hpositive := mul_pos (sub_pos.mpr hhi) (show 0 < p l by have := hp l; omega)
    have hh := he l
    simp [Fin.sum_univ_succ] at hnonneg hpositive hh
    change 0 < p l+v l
    nlinarith
  apply positive_companion_failure g f s k hs hmin ((k : ℤ)-∑ i, a i)
    (by omega) (by omega) (p+v) ?_ hpos
  rw [weight_add, hpw, hvw]
  ring

theorem classResidues_sum_mod (k j : ℤ) (t : Point) (ht : ∑ i, t i = 1)
    (hj : 0 ≤ j) (hjk : j < k) :
    (∑ i, classResidues k t j i) % k = j := by
  rw [classResidues_sum k j t ht]
  simp [Int.sub_emod, Int.mul_emod, Int.emod_eq_of_lt hj hjk]

theorem classResidues_lower (g : Generators) (hm : 0 < g.m)
    (f s : ℤ) (k : ℕ) (hk : 0 < k) (p z t : Point) (R : Fin 3 → Point)
    (hs : f + ∑ i, g.n i = s)
    (hp : ∀ i, 1 ≤ p i) (hR : ∀ i l, 0 ≤ R i l)
    (hpw : weight g.n p = s-(k : ℤ)*g.m)
    (hRw : ∀ i, weight g.n (R i) = s)
    (ht : ∑ i, t i = 1)
    (he : ∀ l, (k : ℤ)*z l = ∑ i, t i*(R i l-p l))
    (hmin : ∀ k' : ℕ, ∀ x : Fin 3 → ℕ,
      f = (k' : ℤ)*g.m+value g.n x → k ≤ k')
    (j : ℤ) (hj : 0 < j) (hjk : j < k) :
    (k : ℤ) < ∑ i, classResidues k t j i := by
  have hkz : (0 : ℤ) < k := by exact_mod_cast hk
  have ha i : 0 ≤ classResidues k t j i := Int.emod_nonneg _ (ne_of_gt hkz)
  have hn := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => ha i)
  have hmod := classResidues_sum_mod k j t ht hj.le hjk
  have hpS : 0 < ∑ i, classResidues k t j i := by
    by_contra h
    have hz : ∑ i, classResidues k t j i = 0 := by omega
    rw [hz, Int.zero_emod] at hmod
    omega
  have hlarge : (k : ℤ) ≤ ∑ i, classResidues k t j i := by
    by_contra h
    exact small_mass_impossible g hm f s k hk p (classRepresentative R p z t k j)
      (classResidues k t j) R hs hp hR hpw hRw ha
      (classRepresentative_equation R p z t k j he) hmin hpS (by omega)
  by_contra h
  have heq : ∑ i, classResidues k t j i = k := by omega
  rw [heq, Int.emod_self] at hmod
  omega

theorem classResidues_complement (k j : ℤ) (t : Point) (hk : 0 < k) (i : Fin 3) :
    classResidues k t j i + classResidues k t (k-j) i =
      if classResidues k t j i = 0 then 0 else k := by
  have h0 := Int.emod_nonneg (j*t i) (ne_of_gt hk)
  have h1 := Int.emod_lt_of_pos (j*t i) hk
  have he : ((k-j)*t i)%k = (-(j*t i))%k := by
    calc
      ((k-j)*t i)%k = (k*t i + -(j*t i))%k := by congr 1; ring
      _ = (-(j*t i))%k := by rw [Int.add_emod]; simp
  change (j*t i)%k+((k-j)*t i)%k = if (j*t i)%k = 0 then 0 else k
  rw [he]
  rw [Int.neg_emod]
  simp only [Int.dvd_iff_emod_eq_zero, Int.natCast_natAbs, abs_of_pos hk]
  split_ifs <;> omega

/-- The complete cyclic AGE identity follows from the original actual minimum.
No width-one functional or White class is an input to this theorem. -/
theorem cyclic_age_of_minimum (g : Generators) (hm : 0 < g.m)
    (f s : ℤ) (k : ℕ) (hk : 0 < k) (p z t : Point) (R : Fin 3 → Point)
    (hs : f + ∑ i, g.n i = s)
    (hp : ∀ i, 1 ≤ p i) (hR : ∀ i l, 0 ≤ R i l)
    (hpw : weight g.n p = s-(k : ℤ)*g.m)
    (hRw : ∀ i, weight g.n (R i) = s)
    (ht : ∑ i, t i = 1)
    (he : ∀ l, (k : ℤ)*z l = ∑ i, t i*(R i l-p l))
    (hmin : ∀ k' : ℕ, ∀ x : Fin 3 → ℕ,
      f = (k' : ℤ)*g.m+value g.n x → k ≤ k')
    (j : ℤ) (hj : 0 < j) (hjk : j < k) :
    (∀ i, 0 < classResidues k t j i) ∧
      ∑ i, classResidues k t j i = (k : ℤ)+j := by
  have hkz : (0 : ℤ) < k := by exact_mod_cast hk
  have hlo := classResidues_lower g hm f s k hk p z t R hs hp hR hpw hRw ht he hmin j hj hjk
  have hneg := classResidues_lower g hm f s k hk p z t R hs hp hR hpw hRw ht he hmin
    ((k : ℤ)-j) (by omega) (by omega)
  have hpair := classResidues_complement (k : ℤ) j t hkz
  have hle i : classResidues k t j i + classResidues k t ((k : ℤ)-j) i ≤ k := by
    rw [hpair i]; split_ifs <;> omega
  have hnz (i) : classResidues k t j i ≠ 0 := by
    intro hz
    have heq := hpair i
    rw [if_pos hz] at heq
    have h0 := hle 0; have h1 := hle 1; have h2 := hle 2
    simp [Fin.sum_univ_succ] at hlo hneg
    fin_cases i
    · change classResidues k t j 0+classResidues k t ((k : ℤ)-j) 0 = 0 at heq
      omega
    · change classResidues k t j 1+classResidues k t ((k : ℤ)-j) 1 = 0 at heq
      omega
    · change classResidues k t j 2+classResidues k t ((k : ℤ)-j) 2 = 0 at heq
      omega
  have hsum : (∑ i, classResidues k t j i) +
      (∑ i, classResidues k t ((k : ℤ)-j) i) = 3*(k : ℤ) := by
    have h0 := hpair 0; have h1 := hpair 1; have h2 := hpair 2
    rw [if_neg (hnz 0)] at h0
    rw [if_neg (hnz 1)] at h1
    rw [if_neg (hnz 2)] at h2
    simp [Fin.sum_univ_succ]
    omega
  have hupper : (∑ i, classResidues k t j i) < 2*(k : ℤ) := by omega
  have hmod := classResidues_sum_mod k j t ht hj.le hjk
  have hshift : ((∑ i, classResidues k t j i)-(k : ℤ))%(k : ℤ) =
      (∑ i, classResidues k t j i)%(k : ℤ) := by rw [Int.sub_emod]; simp
  rw [Int.emod_eq_of_lt (by omega) (by omega),hmod] at hshift
  refine ⟨?_,by omega⟩
  intro i
  have hn := Int.emod_nonneg (j*t i) (ne_of_gt hkz)
  change 0 ≤ classResidues k t j i at hn
  have := hnz i
  omega

end P21.Nonsymmetric.White
