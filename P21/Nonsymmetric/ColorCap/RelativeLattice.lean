import P21.Nonsymmetric.ColorCap.BoxPaths

namespace P21.Nonsymmetric.ColorCap

/-- The relative lattice is defined by divisibility in the original weight map. -/
def relativeLattice (n : Point) (d : ℤ) : AddSubgroup Point where
  carrier := {z | d ∣ weight n z}
  zero_mem' := by simp [weight]
  add_mem' := by
    intro a b ha hb
    change d ∣ weight n (a+b)
    simpa [weight, add_mul, Finset.sum_add_distrib] using dvd_add ha hb
  neg_mem' := by
    intro a ha
    change d ∣ weight n (-a)
    simpa [weight] using dvd_neg.mpr ha

/-- Every point of the correct affine relative lattice has an integral m-level. -/
theorem relative_lattice_level (n p u : Point) (s m k : ℤ)
    (hp : s - weight n p = k * m)
    (hu : u - p ∈ relativeLattice n m) : ∃ l : ℤ, s - weight n u = l * m := by
  change m ∣ weight n (u-p) at hu
  obtain ⟨t,ht⟩ := hu
  refine ⟨k-t,?_⟩
  simp only [weight, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib] at hp ht ⊢
  linear_combination hp - ht

/-- Strictly positive lower companions give actual smaller levels, never signed witnesses. -/
theorem lower_companion_impossible (g : Generators) (f : ℤ) (k : ℕ)
    (hmin : ∀ k' : ℕ, ∀ x' : Fin 3 → ℕ,
      f = (k' : ℤ) * g.m + value g.n x' → k ≤ k')
    (l : ℤ) (hl : 0 < l) (hlk : l < k) (u : Point) (hu : ∀ i, 1 ≤ u i)
    (he : f = l * g.m + ∑ i, (u i - 1) * g.n i) : False := by
  have hnonneg i : 0 ≤ u i - 1 := by have := hu i; omega
  have hm := hmin l.toNat (fun i => (u i - 1).toNat) (by
    simpa only [value, Int.toNat_of_nonneg hl.le, Int.toNat_of_nonneg (hnonneg _)] using he)
  have hc := Int.toNat_of_nonneg hl.le
  omega

/-- A positive integral point on the socle face is an actual tail factorization. -/
theorem top_face_positive_impossible (g : Generators) (f : ℤ) (u : Point)
    (hf : f ∉ g.H) (hu : ∀ i, 1 ≤ u i)
    (he : f + ∑ i, g.n i = weight g.n u) : False := by
  apply hf
  refine ⟨fun i => (u i - 1).toNat, ?_⟩
  have hn i : 0 ≤ u i - 1 := by have := hu i; omega
  simp only [value, Int.toNat_of_nonneg (hn _), sub_mul, one_mul,
    Finset.sum_sub_distrib]
  dsimp [weight] at he
  omega

end P21.Nonsymmetric.ColorCap


namespace P21.Nonsymmetric.ColorCap

theorem weight_add (n u v : Point) : weight n (u+v) = weight n u+weight n v := by
  simp [weight,add_mul,Finset.sum_add_distrib]

theorem weight_sub (n u v : Point) : weight n (u-v) = weight n u-weight n v := by
  simp [weight,sub_mul,Finset.sum_sub_distrib]

/-- Any lower positive companion in the same relative-lattice class violates the actual minimum. -/
theorem positive_companion_failure (g : Generators) (f s : ℤ) (k : ℕ)
    (hs : f+∑ i, g.n i = s)
    (hmin : ∀ k' : ℕ, ∀ x' : Fin 3 → ℕ,
      f = (k' : ℤ)*g.m+value g.n x' → k ≤ k')
    (l : ℤ) (hl : 0 < l) (hlk : l < k) (u : Point)
    (hu : weight g.n u = s-l*g.m) : ¬ ∀ i, 0 < u i := by
  intro hpos
  apply lower_companion_impossible g f k hmin l hl hlk u (fun i => by have := hpos i; omega)
  simp only [sub_mul,one_mul,Finset.sum_sub_distrib]
  change f = l*g.m+(weight g.n u-∑ i, g.n i)
  rw [hu]
  linear_combination hs

/-- The three lower and three upper companions of COMP fail positivity for actual minimality. -/
theorem six_companion_failures (g : Generators) (f s : ℤ) (k : ℕ)
    (hs : f+∑ i, g.n i = s)
    (hmin : ∀ k' : ℕ, ∀ x' : Fin 3 → ℕ,
      f = (k' : ℤ)*g.m+value g.n x' → k ≤ k')
    (j : ℤ) (hj : 0 < j) (hjk : j < k) (p z : Point) (R : Fin 3 → Point)
    (hp : weight g.n p = s-(k : ℤ)*g.m) (hR : ∀ i, weight g.n (R i) = s)
    (hz : weight g.n z = j*g.m) :
    (¬ ∀ i, 0 < (p+R 2-R 0+z) i) ∧
    (¬ ∀ i, 0 < (p+R 2-R 1+z) i) ∧
    (¬ ∀ i, 0 < (p+z) i) ∧
    (¬ ∀ i, 0 < (R 1-z) i) ∧
    (¬ ∀ i, 0 < (R 0-z) i) ∧
    (¬ ∀ i, 0 < (R 0+R 1-R 2-z) i) := by
  have hlo : 0 < (k : ℤ)-j := by omega
  have hhi : (k : ℤ)-j < k := by omega
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · apply positive_companion_failure g f s k hs hmin ((k : ℤ)-j) hlo hhi
    rw [weight_add,weight_sub,weight_add,hp,hR,hR,hz]
    ring
  · apply positive_companion_failure g f s k hs hmin ((k : ℤ)-j) hlo hhi
    rw [weight_add,weight_sub,weight_add,hp,hR,hR,hz]
    ring
  · apply positive_companion_failure g f s k hs hmin ((k : ℤ)-j) hlo hhi
    rw [weight_add,hp,hz]
    ring
  · apply positive_companion_failure g f s k hs hmin j hj hjk
    rw [weight_sub,hR,hz]
  · apply positive_companion_failure g f s k hs hmin j hj hjk
    rw [weight_sub,hR,hz]
  · apply positive_companion_failure g f s k hs hmin j hj hjk
    rw [weight_sub,weight_sub,weight_add,hR,hR,hR,hz]
    ring

end P21.Nonsymmetric.ColorCap
