import P21.Nonsymmetric.White.CyclicClasses
import P21.Nonsymmetric.White.WidthOne
import P21.Nonsymmetric.ColorCap.MinimumOne.SocleSimplex

namespace P21.Nonsymmetric.ColorCap.MinimumOne

open White

/-- Primitivity and the exact saturated row lattice construct the cyclic
coordinates; the complete AGE condition is derived from actual minimality. -/
theorem exists_cyclic_input (g : Generators) (s : g.Setting)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (D : HerzogCriticalData g) (c : Bool) (k : ℕ) (p : Point)
    (hk : 2 ≤ k) (hp : ∀ i, 1 ≤ p i)
    (he : (if c then D.fA else D.fB) = (k : ℤ)*g.m+∑ i,(p i-1)*g.n i)
    (hmin : ∀ k' : ℕ, ∀ x : Fin 3 → ℕ,
      (if c then D.fA else D.fB) = (k' : ℤ)*g.m+value g.n x → k ≤ k') :
    ∃ z t : Point, (∑ i,t i = 1) ∧
      (∀ l, (k : ℤ)*z l = ∑ i,t i*(socleRows D c i l-p l)) ∧
      (∀ j : ℤ, 0 < j → j < k →
        (∀ i, 0 < classResidues k t j i) ∧
        ∑ i,classResidues k t j i = (k : ℤ)+j) := by
  obtain ⟨z,hz⟩ := weight_surjective hcof g.m
  have hn i := lt_trans s.m_pos (s.n_gt i)
  obtain ⟨t,ht,hst⟩ := socleMatrix_span_level D c p hn ((k : ℤ)*g.m)
    (socleMatrix_weight D c p k he) (fun l => (k : ℤ)*z l) 1
    (by rw [weight_scale,hz]; ring)
  refine ⟨z,t,hst,ht,?_⟩
  intro j hj hjk
  apply cyclic_age_of_minimum g s.m_pos (if c then D.fA else D.fB)
    (socle D c) k (by omega) p z t (socleRows D c) rfl hp
    (socleRows_nonneg D c) ?_ (socleRows_weight D c) hst ht hmin j hj hjk
  have hh := socle_minimum_weight D c p k he
  omega

/-- The White arithmetic input is extracted without postulating any class or
functional. The integral representative remains available for reconstruction. -/
theorem exists_cyclic_age (g : Generators) (s : g.Setting)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (D : HerzogCriticalData g) (c : Bool) (k : ℕ) (p : Point)
    (hk : 2 ≤ k) (hp : ∀ i, 1 ≤ p i)
    (he : (if c then D.fA else D.fB) = (k : ℤ)*g.m+∑ i,(p i-1)*g.n i)
    (hmin : ∀ k' : ℕ, ∀ x : Fin 3 → ℕ,
      (if c then D.fA else D.fB) = (k' : ℤ)*g.m+value g.n x → k ≤ k') :
    ∃ v a : Point, (∀ i, 0 < a i ∧ a i < k) ∧ CyclicAge k a ∧
      (∀ l, (k : ℤ)*v l = ∑ i,a i*(socleRows D c i l-p l)) := by
  obtain ⟨z,t,ht,heq,hage⟩ := exists_cyclic_input g s hcof D c k p hk hp he hmin
  let a := classResidues (k : ℤ) t 1
  refine ⟨classRepresentative (socleRows D c) p z t k 1,a,?_,?_,
    classRepresentative_equation (socleRows D c) p z t k 1 heq⟩
  · intro i
    exact ⟨(hage 1 (by omega) (by omega)).1 i,Int.emod_lt_of_pos _ (by omega)⟩
  · intro j hj hjk
    have ha : ∀ i, (j*a i)%(k : ℤ) = classResidues k t j i := by
      intro i
      simp only [a,classResidues,one_mul]
      simp only [Int.mul_emod, Int.emod_emod]
    simp only [ha]
    exact (hage j hj hjk).2

end P21.Nonsymmetric.ColorCap.MinimumOne
