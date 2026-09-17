import P21.Basic
import Mathlib.Tactic.LinearCombination

namespace P21.Nonsymmetric.ColorCap

/-- Integer tail coefficients are converted to an actual witness only after all signs are checked. -/
theorem actual_of_nonnegative (g : Generators) (f k : ℤ) (x : Fin 3 → ℤ)
    (hk : 0 ≤ k) (hx : ∀ i, 0 ≤ x i)
    (he : f = k * g.m + ∑ i, x i * g.n i) : f ∈ g.Gamma := by
  refine ⟨Fin.cons k.toNat (fun i => (x i).toNat), ?_⟩
  rw [g.value_cons]
  simpa [value, Int.toNat_of_nonneg hk, Int.toNat_of_nonneg (hx _)] using he.symm

/-- An arm gap bounds the coordinate of every actual factorization of its same socle element. -/
theorem arm_coordinate_cap (g : Generators) (f k : ℤ) (x : Fin 3 → ℤ)
    (hk : 0 ≤ k) (hx : ∀ i, 0 ≤ x i)
    (he : f = k * g.m + ∑ i, x i * g.n i)
    (i : Fin 3) (depth : ℤ) (hgap : f - depth * g.n i ∉ g.Gamma) : x i < depth := by
  classical
  by_contra hn
  have hi : depth ≤ x i := by omega
  apply hgap
  apply actual_of_nonnegative g (f - depth * g.n i) k
    (fun j => x j - if j = i then depth else 0) hk
  · intro j
    split_ifs with hj
    · subst j; omega
    · simpa using hx j
  · simp only [sub_mul, Finset.sum_sub_distrib]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    linear_combination he

/-- A positive state beyond any arm cap contradicts that same actual arm gap. -/
theorem same_element_positive_exit (g : Generators) (f k : ℤ)
    (u depth upper : Fin 3 → ℤ) (hk : 0 ≤ k) (hu : ∀ i, 1 ≤ u i)
    (he : f = k * g.m + ∑ i, (u i - 1) * g.n i)
    (hgaps : ∀ i, f - depth i * g.n i ∉ g.Gamma)
    (hbound : ∀ i, depth i ≤ upper i - 1)
    (hexit : ∃ i, upper i ≤ u i) : False := by
  obtain ⟨i,hi⟩ := hexit
  have hc := arm_coordinate_cap g f k (fun j => u j - 1) hk
    (fun j => by have := hu j; omega) he i (depth i) (hgaps i)
  have := hbound i
  omega

/-- A socle element in Γ but outside the tail has an attained least positive m-level. -/
theorem minimal_positive_level (g : Generators) (f : ℤ)
    (hf : f ∈ g.Gamma) (hfH : f ∉ g.H) :
    ∃ k : ℕ, ∃ x : Fin 3 → ℕ,
      0 < k ∧ f = (k : ℤ) * g.m + value g.n x ∧
      ∀ k' : ℕ, ∀ x' : Fin 3 → ℕ,
        f = (k' : ℤ) * g.m + value g.n x' → k ≤ k' := by
  classical
  have hex : ∃ k : ℕ, ∃ x : Fin 3 → ℕ,
      f = (k : ℤ) * g.m + value g.n x := by
    obtain ⟨a,ha⟩ := hf
    refine ⟨a 0, (fun i => a i.succ), ?_⟩
    simpa [value, Generators.all, Fin.sum_univ_succ] using ha.symm
  obtain ⟨x,hx⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex,x,?_,hx,?_⟩
  · by_contra hn
    have hz : Nat.find hex = 0 := by omega
    apply hfH
    exact ⟨x,by simpa [hz] using hx.symm⟩
  · intro k' x' he
    exact Nat.find_min' hex ⟨x',he⟩

/-- The selected minimum remains within every actual arm's coordinate cap. -/
theorem minimal_positive_arm_box (g : Generators) (f : ℤ) (depth : Fin 3 → ℤ)
    (hf : f ∈ g.Gamma) (hfH : f ∉ g.H)
    (hgaps : ∀ i, f - depth i * g.n i ∉ g.Gamma) :
    ∃ k : ℕ, ∃ p : Fin 3 → ℤ,
      0 < k ∧ (∀ i, 1 ≤ p i ∧ p i ≤ depth i) ∧
      f = (k : ℤ) * g.m + ∑ i, (p i - 1) * g.n i ∧
      ∀ k' : ℕ, ∀ x' : Fin 3 → ℕ,
        f = (k' : ℤ) * g.m + value g.n x' → k ≤ k' := by
  obtain ⟨k,x,hk,he,hmin⟩ := minimal_positive_level g f hf hfH
  refine ⟨k,(fun i => (x i : ℤ) + 1),hk,?_,?_,hmin⟩
  · intro i
    have hc := arm_coordinate_cap g f k (fun j => (x j : ℤ))
      (Int.natCast_nonneg _) (fun _ => Int.natCast_nonneg _) he i (depth i) (hgaps i)
    dsimp
    constructor <;> omega
  · simpa [value] using he

end P21.Nonsymmetric.ColorCap

