import P21.Semantics
import P21.External.SymmetricThreeGenerator
import P21.Symmetric.Classification.CriticalRelations

namespace P21.Nonsymmetric

def NonsymmetricTail (g : Generators) : Prop := ¬ Symmetric.SymmetricTail g

/-- One row retains membership in the same full Q set. -/
structure ActualQRow {g : Generators} (s : g.Setting) (F : ℤ) where
  q : ℤ
  mem : q ∈ s.semigroup.Q F

/-- Four selected rows; the full Q set may contain additional rows. -/
structure FourDistinctActualQRows {g : Generators} (s : g.Setting) (F : ℤ) where
  row : Fin 4 → ActualQRow s F
  distinct : Function.Injective (fun i => (row i).q)

theorem select_four_actual_rows {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hcard : 4 ≤ (s.semigroup.Q F).ncard) : Nonempty (FourDistinctActualQRows s F) := by
  obtain ⟨r, hi, hr⟩ := s.select_four_rows hF hc hcard
  exact ⟨⟨fun i => ⟨r i, (hr i).1⟩, hi⟩⟩

theorem pf_antichain (S : NumericalSemigroup) {q r : ℤ}
    (hq : q ∈ S.PF) (hr : r ∈ S.PF) (hne : q ≠ r) : r - q ∉ S.carrier := by
  intro hd
  have hh := hq.2 (r - q) hd (by omega)
  exact hr.1 (by convert hh using 1; ring)

theorem complement_antichain {g : Generators} {s : g.Setting} {F q r : ℤ}
    (hq : q ∈ s.semigroup.Q F) (hr : r ∈ s.semigroup.Q F) (hne : q ≠ r) :
    complement F g.m r - complement F g.m q ∉ g.Gamma := by
  have hh := pf_antichain s.semigroup hr.1 hq.1 (Ne.symm hne)
  change q - r ∉ g.Gamma at hh
  simpa [complement, W] using hh

/-- Coefficient subtraction consumes only copies contained in this vector. -/
theorem value_sub_mem {k : ℕ} (n : Fin k → ℤ) (a b : Fin k → ℕ)
    (hle : ∀ i, b i ≤ a i) : value n a - value n b ∈ generated n := by
  refine ⟨fun i => a i - b i, ?_⟩
  simp only [value, Nat.cast_sub (hle _), sub_mul, Finset.sum_sub_distrib]

theorem actual_sub_copies {g : Generators} {x : ℤ}
    (a : g.ActualFactorization3 x) (i : Fin 3) (k : ℕ) (hk : k ≤ a.coeff i) :
    x - (k : ℤ) * g.n i ∈ g.H := by
  classical
  have h := value_sub_mem g.n a.coeff (fun j => if j = i then k else 0)
    (fun j => by by_cases hj : j = i <;> simp_all)
  have hs : value g.n (fun j => if j = i then k else 0) = (k : ℤ) * g.n i := by
    simp [value]
  rw [a.equation, hs] at h
  exact h

def IsSingleton (g : Generators) (q : ℤ) (i : Fin 3) : Prop := g.SH q = {i}

theorem singleton_coeff_zero {g : Generators} (s : g.Setting) {F q : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hq : q ∈ s.semigroup.Q F) {i j : Fin 3} (hs : IsSingleton g q i)
    (a : g.ActualFactorization3 (complement F g.m q)) (hji : j ≠ i) :
    a.coeff j = 0 := by
  by_contra hn
  have hd : j ∈ g.D (F + g.m - q) := actual_iff_mem.mp
    ⟨removeOne a j (Nat.pos_of_ne_zero hn)⟩
  have hj := (s.key_support_inclusion hF hc hq).2 hd
  rw [hs] at hj
  exact hji hj

theorem singleton_pure_complement {g : Generators} (s : g.Setting) {F q : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hq : q ∈ s.semigroup.Q F) {i : Fin 3} (hs : IsSingleton g q i) :
    ∃ k : ℕ, 0 < k ∧ complement F g.m q = (k : ℤ) * g.n i := by
  obtain ⟨a⟩ := actual_iff_mem.mpr
    (s.apery_in_tail (s.semigroup.complement_of_q_mem_apery hF hc hq))
  have he : value g.n a.coeff = (a.coeff i : ℤ) * g.n i := by
    unfold value
    apply Finset.sum_eq_single i
    · intro j _ hji
      simp [singleton_coeff_zero s hF hc hq hs a hji]
    · simp
  refine ⟨a.coeff i, ?_, by rw [← he]; exact a.equation.symm⟩
  have hqF := s.semigroup.q_lt_frobenius hF hq
  have hm := s.m_pos
  have heq := a.equation
  rw [he] at heq
  by_contra hn
  have hz : a.coeff i = 0 := by omega
  simp only [hz, Nat.cast_zero, zero_mul] at heq
  omega

theorem singleton_complement_cap {g : Generators} {s : g.Setting} {F q r : ℤ}
    (hq : q ∈ s.semigroup.Q F) (hr : r ∈ s.semigroup.Q F) (hne : q ≠ r)
    {i : Fin 3} {k : ℕ} (he : complement F g.m q = (k : ℤ) * g.n i)
    (a : g.ActualFactorization3 (complement F g.m r)) : a.coeff i < k := by
  by_contra hh
  have hm := actual_sub_copies a i k (by omega)
  rw [← he] at hm
  exact complement_antichain hq hr hne (g.h_subset_gamma hm)

theorem singleton_W_cap {g : Generators} {s : g.Setting} {F q : ℤ}
    (hq : q ∈ s.semigroup.Q F) {i : Fin 3} {k : ℕ}
    (he : complement F g.m q = (k : ℤ) * g.n i)
    (a : g.ActualFactorization3 (W F g.m)) : a.coeff i < k := by
  by_contra hh
  have hm := actual_sub_copies a i k (by omega)
  rw [← he] at hm
  apply hq.1.1
  apply g.h_subset_gamma
  convert hm using 1; simp [complement, W]

theorem singleton_W_cap_attained {g : Generators} (s : g.Setting) {F q : ℤ}
    (hq : q ∈ s.semigroup.Q F) {i : Fin 3} {k : ℕ} (hk : 0 < k)
    (hs : IsSingleton g q i) (he : complement F g.m q = (k : ℤ) * g.n i) :
    ∃ a : g.ActualFactorization3 (W F g.m), a.coeff i = k - 1 := by
  classical
  have hret : q + g.n i ∈ g.H := by
    have hi : i ∈ g.SH q := by rw [hs]; simp
    exact hi
  obtain ⟨b⟩ := actual_iff_mem.mpr hret
  have hz := s.return_coordinate_zero hq i b
  let a : Fin 3 → ℕ := fun j => b.coeff j + if j = i then k - 1 else 0
  refine ⟨⟨a, ?_⟩, by simp [a, hz]⟩
  have hv : value g.n a = value g.n b.coeff + ((k - 1 : ℕ) : ℤ) * g.n i := by
    simp [a, value, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  rw [hv, b.equation, Nat.cast_sub (by omega : 1 ≤ k)]
  dsimp [complement, W] at he ⊢
  nlinarith

end P21.Nonsymmetric
