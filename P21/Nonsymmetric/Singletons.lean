import P21.Nonsymmetric.Rows
import P21.Nonsymmetric.CriticalBox

namespace P21.Nonsymmetric
open Symmetric.Classification

theorem singleton_critical_bound {g : Generators} (s : g.Setting) {F q : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hq : q ∈ s.semigroup.Q F) {i : Fin 3} (hs : IsSingleton g q i)
    (r : CriticalRelation g i) {k : ℕ}
    (he : complement F g.m q = (k : ℤ) * g.n i) : k < r.coeff := by
  classical
  by_contra hlt
  have hle : r.coeff ≤ k := by omega
  let b : Fin 3 → ℕ := fun j => r.otherCoeff j + if j = i then k - r.coeff else 0
  have hb : value g.n b = complement F g.m q := by
    have hval : value g.n b = value g.n r.otherCoeff +
        ((k - r.coeff : ℕ) : ℤ) * g.n i := by
      simp [b, value, Nat.cast_add, add_mul, Finset.sum_add_distrib]
    rw [hval, ← r.equality, Nat.cast_sub hle, he]
    ring
  let a : g.ActualFactorization3 (complement F g.m q) := ⟨b, hb⟩
  have hpure : value g.n b = ((k - r.coeff : ℕ) : ℤ) * g.n i := by
    have hother : ∀ j, j ≠ i → b j = 0 := fun j hji =>
      singleton_coeff_zero s hF hc hq hs a hji
    have hval : value g.n b = (b i : ℤ) * g.n i := by
      apply Finset.sum_eq_single i
      · intro j _ hji; simp [hother j hji]
      · simp
    simpa [b, r.zero_self] using hval
  rw [hpure, he, Nat.cast_sub hle] at hb
  have hn : 0 < g.n i := lt_trans s.m_pos (s.n_gt i)
  have hr : (0 : ℤ) < r.coeff := by exact_mod_cast r.coeff_pos
  nlinarith

theorem singletons_same_direction {g : Generators} (s : g.Setting) {F q r : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hq : q ∈ s.semigroup.Q F) (hr : r ∈ s.semigroup.Q F) {i : Fin 3}
    (hsq : IsSingleton g q i) (hsr : IsSingleton g r i) : q = r := by
  obtain ⟨k, _, hk⟩ := singleton_pure_complement s hF hc hq hsq
  obtain ⟨l, _, hl⟩ := singleton_pure_complement s hF hc hr hsr
  by_contra hne
  rcases le_total k l with hle | hle
  · have hm := g.H.nsmul_mem (generator_mem g.n i) (l - k)
    have he : complement F g.m r - complement F g.m q = ((l - k : ℕ) : ℤ) * g.n i := by
      rw [hk, hl, Nat.cast_sub hle]; ring
    apply complement_antichain hq hr hne
    apply g.h_subset_gamma
    simpa [he, nsmul_eq_mul] using hm
  · have hm := g.H.nsmul_mem (generator_mem g.n i) (k - l)
    have he : complement F g.m q - complement F g.m r = ((k - l : ℕ) : ℤ) * g.n i := by
      rw [hk, hl, Nat.cast_sub hle]; ring
    apply complement_antichain hr hq (Ne.symm hne)
    apply g.h_subset_gamma
    simpa [he, nsmul_eq_mul] using hm

/-- The caps apply to every W-factorization before uniqueness is deduced. -/
theorem three_singletons_W_unique {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (q : Fin 3 → ℤ) (hq : ∀ i, q i ∈ s.semigroup.Q F)
    (hs : ∀ i, IsSingleton g (q i) i)
    (a b : g.ActualFactorization3 (W F g.m)) : a.coeff = b.coeff := by
  classical
  choose k hk he using fun i => singleton_pure_complement s hF hc (hq i) (hs i)
  have hpos : ∀ i, 0 < g.n i := fun i => lt_trans s.m_pos (s.n_gt i)
  let critical := fun i => Classical.choice (criticalRelation_exists g hpos i)
  have hbound := fun i => singleton_critical_bound s hF hc (hq i) (hs i) (critical i) (he i)
  apply critical_box_unique hpos critical
  · intro i; exact lt_trans (singleton_W_cap (hq i) (he i) a) (hbound i)
  · intro i; exact lt_trans (singleton_W_cap (hq i) (he i) b) (hbound i)
  · exact a.equation.trans b.equation.symm

/-- Three singletons exhaust the full Q, not merely a chosen subset. -/
theorem three_singletons_Q_eq_range {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (q : Fin 3 → ℤ) (hq : ∀ i, q i ∈ s.semigroup.Q F)
    (hs : ∀ i, IsSingleton g (q i) i) : s.semigroup.Q F = Set.range q := by
  classical
  choose k hk he using fun i => singleton_pure_complement s hF hc (hq i) (hs i)
  obtain ⟨a⟩ := actual_iff_mem.mpr (s.apery_in_tail (s.semigroup.W_mem_apery hF s.m_pos))
  have ha : ∀ i, a.coeff i = k i - 1 := by
    intro i
    obtain ⟨b, hb⟩ := singleton_W_cap_attained s (hq i) (hk i) (hs i) (he i)
    rw [three_singletons_W_unique s hF hc q hq hs a b]
    exact hb
  apply Set.Subset.antisymm
  · intro r hr
    by_contra hnr
    have hne : ∀ i, q i ≠ r := by intro i hi; exact hnr ⟨i, hi⟩
    obtain ⟨b⟩ := actual_iff_mem.mpr
      (s.apery_in_tail (s.semigroup.complement_of_q_mem_apery hF hc hr))
    have hbound : ∀ i, b.coeff i ≤ a.coeff i := by
      intro i
      have hh := singleton_complement_cap (hq i) hr (hne i) (he i) b
      rw [ha i]
      omega
    have hm := value_sub_mem g.n a.coeff b.coeff hbound
    rw [a.equation, b.equation] at hm
    apply hr.1.1
    apply g.h_subset_gamma
    simpa [Generators.H] using hm
  · rintro r ⟨i, rfl⟩; exact hq i

theorem three_singletons_force_Q_three {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (q : Fin 3 → ℤ) (hq : ∀ i, q i ∈ s.semigroup.Q F)
    (hs : ∀ i, IsSingleton g (q i) i) : (s.semigroup.Q F).ncard = 3 := by
  have hi : Function.Injective q := by
    intro i j he
    have hh : ({i} : Set (Fin 3)) = {j} := by rw [← hs i, ← hs j, he]
    exact Set.singleton_injective hh
  rw [three_singletons_Q_eq_range s hF hc q hq hs, Set.ncard_range_of_injective hi]
  simp

end P21.Nonsymmetric
