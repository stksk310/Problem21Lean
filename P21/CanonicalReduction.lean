import P21.Apery

namespace P21.Generators
namespace Setting
variable {g : Generators} (s : g.Setting)

/-- Every named Apéry factorization has zero m-coordinate. -/
theorem apery_m_coordinate_zero {x : ℤ} (hx : x ∈ s.semigroup.Apery g.m)
    (a : g.ActualFactorization4 x) : a.coeff 0 = 0 := by
  by_contra hn
  have ha := removeOne a 0 (Nat.pos_of_ne_zero hn)
  exact hx.2 (actual_iff_mem.mp ⟨ha⟩)

theorem apery_in_tail {x : ℤ} (hx : x ∈ s.semigroup.Apery g.m) : x ∈ g.H := by
  obtain ⟨a⟩ := actual_iff_mem.mpr hx.1
  have hz := s.apery_m_coordinate_zero hx a
  refine ⟨fun i => a.coeff i.succ, ?_⟩
  have he := a.equation
  simpa [value, all, Fin.sum_univ_succ, hz] using he

theorem a0_tail_iff {F w : ℤ} (hF : s.semigroup.IsFrobenius F) :
    w ∈ s.semigroup.A0 F g.m ↔ w ∈ g.H ∧ F + g.m - w ∈ g.H := by
  constructor
  · intro h; exact ⟨s.apery_in_tail h.1, s.apery_in_tail h.2⟩
  · rintro ⟨hw, hc⟩
    have ha : w ∈ s.semigroup.Apery g.m := by
      refine ⟨g.h_subset_gamma hw, ?_⟩
      intro h
      apply hF.1
      change F ∈ g.Gamma
      convert g.Gamma.add_mem h (g.h_subset_gamma hc) using 1; ring
    exact ⟨ha, s.semigroup.complement_mem_apery hF ha (g.h_subset_gamma hc)⟩

/-- KEY contradiction keeps precisely the two summands displayed in §2.10. -/
theorem key_return_apery {F q : ℤ} (hF : s.semigroup.IsFrobenius F)
    (hq : q ∈ s.semigroup.Q F) (i : Fin 3) (hs : F + g.m - q - g.n i ∈ g.H) :
    q + g.n i ∈ s.semigroup.Apery g.m := by
  refine ⟨hq.1.2 (g.n i) (g.n_mem i) (by have := s.n_gt i; have := s.m_pos; omega), ?_⟩
  intro hreturn
  apply hF.1
  change F ∈ g.Gamma
  have same_element := g.Gamma.add_mem (g.h_subset_gamma hs) hreturn
  convert same_element using 1; ring

/-- The supplied actual H-factorization itself has support zero in direction i. -/
theorem return_coordinate_zero {F q : ℤ} (hq : q ∈ s.semigroup.Q F)
    (i : Fin 3) (a : g.ActualFactorization3 (q + g.n i)) : a.coeff i = 0 := by
  by_contra hn
  have removed := removeOne a i (Nat.pos_of_ne_zero hn)
  have htail := actual_iff_mem.mp ⟨removed⟩
  have hqmem : q ∈ g.H := by simpa [H] using htail
  exact hq.1.1 (g.h_subset_gamma hqmem)

/-- C2.3 support-zero return; the coefficient-zero witness is actual. -/
theorem key_support_zero {F q : ℤ} (hF : s.semigroup.IsFrobenius F)
    (hq : q ∈ s.semigroup.Q F) (i : Fin 3) (hs : F + g.m - q - g.n i ∈ g.H) :
    g.OffDirection i (q + g.n i) := by
  obtain ⟨a⟩ := actual_iff_mem.mpr (s.apery_in_tail (s.key_return_apery hF hq i hs))
  exact ⟨a, s.return_coordinate_zero hq i a⟩

theorem support_nonempty {c : ℤ} (hc : c ∈ g.H) (hcpos : 0 < c) : (g.D c).Nonempty := by
  obtain ⟨a⟩ := actual_iff_mem.mpr hc
  have hex : ∃ i, 0 < a.coeff i := by
    by_contra hn
    have hz : ∀ i, a.coeff i = 0 := fun i => Nat.eq_zero_of_not_pos (fun h => hn ⟨i, h⟩)
    have he := a.equation
    simp [value, hz] at he
    omega
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, actual_iff_mem.mp ⟨removeOne a i hi⟩⟩

theorem key_support_inclusion {F q : ℤ} (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) (hq : q ∈ s.semigroup.Q F) :
    (g.D (F + g.m - q)).Nonempty ∧ g.D (F + g.m - q) ⊆ g.SH q := by
  constructor
  · have ha := s.semigroup.complement_of_q_mem_apery hF hc hq
    have hqF := s.semigroup.q_lt_frobenius hF hq
    exact support_nonempty (s.apery_in_tail ha) (by have := s.m_pos; omega)
  · intro i hi
    exact s.apery_in_tail (s.key_return_apery hF hq i hi)

theorem supported_rectangle {F q : ℤ} (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) (hq : q ∈ s.semigroup.Q F)
    (i : Fin 3) (hi : i ∈ g.D (F + g.m - q)) :
    (q + g.m ∈ s.semigroup.Apery g.m ∧ q + g.m ∈ g.H) ∧
    (F + g.m - q ∈ s.semigroup.Apery g.m ∧ F + g.m - q ∈ g.H) ∧
    (F + g.m - q - g.n i ∈ s.semigroup.Apery g.m ∧ F + g.m - q - g.n i ∈ g.H) ∧
    (q + g.n i ∈ s.semigroup.Apery g.m ∧ q + g.n i ∈ g.H) ∧
    (q + g.m) + (F + g.m - q) = (F + g.m) + g.m ∧
    (F + g.m - q - g.n i) + (q + g.n i) = F + g.m := by
  have hh := s.semigroup.pf_add_m_mem_apery g.m_mem (ne_of_gt s.m_pos) hq.1
  have hcomp := s.semigroup.complement_of_q_mem_apery hF hc hq
  have hx : F + g.m - q - g.n i ∈ s.semigroup.Apery g.m :=
    s.semigroup.apery_lower (g.h_subset_gamma hi) hcomp (by
      change (F + g.m - q) - (F + g.m - q - g.n i) ∈ g.Gamma
      convert g.n_mem i using 1; ring)
  have hy := s.key_return_apery hF hq i hi
  exact ⟨⟨hh, s.apery_in_tail hh⟩, ⟨hcomp, s.apery_in_tail hcomp⟩,
    ⟨hx, s.apery_in_tail hx⟩, ⟨hy, s.apery_in_tail hy⟩, by ring, by ring⟩

end Setting
end P21.Generators
