import P21.Tail

namespace P21.Generators
variable {g : Generators} (s : g.Setting)

/-- The support-zero predicate is exactly membership in the other two generators. -/
theorem offDirection_iff_pair {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : ℤ) : g.OffDirection i x ↔ ∃ a b : ℕ, x = (a : ℤ) * g.n j + (b : ℤ) * g.n k := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f.coeff j, f.coeff k, ?_⟩
    have he := f.equation
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp_all [value, Fin.sum_univ_succ] <;> omega
  · rintro ⟨a, b, rfl⟩
    let c : Fin 3 → ℕ := fun t => if t = j then a else if t = k then b else 0
    refine ⟨⟨c, ?_⟩, by simp [c, hij, hik]⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp_all [c, value, Fin.sum_univ_succ] <;> ring

namespace Setting

theorem key_pair_return {F q : ℤ} (hF : s.semigroup.IsFrobenius F)
    (hq : q ∈ s.semigroup.Q F) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : i ∈ g.D (F + g.m - q)) :
    ∃ a b : ℕ, q + g.n i = (a : ℤ) * g.n j + (b : ℤ) * g.n k :=
  (offDirection_iff_pair hij hik hjk _).mp (s.key_support_zero hF hq i hi)

/-- A local row carries its actual Q membership and all supported directions simultaneously. -/
def RowFacts (F q : ℤ) : Prop :=
  q ∈ s.semigroup.Q F ∧
  q + g.m ∈ s.semigroup.Apery g.m ∧
  F + g.m - q ∈ s.semigroup.Apery g.m ∧
  q + g.m ∈ g.H ∧ F + g.m - q ∈ g.H ∧
  (g.D (F + g.m - q)).Nonempty ∧
  g.D (F + g.m - q) ⊆ g.SH q ∧
  ∀ i ∈ g.D (F + g.m - q), g.OffDirection i (q + g.n i)

theorem all_q_row_facts {F : ℤ} (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) : ∀ q ∈ s.semigroup.Q F, s.RowFacts F q := by
  intro q hq
  have hh := s.semigroup.pf_add_m_mem_apery g.m_mem (ne_of_gt s.m_pos) hq.1
  have hcomp := s.semigroup.complement_of_q_mem_apery hF hc hq
  have hs := s.key_support_inclusion hF hc hq
  exact ⟨hq, hh, hcomp, s.apery_in_tail hh, s.apery_in_tail hcomp,
    hs.1, hs.2, fun i hi => s.key_support_zero hF hq i hi⟩

/-- C2.5: four selected rows; Q itself is never restricted to four elements. -/
theorem select_four_rows {F : ℤ} (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) (hcard : 4 ≤ (s.semigroup.Q F).ncard) :
    ∃ rows : Fin 4 → ℤ, Function.Injective rows ∧ ∀ r, s.RowFacts F (rows r) := by
  have hfin : (s.semigroup.Q F).Finite :=
    (s.semigroup.pf_finite hF g.m_mem (ne_of_gt s.m_pos)).subset Set.sdiff_subset
  obtain ⟨a, b, c, d, ha, hb, hc', hd, hab, hac, had, hbc, hbd, hcd⟩ :=
    (Set.three_lt_ncard_iff hfin).mp (by omega : 3 < (s.semigroup.Q F).ncard)
  let rows : Fin 4 → ℤ := ![a, b, c, d]
  refine ⟨rows, ?_, ?_⟩
  · intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [rows]
  · intro i
    apply s.all_q_row_facts hF hc
    fin_cases i <;> simpa [rows] using (by assumption : _ ∈ s.semigroup.Q F)

theorem tail_minimal_and_cofinite {F : ℤ} (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) (hQ : (s.semigroup.Q F).Nonempty) :
    g.TailMinimal ∧ g.tailGcd = 1 ∧ (∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H) :=
  ⟨g.tail_minimal s.minimal, s.tail_gcd_eq_one hF hc hQ, s.tail_cofinite hF hc hQ⟩

end Setting
end P21.Generators
