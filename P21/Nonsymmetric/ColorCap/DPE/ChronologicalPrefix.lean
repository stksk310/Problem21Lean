import P21.Nonsymmetric.ColorCap.DPE.SuccessfulPrefix

namespace P21.Nonsymmetric.ColorCap

/-- Every non-first-color occurrence has a genuine immediately preceding row-zero firing. -/
def ProperNonzeroPredecessors (l : List (Fin 3)) : Prop :=
  ∀ a i b, l = a ++ i :: b → i ≠ 0 → ∃ p, a = p ++ [0]

/-- The `h`-th occurrence is split from the original list, preserving its exact prefix. -/
theorem nth_occurrence_split {α : Type*} [DecidableEq α] (r : α) :
    ∀ (l : List α) (h : ℕ), 1 ≤ h → h ≤ l.count r →
      ∃ a b, l = a ++ r :: b ∧ a.count r = h - 1 := by
  intro l
  induction l with
  | nil => intro h hh hc; simp at hc; omega
  | cons x xs ih =>
      intro h hh hc
      by_cases hx : x = r
      · subst x
        by_cases he : h = 1
        · subst h
          exact ⟨[],xs,rfl,by simp⟩
        · have hh' : 1 ≤ h-1 := by omega
          have hc' : h-1 ≤ xs.count r := by simp at hc; omega
          obtain ⟨a,b,hab,hcount⟩ := ih (h-1) hh' hc'
          refine ⟨r::a,b,?_,?_⟩
          · simp [hab]
          · simp [hcount]
            omega
      · have hc' : h ≤ xs.count r := by simpa [hx] using hc
        obtain ⟨a,b,hab,hcount⟩ := ih h hh hc'
        refine ⟨x::a,b,?_,?_⟩
        · simp [hab]
        · simpa [hx] using hcount

theorem occurrence_source_ends_zero (l : List (Fin 3)) (r : Fin 3)
    (hp : ProperNonzeroPredecessors l) (hr : r ≠ 0)
    {h : ℕ} (hh : 1 ≤ h) (hc : h ≤ l.count r) :
    ∃ p b, l = (p ++ [0]) ++ r :: b ∧ (p ++ [0]).count r = h-1 := by
  obtain ⟨a,b,hab,hcount⟩ := nth_occurrence_split r l h hh hc
  obtain ⟨p,rfl⟩ := hp a r b hab hr
  exact ⟨p,b,hab,hcount⟩

theorem count_eq_zero_of_members {l : List (Fin 3)} {a b c : Fin 3}
    (hmem : ∀ i ∈ l, i = a ∨ i = b) (hc : c ≠ a) (hc' : c ≠ b) :
    l.count c = 0 := by
  rw [List.count_eq_zero]
  intro hm
  rcases hmem c hm with h | h <;> contradiction

end P21.Nonsymmetric.ColorCap
