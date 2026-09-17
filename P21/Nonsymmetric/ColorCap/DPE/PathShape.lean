import P21.Nonsymmetric.ColorCap.DPE.ChronologicalPrefix

namespace P21.Nonsymmetric.ColorCap

theorem FiringTrace.endpoint_inBox {upper : Point} {C : Fin 3 → Point}
    {l : List (Fin 3)} {x u : Point} (h : FiringTrace upper C x l u) :
    InBox upper u := by
  cases h with
  | nil hb => exact hb
  | snoc _ _ hb => exact hb

/-- After a nonzero row has fired, the box upper bound and the canonical START
inequality force the next chronological firing (if any) to be row zero. -/
theorem FiringTrace.nonzero_followed_by_zero (D : BoxInput)
    {l : List (Fin 3)} {u : Point} (h : FiringTrace D.upper D.rows D.x l u)
    (hstart : D.x 0 < D.y 0) :
    ∀ p i j b, l = p ++ i :: j :: b → i ≠ 0 → j = 0 := by
  intro p i j b hl hi
  have hp : p <+: l := by
    refine ⟨i :: j :: b, ?_⟩
    simpa [hl]
  have hpi : p ++ [i] <+: l := by
    refine ⟨j :: b, ?_⟩
    simpa [hl, List.append_assoc]
  have hpij : p ++ [i, j] <+: l := by
    refine ⟨b, ?_⟩
    simpa [hl, List.append_assoc]
  obtain ⟨s, hs⟩ := h.prefix_trace hp
  obtain ⟨v, hv⟩ := h.prefix_trace hpi
  obtain ⟨w, hw⟩ := h.prefix_trace hpij
  have hv_eq : v = fire D.rows i s := by
    rw [← hs.execute_eq, ← hv.execute_eq]
    simp [execute_append]
  have hw_eq : w = fire D.rows j v := by
    rw [← hv.execute_eq, ← hw.execute_eq]
    simp [execute_append]
  have hs0 := hs.endpoint_inBox 0
  have hw0 := hw.endpoint_inBox 0
  have hv0 := congrFun hv_eq 0
  have hw0eq := congrFun hw_eq 0
  have hb0 := D.b_pos 0
  fin_cases i <;> fin_cases j
  all_goals simp_all [fire, BoxInput.rows, BoxInput.upper]
  all_goals omega

private theorem proper_of_head_and_adjacent
    (l : List (Fin 3))
    (hhead : l = [] ∨ ∃ b, l = 0 :: b)
    (hadj : ∀ p i j b, l = p ++ i :: j :: b → i ≠ 0 → j = 0) :
    ProperNonzeroPredecessors l := by
  intro a i b hl hi
  cases a with
  | nil =>
      rcases hhead with hnil | ⟨c, hcons⟩
      · simp [hl] at hnil
      · rw [hl] at hcons
        simp at hcons
        exact (hi hcons.1).elim
  | cons x xs =>
      have hlast : ∀ (x : Fin 3) (xs : List (Fin 3)),
          ∃ p j, x :: xs = p ++ [j] := by
        intro z zs
        induction zs generalizing z with
        | nil => exact ⟨[], z, rfl⟩
        | cons y ys ih =>
            obtain ⟨p, j, hj⟩ := ih y
            exact ⟨z :: p, j, by simp [hj]⟩
      obtain ⟨p, j, hj⟩ := hlast x xs
      refine ⟨p, ?_⟩
      have hsplit : l = p ++ j :: i :: b := by
        simpa [hj, List.append_assoc] using hl
      fin_cases j
      · simpa using hj
      · have hz := hadj p 1 i b hsplit (by decide)
        exact (hi hz).elim
      · have hz := hadj p 2 i b hsplit (by decide)
        exact (hi hz).elim

theorem FiringTrace.properNonzeroPredecessors (D : BoxInput)
    {l : List (Fin 3)} {u : Point} (h : FiringTrace D.upper D.rows D.x l u)
    (hstart : D.x 0 < D.y 0)
    (hhead : l = [] ∨ ∃ b, l = 0 :: b) :
    ProperNonzeroPredecessors l := by
  apply proper_of_head_and_adjacent l hhead
  exact h.nonzero_followed_by_zero D hstart

end P21.Nonsymmetric.ColorCap
