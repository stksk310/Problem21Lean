import P21.Nonsymmetric.ColorCap.DPE.TraceSuccessfulPrefix
import P21.Nonsymmetric.ColorCap.DPEOneColor

namespace P21.Nonsymmetric.ColorCap

theorem FiringTrace.head_zero (D : BoxInput)
    {l : List (Fin 3)} {u : Point}
    (ht : FiringTrace D.upper D.rows D.x l u) (hne : l ≠ [])
    (hfirst : InBox D.upper (fire D.rows 0 D.x)) :
    ∃ b, l = 0 :: b := by
  cases l with
  | nil => contradiction
  | cons i is =>
      have hp : [i] <+: i :: is := by
        exact ⟨is, by simp⟩
      obtain ⟨v, hv⟩ := ht.prefix_trace hp
      have hveq : v = fire D.rows i D.x := by
        rw [← hv.execute_eq]
        rfl
      have hi : InBox D.upper (fire D.rows i D.x) := by
        rw [← hveq]
        exact hv.endpoint_inBox
      have hei : (0 : Fin 3) = i := D.in_box_fire_unique D.x 0 i hfirst hi
      subst i
      exact ⟨is, rfl⟩

theorem one_color_trace_sink_impossible (D : BoxInput)
    {l : List (Fin 3)} {u : Point}
    (ht : FiringTrace D.upper D.rows D.x l u) (hne : l ≠ [])
    (hno1 : l.count 1 = 0) (hno2 : l.count 2 = 0)
    (hsink : ¬ ∃ i, ∀ j, 1 ≤ fire D.rows i u j) : False := by
  have hcount0 : 1 ≤ l.count 0 := by
    have hm : ∃ i ∈ l, i = 0 := by
      by_contra hn
      push Not at hn
      have hall : ∀ i ∈ l, i = 1 ∨ i = 2 := by
        intro i hi
        fin_cases i
        · exact (hn 0 hi rfl).elim
        · exact Or.inl rfl
        · exact Or.inr rfl
      have : l = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro i hi
        rcases hall i hi with rfl | rfl
        · have := List.count_pos_iff.mpr hi; omega
        · have := List.count_pos_iff.mpr hi; omega
      contradiction
    obtain ⟨i, hi, rfl⟩ := hm
    exact List.count_pos_iff.mpr hi
  let N : ℤ := (l.count 0 : ℤ) + 1
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hu0 := ht.endpoint_eq_sub_sum 0
  have hu1 := ht.endpoint_eq_sub_sum 1
  have hu2 := ht.endpoint_eq_sub_sum 2
  simp [BoxInput.rows, Fin.sum_univ_succ, hno1, hno2] at hu0 hu1 hu2
  have hueq : u = ![N * D.x 0,
      D.x 1 - (N - 1) * (D.y 1 + D.b 1),
      D.x 2 - (N - 1) * D.y 2] := by
    funext j
    fin_cases j
    · dsimp [N]
      ring_nf at hu0 ⊢
      omega
    · dsimp [N]
      ring_nf at hu1 ⊢
      omega
    · dsimp [N]
      ring_nf at hu2 ⊢
      omega
  rw [hueq] at hsink
  have hbox : InBox D.upper ![N * D.x 0,
      D.x 1 - (N - 1) * (D.y 1 + D.b 1),
      D.x 2 - (N - 1) * D.y 2] := by
    rw [← hueq]
    exact ht.endpoint_inBox
  exact one_color_sink_impossible D N hN hbox hsink

end P21.Nonsymmetric.ColorCap
