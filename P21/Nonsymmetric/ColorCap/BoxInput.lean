import P21.Nonsymmetric.ColorCap.BoxPaths

namespace P21.Nonsymmetric.ColorCap

/-- A nonnegative weighted certificate of sufficient mass contradicts multiplicity. -/
theorem weighted_certificate_impossible (m l : ℤ) (n v : Point)
    (hm : 0 < m) (hl : 0 < l) (hn : ∀ i, m < n i)
    (hv : ∀ i, 0 ≤ v i) (hmass : l ≤ ∑ i, v i)
    (he : l * m = weight n v) : False := by
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have hn0 := hn 0
  have hn1 := hn 1
  have hn2 := hn 2
  have hd0 := mul_nonneg h0 (sub_nonneg.mpr hn0.le)
  have hd1 := mul_nonneg h1 (sub_nonneg.mpr hn1.le)
  have hd2 := mul_nonneg h2 (sub_nonneg.mpr hn2.le)
  simp [weight, Fin.sum_univ_succ] at he hmass
  rcases lt_or_ge 0 (v 0) with h | h
  · have := mul_pos h (sub_pos.mpr hn0)
    nlinarith [mul_nonneg hm.le (sub_nonneg.mpr hmass)]
  rcases lt_or_ge 0 (v 1) with h' | h'
  · have := mul_pos h' (sub_pos.mpr hn1)
    nlinarith [mul_nonneg hm.le (sub_nonneg.mpr hmass)]
  have h'' : 0 < v 2 := by omega
  have := mul_pos h'' (sub_pos.mpr hn2)
  nlinarith [mul_nonneg hm.le (sub_nonneg.mpr hmass)]

/-- Exact INPUT of Appendix B.10; determinant and path-exit claims are not fields. -/
structure BoxInput where
  m : ℤ
  n : Point
  x : Point
  y : Point
  b : Point
  m_pos : 0 < m
  n_gt : ∀ i, m < n i
  x_pos : ∀ i, 1 ≤ x i
  y_pos : ∀ i, 1 ≤ y i
  b_pos : ∀ i, 1 ≤ b i
  row0 : -x 0 * n 0 + (y 1 + b 1) * n 1 + y 2 * n 2 = m
  row1 : y 0 * n 0 - x 1 * n 1 + (y 2 + b 2) * n 2 = m
  row2 : (y 0 + b 0) * n 0 + y 1 * n 1 - x 2 * n 2 = m

namespace BoxInput

def rows (D : BoxInput) : Fin 3 → Point :=
  ![![-D.x 0,D.y 1 + D.b 1,D.y 2],
    ![D.y 0,-D.x 1,D.y 2 + D.b 2],
    ![D.y 0 + D.b 0,D.y 1,-D.x 2]]

def upper (D : BoxInput) : Point := fun i => D.x i + D.y i

theorem rows_weight (D : BoxInput) (i : Fin 3) : weight D.n (D.rows i) = D.m := by
  fin_cases i
  · simpa [weight, rows, Fin.sum_univ_succ, add_assoc] using D.row0
  · simpa [weight, rows, Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using D.row1
  · simpa [weight, rows, Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using D.row2

theorem initial_in_box (D : BoxInput) : InBox D.upper D.x := by
  intro i
  have := D.y_pos i
  exact ⟨D.x_pos i,by dsimp [upper]; omega⟩

/-- A maximal finite path exists; proving it is not a sink remains a separate obligation. -/
theorem maximal_path (D : BoxInput) :
    ∃ t u, BoxPath D.upper D.rows t D.x u ∧ ∀ i, ¬ InBox D.upper (fire D.rows i u) := by
  exact maximal_box_path D.upper D.x D.n D.rows D.m D.m_pos
    (fun i => (lt_trans D.m_pos (D.n_gt i)).le) D.initial_in_box D.rows_weight

end BoxInput
end P21.Nonsymmetric.ColorCap


namespace P21.Nonsymmetric.ColorCap.BoxInput

/-- Negating the three genuine positivity conditions gives exactly the source sink cover. -/
theorem sink_cover (D : BoxInput) (u : Point) (hu : ∀ j, 1 ≤ u j)
    (hsink : ¬ ∃ i, ∀ j, 1 ≤ fire D.rows i u j) :
    (u 0 ≤ D.y 0 ∧ u 1 ≤ D.y 1 + D.b 1) ∨
    (u 0 ≤ D.y 0 + D.b 0 ∧ u 2 ≤ D.y 2) ∨
    (u 1 ≤ D.y 1 ∧ u 2 ≤ D.y 2 + D.b 2) ∨
    (u 0 ≤ D.y 0 + D.b 0 ∧ u 1 ≤ D.y 1 + D.b 1 ∧ u 2 ≤ D.y 2 + D.b 2) := by
  have h0 : u 1 ≤ D.y 1 + D.b 1 ∨ u 2 ≤ D.y 2 := by
    by_contra hn
    push Not at hn
    apply hsink
    refine ⟨0,?_⟩
    intro j
    fin_cases j <;> simp [fire, rows]
    · have := hu 0; have := D.x_pos 0; omega
    · omega
    · omega
  have h1 : u 0 ≤ D.y 0 ∨ u 2 ≤ D.y 2 + D.b 2 := by
    by_contra hn
    push Not at hn
    apply hsink
    refine ⟨1,?_⟩
    intro j
    fin_cases j <;> simp [fire, rows]
    · omega
    · have := hu 1; have := D.x_pos 1; omega
    · omega
  have h2 : u 0 ≤ D.y 0 + D.b 0 ∨ u 1 ≤ D.y 1 := by
    by_contra hn
    push Not at hn
    apply hsink
    refine ⟨2,?_⟩
    intro j
    fin_cases j <;> simp [fire, rows]
    · omega
    · omega
    · have := hu 2; have := D.x_pos 2; omega
  have := D.b_pos 0
  have := D.b_pos 1
  have := D.b_pos 2
  omega

/-- The initial point cannot be any of the four positivity sinks. -/
theorem initial_positive_firing (D : BoxInput) : ∃ i, ∀ j, 1 ≤ fire D.rows i D.x j := by
  by_contra hsink
  have hy0 := D.y_pos 0
  have hy1 := D.y_pos 1
  have hy2 := D.y_pos 2
  have hb0 := D.b_pos 0
  have hb1 := D.b_pos 1
  have hb2 := D.b_pos 2
  rcases D.sink_cover D.x D.x_pos hsink with h | h | h | h
  · apply weighted_certificate_impossible D.m 2 D.n
      ![D.y 0-D.x 0,D.y 1+D.b 1-D.x 1,2*D.y 2+D.b 2]
      D.m_pos (by norm_num) D.n_gt
    · intro i; fin_cases i <;> simp <;> omega
    · simp [Fin.sum_univ_succ]; omega
    · simp [weight, Fin.sum_univ_succ]
      linear_combination -D.row0 - D.row1
  · apply weighted_certificate_impossible D.m 2 D.n
      ![D.y 0+D.b 0-D.x 0,2*D.y 1+D.b 1,D.y 2-D.x 2]
      D.m_pos (by norm_num) D.n_gt
    · intro i; fin_cases i <;> simp <;> omega
    · simp [Fin.sum_univ_succ]; omega
    · simp [weight, Fin.sum_univ_succ]
      linear_combination -D.row0 - D.row2
  · apply weighted_certificate_impossible D.m 2 D.n
      ![2*D.y 0+D.b 0,D.y 1-D.x 1,D.y 2+D.b 2-D.x 2]
      D.m_pos (by norm_num) D.n_gt
    · intro i; fin_cases i <;> simp <;> omega
    · simp [Fin.sum_univ_succ]; omega
    · simp [weight, Fin.sum_univ_succ]
      linear_combination -D.row1 - D.row2
  · apply weighted_certificate_impossible D.m 3 D.n
      ![2*D.y 0+D.b 0-D.x 0,2*D.y 1+D.b 1-D.x 1,2*D.y 2+D.b 2-D.x 2]
      D.m_pos (by norm_num) D.n_gt
    · intro i; fin_cases i <;> simp <;> omega
    · simp [Fin.sum_univ_succ]; omega
    · simp [weight, Fin.sum_univ_succ]
      linear_combination -D.row0 - D.row1 - D.row2

end P21.Nonsymmetric.ColorCap.BoxInput

