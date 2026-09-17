import P21.Nonsymmetric.ColorCap.BoxInput

namespace P21.Nonsymmetric.ColorCap

/-- Appendix B.16: any nonempty one-color in-box run cannot finish at a sink. -/
theorem one_color_sink_impossible (D : BoxInput) (N : ℤ) (hN : 2 ≤ N)
    (hbox : InBox D.upper
      ![N*D.x 0,D.x 1-(N-1)*(D.y 1+D.b 1),D.x 2-(N-1)*D.y 2])
    (hsink : ¬ ∃ i, ∀ j, 1 ≤ fire D.rows i
      ![N*D.x 0,D.x 1-(N-1)*(D.y 1+D.b 1),D.x 2-(N-1)*D.y 2] j) : False := by
  let u : Point := ![N*D.x 0,D.x 1-(N-1)*(D.y 1+D.b 1),D.x 2-(N-1)*D.y 2]
  have hu : ∀ j, 1 ≤ u j := fun j => (hbox j).1
  have h0 := (hbox 0).2
  simp [BoxInput.upper] at h0
  have hx0 := D.x_pos 0
  have hy0 := D.y_pos 0
  have hy1 := D.y_pos 1
  have hy2 := D.y_pos 2
  have hb0 := D.b_pos 0
  have hb1 := D.b_pos 1
  have hb2 := D.b_pos 2
  have hprod : 0 ≤ (N-2)*(D.x 0-1) := by positivity
  have hfirst : N+D.b 0 ≤ 2*D.y 0+D.b 0-N*D.x 0 := by nlinarith
  have hNy : N ≤ N*D.y 2 := by nlinarith
  have hNz : 2*N ≤ N*(D.y 1+D.b 1) := by nlinarith
  have hcommon (h1 : u 1 ≤ D.y 1+D.b 1) (h2 : u 2 ≤ D.y 2+D.b 2) : False := by
    apply weighted_certificate_impossible D.m (N+2) D.n
      ![2*D.y 0+D.b 0-N*D.x 0,
        D.y 1+N*(D.y 1+D.b 1)-D.x 1,
        N*D.y 2+D.y 2+D.b 2-D.x 2] D.m_pos (by omega) D.n_gt
    · intro i; fin_cases i <;> simp <;> dsimp [u] at h1 h2 <;> nlinarith
    · simp [Fin.sum_univ_succ]
      dsimp [u] at h1 h2
      nlinarith
    · simp [weight, Fin.sum_univ_succ]
      linear_combination -N*D.row0 - D.row1 - D.row2
  rcases D.sink_cover u hu hsink with h | h | h | h
  · apply weighted_certificate_impossible D.m (N+1) D.n
      ![D.y 0-N*D.x 0,N*(D.y 1+D.b 1)-D.x 1,N*D.y 2+D.y 2+D.b 2]
      D.m_pos (by omega) D.n_gt
    · intro i; fin_cases i <;> simp <;> dsimp [u] at h <;> nlinarith
    · simp [Fin.sum_univ_succ]
      dsimp [u] at h
      nlinarith
    · simp [weight, Fin.sum_univ_succ]
      linear_combination -N*D.row0-D.row1
  · apply weighted_certificate_impossible D.m (N+1) D.n
      ![D.y 0+D.b 0-N*D.x 0,N*(D.y 1+D.b 1)+D.y 1,N*D.y 2-D.x 2]
      D.m_pos (by omega) D.n_gt
    · intro i; fin_cases i <;> simp <;> dsimp [u] at h <;> nlinarith
    · simp [Fin.sum_univ_succ]
      dsimp [u] at h
      nlinarith
    · simp [weight, Fin.sum_univ_succ]
      linear_combination -N*D.row0-D.row2
  · exact hcommon (by have := h.1; omega) h.2
  · exact hcommon h.2.1 h.2.2

end P21.Nonsymmetric.ColorCap

