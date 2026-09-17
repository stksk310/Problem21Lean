import P21.Nonsymmetric.ColorCap.DPE.TwoColor13

namespace P21.Nonsymmetric.ColorCap

/-- B.19.1 certificate at the actual source of the first row-3 firing. -/
theorem first_third_12_to_3_certificate (D : BoxInput) (N Q E Delta : ℤ)
    (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hNE : N + E ≤ D.y 0)
    (hQD : Q ≤ D.y 1 + Delta)
    (source : Point) (hsource2 : source 2 ≤ D.y 2 - 1)
    (hsource : source 2 = D.x 2 - (N - 1) * D.y 2 -
      (Q - 1) * (D.y 2 + D.b 2))
    (hE : E = N * D.x 0 - Q * D.y 0)
    (hDelta : Delta = N * (D.y 1 + D.b 1) - Q * D.x 1) : False := by
  let w : Point := ![D.y 0 + D.b 0 - E,
    D.y 1 + Delta,
    2 * D.y 2 + D.b 2 - source 2]
  apply weighted_certificate_impossible D.m (N + Q + 1) D.n w
    D.m_pos (by omega) D.n_gt
  · intro i
    fin_cases i
    · simp [w]
      have := D.b_pos 0
      omega
    · simp [w]
      omega
    · simp [w]
      have := D.y_pos 2
      have := D.b_pos 2
      omega
  · simp [w, Fin.sum_univ_succ]
    have hb0 := D.b_pos 0
    have hy2 := D.y_pos 2
    have hb2 := D.b_pos 2
    omega
  · simp [w, weight, hE, hDelta, hsource, Fin.sum_univ_succ]
    linear_combination -N * D.row0 - Q * D.row1 - D.row2

/-- B.19.2 certificate at the actual source of the first row-2 firing. -/
theorem first_third_13_to_2_certificate (D : BoxInput) (N R P W : ℤ)
    (hN : 1 ≤ N) (hR : 1 ≤ R)
    (hNP : N + P ≤ D.y 0)
    (hRW : R + W ≤ D.y 2)
    (source : Point) (hsource1 : source 1 ≤ D.y 1 - 1)
    (hP : P = D.b 0 - X13 D N R)
    (hW : W = -D.b 2 - Y13 D N R)
    (hsource : source 1 = D.x 1 - (N - 1) * (D.y 1 + D.b 1) -
      (R - 1) * D.y 1) : False := by
  let w : Point := ![D.y 0 + D.b 0 - P,
    2 * D.y 1 + D.b 1 - source 1,
    D.y 2 - W]
  apply weighted_certificate_impossible D.m (N + R + 1) D.n w
    D.m_pos (by omega) D.n_gt
  · intro i
    fin_cases i
    · simp [w]
      have := D.b_pos 0
      omega
    · simp [w]
      have := D.y_pos 1
      have := D.b_pos 1
      omega
    · simp [w]
      rw [hW]
      omega
  · simp [w, Fin.sum_univ_succ]
    have hb0 := D.b_pos 0
    have hy1 := D.y_pos 1
    have hb1 := D.b_pos 1
    omega
  · simp [w, weight, hP, hW, hsource, X13, Y13, Fin.sum_univ_succ]
    linear_combination -N * D.row0 - D.row1 - R * D.row2

end P21.Nonsymmetric.ColorCap
