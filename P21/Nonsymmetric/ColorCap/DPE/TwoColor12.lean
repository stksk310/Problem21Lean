import P21.Nonsymmetric.ColorCap.DPE.TerminalCoordinates

namespace P21.Nonsymmetric.ColorCap

def X12 (D : BoxInput) (N Q : ℤ) : ℤ := Q * D.y 0 - N * D.x 0
def Y12 (D : BoxInput) (N Q : ℤ) : ℤ :=
  N * (D.y 1 + D.b 1) - Q * D.x 1 - D.b 1

theorem terminal12_not_sinkA (D : BoxInput) (N Q : ℤ) (hN : 0 < N)
    (hA : 0 ≤ X12 D N Q ∧ -D.b 1 ≤ Y12 D N Q) : False := by
  exact D.two_color12_not_sinkA N Q hN (by simpa [X12, Y12] using hA)

/-- B.17 sink D certificate `lambda=(N,Q,1)`. -/
theorem terminal12_sinkD_impossible (D : BoxInput) (N Q : ℤ)
    (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hNy : N ≤ D.y 0) (hQy : Q ≤ D.y 1)
    (u : Point) (hu : u = ![D.y 0 - X12 D N Q,
      D.y 1 - Y12 D N Q,
      u 2])
    (hu2 : u 2 = D.x 2 - (N - 1) * D.y 2 - (Q - 1) * (D.y 2 + D.b 2))
    (hD : u 0 ≤ D.y 0 + D.b 0 ∧ u 1 ≤ D.y 1 + D.b 1 ∧
      u 2 ≤ D.y 2 + D.b 2) : False := by
  let w : Point := ![D.y 0 + D.b 0 + X12 D N Q,
    D.y 1 + D.b 1 + Y12 D N Q,
    2 * D.y 2 + D.b 2 - u 2]
  rw [hu] at hD
  simp [X12, Y12] at hD
  have hw0 : N ≤ w 0 := by
    simp [w, X12]
    omega
  have hw1 : Q ≤ w 1 := by
    simp [w, Y12]
    omega
  have hw2 : 1 ≤ w 2 := by
    simp [w]
    have := D.y_pos 2
    omega
  apply weighted_certificate_impossible D.m (N + Q + 1) D.n w D.m_pos (by omega) D.n_gt
  · intro i
    fin_cases i
    · exact le_trans (by omega : 0 ≤ N) hw0
    · exact le_trans (by omega : 0 ≤ Q) hw1
    · exact le_trans (by omega : (0 : ℤ) ≤ 1) hw2
  · simp [Fin.sum_univ_succ]
    omega
  · simp [w, weight, X12, Y12, Fin.sum_univ_succ]
    rw [hu2]
    linear_combination -N * D.row0 - Q * D.row1 - D.row2

end P21.Nonsymmetric.ColorCap
