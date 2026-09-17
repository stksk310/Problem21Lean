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

/-- B.17.1.  The terminal state immediately after the last row-2 firing
(`Fin 3` label `1`) is excluded by LR and the certificate `(N,q,1)`. -/
theorem terminal12_last_row1_impossible (D : BoxInput) (q : ℕ)
    (P : SuccessfulPrefix (D.x 0) (D.y 0) (D.y 1 + D.b 1)
      (D.x 1) 0 (D.b 1) q)
    (hq : 1 ≤ q) (hqX : (q : ℤ) < D.x 0) (hqY : (q : ℤ) < D.y 1)
    (hstart : D.x 0 < D.y 0) (N : ℤ) (hN : N = P.N q)
    (u : Point)
    (hu0 : u 0 = P.E q) (_hu1 : u 1 = D.x 1 + P.U q)
    (hu2 : u 2 = D.x 2 - (N - 1) * D.y 2 -
      (q : ℤ) * (D.y 2 + D.b 2))
    (hB : u 0 ≤ D.y 0 + D.b 0 ∧ u 2 ≤ D.y 2) : False := by
  have hres := P.residues q hq le_rfl
  subst N
  have hNq : P.N q - (q : ℤ) ≤ D.y 0 - D.x 0 := by
    have hE := hres.1
    have hEx := hres.2.1
    have hx := D.x_pos 0
    have hA := D.y_pos 0
    have hprod : (q : ℤ) * (D.y 0 - D.x 0) <
        D.x 0 * (D.y 0 - D.x 0) := by nlinarith
    nlinarith
  have hLR := P.last_rank hq
  let w : Point := ![D.y 0 + D.b 0 -
      (P.N q * D.x 0 - (q : ℤ) * D.y 0),
    2 * D.y 1 + D.b 1 -
      ((q : ℤ) * D.x 1 - (P.N q - 1) * (D.y 1 + D.b 1)),
    D.y 2 - u 2]
  have hEdef : P.E q = P.N q * D.x 0 - (q : ℤ) * D.y 0 := rfl
  have hUdef : P.U q = (q : ℤ) * D.x 1 -
      (P.N q - 1) * (D.y 1 + D.b 1) := rfl
  have hw0 : 0 ≤ w 0 := by
    have huE : u 0 = P.N q * D.x 0 - (q : ℤ) * D.y 0 := hu0.trans hEdef
    simp [w]
    omega
  have hw1 : 0 ≤ w 1 := by
    simp [w]
    have hU := hres.2.2.2
    have := D.y_pos 1
    have := D.b_pos 1
    omega
  have hw2 : 0 ≤ w 2 := by simp [w]; omega
  apply weighted_certificate_impossible D.m (P.N q + (q : ℤ) + 1) D.n w
    D.m_pos (by
      have hE := hres.1
      have := D.x_pos 0
      have := D.y_pos 0
      nlinarith) D.n_gt
  · intro i
    fin_cases i
    · exact hw0
    · exact hw1
    · exact hw2
  · simp [w, Fin.sum_univ_succ]
    rw [hu2]
    rw [hEdef, hUdef] at hLR
    have hb0 := D.b_pos 0
    have hb1 := D.b_pos 1
    have hy2 := D.y_pos 2
    omega
  · simp [w, weight, Fin.sum_univ_succ]
    rw [hu2]
    linear_combination -(P.N q) * D.row0 - (q : ℤ) * D.row1 - D.row2

/-- B.17.1 with both slot bounds discharged from the successful prefix. -/
theorem terminal12_last_row1_of_prefix (D : BoxInput) (q : ℕ)
    (P : SuccessfulPrefix (D.x 0) (D.y 0) (D.y 1 + D.b 1)
      (D.x 1) 0 (D.b 1) q)
    (hq : 1 ≤ q) (hstart : D.x 0 < D.y 0) (N : ℤ) (hN : N = P.N q)
    (u : Point)
    (hu0 : u 0 = P.E q) (hu1 : u 1 = D.x 1 + P.U q)
    (hu2 : u 2 = D.x 2 - (N - 1) * D.y 2 -
      (q : ℤ) * (D.y 2 + D.b 2))
    (hB : u 0 ≤ D.y 0 + D.b 0 ∧ u 2 ≤ D.y 2) : False := by
  have hqx := P.E_slot_count (by have := D.x_pos 0; omega)
  have hqy := P.U_slot_count (by have := D.y_pos 1; omega)
  exact terminal12_last_row1_impossible D q P hq (by omega) (by omega)
    hstart N hN u hu0 hu1 hu2 hB

/-- B.17.2 arithmetic certificate after reciprocal rank.  The closed
hypothesis `0 ≤ X` deliberately includes the boundary `X = 0`. -/
theorem terminal12_sinkB_nonnegativeX_impossible (D : BoxInput) (N Q : ℤ)
    (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hQy : Q ≤ D.y 1)
    (u : Point)
    (hu2 : u 2 = D.x 2 - (N - 1) * D.y 2 -
      (Q - 1) * (D.y 2 + D.b 2))
    (hB : u 0 ≤ D.y 0 + D.b 0 ∧ u 2 ≤ D.y 2)
    (hX : 0 ≤ X12 D N Q)
    (hYbox : 1 ≤ D.x 1 + Y12 D N Q)
    (hrank : (N - Q) + (-(Y12 D N Q + D.b 1)) +
      ((D.y 0 - D.x 0) - X12 D N Q) ≤
      (D.x 1 - (D.y 1 + D.b 1)) + (D.y 0 - D.x 0)) : False := by
  let w : Point := ![D.b 0 + X12 D N Q,
    D.x 1 + D.y 1 + D.b 1 + Y12 D N Q,
    D.y 2 - u 2]
  have hw0 : 0 ≤ w 0 := by
    simp [w]
    have := D.b_pos 0
    omega
  have hw1 : 0 ≤ w 1 := by
    simp [w]
    have := D.y_pos 1
    have := D.b_pos 1
    omega
  have hw2 : 0 ≤ w 2 := by simp [w]; omega
  apply weighted_certificate_impossible D.m (N + Q) D.n w D.m_pos (by omega) D.n_gt
  · intro i
    fin_cases i
    · exact hw0
    · exact hw1
    · exact hw2
  · simp [w, Fin.sum_univ_succ]
    have hb0 := D.b_pos 0
    have hb1 := D.b_pos 1
    have hy2 := D.y_pos 2
    omega
  · simp [w, weight, X12, Y12, Fin.sum_univ_succ]
    rw [hu2]
    linear_combination -N * D.row0 - (Q - 1) * D.row1 - D.row2

/-- B.17.3 weighted certificate once the predecessor/PREFIX argument has
proved `0 ≤ x₂-N+D`, where `D = Y+b₂`. -/
theorem terminal12_sinkB_negativeX_certificate (D : BoxInput) (N Q : ℤ)
    (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hQy : Q ≤ D.y 1)
    (u : Point)
    (hu2 : u 2 = D.x 2 - (N - 1) * D.y 2 -
      (Q - 1) * (D.y 2 + D.b 2))
    (hB : u 0 ≤ D.y 0 + D.b 0 ∧ u 2 ≤ D.y 2)
    (hcoef0 : 0 ≤ D.b 0 + X12 D N Q)
    (hsecond : 0 ≤ D.x 1 - N + (Y12 D N Q + D.b 1)) : False := by
  let w : Point := ![D.b 0 + X12 D N Q,
    D.x 1 + D.y 1 + (Y12 D N Q + D.b 1),
    D.y 2 - u 2]
  apply weighted_certificate_impossible D.m (N + Q) D.n w D.m_pos (by omega) D.n_gt
  · intro i
    fin_cases i
    · simpa [w]
    · simp [w]
      have := D.y_pos 1
      omega
    · simp [w]
      omega
  · simp [w, Fin.sum_univ_succ]
    omega
  · simp [w, weight, X12, Y12, Fin.sum_univ_succ]
    rw [hu2]
    linear_combination -N * D.row0 - (Q - 1) * D.row1 - D.row2

/-- B.17.4 ELR certificate for a row-1 terminal state in sink C. -/
theorem terminal12_sinkC_certificate (D : BoxInput) (N Q : ℤ)
    (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hNy : N ≤ D.y 0)
    (u : Point)
    (hu1 : u 1 = D.y 1 - Y12 D N Q)
    (hu2 : u 2 = D.x 2 - (N - 1) * D.y 2 -
      (Q - 1) * (D.y 2 + D.b 2))
    (hC : u 1 ≤ D.y 1 ∧ u 2 ≤ D.y 2 + D.b 2)
    (hcoef0 : 0 ≤ D.x 0 + D.y 0 + D.b 0 + X12 D N Q)
    (hELR : Q ≤ D.x 0 + X12 D N Q + Y12 D N Q) : False := by
  let w : Point := ![D.x 0 + D.y 0 + D.b 0 + X12 D N Q,
    Y12 D N Q,
    D.y 2 + D.b 2 - u 2]
  have hY : 0 ≤ Y12 D N Q := by
    omega
  apply weighted_certificate_impossible D.m (N + Q) D.n w D.m_pos (by omega) D.n_gt
  · intro i
    fin_cases i
    · simpa [w]
    · simpa [w]
    · simp [w]
      omega
  · simp [w, Fin.sum_univ_succ]
    have hb0 := D.b_pos 0
    omega
  · simp [w, weight, X12, Y12, Fin.sum_univ_succ]
    rw [hu2]
    linear_combination -(N - 1) * D.row0 - Q * D.row1 - D.row2

end P21.Nonsymmetric.ColorCap
