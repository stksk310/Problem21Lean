import P21.Nonsymmetric.ColorCap.DPE.TwoColor12

namespace P21.Nonsymmetric.ColorCap

def X13 (D : BoxInput) (N R : ℤ) : ℤ := R * (D.y 0 + D.b 0) - N * D.x 0
def Y13 (D : BoxInput) (N R : ℤ) : ℤ := N * D.y 2 - R * D.x 2

theorem terminal13_not_sinkB (D : BoxInput) (N R : ℤ) (hN : 0 < N)
    (hB : 0 ≤ X13 D N R ∧ 0 ≤ Y13 D N R) : False := by
  exact D.two_color13_not_sinkB N R hN (by simpa [X13, Y13] using hB)

/-- B.18 sink D certificate `(N,1,R)`. -/
theorem terminal13_sinkD_impossible (D : BoxInput) (N R : ℤ)
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hNy : N ≤ D.y 0) (hRy : R ≤ D.y 2)
    (u : Point)
    (hu0 : u 0 = D.y 0 + D.b 0 - X13 D N R)
    (hu1 : u 1 = D.x 1 - (N - 1) * (D.y 1 + D.b 1) - (R - 1) * D.y 1)
    (hu2 : u 2 = D.y 2 - Y13 D N R)
    (hD : u 0 ≤ D.y 0 + D.b 0 ∧ u 1 ≤ D.y 1 + D.b 1 ∧
      u 2 ≤ D.y 2 + D.b 2) : False := by
  let w : Point := ![D.y 0 + X13 D N R,
    2 * D.y 1 + D.b 1 - u 1,
    D.y 2 + D.b 2 + Y13 D N R]
  apply weighted_certificate_impossible D.m (N + R + 1) D.n w
    D.m_pos (by omega) D.n_gt
  · intro i
    fin_cases i
    · simp [w]
      have hX : 0 ≤ X13 D N R := by omega
      have := D.y_pos 0
      omega
    · simp [w]
      have := D.y_pos 1
      omega
    · simp [w]
      have hY : -D.b 2 ≤ Y13 D N R := by omega
      have := D.y_pos 2
      omega
  · simp [w, Fin.sum_univ_succ]
    have hy0 := D.y_pos 0
    have hy1 := D.y_pos 1
    have hy2 := D.y_pos 2
    have hb1 := D.b_pos 1
    have hb2 := D.b_pos 2
    omega
  · simp [w, weight, X13, Y13, Fin.sum_univ_succ]
    rw [hu1]
    linear_combination -N * D.row0 - D.row1 - R * D.row2

/-- B.18.1, independently proved for the `{1,3}` orientation. -/
theorem terminal13_last_row2_of_prefix (D : BoxInput) (q : ℕ)
    (P : SuccessfulPrefix (D.x 0) (D.y 0 + D.b 0) (D.y 2)
      (D.x 2) (D.b 0) 0 q)
    (hq : 1 ≤ q) (hstart : D.x 0 < D.y 0 + D.b 0)
    (N : ℤ) (hN : N = P.N q) (u : Point)
    (hu0 : u 0 = P.E q) (hu2 : u 2 = D.x 2 + P.U q)
    (hu1 : u 1 = D.x 1 - (N - 1) * (D.y 1 + D.b 1) -
      (q : ℤ) * D.y 1)
    (hA : u 0 ≤ D.y 0 ∧ u 1 ≤ D.y 1 + D.b 1) : False := by
  have hres := P.residues q hq le_rfl
  have hqx := P.E_slot_count (by
    have hx := D.x_pos 0
    have hb := D.b_pos 0
    have he := hres.2.1
    omega)
  have hqy := P.U_slot_count (by have := D.y_pos 2; omega)
  subst N
  have hNq : P.N q - (q : ℤ) ≤ D.y 0 + D.b 0 - D.x 0 := by
    have hE := hres.1
    have hEx := hres.2.1
    have hx := D.x_pos 0
    have hb := D.b_pos 0
    have hprod : (q : ℤ) * (D.y 0 + D.b 0 - D.x 0) <
        D.x 0 * (D.y 0 + D.b 0 - D.x 0) := by nlinarith
    nlinarith
  have hLR := P.last_rank hq
  let w : Point := ![D.y 0 -
      (P.N q * D.x 0 - (q : ℤ) * (D.y 0 + D.b 0)),
    D.y 1 + D.b 1 - u 1,
    2 * D.y 2 + D.b 2 -
      ((q : ℤ) * D.x 2 - (P.N q - 1) * D.y 2)]
  have hEdef : P.E q = P.N q * D.x 0 -
      (q : ℤ) * (D.y 0 + D.b 0) := rfl
  have hUdef : P.U q = (q : ℤ) * D.x 2 - (P.N q - 1) * D.y 2 := rfl
  apply weighted_certificate_impossible D.m (P.N q + (q : ℤ) + 1) D.n w
    D.m_pos (by
      have hE := hres.1
      have := D.x_pos 0
      have := D.y_pos 0
      nlinarith) D.n_gt
  · intro i
    fin_cases i
    · simp [w]
      have huE : u 0 = P.N q * D.x 0 -
          (q : ℤ) * (D.y 0 + D.b 0) := hu0.trans hEdef
      omega
    · simp [w]
      omega
    · simp [w]
      have hU := hres.2.2.2
      have := D.y_pos 2
      have := D.b_pos 2
      omega
  · simp [w, Fin.sum_univ_succ]
    rw [hEdef, hUdef] at hLR
    have hb2 := D.b_pos 2
    omega
  · simp [w, weight, Fin.sum_univ_succ]
    rw [hu1]
    linear_combination -(P.N q) * D.row0 - D.row1 - (q : ℤ) * D.row2

/-- B.18.2 reciprocal-rank certificate for sink A. -/
theorem terminal13_sinkA_certificate (D : BoxInput) (N R : ℤ)
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hRy : R ≤ D.y 2)
    (u : Point)
    (hu1 : u 1 = D.x 1 - (N - 1) * (D.y 1 + D.b 1) - (R - 1) * D.y 1)
    (hA : u 0 ≤ D.y 0 ∧ u 1 ≤ D.y 1 + D.b 1)
    (hX : D.b 0 ≤ X13 D N R)
    (hcoef2 : 0 ≤ D.x 2 + D.y 2 + D.b 2 + Y13 D N R)
    (hrank : (N - R) + (-Y13 D N R) +
      ((D.y 0 + D.b 0 - D.x 0) - X13 D N R) ≤
      (D.x 2 - D.y 2) + (D.y 0 + D.b 0 - D.x 0) - D.b 0) : False := by
  let w : Point := ![X13 D N R - D.b 0,
    D.y 1 + D.b 1 - u 1,
    D.x 2 + D.y 2 + D.b 2 + Y13 D N R]
  apply weighted_certificate_impossible D.m (N + R) D.n w D.m_pos (by omega) D.n_gt
  · intro i
    fin_cases i
    · simp [w]; omega
    · simp [w]; omega
    · simpa [w]
  · simp [w, Fin.sum_univ_succ]
    have hb2 := D.b_pos 2
    omega
  · simp [w, weight, X13, Y13, Fin.sum_univ_succ]
    rw [hu1]
    linear_combination -N * D.row0 - D.row1 - (R - 1) * D.row2

/-- B.18.3 ELR certificate for sink C. -/
theorem terminal13_sinkC_certificate (D : BoxInput) (N R : ℤ)
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hNy : N ≤ D.y 0)
    (u : Point)
    (hu1 : u 1 = D.x 1 - (N - 1) * (D.y 1 + D.b 1) - (R - 1) * D.y 1)
    (hC : u 1 ≤ D.y 1 ∧ u 2 ≤ D.y 2 + D.b 2)
    (hcoef0 : 0 ≤ D.x 0 + D.y 0 + X13 D N R)
    (hY : -D.b 2 ≤ Y13 D N R)
    (hELR : 0 ≤ D.x 0 + X13 D N R + D.b 2 + Y13 D N R - R) : False := by
  let w : Point := ![D.x 0 + D.y 0 + X13 D N R,
    D.y 1 - u 1,
    D.b 2 + Y13 D N R]
  apply weighted_certificate_impossible D.m (N + R) D.n w D.m_pos (by omega) D.n_gt
  · intro i
    fin_cases i
    · simpa [w]
    · simp [w]; omega
    · simp [w]; omega
  · simp [w, Fin.sum_univ_succ]
    omega
  · simp [w, weight, X13, Y13, Fin.sum_univ_succ]
    rw [hu1]
    linear_combination -(N - 1) * D.row0 - D.row1 - R * D.row2

end P21.Nonsymmetric.ColorCap
