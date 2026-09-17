import P21.Nonsymmetric.ColorCap.DPE.TerminalCoordinates

namespace P21.Nonsymmetric.ColorCap

def X12 (D : BoxInput) (N Q : ℤ) : ℤ := Q * D.y 0 - N * D.x 0
def Y12 (D : BoxInput) (N Q : ℤ) : ℤ :=
  N * (D.y 1 + D.b 1) - Q * D.x 1 - D.b 1

theorem terminal12_count_bounds (D : BoxInput)
    {l : List (Fin 3)} {u : Point}
    (ht : FiringTrace D.upper D.rows D.x l u)
    (hp : ProperNonzeroPredecessors l) (hno2 : l.count 2 = 0)
    (hstart : D.x 0 < D.y 0) :
    ((l.count 0 + 1 : ℕ) : ℤ) ≤ D.y 0 ∧
      ((l.count 1 + 1 : ℕ) : ℤ) ≤ D.x 0 ∧
      ((l.count 1 + 1 : ℕ) : ℤ) ≤ D.y 1 := by
  let q := l.count 1
  let P := trace_successfulPrefix12 D ht hp hno2 (q := q) le_rfl
  have hqx := P.E_slot_count (by have := D.x_pos 0; omega)
  have hqy := P.U_slot_count (by have := D.y_pos 1; omega)
  have hu0 := ht.endpoint_eq_sub_sum 0
  have hu0box := ht.endpoint_inBox 0
  simp [BoxInput.rows, Fin.sum_univ_succ, hno2] at hu0
  dsimp [BoxInput.upper] at hu0box
  have hNy : ((l.count 0 + 1 : ℕ) : ℤ) ≤ D.y 0 := by
    by_contra hn
    push Not at hn
    push_cast at hn
    have hqX : (l.count 1 : ℤ) ≤ D.x 0 - 1 := by simpa [q, P] using hqx
    have huUpper := hu0box.2
    push_cast at hu0
    nlinarith
  refine ⟨hNy, ?_, ?_⟩
  · simpa [q, P] using (show (q : ℤ) + 1 ≤ D.x 0 by omega)
  · simpa [q, P] using (show (q : ℤ) + 1 ≤ D.y 1 by omega)

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

/-- B.17.4: PREFIX gives the chronological ELR cover against the current
pre-crossing terminal residue. -/
theorem terminal12_sinkC_ELR_bound (D : BoxInput) (q Q : ℕ) (N E U : ℤ)
    (P : SuccessfulPrefix (D.x 0) (D.y 0) (D.y 1 + D.b 1)
      (D.x 1) 0 (D.b 1) q)
    (hQ : Q = q + 1)
    (hE : E = N * D.x 0 - (Q : ℤ) * D.y 0)
    (hU : U = (Q : ℤ) * D.x 1 - (N - 1) * (D.y 1 + D.b 1))
    (hE0 : 1 ≤ E) (hEx : E ≤ D.x 0 - 1)
    (hU0 : 1 ≤ U) (hUy : U ≤ D.y 1 - 1) :
    (Q : ℤ) ≤ D.x 0 - E + (D.y 1 - U) := by
  have hcover : ∀ i : ℕ, 1 ≤ i → i ≤ q → E < P.E i ∨ U < P.U i := by
    intro i hi hiq
    by_contra hn
    push Not at hn
    have hiQ : i < Q := by omega
    have hsub : ((Q - i : ℕ) : ℤ) = (Q : ℤ) - (i : ℤ) := by
      rw [Nat.cast_sub (by omega)]
    apply P.separator (Q - i) (by omega) (by omega)
    refine ⟨N - P.N i, ?_, ?_⟩
    · have hEdef : P.E i = P.N i * D.x 0 - (i : ℤ) * D.y 0 := rfl
      rw [hEdef] at hn
      rw [hsub]
      nlinarith [hE]
    · have hUdef : P.U i = (i : ℤ) * D.x 1 -
          (P.N i - 1) * (D.y 1 + D.b 1) := rfl
      rw [hUdef] at hn
      rw [hsub]
      nlinarith [hU]
  have hrank := P.terminal_rank hE0 (by simpa using hEx) hU0 (by simpa using hUy) hcover
  omega

/-- B.17.3, `D<0`: every prior `U` residue lies above `W=-D`; PREFIX
then yields the predecessor estimate used by the weighted certificate. -/
theorem terminal12_negativeD_predecessor_bound (D : BoxInput)
    (q Q : ℕ) (N E W : ℤ)
    (P : SuccessfulPrefix (D.x 0) (D.y 0) (D.y 1 + D.b 1)
      (D.x 1) 0 (D.b 1) q)
    (hq : 1 ≤ q) (hQ : Q = q + 1) (hstart : D.x 0 < D.y 0)
    (hE : E = N * D.x 0 - (Q : ℤ) * D.y 0)
    (hW : W = (Q : ℤ) * D.x 1 - N * (D.y 1 + D.b 1))
    (hE0 : 1 ≤ E) (hEx : E ≤ D.x 0 - 1) (hW0 : 1 ≤ W) :
    0 ≤ D.x 1 - N - W := by
  have hprior : ∀ i : ℕ, 1 ≤ i → i ≤ q → W < P.U i := by
    intro i hi hiq
    by_contra hn
    push Not at hn
    have hiQ : i < Q := by omega
    have hsub : ((Q - i : ℕ) : ℤ) = (Q : ℤ) - (i : ℤ) := by
      rw [Nat.cast_sub (by omega)]
    apply P.separator (Q - i) (by omega) (by omega)
    refine ⟨N - P.N i + 1, ?_, ?_⟩
    · have hEi := (P.residues i hi hiq).2.1
      rw [hsub]
      nlinarith [hE]
    · have hUdef : P.U i = (i : ℤ) * D.x 1 -
          (P.N i - 1) * (D.y 1 + D.b 1) := rfl
      rw [hsub]
      rw [hUdef] at hn
      nlinarith [hW]
  have hWupper : W ≤ D.y 1 - 1 := by
    have hp1 := hprior 1 (by omega) hq
    have hu1 := (P.residues 1 (by omega) hq).2.2.2
    have hUdef : P.U 1 = D.x 1 - (P.N 1 - 1) * (D.y 1 + D.b 1) := by
      simp [SuccessfulPrefix.U]
    rw [hUdef] at hp1
    omega
  have hcover : ∀ i : ℕ, 1 ≤ i → i ≤ q →
      D.x 0 - 1 < P.E i ∨ W < P.U i := by
    intro i hi hiq
    exact Or.inr (hprior i hi hiq)
  have hx2 : 2 ≤ D.x 0 := by omega
  have hrank := P.terminal_rank (E := D.x 0 - 1) (U := W)
    (by omega) (by omega) hW0 (by simpa using hWupper) hcover
  have hQW : (Q : ℤ) + W ≤ D.y 1 := by omega
  have hNQ : N - (Q : ℤ) ≤ D.x 1 - (D.y 1 + D.b 1) := by
    have hx := D.x_pos 0
    have hB := P.B_pos
    have hQltB : (Q : ℤ) < D.y 1 + D.b 1 := by
      have hb := D.b_pos 1
      omega
    have hscaled : (Q : ℤ) * (D.y 0 - D.x 0) <
        (D.y 1 + D.b 1) * (D.y 0 - D.x 0) := by nlinarith
    have hcorr : (D.y 1 + D.b 1) * (D.y 0 - D.x 0) <
        D.x 0 * (D.x 1 - (D.y 1 + D.b 1)) := by
      nlinarith [P.corridor]
    nlinarith [hE]
  have hb := D.b_pos 1
  omega

/-- B.17.3, `D≥0`: the corridor and the current `E` residue give
`N≤x₂`, so `x₂-N+D` is nonnegative. -/
theorem terminal12_nonnegativeD_count_bound (D : BoxInput)
    {q : ℕ} (Q : ℕ) (N E : ℤ)
    (P : SuccessfulPrefix (D.x 0) (D.y 0) (D.y 1 + D.b 1)
      (D.x 1) 0 (D.b 1) q)
    (hQ : 1 ≤ Q) (hQy : (Q : ℤ) ≤ D.y 1)
    (hE : E = N * D.x 0 - (Q : ℤ) * D.y 0)
    (hEx : E ≤ D.x 0 - 1) : N ≤ D.x 1 := by
  have hx := D.x_pos 0
  have hB := P.B_pos
  have hQB : (Q : ℤ) < D.y 1 + D.b 1 := by
    have hb := D.b_pos 1
    omega
  have hleft : (N - 1) * D.x 0 < (Q : ℤ) * D.y 0 := by
    nlinarith [hE]
  have hleftB : (N - 1) * D.x 0 * (D.y 1 + D.b 1) <
      (Q : ℤ) * D.y 0 * (D.y 1 + D.b 1) := by
    nlinarith
  have hcorrQ : (Q : ℤ) * D.y 0 * (D.y 1 + D.b 1) <
      (Q : ℤ) * D.x 0 * D.x 1 := by
    have hQz : 0 < (Q : ℤ) := by exact_mod_cast hQ
    nlinarith [P.corridor]
  have hQv : (Q : ℤ) * D.x 1 < (D.y 1 + D.b 1) * D.x 1 := by
    have hv := D.x_pos 1
    nlinarith
  have hQvX : (Q : ℤ) * D.x 0 * D.x 1 <
      D.x 0 * (D.y 1 + D.b 1) * D.x 1 := by nlinarith
  have hchain : (N - 1) * D.x 0 * (D.y 1 + D.b 1) <
      D.x 0 * (D.y 1 + D.b 1) * D.x 1 :=
    lt_trans hleftB (lt_trans hcorrQ hQvX)
  have hpos := mul_pos hx hB
  nlinarith

/-- B.17.2 reciprocal rank, including the closed boundary `X=0`. -/
theorem terminal12_reciprocal_rank (D : BoxInput)
    (q Q H N : ℕ)
    (P : SuccessfulPrefix (D.x 0) (D.y 0) (D.y 1 + D.b 1)
      (D.x 1) 0 (D.b 1) q)
    (hQ : Q = q + 1) (hN : N = H + Q) (hH : 1 ≤ H)
    (hstart : D.x 0 < D.y 0)
    (hX : 0 ≤ X12 D N Q)
    (hE0 : 1 ≤ -(Y12 D N Q + D.b 1))
    (hEa : -(Y12 D N Q + D.b 1) ≤ D.x 1 - (D.y 1 + D.b 1) - 1)
    (hV0 : 1 ≤ (D.y 0 - D.x 0) - X12 D N Q) :
    (H : ℤ) + (-(Y12 D N Q + D.b 1)) +
      ((D.y 0 - D.x 0) - X12 D N Q) ≤
      (D.x 1 - (D.y 1 + D.b 1)) + (D.y 0 - D.x 0) := by
  let a := D.x 1 - (D.y 1 + D.b 1)
  let d := D.y 0 - D.x 0
  have hd : 0 < d := by dsimp [d]; omega
  have ha : 0 < a := by
    dsimp [a]
    have hx := D.x_pos 0
    have hB := P.B_pos
    nlinarith [P.corridor]
  have hNcast : (N : ℤ) = (H : ℤ) + (Q : ℤ) := by exact_mod_cast hN
  have hbracket : (H : ℤ) * D.x 0 ≤ (Q : ℤ) * d := by
    have hXN : (N : ℤ) * D.x 0 ≤ (Q : ℤ) * D.y 0 := by
      simpa [X12] using hX
    dsimp [d]
    calc
      (H : ℤ) * D.x 0 = (N : ℤ) * D.x 0 - (Q : ℤ) * D.x 0 := by
        rw [hNcast]
        ring
      _ ≤ (Q : ℤ) * D.y 0 - (Q : ℤ) * D.x 0 := sub_le_sub_right hXN _
      _ = (Q : ℤ) * (D.y 0 - D.x 0) := by ring
  have hstrict : ∀ s : ℕ, 1 ≤ s → s ≤ H - 1 →
      let K := ((s : ℤ) * (D.y 1 + D.b 1)) / a + 1
      (s : ℤ) * D.x 0 - (K - 1) * d ≤ d - 1 := by
    intro s hs hsH
    dsimp
    let qz : ℤ := ((s : ℤ) * (D.y 1 + D.b 1)) / a
    have hsB : 0 < (s : ℤ) * (D.y 1 + D.b 1) :=
      mul_pos (by exact_mod_cast hs) P.B_pos
    have ha0 : a ≠ 0 := ne_of_gt ha
    have hdecomp := Int.ediv_mul_add_emod ((s : ℤ) * (D.y 1 + D.b 1)) a
    have hrem0 := Int.emod_nonneg ((s : ℤ) * (D.y 1 + D.b 1)) ha0
    have hrema := Int.emod_lt_of_pos ((s : ℤ) * (D.y 1 + D.b 1)) ha
    have hq0 : 0 ≤ qz := Int.ediv_nonneg hsB.le ha.le
    have hKpos : 1 ≤ qz + 1 := by omega
    let k : ℕ := (qz + 1).toNat
    have hkcast : (k : ℤ) = qz + 1 := by
      simp [k, Int.toNat_of_nonneg (by omega : 0 ≤ qz + 1)]
    have hkz : (1 : ℤ) ≤ (k : ℤ) := by rw [hkcast]; exact hKpos
    have hk : 1 ≤ k := by exact_mod_cast hkz
    have hfirst : (s : ℤ) * (D.y 1 + D.b 1) ≤ (k : ℤ) * a := by
      rw [hkcast]
      dsimp [qz]
      nlinarith
    by_contra hn
    push Not at hn
    have hsecond : (k : ℤ) * d ≤ (s : ℤ) * D.x 0 := by
      rw [hkcast]
      dsimp [qz] at hn ⊢
      nlinarith
    exact (P.reciprocal_separator ha hd hQ hbracket s k hs (by omega) hk)
      ⟨hfirst, hsecond⟩
  let DP := P.dual_prefix_of_actuality ha hd hQ hbracket (by
    simpa [a, d] using hstrict)
  have hEnext : -(Y12 D N Q + D.b 1) =
      (Q : ℤ) * a - (H : ℤ) * (D.y 1 + D.b 1) := by
    simp [Y12, a]
    rw [hNcast]
    ring
  have hVnext : (D.y 0 - D.x 0) - X12 D N Q =
      (H : ℤ) * D.x 0 - ((Q : ℤ) - 1) * d := by
    simp [X12, d]
    rw [hNcast]
    ring
  have hVd : (D.y 0 - D.x 0) - X12 D N Q ≤ d := by
    dsimp [d]
    omega
  simpa [a, d] using
    DP.dual_next_residue_rank hH hEnext hVnext hE0 (by simpa [a] using hEa)
      hV0 (by simpa [d] using hVd)

end P21.Nonsymmetric.ColorCap
