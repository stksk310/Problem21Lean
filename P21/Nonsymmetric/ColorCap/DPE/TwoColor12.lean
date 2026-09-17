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

/-- The full ELR split used in B.17.4, including `U>y₂-1`. -/
theorem terminal12_sinkC_ELR_extended (D : BoxInput) (q Q : ℕ) (N E U Y : ℤ)
    (P : SuccessfulPrefix (D.x 0) (D.y 0) (D.y 1 + D.b 1)
      (D.x 1) 0 (D.b 1) q)
    (hQ : Q = q + 1)
    (hE : E = N * D.x 0 - (Q : ℤ) * D.y 0)
    (hU : U = (Q : ℤ) * D.x 1 - (N - 1) * (D.y 1 + D.b 1))
    (hUY : U = D.y 1 - Y) (hY : 0 ≤ Y)
    (hE0 : 1 ≤ E) (hEx : E ≤ D.x 0 - 1) (hU0 : 1 ≤ U) :
    (Q : ℤ) ≤ D.x 0 - E + Y := by
  by_cases hUr : U ≤ D.y 1 - 1
  · have h := terminal12_sinkC_ELR_bound D q Q N E U P hQ hE hU
      hE0 hEx hU0 hUr
    omega
  · have hcover0 : ∀ i : ℕ, 1 ≤ i → i ≤ q → E < P.E i := by
      intro i hi hiq
      have hcover : E < P.E i ∨ U < P.U i := by
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
      rcases hcover with he | hu
      · exact he
      · have hui := (P.residues i hi hiq).2.2.2
        have hUidef : P.U i = (i : ℤ) * D.x 1 -
            (P.N i - 1) * (D.y 1 + D.b 1) := rfl
        rw [hUidef] at hu
        omega
    by_cases hy1 : D.y 1 = 1
    · have hqy := P.U_slot_count (by have := D.y_pos 1; omega)
      omega
    have hy2 : 2 ≤ D.y 1 := by have := D.y_pos 1; omega
    have hrank := P.terminal_rank hE0 (by simpa using hEx)
      (show 1 ≤ D.y 1 - 1 by omega) (by omega) (by
        intro i hi hiq
        exact Or.inl (hcover0 i hi hiq))
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

/-- Appendix B.17 assembled on the actual chronological two-color trace. -/
theorem two_color12_trace_sink_impossible (D : BoxInput)
    {l : List (Fin 3)} {u : Point}
    (ht : FiringTrace D.upper D.rows D.x l u)
    (hp : ProperNonzeroPredecessors l) (hno2 : l.count 2 = 0)
    (hcount1 : 1 ≤ l.count 1) (hstart : D.x 0 < D.y 0)
    (hsink : ¬ ∃ i, ∀ j, 1 ≤ fire D.rows i u j) : False := by
  let Nn : ℕ := l.count 0 + 1
  let Qn : ℕ := l.count 1 + 1
  let N : ℤ := Nn
  let Q : ℤ := Qn
  have hN : 1 ≤ N := by simp [N, Nn]
  have hQ : 1 ≤ Q := by simp [Q, Qn]
  have hbounds := terminal12_count_bounds D ht hp hno2 hstart
  have hNy : N ≤ D.y 0 := by simpa [N, Nn] using hbounds.1
  have hQx : Q ≤ D.x 0 := by simpa [Q, Qn] using hbounds.2.1
  have hQy : Q ≤ D.y 1 := by simpa [Q, Qn] using hbounds.2.2
  have hut := trace_terminal12 D ht hno2
  have hcoords := terminal12Point_coordinates D Nn Qn
  have hu0 : u 0 = D.y 0 - X12 D N Q := by
    rw [hut]
    simpa [N, Q, Nn, Qn, X12] using hcoords.1
  have hu1 : u 1 = D.y 1 - Y12 D N Q := by
    rw [hut]
    simpa [N, Q, Nn, Qn, Y12] using hcoords.2.1
  have hu2 : u 2 = D.x 2 - (N - 1) * D.y 2 -
      (Q - 1) * (D.y 2 + D.b 2) := by
    rw [hut]
    simpa [N, Q] using hcoords.2.2
  have huPos : ∀ j, 1 ≤ u j := fun j => (ht.endpoint_inBox j).1
  have hBC_impossible :
      ((u 0 ≤ D.y 0 + D.b 0 ∧ u 2 ≤ D.y 2) ∨
       (u 1 ≤ D.y 1 ∧ u 2 ≤ D.y 2 + D.b 2)) → False := by
    intro hBC
    have hne : l ≠ [] := by
      intro he
      subst l
      simp at hcount1
    generalize hlastEq : l.getLast hne = last
    have hlastSome := List.getLast?_eq_getLast hne
    rw [hlastEq] at hlastSome
    rw [List.getLast?_eq_some_iff] at hlastSome
    obtain ⟨a, hlast⟩ := hlastSome
    change l = a ++ [last] at hlast
    let q : ℕ := l.count 1
    let P := trace_successfulPrefix12 D ht hp hno2 (q := q) (by simp [q])
    have hq : 1 ≤ q := by simpa [q] using hcount1
    have hactual := trace_successfulPrefix12_actual D ht hp hno2
      (q := q) (by simp [q])
    fin_cases last
    · obtain ⟨v, hv⟩ := ht.prefix_trace (show a <+: l by
          refine ⟨[0], ?_⟩
          simpa using hlast.symm)
      have hfire : u = fire D.rows 0 v := by
        rw [← ht.execute_eq, ← hv.execute_eq, hlast]
        simp [execute_append]
      have hf0 := congrFun hfire 0
      have hf1 := congrFun hfire 1
      simp [fire, BoxInput.rows] at hf0 hf1
      have hv0 := hv.endpoint_inBox 0
      have hv1 := hv.endpoint_inBox 1
      dsimp [BoxInput.upper] at hv0 hv1
      rcases hBC with hB | hC
      ·
        have hcoef0 : 0 ≤ D.b 0 + X12 D N Q := by omega
        by_cases hX : 0 ≤ X12 D N Q
        · have hYlt : Y12 D N Q < -D.b 1 := by
            by_contra hn
            push Not at hn
            exact terminal12_not_sinkA D N Q (by omega) ⟨hX, hn⟩
          have hE0 : 1 ≤ -(Y12 D N Q + D.b 1) := by omega
          have hEa : -(Y12 D N Q + D.b 1) ≤
              D.x 1 - (D.y 1 + D.b 1) - 1 := by
            have hb := D.b_pos 1
            omega
          have hV0 : 1 ≤ (D.y 0 - D.x 0) - X12 D N Q := by omega
          have hlt := hp.count_lt_zero_of_last_zero (by simpa using hlast) 1 (by decide)
          let H : ℕ := Nn - Qn
          have hHN : Nn = H + Qn := by dsimp [H, Nn, Qn]; omega
          have hH : 1 ≤ H := by dsimp [H, Nn, Qn]; omega
          have hrank := terminal12_reciprocal_rank D q Qn H Nn P
            (by simp [q, Qn]) hHN hH hstart (by simpa [N, Q] using hX)
            (by simpa [N, Q] using hE0) (by simpa [N, Q] using hEa)
            (by simpa [N, Q] using hV0)
          have hQN : Qn ≤ Nn := by omega
          rw [Nat.cast_sub hQN] at hrank
          have hYbox : 1 ≤ D.x 1 + Y12 D N Q := by
            have huUpper := (ht.endpoint_inBox 1).2
            dsimp [BoxInput.upper] at huUpper
            omega
          exact terminal12_sinkB_nonnegativeX_impossible D N Q hN hQ hQy u hu2 hB
            hX hYbox (by simpa [N, Q, H] using hrank)
        · push Not at hX
          have hE0 : 1 ≤ -X12 D N Q := by omega
          have hEx : -X12 D N Q ≤ D.x 0 - 1 := by
            have huUpper := (ht.endpoint_inBox 0).2
            dsimp [BoxInput.upper] at huUpper
            omega
          by_cases hDelta : 0 ≤ Y12 D N Q + D.b 1
          · have hNle := terminal12_nonnegativeD_count_bound D Qn N (-X12 D N Q) P
              (by simp [Qn]) (by simpa [Q, Qn] using hQy)
              (by simp [X12, N, Q, Nn, Qn]) (by simpa [N, Q] using hEx)
            exact terminal12_sinkB_negativeX_certificate D N Q hN hQ hQy u hu2 hB
              hcoef0 (by omega)
          · push Not at hDelta
            have hpred := terminal12_negativeD_predecessor_bound D q Qn N
              (-X12 D N Q) (-(Y12 D N Q + D.b 1)) P hq
              (by simp [q, Qn]) hstart
              (by simp [X12, N, Q, Nn, Qn])
              (by simp [Y12, N, Q, Nn, Qn])
              (by simpa [N, Q] using hE0) (by simpa [N, Q] using hEx) (by omega)
            exact terminal12_sinkB_negativeX_certificate D N Q hN hQ hQy u hu2 hB
              hcoef0 (by omega)
      ·
        have hY : 0 ≤ Y12 D N Q := by omega
        have hX : X12 D N Q < 0 := by
          by_contra hn
          push Not at hn
          exact terminal12_not_sinkA D N Q (by omega) ⟨hn, by
            have := D.b_pos 1
            omega⟩
        have hE0 : 1 ≤ -X12 D N Q := by omega
        have hEx : -X12 D N Q ≤ D.x 0 - 1 := by
          have huUpper := (ht.endpoint_inBox 0).2
          dsimp [BoxInput.upper] at huUpper
          omega
        have hU0 : 1 ≤ u 1 := (ht.endpoint_inBox 1).1
        have hELR := terminal12_sinkC_ELR_extended D q Qn N
          (-X12 D N Q) (u 1) (Y12 D N Q) P (by simp [q, Qn])
          (by simp [X12, N, Q, Nn, Qn])
          (by rw [hu1]; simp [Y12, N, Q, Nn, Qn]; ring)
          hu1 hY hE0 hEx hU0
        have hcoef0 : 0 ≤ D.x 0 + D.y 0 + D.b 0 + X12 D N Q := by
          have huUpper := (ht.endpoint_inBox 0).2
          dsimp [BoxInput.upper] at huUpper
          have hb := D.b_pos 0
          omega
        exact terminal12_sinkC_certificate D N Q hN hQ hNy u hu1 hu2 hC hcoef0
          (by simpa [N, Q] using hELR)
    · rcases hBC with hB | hC
      ·
        have hw := hactual q hq le_rfl
        have hPN := hw.at_last (by decide) (by simpa using hlast)
        have hu0E : u 0 = P.E q := by
          rw [hu0]
          simp [X12, SuccessfulPrefix.E, P, q, N, Q, Nn, Qn]
          rw [hPN]
          push_cast
          ring
        have hu1U : u 1 = D.x 1 + P.U q := by
          rw [hu1]
          simp [Y12, SuccessfulPrefix.U, P, q, N, Q, Nn, Qn]
          rw [hPN]
          push_cast
          ring
        exact terminal12_last_row1_of_prefix D q P hq hstart N hPN.symm u hu0E hu1U
          (by simpa [Q, Qn, q] using hu2) hB
      ·
        have hw := hactual q hq le_rfl
        have hPN := hw.at_last (by decide) (by simpa using hlast)
        have hu0E : u 0 = P.E q := by
          rw [hu0]
          simp [X12, SuccessfulPrefix.E, P, q, N, Q, Nn, Qn]
          rw [hPN]
          push_cast
          ring
        have hu1U : u 1 = D.x 1 + P.U q := by
          rw [hu1]
          simp [Y12, SuccessfulPrefix.U, P, q, N, Q, Nn, Qn]
          rw [hPN]
          push_cast
          ring
        have hUpos := (P.residues q hq le_rfl).2.2.1
        have hUdef : P.U q = (q : ℤ) * D.x 1 -
            (P.N q - 1) * (D.y 1 + D.b 1) := rfl
        rw [hUdef] at hu1U
        have hx1B : D.y 1 + D.b 1 < D.x 1 := by
          have hx := D.x_pos 0
          have hBpos := P.B_pos
          nlinarith [P.corridor]
        have hb := D.b_pos 1
        omega
    · have hm : (2 : Fin 3) ∈ l := by rw [hlast]; simp
      have hc := List.count_pos_iff.mpr hm
      omega
  rcases D.sink_cover u huPos hsink with hA | hB | hC | hD
  · apply terminal12_not_sinkA D N Q (by omega)
    constructor <;> omega
  · exact hBC_impossible (Or.inl hB)
  · exact hBC_impossible (Or.inr hC)
  · have huvec : u = ![D.y 0 - X12 D N Q, D.y 1 - Y12 D N Q, u 2] := by
      funext j
      fin_cases j <;> simp [hu0, hu1]
    exact terminal12_sinkD_impossible D N Q hN hQ hNy hQy u huvec hu2 hD

end P21.Nonsymmetric.ColorCap
