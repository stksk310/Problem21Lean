import P21.Nonsymmetric.ColorCap.DPE.TwoColor13

namespace P21.Nonsymmetric.ColorCap

/-- The first occurrence of a nonzero color is cut from the original trace.
Its source is an actual prefix ending in row zero; no firing order is added. -/
theorem first_nonzero_occurrence_actual (D : BoxInput)
    {l : List (Fin 3)} {u : Point}
    (ht : FiringTrace D.upper D.rows D.x l u)
    (hp : ProperNonzeroPredecessors l) (k : Fin 3) (hk : k ≠ 0)
    (hoccurs : 1 ≤ l.count k) :
    ∃ p tail source current,
      l = (p ++ [0]) ++ k :: tail ∧
      (p ++ [0]).count k = 0 ∧
      FiringTrace D.upper D.rows D.x (p ++ [0]) source ∧
      FiringTrace D.upper D.rows D.x ((p ++ [0]) ++ [k]) current ∧
      current = fire D.rows k source := by
  obtain ⟨p, tail, hsplit, hcount⟩ :=
    occurrence_source_ends_zero l k hp hk (h := 1) (by omega) hoccurs
  have hsourcePrefix : p ++ [0] <+: l := by
    refine ⟨k :: tail, ?_⟩
    simpa [List.append_assoc] using hsplit.symm
  have hcurrentPrefix : (p ++ [0]) ++ [k] <+: l := by
    refine ⟨tail, ?_⟩
    simpa [List.append_assoc] using hsplit.symm
  obtain ⟨source, hs⟩ := ht.prefix_trace hsourcePrefix
  obtain ⟨current, hc⟩ := ht.prefix_trace hcurrentPrefix
  have hfire : current = fire D.rows k source := by
    rw [← hs.execute_eq, ← hc.execute_eq]
    simp [execute_append]
  exact ⟨p, tail, source, current, hsplit, by simpa using hcount, hs, hc, hfire⟩

theorem first_row2_after_01_actual (D : BoxInput)
    {l : List (Fin 3)} {u : Point}
    (ht : FiringTrace D.upper D.rows D.x l u)
    (hp : ProperNonzeroPredecessors l) (hoccurs : 1 ≤ l.count 2) :
    ∃ p tail source current,
      l = (p ++ [0]) ++ (2 : Fin 3) :: tail ∧
      (p ++ [0]).count 2 = 0 ∧
      FiringTrace D.upper D.rows D.x (p ++ [0]) source ∧
      FiringTrace D.upper D.rows D.x ((p ++ [0]) ++ [2]) current ∧
      current = fire D.rows 2 source := by
  exact first_nonzero_occurrence_actual D ht hp 2 (by decide) hoccurs

theorem first_row1_after_02_actual (D : BoxInput)
    {l : List (Fin 3)} {u : Point}
    (ht : FiringTrace D.upper D.rows D.x l u)
    (hp : ProperNonzeroPredecessors l) (hoccurs : 1 ≤ l.count 1) :
    ∃ p tail source current,
      l = (p ++ [0]) ++ (1 : Fin 3) :: tail ∧
      (p ++ [0]).count 1 = 0 ∧
      FiringTrace D.upper D.rows D.x (p ++ [0]) source ∧
      FiringTrace D.upper D.rows D.x ((p ++ [0]) ++ [1]) current ∧
      current = fire D.rows 1 source := by
  exact first_nonzero_occurrence_actual D ht hp 1 (by decide) hoccurs

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

/-- B.19.1 rank calculation.  No monotonicity of the residues is used:
both strict prior-residue bounds are consequences of PREFIX. -/
theorem first_third_12_rank (D : BoxInput) (q Q : ℕ) (N E Delta : ℤ)
    (P : SuccessfulPrefix (D.x 0) (D.y 0) (D.y 1 + D.b 1)
      (D.x 1) 0 (D.b 1) q)
    (hq : 1 ≤ q) (hQ : Q = q + 1) (hstart : D.x 0 < D.y 0)
    (hE : E = N * D.x 0 - (Q : ℤ) * D.y 0)
    (hDelta : Delta = N * (D.y 1 + D.b 1) - (Q : ℤ) * D.x 1)
    (hE0 : 1 ≤ E) (hEx : E ≤ D.x 0 - 1)
    (hDeltaUpper : Delta ≤ D.b 1 - 1) :
    N + E ≤ D.y 0 ∧ (Q : ℤ) ≤ D.y 1 + Delta := by
  let s := Finset.Icc 1 q
  have hpriorE : ∀ i ∈ s, E < P.E i := by
    intro i hi
    have hir := Finset.mem_Icc.mp hi
    by_contra hn
    push Not at hn
    have hiQ : i < Q := by omega
    have hsub : ((Q - i : ℕ) : ℤ) = (Q : ℤ) - (i : ℤ) := by
      rw [Nat.cast_sub (by omega)]
    apply P.separator (Q - i) (by omega) (by omega)
    refine ⟨N - P.N i, ?_, ?_⟩
    · have hEi : P.E i = P.N i * D.x 0 - (i : ℤ) * D.y 0 := rfl
      rw [hEi] at hn
      rw [hsub]
      nlinarith [hE]
    · have hUi := (P.residues i hir.1 hir.2).2.2.2
      rw [hsub]
      nlinarith [hDelta]
  have hEupper : ∀ i ∈ s, P.E i ≤ D.x 0 - 1 := by
    intro i hi
    have he := (P.residues i (Finset.mem_Icc.mp hi).1
      (Finset.mem_Icc.mp hi).2).2.1
    change P.N i * D.x 0 - (i : ℤ) * D.y 0 ≤ D.x 0 - 1
    omega
  have hUupper : ∀ i ∈ s, P.U i ≤ D.y 1 - 1 := by
    intro i hi
    have hu := (P.residues i (Finset.mem_Icc.mp hi).1
      (Finset.mem_Icc.mp hi).2).2.2.2
    change (i : ℤ) * D.x 1 - (P.N i - 1) * (D.y 1 + D.b 1) ≤ D.y 1 - 1
    omega
  have hEinj : Set.InjOn P.E (s : Set ℕ) := by
    intro i hi j hj he
    exact P.coordinate_injective (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 he
  have hUinj : Set.InjOn P.U (s : Set ℕ) := by
    intro i hi j hj he
    exact P.coordinateU_injective (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 he
  have hcE := residue_slot_bound s P.E P.U E (D.y 1 - 1)
    (D.x 0 - 1) (D.y 1 - 1) hEupper hUupper hEinj hUinj (by
      intro i hi
      exact Or.inl (hpriorE i hi))
  have hdE : 0 ≤ D.x 0 - 1 - E := by omega
  have hcEZ : (s.card : ℤ) ≤ (D.x 0 - 1 - E).toNat := by
    exact_mod_cast (by simpa using hcE)
  simp [s, Int.toNat_of_nonneg hdE] at hcEZ
  have hQE : (Q : ℤ) + E ≤ D.x 0 := by omega
  have hQx : (Q : ℤ) ≤ D.x 0 - 1 := by omega
  have hNE : N + E ≤ D.y 0 := by
    have hd : 1 ≤ D.y 0 - D.x 0 := by omega
    have hprod : 0 ≤ (D.x 0 - (Q : ℤ)) *
        (D.y 0 - D.x 0 - 1) := mul_nonneg (by omega) (by omega)
    nlinarith [hE]
  have hQD : (Q : ℤ) ≤ D.y 1 + Delta := by
    by_cases hD : 0 ≤ Delta
    · have hqy := P.U_slot_count (by have := D.y_pos 1; omega)
      omega
    · push Not at hD
      have hpriorU : ∀ i ∈ s, -Delta < P.U i := by
        intro i hi
        have hir := Finset.mem_Icc.mp hi
        by_contra hn
        push Not at hn
        have hiQ : i < Q := by omega
        have hsub : ((Q - i : ℕ) : ℤ) = (Q : ℤ) - (i : ℤ) := by
          rw [Nat.cast_sub (by omega)]
        apply P.separator (Q - i) (by omega) (by omega)
        refine ⟨N - P.N i + 1, ?_, ?_⟩
        · have hEi := (P.residues i hir.1 hir.2).2.1
          rw [hsub]
          nlinarith [hE]
        · have hUdef : P.U i = (i : ℤ) * D.x 1 -
              (P.N i - 1) * (D.y 1 + D.b 1) := rfl
          rw [hUdef] at hn
          rw [hsub]
          nlinarith [hDelta]
      have hcU := residue_slot_bound s P.E P.U (D.x 0 - 1) (-Delta)
        (D.x 0 - 1) (D.y 1 - 1) hEupper hUupper hEinj hUinj (by
          intro i hi
          exact Or.inr (hpriorU i hi))
      have hdU : 0 ≤ D.y 1 - 1 - (-Delta) := by
        have hu := hpriorU 1 (by simp [s]; omega)
        have huu := hUupper 1 (by simp [s]; omega)
        omega
      have hcUZ : (s.card : ℤ) ≤ (D.y 1 - 1 - (-Delta)).toNat := by
        exact_mod_cast (by simpa using hcU)
      simp [s, Int.toNat_of_nonneg hdU] at hcUZ
      omega
  exact ⟨hNE, hQD⟩

/-- B.19.1 on the actual source/current states of the first row-3 firing. -/
theorem first_third_12_to_3_actual_impossible (D : BoxInput)
    {l : List (Fin 3)} {u : Point}
    (ht : FiringTrace D.upper D.rows D.x l u)
    (hp : ProperNonzeroPredecessors l)
    (hcount2 : 1 ≤ l.count 2) (hstart : D.x 0 < D.y 0)
    (hprior1 : ∀ p tail, l = (p ++ [0]) ++ (2 : Fin 3) :: tail →
      1 ≤ (p ++ [0]).count 1) : False := by
  obtain ⟨p, tail, source, current, hsplit, hsourceNo2, hs, hc, hfire⟩ :=
    first_row2_after_01_actual D ht hp hcount2
  let sl : List (Fin 3) := p ++ [0]
  have hno2 : sl.count 2 = 0 := by simpa [sl] using hsourceNo2
  have hcount1sl : 1 ≤ sl.count 1 := by simpa [sl] using hprior1 p tail hsplit
  let Nn : ℕ := sl.count 0 + 1
  let Qn : ℕ := sl.count 1 + 1
  let N : ℤ := Nn
  let Q : ℤ := Qn
  let E : ℤ := N * D.x 0 - Q * D.y 0
  let Delta : ℤ := N * (D.y 1 + D.b 1) - Q * D.x 1
  have hterminal := trace_terminal12 D hs hno2
  have hcoords := terminal12Point_coordinates D Nn Qn
  change source = terminal12Point D Nn Qn at hterminal
  have hsource0 : source 0 = D.y 0 + E := by
    rw [hterminal]
    rw [hcoords.1]
    simp [E, N, Q]
    ring
  have hsource1 : source 1 = D.y 1 + D.b 1 - Delta := by
    rw [hterminal]
    rw [hcoords.2.1]
    simp [Delta, N, Q]
    ring
  have hsource2 : source 2 = D.x 2 - (N - 1) * D.y 2 -
      (Q - 1) * (D.y 2 + D.b 2) := by
    rw [hterminal]
    rw [hcoords.2.2]
  have hf0 := congrFun hfire 0
  have hf1 := congrFun hfire 1
  have hf2 := congrFun hfire 2
  simp [fire, BoxInput.rows] at hf0 hf1 hf2
  have hs0 := hs.endpoint_inBox 0
  have hs2 := hs.endpoint_inBox 2
  have hc0 := hc.endpoint_inBox 0
  have hc1 := hc.endpoint_inBox 1
  have hc2 := hc.endpoint_inBox 2
  dsimp [BoxInput.upper] at hs0 hs2 hc0 hc1 hc2
  have hE0 : 1 ≤ E := by
    have hb := D.b_pos 0
    omega
  have hEx : E ≤ D.x 0 - 1 := by omega
  have hDeltaUpper : Delta ≤ D.b 1 - 1 := by omega
  have hsource2Upper : source 2 ≤ D.y 2 - 1 := by omega
  let q : ℕ := sl.count 1
  have hslprefix : sl <+: l := by
    refine ⟨2 :: tail, ?_⟩
    simpa [sl, List.append_assoc] using hsplit.symm
  let P := trace_successfulPrefix12 D hs (hp.prefix hslprefix) hno2
    (q := q) le_rfl
  have hq : 1 ≤ q := by simpa [q] using hcount1sl
  have hrank := first_third_12_rank D q Qn N E Delta P hq (by simp [q, Qn]) hstart
    (by simp [E, N, Q]) (by simp [Delta, N, Q]) hE0 hEx hDeltaUpper
  exact first_third_12_to_3_certificate D N Q E Delta
    (by simp [N, Nn]) (by simp [Q, Qn]) hrank.1 hrank.2 source hsource2Upper
    hsource2 (by simp [E]) (by simp [Delta])

end P21.Nonsymmetric.ColorCap
