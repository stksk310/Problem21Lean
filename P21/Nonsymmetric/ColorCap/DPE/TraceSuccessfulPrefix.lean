import P21.Nonsymmetric.ColorCap.DPE.PathShape
import P21.Nonsymmetric.ColorCap.PositiveMinors

namespace P21.Nonsymmetric.ColorCap

private theorem crossing12_residue (D : BoxInput)
    {l : List (Fin 3)} {u : Point}
    (ht : FiringTrace D.upper D.rows D.x l u)
    (hp : ProperNonzeroPredecessors l) (hno2 : l.count 2 = 0)
    (h : ℕ) (hh : 1 ≤ h) (hc : h ≤ l.count 1) :
    ∃ N : ℤ,
      0 < N * D.x 0 - (h : ℤ) * D.y 0 ∧
      N * D.x 0 - (h : ℤ) * D.y 0 ≤ D.x 0 - 1 ∧
      0 < (h : ℤ) * D.x 1 - (N - 1) * (D.y 1 + D.b 1) ∧
      (h : ℤ) * D.x 1 - (N - 1) * (D.y 1 + D.b 1) ≤ D.y 1 - 1 := by
  obtain ⟨p, b, hl, hcount1⟩ := occurrence_source_ends_zero l 1 hp (by decide) hh hc
  let a : List (Fin 3) := p ++ [0]
  have ha : a <+: l := by
    refine ⟨1 :: b, ?_⟩
    simpa [a, List.append_assoc] using hl.symm
  have ha1 : a ++ [1] <+: l := by
    refine ⟨b, ?_⟩
    simpa [a, List.append_assoc] using hl.symm
  obtain ⟨s, hs⟩ := ht.prefix_trace ha
  obtain ⟨w, hw⟩ := ht.prefix_trace ha1
  have hw_eq : w = fire D.rows 1 s := by
    rw [← hs.execute_eq, ← hw.execute_eq]
    simp [execute_append]
  have hcount1a : a.count 1 = h - 1 := by simpa [a] using hcount1
  have hcount2a : a.count 2 = 0 := by
    rw [hl] at hno2
    simp at hno2
    simpa [a] using hno2.1
  have hs0eq := hs.endpoint_eq_sub_sum 0
  have hs1eq := hs.endpoint_eq_sub_sum 1
  have hs0 := hs.endpoint_inBox 0
  have hs1 := hs.endpoint_inBox 1
  have hw0 := hw.endpoint_inBox 0
  have hw1 := hw.endpoint_inBox 1
  have hw0eq := congrFun hw_eq 0
  have hw1eq := congrFun hw_eq 1
  simp [BoxInput.rows, Fin.sum_univ_succ, hcount1a, hcount2a] at hs0eq hs1eq
  simp [fire, BoxInput.rows] at hw0eq hw1eq
  refine ⟨(a.count 0 : ℤ) + 1, ?_⟩
  dsimp [BoxInput.upper] at hs0 hs1 hw0 hw1
  have hx0 := D.x_pos 0
  have hy0 := D.y_pos 0
  have hx1 := D.x_pos 1
  have hy1 := D.y_pos 1
  have hb1 := D.b_pos 1
  have hcast : ((h - 1 : ℕ) : ℤ) = (h : ℤ) - 1 := by omega
  rw [hcast] at hs0eq hs1eq
  ring_nf at hs0eq hs1eq hw0eq hw1eq ⊢
  omega

noncomputable def trace_successfulPrefix12 (D : BoxInput)
    {l : List (Fin 3)} {u : Point} {q : ℕ}
    (ht : FiringTrace D.upper D.rows D.x l u)
    (hp : ProperNonzeroPredecessors l)
    (hno2 : l.count 2 = 0) (hq : q ≤ l.count 1) :
    SuccessfulPrefix (D.x 0) (D.y 0) (D.y 1 + D.b 1)
      (D.x 1) 0 (D.b 1) q := by
  classical
  have hex : ∀ h : ℕ, 1 ≤ h → h ≤ q → ∃ N : ℤ,
      0 < N * D.x 0 - (h : ℤ) * D.y 0 ∧
      N * D.x 0 - (h : ℤ) * D.y 0 ≤ D.x 0 - 1 ∧
      0 < (h : ℤ) * D.x 1 - (N - 1) * (D.y 1 + D.b 1) ∧
      (h : ℤ) * D.x 1 - (N - 1) * (D.y 1 + D.b 1) ≤ D.y 1 - 1 := by
    intro h hh hhq
    exact crossing12_residue D ht hp hno2 h hh (le_trans hhq hq)
  let N : ℕ → ℤ := fun h => if hh : 1 ≤ h ∧ h ≤ q then Classical.choose (hex h hh.1 hh.2) else 0
  refine {
    N := N
    x_pos := by have := D.x_pos 0; omega
    B_pos := by have := D.y_pos 1; have := D.b_pos 1; omega
    b_nonneg := by omega
    c_nonneg := by have := D.b_pos 1; omega
    corridor := by have hm := D.minor01_pos; nlinarith
    residues := ?_ }
  intro h hh hhq
  have hchosen := Classical.choose_spec (hex h hh hhq)
  simpa [N, hh, hhq] using hchosen

private theorem crossing13_residue (D : BoxInput)
    {l : List (Fin 3)} {u : Point}
    (ht : FiringTrace D.upper D.rows D.x l u)
    (hp : ProperNonzeroPredecessors l) (hno1 : l.count 1 = 0)
    (h : ℕ) (hh : 1 ≤ h) (hc : h ≤ l.count 2) :
    ∃ N : ℤ,
      0 < N * D.x 0 - (h : ℤ) * (D.y 0 + D.b 0) ∧
      N * D.x 0 - (h : ℤ) * (D.y 0 + D.b 0) ≤ D.x 0 - D.b 0 - 1 ∧
      0 < (h : ℤ) * D.x 2 - (N - 1) * D.y 2 ∧
      (h : ℤ) * D.x 2 - (N - 1) * D.y 2 ≤ D.y 2 - 1 := by
  obtain ⟨p, b, hl, hcount2⟩ := occurrence_source_ends_zero l 2 hp (by decide) hh hc
  let a : List (Fin 3) := p ++ [0]
  have ha : a <+: l := by
    refine ⟨2 :: b, ?_⟩
    simpa [a, List.append_assoc] using hl.symm
  have ha2 : a ++ [2] <+: l := by
    refine ⟨b, ?_⟩
    simpa [a, List.append_assoc] using hl.symm
  obtain ⟨s, hs⟩ := ht.prefix_trace ha
  obtain ⟨w, hw⟩ := ht.prefix_trace ha2
  have hw_eq : w = fire D.rows 2 s := by
    rw [← hs.execute_eq, ← hw.execute_eq]
    simp [execute_append]
  have hcount2a : a.count 2 = h - 1 := by simpa [a] using hcount2
  have hcount1a : a.count 1 = 0 := by
    rw [hl] at hno1
    simp at hno1
    simpa [a] using hno1.1
  have hs0eq := hs.endpoint_eq_sub_sum 0
  have hs2eq := hs.endpoint_eq_sub_sum 2
  have hs0 := hs.endpoint_inBox 0
  have hs2 := hs.endpoint_inBox 2
  have hw0 := hw.endpoint_inBox 0
  have hw2 := hw.endpoint_inBox 2
  have hw0eq := congrFun hw_eq 0
  have hw2eq := congrFun hw_eq 2
  simp [BoxInput.rows, Fin.sum_univ_succ, hcount1a, hcount2a] at hs0eq hs2eq
  simp [fire, BoxInput.rows] at hw0eq hw2eq
  refine ⟨(a.count 0 : ℤ) + 1, ?_⟩
  dsimp [BoxInput.upper] at hs0 hs2 hw0 hw2
  have hx0 := D.x_pos 0
  have hy0 := D.y_pos 0
  have hb0 := D.b_pos 0
  have hx2 := D.x_pos 2
  have hy2 := D.y_pos 2
  have hcast : ((h - 1 : ℕ) : ℤ) = (h : ℤ) - 1 := by omega
  rw [hcast] at hs0eq hs2eq
  ring_nf at hs0eq hs2eq hw0eq hw2eq ⊢
  omega

noncomputable def trace_successfulPrefix13 (D : BoxInput)
    {l : List (Fin 3)} {u : Point} {q : ℕ}
    (ht : FiringTrace D.upper D.rows D.x l u)
    (hp : ProperNonzeroPredecessors l)
    (hno1 : l.count 1 = 0) (hq : q ≤ l.count 2) :
    SuccessfulPrefix (D.x 0) (D.y 0 + D.b 0) (D.y 2)
      (D.x 2) (D.b 0) 0 q := by
  classical
  have hex : ∀ h : ℕ, 1 ≤ h → h ≤ q → ∃ N : ℤ,
      0 < N * D.x 0 - (h : ℤ) * (D.y 0 + D.b 0) ∧
      N * D.x 0 - (h : ℤ) * (D.y 0 + D.b 0) ≤ D.x 0 - D.b 0 - 1 ∧
      0 < (h : ℤ) * D.x 2 - (N - 1) * D.y 2 ∧
      (h : ℤ) * D.x 2 - (N - 1) * D.y 2 ≤ D.y 2 - 1 := by
    intro h hh hhq
    exact crossing13_residue D ht hp hno1 h hh (le_trans hhq hq)
  let N : ℕ → ℤ := fun h => if hh : 1 ≤ h ∧ h ≤ q then Classical.choose (hex h hh.1 hh.2) else 0
  refine {
    N := N
    x_pos := by have := D.x_pos 0; omega
    B_pos := by have := D.y_pos 2; omega
    b_nonneg := by have := D.b_pos 0; omega
    c_nonneg := by omega
    corridor := by have hm := D.minor02_pos; nlinarith
    residues := ?_ }
  intro h hh hhq
  have hchosen := Classical.choose_spec (hex h hh hhq)
  simpa [N, hh, hhq] using hchosen

end P21.Nonsymmetric.ColorCap
