import P21.Nonsymmetric.ColorCap.DPE.Canonical

namespace P21.Nonsymmetric.ColorCap.SuccessfulPrefix

/-- The dual PREFIX is an algebraic consequence of the original successful
PREFIX.  Its denominator `k` is bounded by the original chronological range;
no symmetric or imaginary path is introduced. -/
theorem reciprocal_separator {x A B v b c : ℤ} {q H Q : ℕ}
    (P : SuccessfulPrefix x A B v b c q)
    (ha : 0 < v - B) (hd : 0 < A - x) (hQ : Q = q + 1)
    (hbracket : (H : ℤ) * x ≤ (Q : ℤ) * (A - x)) :
    ∀ s k : ℕ, 1 ≤ s → s < H → 1 ≤ k →
      ¬ ((s : ℤ) * B ≤ (k : ℤ) * (v - B) ∧
         (k : ℤ) * (A - x) ≤ (s : ℤ) * x) := by
  intro s k hs hsH hk hdual
  have hx := P.x_pos
  have hsd : (s : ℤ) * x < (H : ℤ) * x := by
    have : (s : ℤ) < (H : ℤ) := by exact_mod_cast hsH
    nlinarith
  have hkQ : k < Q := by
    have hkQi : (k : ℤ) < (Q : ℤ) := by
      nlinarith [mul_pos (show (0 : ℤ) < (Q : ℤ) - (k : ℤ) by
        by_contra hn; push Not at hn; nlinarith) hd]
    exact_mod_cast hkQi
  have hkq : k ≤ q := by omega
  apply P.separator k hk hkq
  refine ⟨(k : ℤ) + (s : ℤ), ?_, ?_⟩
  · nlinarith
  · nlinarith

/-- DR slot count, including the upper boundary `V = d-b`.  The supplied
dual prefix contains only residues already certified by the path layer. -/
theorem dual_rank {a B d x b : ℤ} {q H : ℕ}
    (P : SuccessfulPrefix a B d x 0 b q) (hH : H = q + 1)
    {E V : ℤ} (hE0 : 1 ≤ E) (hEa : E ≤ a - 1)
    (hV0 : 1 ≤ V) (hVd : V ≤ d - b)
    (hcover : ∀ i : ℕ, 1 ≤ i → i ≤ q → E < P.E i ∨ V < P.U i) :
    (H : ℤ) + E + V ≤ a + d - b := by
  by_cases hv : V ≤ d - b - 1
  · have hr := P.terminal_rank hE0 (by simpa using hEa) hV0 hv hcover
    omega
  · have hveq : V = d - b := by omega
    by_cases hq0 : q = 0
    · subst q
      norm_num at hH
      omega
    have hq1 : 1 ≤ q := by omega
    have hcover' : ∀ i : ℕ, 1 ≤ i → i ≤ q →
        E < P.E i ∨ d - b - 1 < P.U i := by
      intro i hi hiq
      rcases hcover i hi hiq with he | hu
      · exact Or.inl he
      · have hui := (P.residues i hi hiq).2.2.2
        omega
    have hr := P.terminal_rank hE0 (by simpa using hEa)
      (show 1 ≤ d - b - 1 by
        have hU := (P.residues 1 (by omega) hq1).2.2.1
        have hUb := (P.residues 1 (by omega) hq1).2.2.2
        omega)
      (le_rfl) hcover'
    omega

end P21.Nonsymmetric.ColorCap.SuccessfulPrefix
