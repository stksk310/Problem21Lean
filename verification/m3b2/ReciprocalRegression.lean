import P21.Nonsymmetric.ColorCap.DPE.ReciprocalRank

open P21.Nonsymmetric.ColorCap

example {x A B v b c : ℤ} {q H Q : ℕ}
    (P : SuccessfulPrefix x A B v b c q)
    (ha : 0 < v - B) (hd : 0 < A - x) (hQ : Q = q + 1)
    (hbracket : (H : ℤ) * x ≤ (Q : ℤ) * (A - x)) :
    ∀ s k : ℕ, 1 ≤ s → s < H → 1 ≤ k →
      ¬ ((s : ℤ) * B ≤ (k : ℤ) * (v - B) ∧
         (k : ℤ) * (A - x) ≤ (s : ℤ) * x) :=
  P.reciprocal_separator ha hd hQ hbracket

example {a B d x b E V : ℤ} {q H : ℕ}
    (P : SuccessfulPrefix a B d x 0 b q) (hH : H = q + 1)
    (hE0 : 1 ≤ E) (hEa : E ≤ a - 1)
    (hV0 : 1 ≤ V) (hVd : V ≤ d - b)
    (hcover : ∀ i : ℕ, 1 ≤ i → i ≤ q → E < P.E i ∨ V < P.U i) :
    (H : ℤ) + E + V ≤ a + d - b :=
  P.dual_rank hH hE0 hEa hV0 hVd hcover
