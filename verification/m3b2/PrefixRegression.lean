import P21.Nonsymmetric.ColorCap.DPE.SuccessfulPrefix
import P21.Nonsymmetric.ColorCap.DPE.ChronologicalPrefix

open P21.Nonsymmetric.ColorCap

#check SuccessfulPrefix.E_slot_count
#check SuccessfulPrefix.U_slot_count
#check SuccessfulPrefix.cover_by_next_residue

-- LR follows from the successful prefix; it is not an additional hypothesis.
example {x A B v b c : ℤ} {q : ℕ}
    (P : SuccessfulPrefix x A B v b c q) (hq : 1 ≤ q) :
    (q : ℤ) + P.E q + P.U q ≤ (x - b) + (B - c) - 1 :=
  P.last_rank hq

-- ELR exposes every terminal range and chronological cover premise.
example {x A B v b c E U : ℤ} {q : ℕ}
    (P : SuccessfulPrefix x A B v b c q)
    (hE0 : 1 ≤ E) (hEx : E ≤ x - b - 1)
    (hU0 : 1 ≤ U) (hUB : U ≤ B - c - 1)
    (hcover : ∀ i : ℕ, 1 ≤ i → i ≤ q → E < P.E i ∨ U < P.U i) :
    (q : ℤ) ≤ (x - b - 1 - E) + (B - c - 1 - U) :=
  P.terminal_rank hE0 hEx hU0 hUB hcover

-- The h-th crossing is a real split of the original chronological list.
example (l : List (Fin 3)) (r : Fin 3) (h : ℕ)
    (hh : 1 ≤ h) (hc : h ≤ l.count r) :
    ∃ a b, l = a ++ r :: b ∧ a.count r = h-1 :=
  nth_occurrence_split r l h hh hc
