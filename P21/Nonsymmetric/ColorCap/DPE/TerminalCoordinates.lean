import P21.Nonsymmetric.ColorCap.DPE.ReciprocalRank

namespace P21.Nonsymmetric.ColorCap

def terminal12Point (D : BoxInput) (N Q : ℕ) : Point :=
  ![(N : ℤ) * D.x 0 - ((Q : ℤ) - 1) * D.y 0,
    (Q : ℤ) * D.x 1 - ((N : ℤ) - 1) * (D.y 1 + D.b 1),
    D.x 2 - ((N : ℤ) - 1) * D.y 2 -
      ((Q : ℤ) - 1) * (D.y 2 + D.b 2)]

def terminal13Point (D : BoxInput) (N R : ℕ) : Point :=
  ![(N : ℤ) * D.x 0 - ((R : ℤ) - 1) * (D.y 0 + D.b 0),
    D.x 1 - ((N : ℤ) - 1) * (D.y 1 + D.b 1) -
      ((R : ℤ) - 1) * D.y 1,
    (R : ℤ) * D.x 2 - ((N : ℤ) - 1) * D.y 2]

theorem trace_terminal12 (D : BoxInput) {l : List (Fin 3)} {u : Point}
    (ht : FiringTrace D.upper D.rows D.x l u) (hno2 : l.count 2 = 0) :
    u = terminal12Point D (l.count 0 + 1) (l.count 1 + 1) := by
  funext j
  have hj := ht.endpoint_eq_sub_sum j
  fin_cases j <;>
    simp [terminal12Point, BoxInput.rows, Fin.sum_univ_succ, hno2] at hj ⊢ <;>
    push_cast <;> ring_nf at hj ⊢ <;> omega

theorem trace_terminal13 (D : BoxInput) {l : List (Fin 3)} {u : Point}
    (ht : FiringTrace D.upper D.rows D.x l u) (hno1 : l.count 1 = 0) :
    u = terminal13Point D (l.count 0 + 1) (l.count 2 + 1) := by
  funext j
  have hj := ht.endpoint_eq_sub_sum j
  fin_cases j <;>
    simp [terminal13Point, BoxInput.rows, Fin.sum_univ_succ, hno1] at hj ⊢ <;>
    push_cast <;> ring_nf at hj ⊢ <;> omega

end P21.Nonsymmetric.ColorCap
