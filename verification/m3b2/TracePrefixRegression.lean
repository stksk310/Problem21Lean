import P21.Nonsymmetric.ColorCap.DPE.TraceSuccessfulPrefix

open P21.Nonsymmetric.ColorCap

noncomputable section

example (D : BoxInput) (l : List (Fin 3)) (u : Point) (q : ℕ)
    (ht : FiringTrace D.upper D.rows D.x l u)
    (hp : ProperNonzeroPredecessors l)
    (hno2 : l.count 2 = 0) (hq : q ≤ l.count 1) :
    SuccessfulPrefix (D.x 0) (D.y 0) (D.y 1 + D.b 1)
      (D.x 1) 0 (D.b 1) q :=
  trace_successfulPrefix12 D ht hp hno2 hq

example (D : BoxInput) (l : List (Fin 3)) (u : Point) (q : ℕ)
    (ht : FiringTrace D.upper D.rows D.x l u)
    (hp : ProperNonzeroPredecessors l)
    (hno1 : l.count 1 = 0) (hq : q ≤ l.count 2) :
    SuccessfulPrefix (D.x 0) (D.y 0 + D.b 0) (D.y 2)
      (D.x 2) (D.b 0) 0 q :=
  trace_successfulPrefix13 D ht hp hno1 hq
