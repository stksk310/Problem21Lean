import P21.Nonsymmetric.ColorCap.DPE.Canonical

open P21.Nonsymmetric.ColorCap

example (D : BoxInput) (l : List (Fin 3)) (u : Point)
    (ht : FiringTrace D.upper D.rows D.x l u)
    (hne : l ≠ []) (hfirst : InBox D.upper (fire D.rows 0 D.x)) :
    ∃ b, l = 0 :: b :=
  ht.head_zero D hne hfirst

example (D : BoxInput) (l : List (Fin 3)) (u : Point)
    (ht : FiringTrace D.upper D.rows D.x l u)
    (hne : l ≠ []) (hno1 : l.count 1 = 0) (hno2 : l.count 2 = 0)
    (hsink : ¬ ∃ i, ∀ j, 1 ≤ fire D.rows i u j) : False :=
  one_color_trace_sink_impossible D ht hne hno1 hno2 hsink
