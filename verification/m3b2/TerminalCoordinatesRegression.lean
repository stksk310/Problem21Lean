import P21.Nonsymmetric.ColorCap.DPE.TerminalCoordinates

open P21.Nonsymmetric.ColorCap

example (D : BoxInput) (l : List (Fin 3)) (u : Point)
    (ht : FiringTrace D.upper D.rows D.x l u) (hno2 : l.count 2 = 0) :
    u = terminal12Point D (l.count 0 + 1) (l.count 1 + 1) :=
  trace_terminal12 D ht hno2

example (D : BoxInput) (l : List (Fin 3)) (u : Point)
    (ht : FiringTrace D.upper D.rows D.x l u) (hno1 : l.count 1 = 0) :
    u = terminal13Point D (l.count 0 + 1) (l.count 2 + 1) :=
  trace_terminal13 D ht hno1
