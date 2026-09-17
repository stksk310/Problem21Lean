import P21.Nonsymmetric.ColorCap.DPE.PathShape

open P21.Nonsymmetric.ColorCap

example (D : BoxInput) (l : List (Fin 3)) (u : Point)
    (hs : D.x 0 < D.y 0)
    (hhead : l = [] ∨ ∃ b, l = 0 :: b)
    (ht : FiringTrace D.upper D.rows D.x l u) :
    ProperNonzeroPredecessors l :=
  ht.properNonzeroPredecessors D hs hhead
