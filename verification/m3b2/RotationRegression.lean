import P21.Nonsymmetric.ColorCap.DPE.Rotation

open P21.Nonsymmetric P21.Nonsymmetric.ColorCap

-- Cyclic transport preserves the exact box matrix, coordinates, and row order.
example (D : BoxInput) (i j k : Fin 3) :
    (D.rotate i).rows j k = D.rows (rotatePerm i j) (rotatePerm i k) :=
  D.rotate_rows i j k

-- START is derived from the genuine first in-box row-zero firing.
example (D : BoxInput) (h : InBox D.upper (fire D.rows 0 D.x)) :
    D.x 0 < D.y 0 ∧ D.y 1 + D.b 1 < D.x 1 ∧ D.y 2 < D.x 2 :=
  D.start_of_row0 h

-- A path is transported without changing its chronology or inventing a row.
example (D : BoxInput) (i : Fin 3) {t : ℕ} {u : Point}
    (h : BoxPath D.upper D.rows t D.x u) :
    BoxPath (D.rotate i).upper (D.rotate i).rows t (permutePoint (rotatePerm i) D.x)
      (permutePoint (rotatePerm i) u) :=
  h.rotate D i
