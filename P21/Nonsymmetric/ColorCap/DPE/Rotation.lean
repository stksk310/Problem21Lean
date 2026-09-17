import P21.Nonsymmetric.ColorCap.DPE.Trace
import P21.Nonsymmetric.ColorCap.BoxInput
import P21.Nonsymmetric.Relabel

namespace P21.Nonsymmetric.ColorCap

def permutePoint (e : Equiv.Perm (Fin 3)) (u : Point) : Point := fun j => u (e j)

namespace BoxInput

/-- Cyclically rename every coordinate and row of the same box input. -/
def rotate (D : BoxInput) (i : Fin 3) : BoxInput where
  m := D.m
  n := permutePoint (P21.Nonsymmetric.rotatePerm i) D.n
  x := permutePoint (P21.Nonsymmetric.rotatePerm i) D.x
  y := permutePoint (P21.Nonsymmetric.rotatePerm i) D.y
  b := permutePoint (P21.Nonsymmetric.rotatePerm i) D.b
  m_pos := D.m_pos
  n_gt j := D.n_gt _
  x_pos j := D.x_pos _
  y_pos j := D.y_pos _
  b_pos j := D.b_pos _
  row0 := by
    fin_cases i
    all_goals simp [permutePoint, P21.Nonsymmetric.rotatePerm, P21.Nonsymmetric.cyclePerm,
      P21.Nonsymmetric.next, P21.Nonsymmetric.prev]
    · linear_combination D.row0
    · linear_combination D.row1
    · linear_combination D.row2
  row1 := by
    fin_cases i
    all_goals simp [permutePoint, P21.Nonsymmetric.rotatePerm, P21.Nonsymmetric.cyclePerm,
      P21.Nonsymmetric.next, P21.Nonsymmetric.prev]
    · linear_combination D.row1
    · linear_combination D.row2
    · linear_combination D.row0
  row2 := by
    fin_cases i
    all_goals simp [permutePoint, P21.Nonsymmetric.rotatePerm, P21.Nonsymmetric.cyclePerm,
      P21.Nonsymmetric.next, P21.Nonsymmetric.prev]
    · linear_combination D.row2
    · linear_combination D.row0
    · linear_combination D.row1

@[simp] theorem rotate_upper (D : BoxInput) (i j : Fin 3) :
    (D.rotate i).upper j = D.upper (P21.Nonsymmetric.rotatePerm i j) := by
  rfl

theorem rotate_rows (D : BoxInput) (i j k : Fin 3) :
    (D.rotate i).rows j k =
      D.rows (P21.Nonsymmetric.rotatePerm i j) (P21.Nonsymmetric.rotatePerm i k) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    rfl

/-- The exact START inequalities, derived from an actual first firing. -/
theorem start_of_row0 (D : BoxInput) (h : InBox D.upper (fire D.rows 0 D.x)) :
    D.x 0 < D.y 0 ∧ D.y 1 + D.b 1 < D.x 1 ∧ D.y 2 < D.x 2 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp [fire, rows, upper] at h0 h1 h2
  omega

end BoxInput

theorem permutePoint_fire (D : BoxInput) (i k : Fin 3) (u : Point) :
    permutePoint (P21.Nonsymmetric.rotatePerm i) (fire D.rows k u) =
      fire (D.rotate i).rows ((P21.Nonsymmetric.rotatePerm i).symm k)
        (permutePoint (P21.Nonsymmetric.rotatePerm i) u) := by
  funext j
  simp only [permutePoint, fire]
  rw [D.rotate_rows]
  simp

theorem inBox_permute_iff (D : BoxInput) (i : Fin 3) (u : Point) :
    InBox (D.rotate i).upper (permutePoint (P21.Nonsymmetric.rotatePerm i) u) ↔
      InBox D.upper u := by
  constructor
  · intro h j
    have hh := h ((P21.Nonsymmetric.rotatePerm i).symm j)
    simpa [permutePoint] using hh
  · intro h j
    simpa [permutePoint] using h (P21.Nonsymmetric.rotatePerm i j)

/-- Transport any supplied actual path, including every chronological firing. -/
theorem BoxPath.rotateGeneral (D : BoxInput) (i : Fin 3) {t : ℕ} {p u : Point}
    (h : BoxPath D.upper D.rows t p u) :
    BoxPath (D.rotate i).upper (D.rotate i).rows t
      (permutePoint (P21.Nonsymmetric.rotatePerm i) p)
      (permutePoint (P21.Nonsymmetric.rotatePerm i) u) := by
  induction h with
  | nil hb => exact BoxPath.nil ((inBox_permute_iff D i _).mpr hb)
  | @snoc t u v h k hk ih =>
      have hki := (inBox_permute_iff D i _).mpr hk
      rw [permutePoint_fire D i k] at hki
      rw [permutePoint_fire D i k]
      exact BoxPath.snoc ih _ hki

theorem BoxPath.rotate (D : BoxInput) (i : Fin 3) {t : ℕ} {u : Point}
    (h : BoxPath D.upper D.rows t D.x u) :
    BoxPath (D.rotate i).upper (D.rotate i).rows t
      (permutePoint (P21.Nonsymmetric.rotatePerm i) D.x)
      (permutePoint (P21.Nonsymmetric.rotatePerm i) u) :=
  h.rotateGeneral D i

end P21.Nonsymmetric.ColorCap
