import P21.Nonsymmetric.ColorCap.BoxInput

namespace P21.Nonsymmetric.ColorCap.BoxInput

/-- The first corridor orientation follows directly from INPUT, without a determinant assumption. -/
theorem minor01_pos (D : BoxInput) : 0 < D.x 0*D.x 1-D.y 0*(D.y 1+D.b 1) := by
  have hx := D.x_pos 0
  have hy := D.y_pos 0
  have hy2 := D.y_pos 2
  have hb2 := D.b_pos 2
  have hn1 : 0 < D.n 1 := lt_trans D.m_pos (D.n_gt 1)
  have hn2 : 0 < D.n 2 := lt_trans D.m_pos (D.n_gt 2)
  have hc : D.x 0+D.y 0 ≤ D.y 0*D.y 2+D.x 0*(D.y 2+D.b 2) := by nlinarith
  have hp : 0 < (D.x 0+D.y 0)*(D.n 2-D.m) := by
    apply mul_pos <;> nlinarith [D.n_gt 2]
  have hq := mul_nonneg (sub_nonneg.mpr hc) hn2.le
  have he : (D.x 0*D.x 1-D.y 0*(D.y 1+D.b 1))*D.n 1 =
      (D.y 0*D.y 2+D.x 0*(D.y 2+D.b 2))*D.n 2-(D.x 0+D.y 0)*D.m := by
    linear_combination -D.y 0*D.row0-D.x 0*D.row1
  have hpos : 0 < (D.x 0*D.x 1-D.y 0*(D.y 1+D.b 1))*D.n 1 := by nlinarith
  exact (mul_pos_iff_of_pos_right hn1).mp hpos

/-- The second corridor orientation is the corresponding row-1/row-3 elimination. -/
theorem minor02_pos (D : BoxInput) : 0 < D.x 0*D.x 2-D.y 2*(D.y 0+D.b 0) := by
  have hx := D.x_pos 0
  have hy0 := D.y_pos 0
  have hb0 := D.b_pos 0
  have hy1 := D.y_pos 1
  have hb1 := D.b_pos 1
  have hn1 : 0 < D.n 1 := lt_trans D.m_pos (D.n_gt 1)
  have hn2 : 0 < D.n 2 := lt_trans D.m_pos (D.n_gt 2)
  have hc : D.x 0+(D.y 0+D.b 0) ≤
      (D.y 0+D.b 0)*(D.y 1+D.b 1)+D.x 0*D.y 1 := by nlinarith
  have hp : 0 < (D.x 0+(D.y 0+D.b 0))*(D.n 1-D.m) := by
    apply mul_pos <;> nlinarith [D.n_gt 1]
  have hq := mul_nonneg (sub_nonneg.mpr hc) hn1.le
  have he : (D.x 0*D.x 2-D.y 2*(D.y 0+D.b 0))*D.n 2 =
      ((D.y 0+D.b 0)*(D.y 1+D.b 1)+D.x 0*D.y 1)*D.n 1-
        (D.x 0+D.y 0+D.b 0)*D.m := by
    linear_combination -(D.y 0+D.b 0)*D.row0-D.x 0*D.row2
  have hpos : 0 < (D.x 0*D.x 2-D.y 2*(D.y 0+D.b 0))*D.n 2 := by nlinarith
  exact (mul_pos_iff_of_pos_right hn2).mp hpos

/-- The {1,2} corridor excludes sink A before any residue-counting argument. -/
theorem two_color12_not_sinkA (D : BoxInput) (N Q : ℤ) (hN : 0 < N) :
    ¬ (0 ≤ Q*D.y 0-N*D.x 0 ∧
      -D.b 1 ≤ N*(D.y 1+D.b 1)-Q*D.x 1-D.b 1) := by
  rintro ⟨hX,hY⟩
  have hx1 := D.x_pos 1
  have hy0 := D.y_pos 0
  have h1 := mul_nonneg (show 0 ≤ D.x 1 by omega) hX
  have h2 := mul_nonneg (show 0 ≤ D.y 0 by omega)
    (show 0 ≤ N*(D.y 1+D.b 1)-Q*D.x 1 by omega)
  have h3 := mul_pos hN D.minor01_pos
  nlinarith

/-- The {1,3} corridor similarly excludes sink B. -/
theorem two_color13_not_sinkB (D : BoxInput) (N R : ℤ) (hN : 0 < N) :
    ¬ (0 ≤ R*(D.y 0+D.b 0)-N*D.x 0 ∧ 0 ≤ N*D.y 2-R*D.x 2) := by
  rintro ⟨hX,hY⟩
  have hx2 := D.x_pos 2
  have hy0 := D.y_pos 0
  have hb0 := D.b_pos 0
  have h1 := mul_nonneg (show 0 ≤ D.x 2 by omega) hX
  have h2 := mul_nonneg (show 0 ≤ D.y 0+D.b 0 by omega) hY
  have h3 := mul_pos hN D.minor02_pos
  nlinarith

end P21.Nonsymmetric.ColorCap.BoxInput

namespace P21.Nonsymmetric.ColorCap.BoxInput

/-- The three in-box source regions are disjoint, so every in-box continuation is unique. -/
theorem in_box_fire_unique (D : BoxInput) (u : Point) (i j : Fin 3)
    (hi : InBox D.upper (fire D.rows i u)) (hj : InBox D.upper (fire D.rows j u)) : i = j := by
  have hi0 := hi 0; have hi1 := hi 1; have hi2 := hi 2
  have hj0 := hj 0; have hj1 := hj 1; have hj2 := hj 2
  have hb0 := D.b_pos 0; have hb1 := D.b_pos 1; have hb2 := D.b_pos 2
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals
    simp [fire,rows,upper] at hi0 hi1 hi2 hj0 hj1 hj2
    omega

end P21.Nonsymmetric.ColorCap.BoxInput
