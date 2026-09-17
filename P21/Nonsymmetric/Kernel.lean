import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Rat.Floor
import P21.Nonsymmetric.CriticalBox
import P21.Nonsymmetric.HerzogData

namespace P21.Nonsymmetric

/-- The publication's `r_j`, in the fixed coordinate order `(i,j,k)`. -/
def kernelRowJ {g : Generators} (d : HerzogCriticalData g) : Fin 3 → ℤ :=
  ![(d.a 0 : ℤ), -(d.rho 1 : ℤ), (d.b 2 : ℤ)]

/-- The publication's `r_k`, in the fixed coordinate order `(i,j,k)`. -/
def kernelRowK {g : Generators} (d : HerzogCriticalData g) : Fin 3 → ℤ :=
  ![(d.b 0 : ℤ), (d.a 1 : ℤ), -(d.rho 2 : ℤ)]

theorem kernelRowJ_mem {g : Generators} (d : HerzogCriticalData g) :
    integerValue g (kernelRowJ d) = 0 := by
  simp [integerValue, kernelRowJ, Fin.sum_univ_succ]
  linarith [d.relation_one]

theorem kernelRowK_mem {g : Generators} (d : HerzogCriticalData g) :
    integerValue g (kernelRowK d) = 0 := by
  simp [integerValue, kernelRowK, Fin.sum_univ_succ]
  linarith [d.relation_two]

/-- Strict positivity of the two by two minor; no primitive-generator or
pairwise-coprimality assumption is needed. -/
theorem kernel_minor_pos {g : Generators} (d : HerzogCriticalData g) :
    0 < (d.rho 1 : ℤ) * d.rho 2 - (d.a 1 : ℤ) * d.b 2 := by
  have ha1 : (0 : ℤ) < d.a 1 := by exact_mod_cast d.a_pos 1
  have hb1 : (0 : ℤ) < d.b 1 := by exact_mod_cast d.b_pos 1
  have ha2 : (0 : ℤ) < d.a 2 := by exact_mod_cast d.a_pos 2
  have hb2 : (0 : ℤ) < d.b 2 := by exact_mod_cast d.b_pos 2
  rw [d.rho_eq 1, d.rho_eq 2]
  push_cast
  nlinarith

/-- The two displayed integer kernel vectors are independent over the integers. -/
theorem kernel_rows_independent {g : Generators} (d : HerzogCriticalData g)
    {s t : ℤ} (he : ∀ i, s * kernelRowJ d i + t * kernelRowK d i = 0) :
    s = 0 ∧ t = 0 := by
  have h1 := he 1
  have h2 := he 2
  simp [kernelRowJ, kernelRowK] at h1 h2
  have hd := kernel_minor_pos d
  have hs : s * ((d.rho 1 : ℤ) * d.rho 2 - (d.a 1 : ℤ) * d.b 2) = 0 := by
    nlinarith [h1, h2]
  have hsz : s = 0 := (mul_eq_zero.mp hs).resolve_right (ne_of_gt hd)
  subst s
  have ha : (0 : ℤ) < d.a 1 := by exact_mod_cast d.a_pos 1
  constructor
  · rfl
  · nlinarith



/-- Rational spanning is elementary elimination in the nonzero minor. The
integer saturation step below is separate. -/
theorem kernel_span_rat {g : Generators} (hpos : ∀ i, 0 < g.n i)
    (d : HerzogCriticalData g) (v : Fin 3 → ℤ) (hv : integerValue g v = 0) :
    ∃ s t : ℚ, ∀ i, (v i : ℚ) = s * (kernelRowJ d i : ℚ) + t * (kernelRowK d i : ℚ) := by
  let D : ℚ := (d.rho 1 : ℚ) * d.rho 2 - (d.a 1 : ℚ) * d.b 2
  have hD : D ≠ 0 := ne_of_gt (show 0 < D by dsimp [D]; exact_mod_cast kernel_minor_pos d)
  let s : ℚ := (-(d.rho 2 : ℚ) * v 1 - (d.a 1 : ℚ) * v 2) / D
  let t : ℚ := (-(d.b 2 : ℚ) * v 1 - (d.rho 1 : ℚ) * v 2) / D
  have h1 : (v 1 : ℚ) = s * (-(d.rho 1 : ℚ)) + t * (d.a 1 : ℚ) := by
    dsimp [s, t]; field_simp [hD]; dsimp [D]; ring
  have h2 : (v 2 : ℚ) = s * (d.b 2 : ℚ) + t * (-(d.rho 2 : ℚ)) := by
    dsimp [s, t]; field_simp [hD]; dsimp [D]; ring
  have he : (v 0 : ℚ) * g.n 0 + (v 1 : ℚ) * g.n 1 + (v 2 : ℚ) * g.n 2 = 0 := by
    exact_mod_cast (show v 0 * g.n 0 + v 1 * g.n 1 + v 2 * g.n 2 = 0 by
      simpa [integerValue, Fin.sum_univ_succ, add_assoc] using hv)
  have hr1 : (d.rho 1 : ℚ) * g.n 1 = (d.a 0 : ℚ) * g.n 0 + (d.b 2 : ℚ) * g.n 2 := by
    exact_mod_cast d.relation_one
  have hr2 : (d.rho 2 : ℚ) * g.n 2 = (d.b 0 : ℚ) * g.n 0 + (d.a 1 : ℚ) * g.n 1 := by
    exact_mod_cast d.relation_two
  have hz : ((v 0 : ℚ) - (s * d.a 0 + t * d.b 0)) * g.n 0 = 0 := by
    linear_combination he - (g.n 1 : ℚ) * h1 - (g.n 2 : ℚ) * h2 + s * hr1 + t * hr2
  have hn0 : (g.n 0 : ℚ) ≠ 0 := ne_of_gt (by exact_mod_cast hpos 0)
  have h0 := (mul_eq_zero.mp hz).resolve_right hn0
  refine ⟨s, t, ?_⟩
  intro i
  fin_cases i <;> simp [kernelRowJ, kernelRowK] <;> first | exact h1 | exact h2 | linarith




/-- The displayed rows span the entire integer kernel. The proof reduces the
rational coefficients modulo integers and applies critical-box uniqueness to
the remaining integer vector, thereby proving saturation rather than assuming it. -/
theorem integer_kernel_span {g : Generators} (hpos : ∀ i, 0 < g.n i)
    (d : HerzogCriticalData g) (v : Fin 3 → ℤ) (hv : integerValue g v = 0) :
    ∃ s t : ℤ, ∀ i, v i = s * kernelRowJ d i + t * kernelRowK d i := by
  obtain ⟨s, t, hst⟩ := kernel_span_rat hpos d v hv
  let S : ℤ := ⌊s⌋
  let T : ℤ := ⌊t⌋
  let x : ℚ := s - S
  let y : ℚ := t - T
  have hx0 : 0 ≤ x := by exact Int.fract_nonneg s
  have hy0 : 0 ≤ y := by exact Int.fract_nonneg t
  have hx1 : x < 1 := by exact Int.fract_lt_one s
  have hy1 : y < 1 := by exact Int.fract_lt_one t
  let w : Fin 3 → ℤ := fun i => v i - S * kernelRowJ d i - T * kernelRowK d i
  have hw : integerValue g w = 0 := by
    dsimp [w, integerValue]
    simp only [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
    change integerValue g v - S * integerValue g (kernelRowJ d) - T * integerValue g (kernelRowK d) = 0
    rw [hv, kernelRowJ_mem, kernelRowK_mem]
    ring
  have hwq (i : Fin 3) : (w i : ℚ) = x * (kernelRowJ d i : ℚ) + y * (kernelRowK d i : ℚ) := by
    dsimp [w, x, y]
    push_cast
    rw [hst i]
    ring
  have ha (i : Fin 3) : (0 : ℚ) < d.a i := by exact_mod_cast d.a_pos i
  have hb (i : Fin 3) : (0 : ℚ) < d.b i := by exact_mod_cast d.b_pos i
  have hr (i : Fin 3) : (d.rho i : ℚ) = (d.a i : ℚ) + d.b i := by exact_mod_cast d.rho_eq i
  have hbound : ∀ i, -(d.rho i : ℚ) < (w i : ℚ) ∧ (w i : ℚ) < (d.rho i : ℚ) := by
    intro i
    rw [hwq]
    fin_cases i
    · norm_num [kernelRowJ, kernelRowK]
      have ha0 := ha 0
      have hb0 := hb 0
      simp only [hr]
      constructor <;> nlinarith
    · norm_num [kernelRowJ, kernelRowK]
      have ha1 := ha 1
      have hb1 := hb 1
      simp only [hr]
      constructor <;> nlinarith
    · have hc : -(d.rho 2 : ℚ) < x * (d.b 2 : ℚ) + y * (-(d.rho 2 : ℚ)) ∧
          x * (d.b 2 : ℚ) + y * (-(d.rho 2 : ℚ)) < (d.rho 2 : ℚ) := by
        have ha2 := ha 2
        have hb2 := hb 2
        have hr2 := hr 2
        have hp : (0 : ℚ) < d.rho 2 := by linarith
        constructor <;> nlinarith [mul_nonneg hx0 hb2.le,
          mul_nonneg hy0 hp.le, mul_lt_mul_of_pos_right hy1 hp,
          mul_lt_mul_of_pos_right hx1 hb2]
      simpa [kernelRowJ, kernelRowK] using hc
  have hwzero := critical_kernel_box_zero hpos d.critical w hw
    (by intro i; rw [d.coeff_rho]; exact_mod_cast (hbound i).1)
    (by intro i; rw [d.coeff_rho]; exact_mod_cast (hbound i).2)
  refine ⟨S, T, ?_⟩
  intro i
  have := congrFun hwzero i
  change v i - S * kernelRowJ d i - T * kernelRowK d i = 0 at this
  omega

/-- Exact integer-basis statement: every integer kernel vector has unique
integer coordinates in the two publication rows. -/
theorem integer_kernel_basis {g : Generators} (hpos : ∀ i, 0 < g.n i)
    (d : HerzogCriticalData g) (v : Fin 3 → ℤ) (hv : integerValue g v = 0) :
    ∃! st : ℤ × ℤ, ∀ i, v i = st.1 * kernelRowJ d i + st.2 * kernelRowK d i := by
  obtain ⟨s, t, hst⟩ := integer_kernel_span hpos d v hv
  refine ⟨(s, t), hst, ?_⟩
  rintro ⟨s', t'⟩ he
  have hz : ∀ i, (s' - s) * kernelRowJ d i + (t' - t) * kernelRowK d i = 0 := by
    intro i
    have h1 := hst i
    have h2 := he i
    dsimp at h2
    nlinarith
  obtain ⟨hs, ht⟩ := kernel_rows_independent d hz
  have : s' = s := by omega
  have : t' = t := by omega
  simp_all

end P21.Nonsymmetric







