import P21.Nonsymmetric.Chain.C10.State
import Mathlib

namespace P21.Nonsymmetric
namespace EuclideanState

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

theorem ical_pos (X : EuclideanState s F D) : 0 < X.Ical := by
  have ha1 : (0 : ℤ) < D.a 1 := by exact_mod_cast D.a_pos 1
  have ha2 : (0 : ℤ) < D.a 2 := by exact_mod_cast D.a_pos 2
  have hb1 : (0 : ℤ) < D.b 1 := by exact_mod_cast D.b_pos 1
  have hb2 : (0 : ℤ) < D.b 2 := by exact_mod_cast D.b_pos 2
  have hr1 : (D.rho 1 : ℤ) = D.a 1 + D.b 1 := by exact_mod_cast D.rho_eq 1
  have hr2 : (D.rho 2 : ℤ) = D.a 2 + D.b 2 := by exact_mod_cast D.rho_eq 2
  simp only [Ical, hr1, hr2]
  nlinarith [mul_pos ha1 ha2, mul_pos hb1 ha2, mul_pos hb1 hb2]

theorem jcal_pos (X : EuclideanState s F D) : 0 < X.Jcal := by
  have ha0 : (0 : ℤ) < D.a 0 := by exact_mod_cast D.a_pos 0
  have hr2 : (0 : ℤ) < D.rho 2 := by exact_mod_cast D.rho_pos 2
  have hb0 : (0 : ℤ) ≤ D.b 0 := by positivity
  have hb2 : (0 : ℤ) ≤ D.b 2 := by positivity
  simp only [Jcal]
  nlinarith [mul_pos ha0 hr2, mul_nonneg hb0 hb2]

theorem kcal_pos (X : EuclideanState s F D) : 0 < X.Kcal := by
  have hb0 : (0 : ℤ) < D.b 0 := by exact_mod_cast D.b_pos 0
  have hr1 : (0 : ℤ) < D.rho 1 := by exact_mod_cast D.rho_pos 1
  have ha0 : (0 : ℤ) ≤ D.a 0 := by positivity
  have ha1 : (0 : ℤ) ≤ D.a 1 := by positivity
  simp only [Kcal]
  nlinarith [mul_pos hb0 hr1, mul_nonneg ha0 ha1]

theorem jcal_cross (X : EuclideanState s F D) :
    X.Jcal * g.n 0 = X.Ical * g.n 1 := by
  simp only [Jcal, Ical]
  linear_combination -(D.rho 2 : ℤ) * D.relation_one -
    (D.b 2 : ℤ) * D.relation_two

theorem kcal_cross (X : EuclideanState s F D) :
    X.Kcal * g.n 0 = X.Ical * g.n 2 := by
  simp only [Kcal, Ical]
  linear_combination -(D.rho 1 : ℤ) * D.relation_two -
    (D.a 1 : ℤ) * D.relation_one

def sigma (X : EuclideanState s F D) : ℚ := (g.n 0 : ℚ) / (X.Ical : ℚ)

theorem sigma_pos (X : EuclideanState s F D) : 0 < X.sigma := by
  have hn : (0 : ℚ) < g.n 0 := by
    exact_mod_cast lt_trans s.m_pos (s.n_gt 0)
  have hI : (0 : ℚ) < X.Ical := by exact_mod_cast X.ical_pos
  exact div_pos hn hI

theorem ni_scale (X : EuclideanState s F D) :
    (g.n 0 : ℚ) = X.sigma * X.Ical := by
  have hI : (X.Ical : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt X.ical_pos
  simp [sigma, hI]

theorem nj_scale (X : EuclideanState s F D) :
    (g.n 1 : ℚ) = X.sigma * X.Jcal := by
  have hI : (X.Ical : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt X.ical_pos
  rw [sigma]
  field_simp [hI]
  have hcross : (X.Ical : ℚ) * g.n 1 = X.Jcal * g.n 0 := by
    exact_mod_cast X.jcal_cross.symm
  simpa [mul_comm] using hcross

theorem nk_scale (X : EuclideanState s F D) :
    (g.n 2 : ℚ) = X.sigma * X.Kcal := by
  have hI : (X.Ical : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt X.ical_pos
  rw [sigma]
  field_simp [hI]
  have hcross : (X.Ical : ℚ) * g.n 2 = X.Kcal * g.n 0 := by
    exact_mod_cast X.kcal_cross.symm
  simpa [mul_comm] using hcross

theorem cross_product_scale (X : EuclideanState s F D) :
    0 < X.sigma ∧
      (g.n 0 : ℚ) = X.sigma * X.Ical ∧
      (g.n 1 : ℚ) = X.sigma * X.Jcal ∧
      (g.n 2 : ℚ) = X.sigma * X.Kcal :=
  ⟨X.sigma_pos, X.ni_scale, X.nj_scale, X.nk_scale⟩

end EuclideanState
end P21.Nonsymmetric
