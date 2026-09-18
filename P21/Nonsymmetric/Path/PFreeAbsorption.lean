import P21.Nonsymmetric.Path.PFreeSign

namespace P21.Nonsymmetric
namespace PathInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

namespace PFreeI

theorem left_j_equation (P : PathInput s F D) (LJ : ActualReturn g P.qL 1) :
    (LJ.factorization.coeff 0 : ℤ) * g.m +
      (LJ.factorization.coeff 1 : ℤ) * g.n 0 +
      (LJ.factorization.coeff 3 : ℤ) * g.n 2 = P.qL + g.n 1 := by
  have h := LJ.factorization.equation
  have hz : LJ.factorization.coeff 2 = 0 := by simpa using LJ.direction_zero
  simp [value, Generators.all, Fin.sum_univ_succ, hz] at h
  linarith

theorem left_k_equation (P : PathInput s F D) (LK : ActualReturn g P.qL 2) :
    (LK.factorization.coeff 0 : ℤ) * g.m +
      (LK.factorization.coeff 1 : ℤ) * g.n 0 +
      (LK.factorization.coeff 2 : ℤ) * g.n 1 = P.qL + g.n 2 := by
  have h := LK.factorization.equation
  have hz : LK.factorization.coeff 3 = 0 := by simpa using LK.direction_zero
  simp [value, Generators.all, Fin.sum_univ_succ, hz] at h
  linarith

theorem left_j_C_cert (P : PathInput s F D) (p : PFreeI P)
    (LJ : ActualReturn g P.qL 1) :
    F = ((LJ.factorization.coeff 0 : ℤ) - 1) * g.m +
      (P.beta + LJ.factorization.coeff 1) * g.n 0 +
      ((D.rho 1 : ℤ) - 1) * g.n 1 +
      ((LJ.factorization.coeff 3 : ℤ) - D.b 2) * g.n 2 := by
  have hr := left_j_equation P LJ
  have hc := P.cL
  change F + g.m - P.qL = P.P0 * g.n 0 at hc
  have hP := P.P0_eq
  linear_combination hc - hr + g.n 0 * hP - D.relation_one

theorem left_j_signed (P : PathInput s F D) (p : PFreeI P)
    (LJ : ActualReturn g P.qL 1) :
    P.qL = ((LJ.factorization.coeff 0 : ℤ) - 1) * g.m +
      ((LJ.factorization.coeff 1 : ℤ) - p.D0 P) * g.n 0 +
      (p.E0 D - 1) * g.n 1 +
      ((LJ.factorization.coeff 3 : ℤ) + p.F0 D P) * g.n 2 := by
  have hr := left_j_equation P LJ
  have hm := p.Mminus P
  linear_combination -hr + hm

theorem left_j_fabs (P : PathInput s F D) (p : PFreeI P)
    (LJ : ActualReturn g P.qL 1) :
    F = ((LJ.factorization.coeff 0 : ℤ) - 2) * g.m +
      (P.P0 + LJ.factorization.coeff 1 - p.D0 P) * g.n 0 +
      (p.E0 D - 1) * g.n 1 +
      ((LJ.factorization.coeff 3 : ℤ) + p.F0 D P) * g.n 2 := by
  have hq := p.left_j_signed P LJ
  have hc := P.cL
  change F + g.m - P.qL = P.P0 * g.n 0 at hc
  linear_combination hc + hq

theorem left_j_caps (P : PathInput s F D) (hF : s.semigroup.IsFrobenius F)
    (p : PFreeI P) (hF0 : 1 ≤ p.F0 D P) (LJ : ActualReturn g P.qL 1) :
    (LJ.factorization.coeff 3 : ℤ) ≤ D.b 2 - 1 ∧
      (LJ.factorization.coeff 1 : ℤ) ≤ p.D0 P - 1 := by
  constructor
  · by_contra hn
    have hcert := p.left_j_C_cert P LJ
    have hmem := gamma_of_coordinates g F
      ((LJ.factorization.coeff 0 : ℤ) - 1)
      (P.beta + LJ.factorization.coeff 1)
      ((D.rho 1 : ℤ) - 1)
      ((LJ.factorization.coeff 3 : ℤ) - D.b 2)
      (by have := LJ.level_pos; omega) (by have := P.beta_pos; omega)
      (by have := D.rho_pos 1; omega) (by omega) hcert
    exact hF.1 hmem
  · by_contra hn
    have hcert := p.left_j_signed P LJ
    have hmem := gamma_of_coordinates g P.qL
      ((LJ.factorization.coeff 0 : ℤ) - 1)
      ((LJ.factorization.coeff 1 : ℤ) - p.D0 P)
      (p.E0 D - 1)
      ((LJ.factorization.coeff 3 : ℤ) + p.F0 D P)
      (by have := LJ.level_pos; omega) (by omega)
      (by have := D.b_pos 1; simp only [E0]; omega) (by omega) hcert
    exact (P.actual 0).1.1 hmem

/-- P5.5: the first left return is forced to unit m-level. -/
theorem left_j_level_one (P : PathInput s F D) (hF : s.semigroup.IsFrobenius F)
    (p : PFreeI P) (LJ : ActualReturn g P.qL 1) :
    LJ.factorization.coeff 0 = 1 := by
  have hF0 := p.F0_pos P hF
  have caps := p.left_j_caps P hF hF0 LJ
  by_contra hn
  have hlvl : 2 ≤ LJ.factorization.coeff 0 := by
    have := LJ.level_pos
    omega
  have hcert := p.left_j_fabs P LJ
  have hP : P.P0 + (LJ.factorization.coeff 1 : ℤ) - p.D0 P =
      (LJ.factorization.coeff 1 : ℤ) + p.Y + 1 := by
    simp [D0]
    ring
  have hmem := gamma_of_coordinates g F
    ((LJ.factorization.coeff 0 : ℤ) - 2)
    (P.P0 + LJ.factorization.coeff 1 - p.D0 P)
    (p.E0 D - 1)
    ((LJ.factorization.coeff 3 : ℤ) + p.F0 D P)
    (by omega) (by rw [hP]; omega)
    (by have := D.b_pos 1; simp only [E0]; omega) (by omega) hcert
  exact hF.1 hmem

end PFreeI
end PathInput
end P21.Nonsymmetric
