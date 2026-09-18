import P21.Nonsymmetric.Path.PFreeCoordinates

namespace P21.Nonsymmetric
namespace PathInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

namespace PFreeI

/-- RIGHT-I, extracted from the named actual return without losing provenance. -/
theorem right_i_equation (P : PathInput s F D) (RI : ActualReturn g P.qR 0) :
    (RI.factorization.coeff 0 : ℤ) * g.m +
      (RI.factorization.coeff 2 : ℤ) * g.n 1 +
      (RI.factorization.coeff 3 : ℤ) * g.n 2 = P.qR + g.n 0 := by
  have h := RI.factorization.equation
  have hz : RI.factorization.coeff 1 = 0 := by simpa using RI.direction_zero
  simp [value, Generators.all, Fin.sum_univ_succ, hz, add_assoc] at h
  linarith

/-- RIGHT-J, extracted from the named actual return without losing provenance. -/
theorem right_j_equation (P : PathInput s F D) (RJ : ActualReturn g P.qR 1) :
    (RJ.factorization.coeff 0 : ℤ) * g.m +
      (RJ.factorization.coeff 1 : ℤ) * g.n 0 +
      (RJ.factorization.coeff 3 : ℤ) * g.n 2 = P.qR + g.n 1 := by
  have h := RJ.factorization.equation
  have hz : RJ.factorization.coeff 2 = 0 := by simpa using RJ.direction_zero
  simp [value, Generators.all, Fin.sum_univ_succ, hz, add_assoc] at h
  linarith

theorem T_bounds_of_F0_nonpos (P : PathInput s F D) (p : PFreeI P)
    (hF0 : p.F0 D P ≤ 0) :
    (D.a 2 : ℤ) + 1 ≤ P.T ∧ (D.b 2 : ℤ) + 1 ≤ P.T := by
  have hsum := p.C0_add_F0 P
  have hT := P.T_eq
  have halpha := P.alpha_pos
  have hK : 0 ≤ (p.K : ℤ) := by omega
  simp only [C0] at hsum
  constructor
  · omega
  · omega

/-- J-FABS: a level-two RIGHT-J return gives an actual factorization of F. -/
theorem j_fabs (P : PathInput s F D) (p : PFreeI P)
    (RJ : ActualReturn g P.qR 1) :
    F = ((RJ.factorization.coeff 0 : ℤ) - 2) * g.m +
      ((RJ.factorization.coeff 1 : ℤ) + p.A0 P) * g.n 0 +
      (p.H0 : ℤ) * g.n 1 +
      (P.T + RJ.factorization.coeff 3 - p.C0 P) * g.n 2 := by
  have hr := right_j_equation P RJ
  have hc := P.cR
  change F + g.m - P.qR = P.T * g.n 2 at hc
  have hm := p.Mplus P
  have hB : p.B0 = (p.H0 : ℤ) + 1 := by simp [B0]
  rw [hB] at hm
  linear_combination hc - hr + hm

/-- I-FABS: a level-two RIGHT-I return gives an actual factorization of F. -/
theorem i_fabs (P : PathInput s F D) (p : PFreeI P)
    (RI : ActualReturn g P.qR 0) :
    F = ((RI.factorization.coeff 0 : ℤ) - 2) * g.m +
      (p.A0 P - 1) * g.n 0 +
      ((RI.factorization.coeff 2 : ℤ) + p.H0 + 1) * g.n 1 +
      (P.T + RI.factorization.coeff 3 - p.C0 P) * g.n 2 := by
  have hr := right_i_equation P RI
  have hc := P.cR
  change F + g.m - P.qR = P.T * g.n 2 at hc
  have hm := p.Mplus P
  have hB : p.B0 = (p.H0 : ℤ) + 1 := by simp [B0]
  rw [hB] at hm
  linear_combination hc - hr + hm

/-- U-CERT, kept as a signed identity until every coefficient is checked. -/
theorem u_cert (P : PathInput s F D) (p : PFreeI P)
    (RI : ActualReturn g P.qR 0) :
    F = ((RI.factorization.coeff 0 : ℤ) - 1) * g.m +
      ((D.rho 0 : ℤ) - 1) * g.n 0 +
      ((RI.factorization.coeff 2 : ℤ) - D.b 1) * g.n 1 +
      (P.T + RI.factorization.coeff 3 - D.a 2) * g.n 2 := by
  have hr := right_i_equation P RI
  have hc := P.cR
  change F + g.m - P.qR = P.T * g.n 2 at hc
  linear_combination hc - hr - D.relation_zero

/-- X-CERT, kept as a signed identity until every coefficient is checked. -/
theorem x_cert (P : PathInput s F D) (p : PFreeI P)
    (RJ : ActualReturn g P.qR 1) :
    F = ((RJ.factorization.coeff 0 : ℤ) - 1) * g.m +
      ((RJ.factorization.coeff 1 : ℤ) - D.a 0) * g.n 0 +
      ((D.rho 1 : ℤ) - 1) * g.n 1 +
      (P.T + RJ.factorization.coeff 3 - D.b 2) * g.n 2 := by
  have hr := right_j_equation P RJ
  have hc := P.cR
  change F + g.m - P.qR = P.T * g.n 2 at hc
  linear_combination hc - hr - D.relation_one

/-- Publication P5.4: the signed coefficient in M- is genuinely positive. -/
theorem F0_pos (P : PathInput s F D) (hF : s.semigroup.IsFrobenius F)
    (p : PFreeI P) : 1 ≤ p.F0 D P := by
  by_contra hn
  have hF0 : p.F0 D P ≤ 0 := by omega
  have hT := p.T_bounds_of_F0_nonpos P hF0
  obtain ⟨RI⟩ := P.qR_n0_return
  obtain ⟨RJ⟩ := P.qR_n1_return
  have hs : RI.factorization.coeff 0 = 1 := by
    by_contra hne
    have hs2 : 2 ≤ RI.factorization.coeff 0 := by
      have := RI.level_pos
      omega
    have hcert := p.i_fabs P RI
    have htail : 0 ≤ P.T + (RI.factorization.coeff 3 : ℤ) - p.C0 P := by
      have hK : 0 ≤ (p.K : ℤ) := by omega
      simp only [C0]
      omega
    have hmem := gamma_of_coordinates g F
      ((RI.factorization.coeff 0 : ℤ) - 2)
      (p.A0 P - 1)
      ((RI.factorization.coeff 2 : ℤ) + p.H0 + 1)
      (P.T + RI.factorization.coeff 3 - p.C0 P)
      (by omega) (by have := p.A0_pos P; omega) (by omega) htail hcert
    exact hF.1 hmem
  have hr : RJ.factorization.coeff 0 = 1 := by
    by_contra hne
    have hr2 : 2 ≤ RJ.factorization.coeff 0 := by
      have := RJ.level_pos
      omega
    have hcert := p.j_fabs P RJ
    have htail : 0 ≤ P.T + (RJ.factorization.coeff 3 : ℤ) - p.C0 P := by
      have hK : 0 ≤ (p.K : ℤ) := by omega
      simp only [C0]
      omega
    have hmem := gamma_of_coordinates g F
      ((RJ.factorization.coeff 0 : ℤ) - 2)
      ((RJ.factorization.coeff 1 : ℤ) + p.A0 P)
      p.H0
      (P.T + RJ.factorization.coeff 3 - p.C0 P)
      (by omega) (by have := p.A0_pos P; omega) (by omega) htail hcert
    exact hF.1 hmem
  have hU : (RI.factorization.coeff 2 : ℤ) ≤ D.b 1 - 1 := by
    by_contra hUn
    have hcert := p.u_cert P RI
    have hmem := gamma_of_coordinates g F
      ((RI.factorization.coeff 0 : ℤ) - 1)
      ((D.rho 0 : ℤ) - 1)
      ((RI.factorization.coeff 2 : ℤ) - D.b 1)
      (P.T + RI.factorization.coeff 3 - D.a 2)
      (by omega) (by have := D.rho_pos 0; omega) (by omega) (by omega) hcert
    exact hF.1 hmem
  have hX : (RJ.factorization.coeff 1 : ℤ) ≤ D.a 0 - 1 := by
    by_contra hXn
    have hcert := p.x_cert P RJ
    have hmem := gamma_of_coordinates g F
      ((RJ.factorization.coeff 0 : ℤ) - 1)
      ((RJ.factorization.coeff 1 : ℤ) - D.a 0)
      ((D.rho 1 : ℤ) - 1)
      (P.T + RJ.factorization.coeff 3 - D.b 2)
      (by omega) (by omega) (by have := D.rho_pos 1; omega) (by omega) hcert
    exact hF.1 hmem
  have hdiff : ((RJ.factorization.coeff 1 : ℤ) + 1) * g.n 0 =
      ((RI.factorization.coeff 2 : ℤ) + 1) * g.n 1 +
      ((RI.factorization.coeff 3 : ℤ) - RJ.factorization.coeff 3) * g.n 2 := by
    have hi := right_i_equation P RI
    have hj := right_j_equation P RJ
    rw [hs] at hi
    rw [hr] at hj
    norm_num at hi hj
    linear_combination hj - hi
  by_cases hv : (RJ.factorization.coeff 3 : ℤ) ≤ RI.factorization.coeff 3
  · have hcrit := herzog_critical_le_int D
      (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)
      ((RJ.factorization.coeff 1 : ℤ) + 1)
      ((RI.factorization.coeff 2 : ℤ) + 1)
      ((RI.factorization.coeff 3 : ℤ) - RJ.factorization.coeff 3)
      (by omega) (by omega) (by omega) hdiff
    have hrho := D.rho_eq 0
    have := D.b_pos 0
    omega
  · have hdiff' : ((RI.factorization.coeff 2 : ℤ) + 1) * g.n 1 =
        ((RJ.factorization.coeff 1 : ℤ) + 1) * g.n 0 +
        ((RJ.factorization.coeff 3 : ℤ) - RI.factorization.coeff 3) * g.n 2 := by
      linarith [hdiff]
    have hcrit := herzog_critical_le_int D
      (by decide : (1 : Fin 3) ≠ 0) (by decide : (1 : Fin 3) ≠ 2)
      ((RI.factorization.coeff 2 : ℤ) + 1)
      ((RJ.factorization.coeff 1 : ℤ) + 1)
      ((RJ.factorization.coeff 3 : ℤ) - RI.factorization.coeff 3)
      (by omega) (by omega) (by omega) hdiff'
    have hrho := D.rho_eq 1
    have := D.a_pos 1
    omega

end PFreeI
end PathInput
end P21.Nonsymmetric
