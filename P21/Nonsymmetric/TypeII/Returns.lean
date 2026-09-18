import P21.Nonsymmetric.TypeII.Setup
import P21.Nonsymmetric.Path.Returns

namespace P21.Nonsymmetric
namespace TypeIIInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

abbrev ActualReturn := PathInput.ActualReturn

private theorem singleton_missing (T : TypeIIInput s F D) (i : Fin 3) (hi : i ≠ 0) :
    i ∉ g.SH T.qS := by
  rw [T.singleton]
  simpa using hi

/-- Genuine actual return of the singleton in direction 1. -/
theorem singleton_n1_return (T : TypeIIInput s F D) :
    Nonempty (ActualReturn g T.qS 1) :=
  PathInput.actual_return_exists 1 (T.actual 0) (singleton_missing T 1 (by decide))

/-- Genuine actual return of the singleton in direction 2. -/
theorem singleton_n2_return (T : TypeIIInput s F D) :
    Nonempty (ActualReturn g T.qS 2) :=
  PathInput.actual_return_exists 2 (T.actual 0) (singleton_missing T 2 (by decide))

theorem sj_equation (T : TypeIIInput s F D) (SJ : ActualReturn g T.qS 1) :
    (SJ.factorization.coeff 0 : ℤ) * g.m +
      (SJ.factorization.coeff 1 : ℤ) * g.n 0 +
      (SJ.factorization.coeff 3 : ℤ) * g.n 2 = T.qS + g.n 1 := by
  have h := SJ.factorization.equation
  have hz : SJ.factorization.coeff 2 = 0 := by simpa using SJ.direction_zero
  simp [value, Generators.all, Fin.sum_univ_succ, hz] at h
  linarith

theorem sk_equation (T : TypeIIInput s F D) (SK : ActualReturn g T.qS 2) :
    (SK.factorization.coeff 0 : ℤ) * g.m +
      (SK.factorization.coeff 1 : ℤ) * g.n 0 +
      (SK.factorization.coeff 2 : ℤ) * g.n 1 = T.qS + g.n 2 := by
  have h := SK.factorization.equation
  have hz : SK.factorization.coeff 3 = 0 := by simpa using SK.direction_zero
  simp [value, Generators.all, Fin.sum_univ_succ, hz] at h
  linarith

/-- JR is a signed identity derived from the actual SJ return. -/
theorem JR (T : TypeIIInput s F D) (SJ : ActualReturn g T.qS 1) :
    (SJ.factorization.coeff 0 : ℤ) * g.m =
      -((SJ.factorization.coeff 1 : ℤ) + 1) * g.n 0 +
      T.R * g.n 1 +
      (T.T0 - 1 - SJ.factorization.coeff 3) * g.n 2 := by
  have hs := T.sj_equation SJ
  have hq := T.qS_eq
  linear_combination hs + hq

/-- KR is a signed identity derived from the actual SK return. -/
theorem KR (T : TypeIIInput s F D) (SK : ActualReturn g T.qS 2) :
    (SK.factorization.coeff 0 : ℤ) * g.m =
      -((SK.factorization.coeff 1 : ℤ) + 1) * g.n 0 +
      (T.R - 1 - SK.factorization.coeff 2) * g.n 1 +
      T.T0 * g.n 2 := by
  have hs := T.sk_equation SK
  have hq := T.qS_eq
  linear_combination hs + hq

end TypeIIInput
end P21.Nonsymmetric
