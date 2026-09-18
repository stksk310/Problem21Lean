import P21.Nonsymmetric.Path.Returns

namespace P21.Nonsymmetric

/-- PATH left-right reversal: tail coordinates `0` and `2` are exchanged and
coordinate `1` is fixed. -/
def pathReversePerm : Equiv.Perm (Fin 3) where
  toFun := ![2, 1, 0]
  invFun := ![2, 1, 0]
  left_inv i := by fin_cases i <;> decide
  right_inv i := by fin_cases i <;> decide

@[simp] theorem pathReversePerm_self (i : Fin 3) :
    pathReversePerm (pathReversePerm i) = i := by
  fin_cases i <;> rfl

@[simp] theorem pathReversePerm_zero : pathReversePerm 0 = 2 := rfl
@[simp] theorem pathReversePerm_one : pathReversePerm 1 = 1 := rfl
@[simp] theorem pathReversePerm_two : pathReversePerm 2 = 0 := rfl

/-- Exact Herzog transport used by PATH duality.  Reversal exchanges the two
critical colors as well as the endpoint coordinates. -/
def pathReverseHerzog {g : Generators} (D : HerzogCriticalData g) :
    HerzogCriticalData (relabel g pathReversePerm) where
  a j := D.b (pathReversePerm j)
  b j := D.a (pathReversePerm j)
  rho j := D.rho (pathReversePerm j)
  a_pos j := D.b_pos _
  b_pos j := D.a_pos _
  rho_eq j := by rw [D.rho_eq]; omega
  relation_zero := by
    simpa [relabel, pathReversePerm, add_comm] using D.relation_two
  relation_one := by
    simpa [relabel, pathReversePerm, add_comm] using D.relation_one
  relation_two := by
    simpa [relabel, pathReversePerm, add_comm] using D.relation_zero
  critical j := relabelCritical pathReversePerm j (D.critical _)
  coeff_rho j := D.coeff_rho _

@[simp] theorem pathReverseHerzog_fA {g : Generators} (D : HerzogCriticalData g) :
    (pathReverseHerzog D).fA = D.fB := by
  have h := D.fB_cyclic 2
  change (D.rho 2 - 1 : ℤ) * g.n 2 + (D.b 1 - 1 : ℤ) * g.n 1 - g.n 0 = D.fB
  rw [h]
  simp [next, prev]
  ring

@[simp] theorem pathReverseHerzog_fB {g : Generators} (D : HerzogCriticalData g) :
    (pathReverseHerzog D).fB = D.fA := by
  have h := D.fA_cyclic 2
  change (D.rho 2 - 1 : ℤ) * g.n 2 - g.n 1 + (D.a 0 - 1 : ℤ) * g.n 0 = D.fA
  rw [h]
  simp [next, prev]
  ring

namespace PathInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

private def reverseFourPerm : Equiv.Perm (Fin 4) where
  toFun := ![3, 2, 1, 0]
  invFun := ![3, 2, 1, 0]
  left_inv i := by fin_cases i <;> decide
  right_inv i := by fin_cases i <;> decide

/-- Full PATH transport.  It preserves the underlying semigroup and the four
actual integers, reverses their chronological ladder positions, and transports
every singleton, missing-direction, range, complement, and ladder field. -/
def reverse (P : PathInput s F D) :
    PathInput (relabelSetting s pathReversePerm) F (pathReverseHerzog D) where
  lambda := P.nu
  nu := P.lambda
  R := P.R
  qL := P.qR
  qA := P.qB
  qB := P.qA
  qR := P.qL
  actual t := by
    have h := P.actual (reverseFourPerm t)
    change (![P.qR, P.qB, P.qA, P.qL] t) ∈
      (relabelSetting s pathReversePerm).semigroup.Q F
    rw [relabel_Q]
    fin_cases t <;> simpa [reverseFourPerm] using h
  distinct := by
    intro i j hij
    have h : (![P.qL, P.qA, P.qB, P.qR] : Fin 4 → ℤ) (reverseFourPerm i) =
        (![P.qL, P.qA, P.qB, P.qR] : Fin 4 → ℤ) (reverseFourPerm j) := by
      fin_cases i <;> fin_cases j <;> simpa [reverseFourPerm] using hij
    exact reverseFourPerm.injective (P.distinct h)
  left_singleton := by
    rw [relabel_singleton_iff]
    simpa [pathReversePerm] using P.right_singleton
  right_singleton := by
    rw [relabel_singleton_iff]
    simpa [pathReversePerm] using P.left_singleton
  A_eq := by
    rw [pathReverseHerzog_fA]
    simpa [relabel, pathReversePerm] using P.B_eq
  B_eq := by
    rw [pathReverseHerzog_fB]
    simpa [relabel, pathReversePerm] using P.A_eq
  A_missing := by
    change (2 : Fin 3) ∉ (relabel g pathReversePerm).SH P.qB
    simpa [relabel_SH, pathReversePerm] using P.B_missing
  B_missing := by
    change (0 : Fin 3) ∉ (relabel g pathReversePerm).SH P.qA
    simpa [relabel_SH, pathReversePerm] using P.A_missing
  lambda_range := by simpa [pathReverseHerzog, pathReversePerm] using P.nu_range
  nu_range := by simpa [pathReverseHerzog, pathReversePerm] using P.lambda_range
  R_range := by simpa [pathReverseHerzog, pathReversePerm] using P.R_range
  cL := by simpa [relabel, pathReverseHerzog, pathReversePerm] using P.cR
  cA := by
    simpa [relabel, pathReverseHerzog, pathReversePerm, add_comm] using P.cB
  cB := by
    simpa [relabel, pathReverseHerzog, pathReversePerm, add_comm] using P.cA
  cR := by simpa [relabel, pathReverseHerzog, pathReversePerm] using P.cL
  boxW := by
    simpa [relabel, pathReverseHerzog, pathReversePerm, add_comm, add_left_comm,
      add_assoc] using P.boxW
  ladder_left := by
    simpa [relabel, pathReverseHerzog, pathReversePerm, add_comm] using P.ladder_right
  ladder_middle := by
    simpa [relabel, pathReverseHerzog, pathReversePerm, add_comm] using P.ladder_middle.symm
  ladder_right := by
    simpa [relabel, pathReverseHerzog, pathReversePerm, add_comm] using P.ladder_left

end PathInput
end P21.Nonsymmetric
