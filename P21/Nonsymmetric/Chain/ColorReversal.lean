import P21.Nonsymmetric.Chain.Root

namespace P21.Nonsymmetric
namespace ChainInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

def reverseFour : Equiv.Perm (Fin 4) where
  toFun := ![3, 2, 1, 0]
  invFun := ![3, 2, 1, 0]
  left_inv i := by fin_cases i <;> decide
  right_inv i := by fin_cases i <;> decide

/-- The full CHAIN color reversal: tail directions 1 and 2 are exchanged and
the Herzog colors are reversed. -/
def reverseChain (C : ChainInput s F D) :
    ChainInput (relabelSetting s reversePerm) F (reverseHerzog D) where
  lambda := C.lambda
  mu := C.nu
  nu := C.mu
  actual := by
    intro t
    rw [relabel_Q]
    fin_cases t
    · rw [reverseHerzog_fB]
      simpa [relabel, reversePerm] using C.actual 3
    · rw [reverseHerzog_fA]
      simpa [relabel, reversePerm] using C.actual 2
    · rw [reverseHerzog_fB]
      simpa [relabel, reversePerm] using C.actual 1
    · rw [reverseHerzog_fA]
      simpa [relabel, reversePerm] using C.actual 0
  distinct := by
    intro x y h
    apply reverseFour.injective
    apply C.distinct
    fin_cases x <;> fin_cases y <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, reverseFour] at h ⊢ <;>
      simp only [reverseHerzog_fA, reverseHerzog_fB] at h <;>
      simpa [relabel, reversePerm] using h
  Bj_missing := by
    rw [relabel_SH, reverseHerzog_fB]
    simpa [relabel, reversePerm] using C.Ak_missing
  Ai_missing := by
    rw [relabel_SH, reverseHerzog_fA]
    simpa [relabel, reversePerm] using C.Bi_missing
  Bi_missing := by
    rw [relabel_SH, reverseHerzog_fB]
    simpa [relabel, reversePerm] using C.Ai_missing
  Ak_missing := by
    rw [relabel_SH, reverseHerzog_fA]
    simpa [relabel, reversePerm] using C.Bj_missing
  lambda_range := by
    simpa [reverseHerzog, reversePerm] using
      ⟨C.lambda_range.1, C.lambda_range.2.2, C.lambda_range.2.1⟩
  mu_range := by simpa [reverseHerzog, reversePerm] using C.nu_range
  nu_range := by simpa [reverseHerzog, reversePerm] using C.mu_range
  cBj := by
    rw [reverseHerzog_fB]
    simpa [reverseHerzog, relabel, reversePerm, add_comm] using C.cAk
  cAi := by
    rw [reverseHerzog_fA]
    simpa [reverseHerzog, relabel, reversePerm, add_comm] using C.cBi
  cBi := by
    rw [reverseHerzog_fB]
    simpa [reverseHerzog, relabel, reversePerm, add_comm] using C.cAi
  cAk := by
    rw [reverseHerzog_fA]
    simpa [reverseHerzog, relabel, reversePerm, add_comm] using C.cBj
  boxW := by
    simpa [reverseHerzog, relabel, reversePerm, add_comm, add_left_comm, add_assoc] using C.boxW

@[simp] theorem reverseChain_lambda (C : ChainInput s F D) : C.reverseChain.lambda = C.lambda := rfl
@[simp] theorem reverseChain_delta (C : ChainInput s F D) : C.reverseChain.delta = C.beta := by
  rfl
@[simp] theorem reverseChain_beta (C : ChainInput s F D) : C.reverseChain.beta = C.delta := by
  rfl
@[simp] theorem reverseChain_gapJ (C : ChainInput s F D) : C.reverseChain.gapJ = C.alpha := by
  rfl
@[simp] theorem reverseChain_alpha (C : ChainInput s F D) : C.reverseChain.alpha = C.gapJ := by
  rfl
@[simp] theorem reverseChain_P (C : ChainInput s F D) : C.reverseChain.P = C.P := by
  rfl
@[simp] theorem reverseChain_R (C : ChainInput s F D) : C.reverseChain.R = C.T := by
  rfl
@[simp] theorem reverseChain_T (C : ChainInput s F D) : C.reverseChain.T = C.R := by
  rfl

theorem reverseChain_rows (C : ChainInput s F D) :
    C.reverseChain.qA = C.qB ∧ C.reverseChain.qB = C.qA ∧
    C.reverseChain.qJ = C.qK ∧ C.reverseChain.qK = C.qJ := by
  constructor
  · simp only [qA, qB, reverseChain]
    rw [reverseHerzog_fA]
    simp [relabel, reversePerm]
  constructor
  · simp only [qA, qB, reverseChain]
    rw [reverseHerzog_fB]
    simp [relabel, reversePerm]
  constructor
  · simp only [qJ, qK, reverseChain]
    rw [reverseHerzog_fB]
    simp [relabel, reversePerm]
  · simp only [qJ, qK, reverseChain]
    rw [reverseHerzog_fA]
    simp [relabel, reversePerm]

/-- PFIBER is transported as the same actual element, exchanging its two
positive tail coefficients. -/
def reversePFiber (C : ChainInput s F D) (PF : C.PFiber) : C.reverseChain.PFiber := by
  let coeff : Fin 4 → ℕ :=
    ![PF.L.toNat, 0, (PF.u + 1).toNat, (PF.t + 1).toNat]
  have hL0 : 0 ≤ PF.L := le_trans (by norm_num) PF.L_pos
  have htN := PF.t_nonneg
  have huN := PF.u_nonneg
  have ht0 : 0 ≤ PF.t + 1 := by omega
  have hu0 : 0 ≤ PF.u + 1 := by omega
  have hL : (PF.L.toNat : ℤ) = PF.L := Int.toNat_of_nonneg hL0
  have ht : ((PF.t + 1).toNat : ℤ) = PF.t + 1 := Int.toNat_of_nonneg ht0
  have hu : ((PF.u + 1).toNat : ℤ) = PF.u + 1 := Int.toNat_of_nonneg hu0
  let actual : (relabel g reversePerm).ActualFactorization4
      (C.reverseChain.P * (relabel g reversePerm).n 0) := {
    coeff := coeff
    equation := by
      simp [value, Generators.all, Fin.sum_univ_succ, coeff, hL, ht, hu,
        relabel, reversePerm]
      change PF.L * g.m + ((PF.u + 1) * g.n 2 + (PF.t + 1) * g.n 1) =
        C.P * g.n 0
      linarith [PF.equation] }
  exact {
    L := PF.L
    t := PF.u
    u := PF.t
    L_pos := PF.L_pos
    t_nonneg := PF.u_nonneg
    u_nonneg := PF.t_nonneg
    equation := by
      rw [reverseChain_P]
      simpa [relabel, reversePerm, add_comm, add_left_comm, add_assoc] using PF.equation
    actual := actual
    coeff_m := by simp [actual, coeff, hL]
    coeff_i := by rfl
    coeff_j := by simp [actual, coeff, hu]
    coeff_k := by simp [actual, coeff, ht] }

end ChainInput
end P21.Nonsymmetric
