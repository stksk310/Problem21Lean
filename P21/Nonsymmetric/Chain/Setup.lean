import P21.Nonsymmetric.Extraction

namespace P21.Nonsymmetric
namespace ChainInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

def qA (C : ChainInput s F D) : ℤ := D.fA - C.lambda * g.n 0
def qB (C : ChainInput s F D) : ℤ := D.fB - C.lambda * g.n 0
def qJ (C : ChainInput s F D) : ℤ := D.fB - C.mu * g.n 1
def qK (C : ChainInput s F D) : ℤ := D.fA - C.nu * g.n 2

def P (C : ChainInput s F D) : ℤ := (D.rho 0 : ℤ) - C.lambda
def R (C : ChainInput s F D) : ℤ := (D.rho 1 : ℤ) - C.mu
def T (C : ChainInput s F D) : ℤ := (D.rho 2 : ℤ) - C.nu

theorem scalar_ranges (C : ChainInput s F D) :
    1 ≤ C.delta ∧ 1 ≤ C.beta ∧ 1 ≤ C.gapJ ∧ 1 ≤ C.alpha :=
  C.all_slacks_positive

theorem a0_exact (C : ChainInput s F D) : (D.a 0 : ℤ) = C.lambda + C.delta := by
  simp [delta]

theorem b0_exact (C : ChainInput s F D) : (D.b 0 : ℤ) = C.lambda + C.beta := by
  simp [beta]

theorem P_exact' (C : ChainInput s F D) :
    C.P = C.lambda + C.delta + C.beta := by
  simpa [P] using C.P_exact

theorem P_eq_a_beta (C : ChainInput s F D) : C.P = D.a 0 + C.beta := by
  rw [C.P_exact', C.a0_exact]

theorem P_eq_b_delta (C : ChainInput s F D) : C.P = D.b 0 + C.delta := by
  rw [C.P_exact', C.b0_exact]
  ring

theorem R_exact (C : ChainInput s F D) : C.R = D.a 1 + C.gapJ := by
  have hr : (D.rho 1 : ℤ) = D.a 1 + D.b 1 := by exact_mod_cast D.rho_eq 1
  simp only [R, gapJ]
  omega

theorem T_exact (C : ChainInput s F D) : C.T = D.b 2 + C.alpha := by
  have hr : (D.rho 2 : ℤ) = D.a 2 + D.b 2 := by exact_mod_cast D.rho_eq 2
  simp only [T, alpha]
  omega

theorem qA_exact (C : ChainInput s F D) :
    C.qA = (C.P - 1) * g.n 0 + (D.a 1 - 1) * g.n 1 - g.n 2 := by
  simp [qA, P, HerzogCriticalData.fA]
  ring

theorem qB_exact (C : ChainInput s F D) :
    C.qB = (C.P - 1) * g.n 0 - g.n 1 + (D.b 2 - 1) * g.n 2 := by
  simp [qB, P, HerzogCriticalData.fB]
  ring

theorem qJ_exact (C : ChainInput s F D) :
    C.qJ = (D.b 0 - 1) * g.n 0 + (C.R - 1) * g.n 1 - g.n 2 := by
  have h := D.fB_cyclic 1
  simp [qJ, R, next, prev] at h ⊢
  linear_combination h

theorem qK_exact (C : ChainInput s F D) :
    C.qK = (D.a 0 - 1) * g.n 0 - g.n 1 + (C.T - 1) * g.n 2 := by
  have h := D.fA_cyclic 2
  simp [qK, T, next, prev] at h ⊢
  linear_combination h

theorem qA_actual (C : ChainInput s F D) : C.qA ∈ s.semigroup.Q F := by
  simpa [qA] using C.actual 1

theorem qB_actual (C : ChainInput s F D) : C.qB ∈ s.semigroup.Q F := by
  simpa [qB] using C.actual 2

theorem qJ_actual (C : ChainInput s F D) : C.qJ ∈ s.semigroup.Q F := by
  simpa [qJ] using C.actual 0

theorem qK_actual (C : ChainInput s F D) : C.qK ∈ s.semigroup.Q F := by
  simpa [qK] using C.actual 3

theorem cA_exact (C : ChainInput s F D) :
    complement F g.m C.qA = C.gapJ * g.n 1 + C.T * g.n 2 := by
  simpa [qA, gapJ, T] using C.cAi

theorem cB_exact (C : ChainInput s F D) :
    complement F g.m C.qB = C.R * g.n 1 + C.alpha * g.n 2 := by
  simpa [qB, R, alpha] using C.cBi

theorem cJ_exact (C : ChainInput s F D) :
    complement F g.m C.qJ = C.delta * g.n 0 + C.T * g.n 2 := by
  simpa [qJ, delta, T] using C.cBj

theorem cK_exact (C : ChainInput s F D) :
    complement F g.m C.qK = C.beta * g.n 0 + C.R * g.n 1 := by
  simpa [qK, beta, R] using C.cAk

theorem W_exact (C : ChainInput s F D) :
    W F g.m = (C.P - 1) * g.n 0 + (C.R - 1) * g.n 1 + (C.T - 1) * g.n 2 := by
  simpa [P, R, T] using C.boxW

end ChainInput
end P21.Nonsymmetric
