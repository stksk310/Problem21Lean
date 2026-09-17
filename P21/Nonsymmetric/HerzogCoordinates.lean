import P21.Nonsymmetric.HerzogData

namespace P21.Nonsymmetric

def next (i : Fin 3) : Fin 3 := ![1, 2, 0] i
def prev (i : Fin 3) : Fin 3 := ![2, 0, 1] i

theorem cyclic_distinct (i : Fin 3) : i ≠ next i ∧ i ≠ prev i ∧ next i ≠ prev i := by
  fin_cases i <;> decide

theorem value_cyclic (g : Generators) (c : Fin 3 → ℕ) (i : Fin 3) :
    value g.n c = (c i : ℤ)*g.n i + (c (next i) : ℤ)*g.n (next i) +
      (c (prev i) : ℤ)*g.n (prev i) := by
  fin_cases i <;> simp [value, Fin.sum_univ_succ, next, prev] <;> ring

namespace HerzogCriticalData
variable {g : Generators} (D : HerzogCriticalData g)

def relationCoeff (i : Fin 3) : Fin 3 → ℕ :=
  ![![0, D.b 1, D.a 2], ![D.a 0, 0, D.b 2], ![D.b 0, D.a 1, 0]] i

theorem relationCoeff_self (i : Fin 3) : D.relationCoeff i i = 0 := by
  fin_cases i <;> rfl

theorem relationCoeff_pos (i j : Fin 3) (h : j ≠ i) : 0 < D.relationCoeff i j := by
  fin_cases i <;> fin_cases j <;> simp_all [relationCoeff, D.a_pos, D.b_pos]

theorem relationCoeff_value (i : Fin 3) :
    value g.n (D.relationCoeff i) = (D.rho i : ℤ) * g.n i := by
  fin_cases i
  · simpa [relationCoeff, value, Fin.sum_univ_succ] using D.relation_zero.symm
  · simpa [relationCoeff, value, Fin.sum_univ_succ] using D.relation_one.symm
  · simpa [relationCoeff, value, Fin.sum_univ_succ] using D.relation_two.symm

theorem fA_cyclic (i : Fin 3) :
    D.fA = (D.rho i - 1 : ℤ)*g.n i + (D.a (next i)-1 : ℤ)*g.n (next i) - g.n (prev i) := by
  have e0 := D.relation_zero
  have e2 := D.relation_two
  have hr : (D.rho 0 : ℤ) = D.a 0 + D.b 0 := by exact_mod_cast D.rho_eq 0
  have hr1 : (D.rho 1 : ℤ) = D.a 1 + D.b 1 := by exact_mod_cast D.rho_eq 1
  fin_cases i
  · rfl
  · change D.fA = (D.rho 1-1 : ℤ)*g.n 1 + (D.a 2-1 : ℤ)*g.n 2-g.n 0
    dsimp [fA]
    linear_combination e0 - hr1 * g.n 1
  · change D.fA = (D.rho 2-1 : ℤ)*g.n 2 + (D.a 0-1 : ℤ)*g.n 0-g.n 1
    dsimp [fA]
    linear_combination -e2 + hr * g.n 0

theorem fB_cyclic (i : Fin 3) :
    D.fB = (D.rho i - 1 : ℤ)*g.n i - g.n (next i) + (D.b (prev i)-1 : ℤ)*g.n (prev i) := by
  have e0 := D.relation_zero
  have e1 := D.relation_one
  have hr0 : (D.rho 0 : ℤ) = D.a 0 + D.b 0 := by exact_mod_cast D.rho_eq 0
  have hr2 : (D.rho 2 : ℤ) = D.a 2 + D.b 2 := by exact_mod_cast D.rho_eq 2
  fin_cases i
  · rfl
  · change D.fB = (D.rho 1-1 : ℤ)*g.n 1-g.n 2+(D.b 0-1 : ℤ)*g.n 0
    dsimp [fB]
    linear_combination -e1 + hr0 * g.n 0
  · change D.fB = (D.rho 2-1 : ℤ)*g.n 2-g.n 0+(D.b 1-1 : ℤ)*g.n 1
    dsimp [fB]
    linear_combination e0 - hr2 * g.n 2

end HerzogCriticalData
end P21.Nonsymmetric
