import P21.Nonsymmetric.Path.Packets

namespace P21.Nonsymmetric
namespace PathInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

/-- The publication PAIR with nonnegative coefficients encoded as naturals. -/
structure Pair (P : PathInput s F D) where
  X : ℕ
  H0 : ℕ
  Z : ℕ
  equationA : P.qA + g.m = value g.n ![X, H0, Z + P.alpha.toNat]
  equationB : P.qB + g.m = value g.n ![X + P.beta.toNat, H0, Z]

def NoPair (P : PathInput s F D) : Prop := ¬ Nonempty (Pair P)

private theorem alpha_cast (P : PathInput s F D) : (P.alpha.toNat : ℤ) = P.alpha := by
  rw [Int.toNat_of_nonneg (by have := P.alpha_pos; omega)]

private theorem beta_cast (P : PathInput s F D) : (P.beta.toNat : ℤ) = P.beta := by
  rw [Int.toNat_of_nonneg (by have := P.beta_pos; omega)]

/-- A large `k` coefficient in this very factorization of `qA+m` produces the
paired factorization of `qB+m` via the exact central ladder. -/
theorem pair_of_A_large (P : PathInput s F D)
    (a : g.ActualFactorization3 (P.qA + g.m))
    (hlarge : P.alpha.toNat ≤ a.coeff 2) : Nonempty (Pair P) := by
  let z := a.coeff 2 - P.alpha.toNat
  have hz : z + P.alpha.toNat = a.coeff 2 := by
    dsimp [z]
    omega
  refine ⟨{
    X := a.coeff 0
    H0 := a.coeff 1
    Z := z
    equationA := ?_
    equationB := ?_ }⟩
  · simpa [value, Fin.sum_univ_succ, hz] using a.equation.symm
  · have he := a.equation
    have hl := P.ladder_middle
    change P.qA + P.beta * g.n 0 = P.qB + P.alpha * g.n 2 at hl
    have ha := P.alpha_cast
    have hb := P.beta_cast
    simp [value, Fin.sum_univ_succ] at he
    rw [← hz] at he
    simp [Nat.cast_add, ha, hb] at he
    simp [value, Fin.sum_univ_succ, Nat.cast_add, ha, hb]
    linear_combination -he - hl

/-- The symmetric ladder conversion starts from the named `qB+m`
factorization and consumes `β` copies of direction `i`. -/
theorem pair_of_B_large (P : PathInput s F D)
    (b : g.ActualFactorization3 (P.qB + g.m))
    (hlarge : P.beta.toNat ≤ b.coeff 0) : Nonempty (Pair P) := by
  let x := b.coeff 0 - P.beta.toNat
  have hx : x + P.beta.toNat = b.coeff 0 := by
    dsimp [x]
    omega
  refine ⟨{
    X := x
    H0 := b.coeff 1
    Z := b.coeff 2
    equationA := ?_
    equationB := ?_ }⟩
  · have he := b.equation
    have hl := P.ladder_middle
    change P.qA + P.beta * g.n 0 = P.qB + P.alpha * g.n 2 at hl
    have ha := P.alpha_cast
    have hb := P.beta_cast
    simp [value, Fin.sum_univ_succ] at he
    rw [← hx] at he
    simp [Nat.cast_add, ha, hb] at he
    simp [value, Fin.sum_univ_succ, Nat.cast_add, ha, hb]
    linear_combination -he + hl
  · simpa [value, Fin.sum_univ_succ, hx] using b.equation.symm

theorem NoPair.A_k_lt (P : PathInput s F D) (hnp : P.NoPair)
    (a : g.ActualFactorization3 (P.qA + g.m)) :
    a.coeff 2 < P.alpha.toNat := by
  by_contra h
  exact hnp (P.pair_of_A_large a (by omega))

theorem NoPair.B_i_lt (P : PathInput s F D) (hnp : P.NoPair)
    (b : g.ActualFactorization3 (P.qB + g.m)) :
    b.coeff 0 < P.beta.toNat := by
  by_contra h
  exact hnp (P.pair_of_B_large b (by omega))

end PathInput
end P21.Nonsymmetric
