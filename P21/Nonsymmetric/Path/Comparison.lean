import P21.Nonsymmetric.Path.Normalization

namespace P21.Nonsymmetric
namespace PathInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

namespace NoPairNormalization

def Ac (P : PathInput s F D) (N : NoPairNormalization P) : ℤ :=
  N.atA.coeff 0 + P.beta - N.atB.coeff 0

def Bc (P : PathInput s F D) (N : NoPairNormalization P) : ℤ :=
  P.alpha + N.atB.coeff 2 - N.atA.coeff 2

theorem Ac_pos (P : PathInput s F D) (N : NoPairNormalization P) : 0 < N.Ac P := by
  have hb : (P.beta.toNat : ℤ) = P.beta :=
    Int.toNat_of_nonneg (by have := P.beta_pos; omega)
  have h := N.B_i_lt
  simp only [Ac]
  omega

theorem Bc_pos (P : PathInput s F D) (N : NoPairNormalization P) : 0 < N.Bc P := by
  have ha : (P.alpha.toNat : ℤ) = P.alpha :=
    Int.toNat_of_nonneg (by have := P.alpha_pos; omega)
  have h := N.A_k_lt
  simp only [Bc]
  omega

/-- Exact pure-H comparison of the two normalized actual central returns. -/
theorem central_relation (P : PathInput s F D) (N : NoPairNormalization P) :
    N.Ac P * g.n 0 + ((N.atA.coeff 1 : ℤ) - N.atB.coeff 1) * g.n 1 =
      N.Bc P * g.n 2 := by
  have hA := N.atA.equation
  have hB := N.atB.equation
  have hl := P.ladder_middle
  change P.qA + P.beta * g.n 0 = P.qB + P.alpha * g.n 2 at hl
  simp [value, Fin.sum_univ_succ] at hA hB
  simp only [Ac, Bc]
  linear_combination hA - hB + hl

theorem middle_trichotomy (P : PathInput s F D) (N : NoPairNormalization P) :
    N.atA.coeff 1 < N.atB.coeff 1 ∨
    N.atA.coeff 1 = N.atB.coeff 1 ∨
    N.atB.coeff 1 < N.atA.coeff 1 := by
  omega

end NoPairNormalization
end PathInput
end P21.Nonsymmetric
