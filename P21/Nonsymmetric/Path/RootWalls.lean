import P21.Nonsymmetric.Path.WeakRoot

namespace P21.Nonsymmetric
namespace PathInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

namespace WeakRoot

/-- Substituting one signed weak root into the same named actual missing-k
return.  This remains an identity until every displayed coefficient is
separately proved nonnegative. -/
theorem qA_identity (P : PathInput s F D) (w : WeakRoot P)
    (LK : ActualReturn g P.qL 2) :
    P.qA = ((LK.factorization.coeff 0 : ℤ) - 1) * g.m +
      ((LK.factorization.coeff 1 : ℤ) - w.d + D.a 0) * g.n 0 +
      ((LK.factorization.coeff 2 : ℤ) + w.S - P.R) * g.n 1 +
      (w.e - 1) * g.n 2 := by
  have hLK := LK.factorization.equation
  have hz := LK.direction_zero
  have hc : LK.factorization.coeff =
      Fin.cons (LK.factorization.coeff 0) (fun j => LK.factorization.coeff j.succ) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [hc, g.value_cons] at hLK
  simp [value, Fin.sum_univ_succ] at hLK
  have hz3 : LK.factorization.coeff 3 = 0 := by simpa using hz
  rw [hz3] at hLK
  simp at hLK
  have hl := P.ladder_left
  have hw := w.equation
  linear_combination -hLK - hl + hw

/-- The exact Frobenius identity obtained by subtracting this signed root
from the frozen PATH box-W identity. -/
theorem F_identity (P : PathInput s F D) (w : WeakRoot P) :
    F = (P.P0 + w.d - 1) * g.n 0 +
      (P.R - w.S - 1) * g.n 1 + (P.T - w.e - 1) * g.n 2 := by
  have hW := P.boxW
  change F + g.m = (P.P0 - 1) * g.n 0 +
    (P.R - 1) * g.n 1 + (P.T - 1) * g.n 2 at hW
  linear_combination hW - w.equation

/-- Publication P5.3.3 root walls.  The LK witness is explicit so repeated
normalization reuses the same actual chronological return. -/
theorem walls (P : PathInput s F D) (hF : s.semigroup.IsFrobenius F)
    (LK : ActualReturn g P.qL 2) (w : WeakRoot P) :
    w.S < P.R ∧ P.T ≤ w.e ∧ (D.b 2 : ℤ) ≤ w.e - P.alpha := by
  have hS : w.S < P.R := by
    by_contra hn
    have hQA := w.qA_identity P LK
    have hmem := gamma_of_coordinates g P.qA
      ((LK.factorization.coeff 0 : ℤ) - 1)
      ((LK.factorization.coeff 1 : ℤ) - w.d + D.a 0)
      ((LK.factorization.coeff 2 : ℤ) + w.S - P.R)
      (w.e - 1)
      (by have := LK.level_pos; omega)
      (by have := w.d_le; omega)
      (by omega)
      (by have := w.e_ge; have := P.alpha_pos; omega)
      hQA
    exact (P.actual 1).1.1 hmem
  have he : P.T ≤ w.e := by
    by_contra hn
    have hFI := w.F_identity P
    have hP := P.P0_eq
    have hb := P.beta_pos
    have hmem := gamma_of_coordinates g F 0
      (P.P0 + w.d - 1) (P.R - w.S - 1) (P.T - w.e - 1)
      (by omega)
      (by have := w.d_pos; have := D.a_pos 0; omega)
      (by omega)
      (by omega)
      (by simpa using hFI)
    exact hF.1 hmem
  have hK : (D.b 2 : ℤ) ≤ w.e - P.alpha := by
    have hT := P.T_eq
    omega
  exact ⟨hS, he, hK⟩

end WeakRoot
end PathInput
end P21.Nonsymmetric
