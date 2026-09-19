import P21.Nonsymmetric.Chain.C10.MatrixOrder

namespace P21.Nonsymmetric
namespace EuclideanState

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

theorem M0_eq (X : EuclideanState s F D) : X.M0 = (D.rho 1 : ℤ) + D.a 1 := by
  rw [M0, X.rhoj]
  ring

theorem K0_eq (X : EuclideanState s F D) : X.K0 = (D.rho 2 : ℤ) + D.b 2 := by
  rw [K0, X.rhok]
  ring

theorem M0_pos (X : EuclideanState s F D) : 0 < X.M0 := by
  rw [X.M0_eq]
  have hr : (0 : ℤ) < D.rho 1 := by exact_mod_cast D.rho_pos 1
  have ha : (0 : ℤ) < D.a 1 := by exact_mod_cast D.a_pos 1
  omega

theorem packet_elimination (X : EuclideanState s F D) :
    X.I0 * g.n 0 = X.M0 * g.m + X.Dp * g.n 2 := by
  simp only [I0, M0, Dp]
  linear_combination X.Epar * X.PP + X.theta * X.DP

theorem source_determinant (X : EuclideanState s F D) :
    X.Acoef * X.M - X.Bcoef * X.L = X.delta - X.beta := by
  rw [X.A_source, X.B_source, X.L_eq, X.M_eq]
  linear_combination (X.delta - X.beta) * X.det_one

theorem packet_source_determinant (X : EuclideanState s F D) :
    X.I0 * X.K0 - X.M0 * X.J0 = -X.Dp * (X.delta - X.beta) := by
  rw [I0, J0, M0, K0, Dp]
  have hsource := X.source_determinant
  linear_combination -(X.theta * X.chi - X.Epar * X.Hp) * hsource

theorem mhat_numerator (X : EuclideanState s F D) :
    X.I0 * X.Ical - X.Dp * X.Kcal = X.M0 * X.mhat := by
  have hdet := X.packet_source_determinant
  have hM := X.M0_eq
  have hK := X.K0_eq
  have hai := X.ai_source
  have hbi := X.bi_source
  simp only [Ical, Kcal, mhat, mhatAt]
  rw [hM] at hdet ⊢
  rw [hK] at hdet
  rw [hbi, hai]
  linear_combination -(D.a 1 : ℤ) * hdet

theorem mhat_scale (X : EuclideanState s F D) :
    (g.m : ℚ) = X.sigma * X.mhat := by
  have hpacket :
      (X.I0 : ℚ) * g.n 0 = (X.M0 : ℚ) * g.m + (X.Dp : ℚ) * g.n 2 := by
    exact_mod_cast X.packet_elimination
  rw [X.ni_scale, X.nk_scale] at hpacket
  have hnum :
      (X.I0 : ℚ) * X.Ical - X.Dp * X.Kcal = X.M0 * X.mhat := by
    exact_mod_cast X.mhat_numerator
  have hM : (X.M0 : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt X.M0_pos
  apply mul_left_cancel₀ hM
  calc
    (X.M0 : ℚ) * g.m =
        X.I0 * (X.sigma * X.Ical) - X.Dp * (X.sigma * X.Kcal) := by
      linarith [hpacket]
    _ = X.sigma * (X.I0 * X.Ical - X.Dp * X.Kcal) := by ring
    _ = X.sigma * (X.M0 * X.mhat) := by rw [hnum]
    _ = X.M0 * (X.sigma * X.mhat) := by ring

end EuclideanState
end P21.Nonsymmetric
