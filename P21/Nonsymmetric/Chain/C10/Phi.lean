import P21.Nonsymmetric.Chain.C10.Elimination

namespace P21.Nonsymmetric
namespace EuclideanState

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

theorem dp_pos (X : EuclideanState s F D) : 0 < X.Dp := by
  simpa only [Dp] using X.packet_det_pos

theorem phi_step (X : EuclideanState s F D) (Px : ℤ) :
    X.Phi (Px + 1) - X.Phi Px = -(X.Dp + X.M0) := by
  rw [Phi, Phi, mhatAt, mhatAt, KcalAt, KcalAt, X.M0_eq]
  ring

theorem phi_step_lt (X : EuclideanState s F D) (Px : ℤ) :
    X.Phi (Px + 1) < X.Phi Px := by
  have hstep := X.phi_step Px
  have hD := X.dp_pos
  have hM := X.M0_pos
  omega

theorem phi_difference (X : EuclideanState s F D) (Plo PhiHi : ℤ) :
    X.Phi Plo - X.Phi PhiHi = (PhiHi - Plo) * (X.Dp + X.M0) := by
  rw [Phi, Phi, mhatAt, mhatAt, KcalAt, KcalAt, X.M0_eq]
  ring

theorem phi_antitone_of_le (X : EuclideanState s F D) {Pstar : ℤ}
    (h : X.P ≤ Pstar) : X.Phi Pstar ≤ X.Phi X.P := by
  have hdiff := X.phi_difference X.P Pstar
  have hprod : 0 ≤ (Pstar - X.P) * (X.Dp + X.M0) :=
    mul_nonneg (by omega) (by have := X.dp_pos; have := X.M0_pos; omega)
  omega

theorem measureZ_ge_two (X : EuclideanState s F D) : 2 ≤ X.measureZ := by
  rw [measureZ, X.E_source]
  have := X.R_pos
  have := X.u_pos
  have := X.chi_pos
  omega

theorem measureNat_cast (X : EuclideanState s F D) : (X.measureNat : ℤ) = X.measureZ := by
  rw [measureNat, Int.toNat_of_nonneg]
  exact le_trans (by omega) X.measureZ_ge_two

end EuclideanState
end P21.Nonsymmetric
