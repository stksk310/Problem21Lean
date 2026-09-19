import P21.Nonsymmetric.Chain.C10.Nonterminal
import P21.Nonsymmetric.Relabel

namespace P21.Nonsymmetric
namespace EuclideanState

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

theorem exchange_det (X : EuclideanState s F D) :
    (X.t + X.e * X.q) * X.p - (X.v + X.e * X.p) * X.q = 1 := by
  rw [← X.det_one]
  ring

theorem exchange_L (X : EuclideanState s F D) :
    (X.t + X.e * X.q) + (X.v + X.e * X.p) = X.M + X.e * X.L := by
  rw [X.L_eq, X.M_eq]
  ring

theorem exchange_M (X : EuclideanState s F D) : X.q + X.p = X.L := by
  rw [X.L_eq]
  ring

theorem exchange_A_source (X : EuclideanState s F D) :
    X.Bcoef + X.e * X.Acoef =
      (X.t + X.e * X.q) * (X.r + X.beta) +
        (X.v + X.e * X.p) * (X.r + X.delta) := by
  rw [X.A_source, X.B_source]
  ring

theorem exchange_B_source (X : EuclideanState s F D) :
    X.Acoef = X.q * (X.r + X.beta) + X.p * (X.r + X.delta) := by
  rw [X.A_source]
  ring

theorem exchange_packet_det (X : EuclideanState s F D) :
    X.kappa * X.theta - X.Hp * X.rhoRem =
      X.theta * X.chi - X.Epar * X.Hp := by
  rw [X.chi_eq, X.E_division]
  ring

theorem exchange_rhoj (X : EuclideanState s F D) :
    (D.rho 2 : ℤ) = (X.M + X.e * X.L) * X.Hp + X.L * X.kappa - D.b 2 := by
  rw [X.rhok, X.chi_eq]
  ring

theorem exchange_rhok (X : EuclideanState s F D) :
    (D.rho 1 : ℤ) = (X.M + X.e * X.L) * X.theta + X.L * X.rhoRem - D.a 1 := by
  rw [X.rhoj, X.E_division]
  ring

def step (X : EuclideanState s F D) (hnot : ¬ X.Terminal) :
    EuclideanState (relabelSetting s reversePerm) F (reverseHerzog D) where
  F_gap := by simpa using X.F_gap
  delta := X.beta
  beta := X.delta
  gap := X.alpha
  alpha := X.gap
  P := X.P
  R := X.T
  T := X.R
  delta_pos := X.beta_pos
  beta_pos := X.delta_pos
  gap_pos := X.alpha_pos
  alpha_pos := X.gap_pos
  P_pos := X.P_pos
  R_pos := X.T_pos
  T_pos := X.R_pos
  ai_source := by simpa [reverseHerzog, reversePerm] using X.bi_source
  bi_source := by simpa [reverseHerzog, reversePerm] using X.ai_source
  R_source := by simpa [reverseHerzog, reversePerm] using X.T_source
  T_source := by simpa [reverseHerzog, reversePerm] using X.R_source
  W_face := by
    simpa [relabel, reversePerm, add_comm, add_left_comm, add_assoc] using X.W_face
  p := X.t + X.e * X.q
  q := X.v + X.e * X.p
  v := X.q
  t := X.p
  p_pos := by
    have := X.t_pos
    have := X.e_pos
    have := X.q_pos
    nlinarith
  q_pos := by
    have := X.v_pos
    have := X.e_pos
    have := X.p_pos
    nlinarith
  v_pos := X.q_pos
  t_pos := X.p_pos
  det_one := X.exchange_det
  L := X.M + X.e * X.L
  M := X.L
  L_eq := X.exchange_L.symm
  M_eq := X.exchange_M.symm
  L_gt_M := by
    have he := X.e_pos
    have hM := X.M_pos
    have hL := X.L_pos
    nlinarith
  r := X.r
  r_nonneg := X.r_nonneg
  Acoef := X.Bcoef + X.e * X.Acoef
  Bcoef := X.Acoef
  A_source := X.exchange_A_source
  B_source := X.exchange_B_source
  u := X.w
  Epar := X.Hp
  u_pos := X.w_pos_of_nonterminal hnot
  E_source := X.Hp_source
  w := X.rhoRem - X.R
  Hp := X.rhoRem
  w_nonneg := by have := X.rhoRem_bounds hnot; omega
  Hp_source := by ring
  theta := X.kappa
  chi := X.theta
  theta_pos := X.kappa_pos
  theta_le := X.kappa_le_w hnot
  chi_pos := X.theta_pos
  packet_det_pos := by
    rw [X.exchange_packet_det]
    exact X.packet_det_pos
  DP := by
    simpa [relabel, reversePerm, add_comm, add_left_comm, add_assoc] using X.PP
  PP := by
    simpa [relabel, reversePerm, add_comm, add_left_comm, add_assoc] using X.new_packet
  rhoj := by simpa [reverseHerzog, reversePerm] using X.exchange_rhoj
  rhok := by simpa [reverseHerzog, reversePerm] using X.exchange_rhok

@[simp] theorem step_measureZ (X : EuclideanState s F D) (hnot : ¬ X.Terminal) :
    (X.step hnot).measureZ = X.Hp + X.theta := rfl

theorem measure_descent_identity (X : EuclideanState s F D) :
    X.measureZ - (X.Hp + X.theta) =
      (X.e - 1) * (X.Hp + X.theta) + X.rhoRem + X.kappa := by
  simp only [measureZ]
  rw [X.E_division, X.chi_eq]
  ring

theorem step_measureZ_lt (X : EuclideanState s F D) (hnot : ¬ X.Terminal) :
    (X.step hnot).measureZ < X.measureZ := by
  rw [X.step_measureZ hnot]
  have he0 : 0 ≤ X.e - 1 := by have := X.e_pos; omega
  have hsum0 : 0 ≤ X.Hp + X.theta := by
    have := X.Hp_pos
    have := X.theta_pos
    omega
  have hprod : 0 ≤ (X.e - 1) * (X.Hp + X.theta) := mul_nonneg he0 hsum0
  have hrho := X.rhoRem_range.1
  have hk := X.kappa_pos
  have hid := X.measure_descent_identity
  linarith

theorem measureZ_nonneg (X : EuclideanState s F D) : 0 ≤ X.measureZ := by
  simp only [measureZ]
  rw [X.E_source]
  have := X.R_pos
  have := X.u_pos
  have := X.chi_pos
  omega

theorem step_measureNat_lt (X : EuclideanState s F D) (hnot : ¬ X.Terminal) :
    (X.step hnot).measureNat < X.measureNat := by
  have hlt := X.step_measureZ_lt hnot
  simp only [measureNat]
  apply (Int.toNat_lt_toNat ?_).mpr hlt
  simp only [measureZ]
  rw [X.E_source]
  have := X.R_pos
  have := X.u_pos
  have := X.chi_pos
  omega

end EuclideanState
end P21.Nonsymmetric
