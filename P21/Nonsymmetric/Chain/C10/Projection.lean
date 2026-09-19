import P21.Nonsymmetric.Chain.C10.State
import P21.Nonsymmetric.Chain.C9.EuclideanSeed

namespace P21.Nonsymmetric

namespace EuclideanSeed

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

/-- Forget the C9 construction baggage and retain exactly the Section 10 state. -/
def toState (seed : EuclideanSeed s F D) : EuclideanState s F D where
  F_gap := seed.frobenius.1
  delta := seed.delta
  beta := seed.beta
  gap := seed.gap
  alpha := seed.alpha
  P := seed.P
  R := seed.R
  T := seed.T
  delta_pos := seed.delta_pos
  beta_pos := seed.beta_pos
  gap_pos := seed.gap_pos
  alpha_pos := seed.alpha_pos
  P_pos := seed.P_pos
  R_pos := seed.R_pos
  T_pos := seed.T_pos
  ai_source := seed.ai_source
  bi_source := seed.bi_source
  R_source := seed.R_source
  T_source := seed.T_source
  W_face := seed.W_face
  p := seed.p
  q := seed.q
  v := seed.v
  t := seed.t
  p_pos := seed.p_pos
  q_pos := seed.q_pos
  v_pos := seed.v_pos
  t_pos := seed.t_pos
  det_one := seed.det_one
  L := seed.L
  M := seed.M
  L_eq := seed.L_eq
  M_eq := seed.M_eq
  L_gt_M := seed.L_gt_M
  r := seed.r
  r_nonneg := seed.r_nonneg
  Acoef := seed.Acoef
  Bcoef := seed.Bcoef
  A_source := seed.A_source
  B_source := seed.B_source
  u := seed.u
  Epar := seed.Epar
  u_pos := seed.u_pos
  E_source := seed.E_source
  w := seed.w
  Hp := seed.Hp
  w_nonneg := seed.w_nonneg
  Hp_source := seed.Hp_source
  theta := seed.theta
  chi := seed.chi
  theta_pos := seed.theta_pos
  theta_le := seed.theta_le
  chi_pos := seed.chi_pos
  packet_det_pos := seed.packet_det_pos
  DP := seed.DP
  PP := seed.PP
  rhoj := seed.rhoj
  rhok := seed.rhok

end EuclideanSeed
end P21.Nonsymmetric
