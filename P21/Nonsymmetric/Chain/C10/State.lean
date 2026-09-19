import P21.Nonsymmetric.HerzogData
import P21.Semantics

namespace P21.Nonsymmetric

/-- The abstract state of publication Section 10.2. -/
structure EuclideanState {g : Generators} (s : g.Setting) (F : ℤ)
    (D : HerzogCriticalData g) where
  F_gap : F ∉ g.Gamma
  delta : ℤ
  beta : ℤ
  gap : ℤ
  alpha : ℤ
  P : ℤ
  R : ℤ
  T : ℤ
  delta_pos : 1 ≤ delta
  beta_pos : 1 ≤ beta
  gap_pos : 1 ≤ gap
  alpha_pos : 1 ≤ alpha
  P_pos : 1 ≤ P
  R_pos : 1 ≤ R
  T_pos : 1 ≤ T
  ai_source : (D.a 0 : ℤ) = P - beta
  bi_source : (D.b 0 : ℤ) = P - delta
  R_source : R = (D.a 1 : ℤ) + gap
  T_source : T = (D.b 2 : ℤ) + alpha
  W_face : W F g.m = (P - 1) * g.n 0 + (R - 1) * g.n 1 + (T - 1) * g.n 2
  p : ℤ
  q : ℤ
  v : ℤ
  t : ℤ
  p_pos : 1 ≤ p
  q_pos : 1 ≤ q
  v_pos : 1 ≤ v
  t_pos : 1 ≤ t
  det_one : p * t - q * v = 1
  L : ℤ
  M : ℤ
  L_eq : L = p + q
  M_eq : M = v + t
  L_gt_M : M < L
  r : ℤ
  r_nonneg : 0 ≤ r
  Acoef : ℤ
  Bcoef : ℤ
  A_source : Acoef = p * (r + delta) + q * (r + beta)
  B_source : Bcoef = v * (r + delta) + t * (r + beta)
  u : ℤ
  Epar : ℤ
  u_pos : 1 ≤ u
  E_source : Epar = R + u
  w : ℤ
  Hp : ℤ
  w_nonneg : 0 ≤ w
  Hp_source : Hp = T + w
  theta : ℤ
  chi : ℤ
  theta_pos : 1 ≤ theta
  theta_le : theta ≤ u
  chi_pos : 1 ≤ chi
  packet_det_pos : 0 < theta * chi - Epar * Hp
  DP : Bcoef * g.n 0 + Epar * g.n 1 = M * g.m + chi * g.n 2
  PP : Acoef * g.n 0 + Hp * g.n 2 = L * g.m + theta * g.n 1
  rhoj : (D.rho 1 : ℤ) = L * Epar + M * theta - (D.a 1 : ℤ)
  rhok : (D.rho 2 : ℤ) = L * chi + M * Hp - (D.b 2 : ℤ)

namespace EuclideanState

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

def Ical (X : EuclideanState s F D) : ℤ :=
  (D.rho 1 : ℤ) * (D.rho 2 : ℤ) - (D.a 1 : ℤ) * (D.b 2 : ℤ)

def Jcal (X : EuclideanState s F D) : ℤ :=
  (D.a 0 : ℤ) * (D.rho 2 : ℤ) + (D.b 0 : ℤ) * (D.b 2 : ℤ)

def Kcal (X : EuclideanState s F D) : ℤ :=
  (D.b 0 : ℤ) * (D.rho 1 : ℤ) + (D.a 0 : ℤ) * (D.a 1 : ℤ)

def Dp (X : EuclideanState s F D) : ℤ := X.theta * X.chi - X.Epar * X.Hp

def I0 (X : EuclideanState s F D) : ℤ := X.Epar * X.Acoef + X.theta * X.Bcoef

def J0 (X : EuclideanState s F D) : ℤ := X.chi * X.Acoef + X.Hp * X.Bcoef

def M0 (X : EuclideanState s F D) : ℤ := X.L * X.Epar + X.M * X.theta

def K0 (X : EuclideanState s F D) : ℤ := X.L * X.chi + X.M * X.Hp

def mhatAt (X : EuclideanState s F D) (Px : ℤ) : ℤ :=
  X.I0 * (D.rho 2 : ℤ) - (D.a 1 : ℤ) * X.J0 - X.Dp * (Px - X.delta)

def mhat (X : EuclideanState s F D) : ℤ := X.mhatAt X.P

def KcalAt (X : EuclideanState s F D) (Px : ℤ) : ℤ :=
  (Px - X.delta) * (D.rho 1 : ℤ) + (Px - X.beta) * (D.a 1 : ℤ)

def Phi (X : EuclideanState s F D) (Px : ℤ) : ℤ := X.mhatAt Px - X.KcalAt Px

def measureZ (X : EuclideanState s F D) : ℤ := X.Epar + X.chi

def measureNat (X : EuclideanState s F D) : ℕ := X.measureZ.toNat

end EuclideanState
end P21.Nonsymmetric
