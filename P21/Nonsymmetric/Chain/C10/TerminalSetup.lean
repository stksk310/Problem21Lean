import P21.Nonsymmetric.Chain.C10.Phi
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificate

namespace P21.Nonsymmetric
namespace EuclideanState

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

def nu (X : EuclideanState s F D) : ℤ := X.u / X.theta + 1
def Z (X : EuclideanState s F D) : ℤ := X.Bcoef + X.nu * X.Acoef
def N (X : EuclideanState s F D) : ℤ := X.M + X.nu * X.L
def jstar (X : EuclideanState s F D) : ℤ := X.Epar - X.nu * X.theta
def kstar (X : EuclideanState s F D) : ℤ := X.nu * X.Hp - X.chi
def Terminal (X : EuclideanState s F D) : Prop := X.kstar ≤ X.T - 1

def z (X : EuclideanState s F D) : ℤ := X.u % X.theta
def hterm (X : EuclideanState s F D) : ℤ := X.theta - X.z
def xterm (X : EuclideanState s F D) : ℤ := X.chi - X.nu * X.Hp + X.T - 1

theorem theta_pos' (X : EuclideanState s F D) : 0 < X.theta := by
  have := X.theta_pos
  omega

theorem nu_ge_two (X : EuclideanState s F D) : 2 ≤ X.nu := by
  have hdiv : 1 ≤ X.u / X.theta := by
    rw [Int.le_ediv_iff_mul_le X.theta_pos]
    simpa using X.theta_le
  simp only [nu]
  omega

theorem z_range (X : EuclideanState s F D) : 0 ≤ X.z ∧ X.z < X.theta := by
  exact ⟨Int.emod_nonneg _ (ne_of_gt X.theta_pos'),
    Int.emod_lt_of_pos _ X.theta_pos'⟩

theorem u_division (X : EuclideanState s F D) :
    X.u = (X.nu - 1) * X.theta + X.z := by
  have h := Int.ediv_mul_add_emod X.u X.theta
  simpa only [nu, z, add_sub_cancel_right] using h.symm

theorem jstar_eq (X : EuclideanState s F D) : X.jstar = X.R + X.z - X.theta := by
  rw [jstar, X.E_source, X.u_division]
  ring

theorem jstar_le (X : EuclideanState s F D) : X.jstar ≤ X.R - 1 := by
  rw [X.jstar_eq]
  have := X.z_range.2
  omega

theorem terminal_signed_packet (X : EuclideanState s F D) :
    X.Z * g.n 0 + X.jstar * g.n 1 + X.kstar * g.n 2 = X.N * g.m := by
  simp only [Z, jstar, kstar, N]
  linear_combination X.DP + X.nu * X.PP

theorem hterm_pos (X : EuclideanState s F D) : 1 ≤ X.hterm := by
  rw [hterm]
  have := X.z_range.2
  omega

theorem xterm_nonneg (X : EuclideanState s F D) (hterminal : X.Terminal) :
    0 ≤ X.xterm := by
  simp only [Terminal, kstar] at hterminal
  simp only [xterm]
  omega

theorem theta_terminal_sub (X : EuclideanState s F D) :
    X.theta = X.hterm + X.z := by
  simp only [hterm]
  ring

theorem E_terminal_sub (X : EuclideanState s F D) :
    X.Epar = X.nu * (X.hterm + X.z) + X.R - X.hterm := by
  rw [X.E_source, X.u_division, X.theta_terminal_sub]
  ring

theorem Hp_terminal_sub (X : EuclideanState s F D) : X.Hp = X.T + X.w := X.Hp_source

theorem chi_terminal_sub (X : EuclideanState s F D) :
    X.chi = X.nu * (X.T + X.w) - X.T + 1 + X.xterm := by
  rw [← X.Hp_source]
  simp only [xterm]
  ring

abbrev CertificateVariables := Chain.C10.TerminalCertificateData.Variables

def terminalShifts (X : EuclideanState s F D) : CertificateVariables where
  p0 := X.p - X.v - 1
  q0 := X.q - X.t
  s0 := X.v - 1
  t0 := X.t - 1
  r0 := X.r
  delta0 := X.delta - 1
  beta0 := X.beta - 1
  aj0 := (D.a 1 : ℤ) - 1
  g0 := X.gap - 1
  alpha0 := X.alpha - 1
  bk0 := (D.b 2 : ℤ) - 1
  nu0 := X.nu - 2
  h0 := X.hterm - 1
  z0 := X.z
  x0 := X.xterm
  w0 := X.w

def ShiftsNonnegative (y : CertificateVariables) : Prop :=
  0 ≤ y.p0 ∧ 0 ≤ y.q0 ∧ 0 ≤ y.s0 ∧ 0 ≤ y.t0 ∧
  0 ≤ y.r0 ∧ 0 ≤ y.delta0 ∧ 0 ≤ y.beta0 ∧ 0 ≤ y.aj0 ∧
  0 ≤ y.g0 ∧ 0 ≤ y.alpha0 ∧ 0 ≤ y.bk0 ∧ 0 ≤ y.nu0 ∧
  0 ≤ y.h0 ∧ 0 ≤ y.z0 ∧ 0 ≤ y.x0 ∧ 0 ≤ y.w0

theorem terminalShifts_nonnegative (X : EuclideanState s F D) (hterminal : X.Terminal) :
    ShiftsNonnegative X.terminalShifts := by
  have horder := X.matrix_order
  have haj : (1 : ℤ) ≤ D.a 1 := by exact_mod_cast D.a_pos 1
  have hbk : (1 : ℤ) ≤ D.b 2 := by exact_mod_cast D.b_pos 2
  have hp := X.p_pos
  have hq := X.q_pos
  have hv := X.v_pos
  have ht := X.t_pos
  have hdelta := X.delta_pos
  have hbeta := X.beta_pos
  have hgap := X.gap_pos
  have halpha := X.alpha_pos
  simp only [ShiftsNonnegative, terminalShifts]
  exact ⟨by omega, by omega, by omega, by omega, X.r_nonneg,
    by omega, by omega, by omega, by omega, by omega, by omega,
    by have := X.nu_ge_two; omega,
    by have := X.hterm_pos; omega, X.z_range.1, X.xterm_nonneg hterminal,
    X.w_nonneg⟩

end EuclideanState
end P21.Nonsymmetric
