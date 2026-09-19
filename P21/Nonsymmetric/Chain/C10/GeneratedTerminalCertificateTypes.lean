/- Generated from the frozen 3234-monomial Section 10 table. -/
import Mathlib

namespace P21.Nonsymmetric.Chain.C10.TerminalCertificateData

def tableSha256 : String := "495504b4bcb8427db04b242cf09b83fbe7bde1188f9324b7e977036a5a4db9b3"
def termCount : Nat := 3234
def totalDegree : Nat := 7
def constantTerm : Nat := 63

structure Variables where
  p0 : ℤ
  q0 : ℤ
  s0 : ℤ
  t0 : ℤ
  r0 : ℤ
  delta0 : ℤ
  beta0 : ℤ
  aj0 : ℤ
  g0 : ℤ
  alpha0 : ℤ
  bk0 : ℤ
  nu0 : ℤ
  h0 : ℤ
  z0 : ℤ
  x0 : ℤ
  w0 : ℤ

structure Term where
  coefficient : Nat
  e_p0 : Nat
  e_q0 : Nat
  e_s0 : Nat
  e_t0 : Nat
  e_r0 : Nat
  e_delta0 : Nat
  e_beta0 : Nat
  e_aj0 : Nat
  e_g0 : Nat
  e_alpha0 : Nat
  e_bk0 : Nat
  e_nu0 : Nat
  e_h0 : Nat
  e_z0 : Nat
  e_x0 : Nat
  e_w0 : Nat

def evalTerm (y : Variables) (term : Term) : ℤ :=
  term.coefficient * y.p0 ^ term.e_p0 * y.q0 ^ term.e_q0 * y.s0 ^ term.e_s0 * y.t0 ^ term.e_t0 * y.r0 ^ term.e_r0 * y.delta0 ^ term.e_delta0 * y.beta0 ^ term.e_beta0 * y.aj0 ^ term.e_aj0 * y.g0 ^ term.e_g0 * y.alpha0 ^ term.e_alpha0 * y.bk0 ^ term.e_bk0 * y.nu0 ^ term.e_nu0 * y.h0 ^ term.e_h0 * y.z0 ^ term.e_z0 * y.x0 ^ term.e_x0 * y.w0 ^ term.e_w0

theorem evalTerm_nonneg (y : Variables)
    (h_p0 : 0 ≤ y.p0)
    (h_q0 : 0 ≤ y.q0)
    (h_s0 : 0 ≤ y.s0)
    (h_t0 : 0 ≤ y.t0)
    (h_r0 : 0 ≤ y.r0)
    (h_delta0 : 0 ≤ y.delta0)
    (h_beta0 : 0 ≤ y.beta0)
    (h_aj0 : 0 ≤ y.aj0)
    (h_g0 : 0 ≤ y.g0)
    (h_alpha0 : 0 ≤ y.alpha0)
    (h_bk0 : 0 ≤ y.bk0)
    (h_nu0 : 0 ≤ y.nu0)
    (h_h0 : 0 ≤ y.h0)
    (h_z0 : 0 ≤ y.z0)
    (h_x0 : 0 ≤ y.x0)
    (h_w0 : 0 ≤ y.w0)
    (term : Term) : 0 ≤ evalTerm y term := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Int.ofNat_nonneg term.coefficient) (pow_nonneg h_p0 term.e_p0)) (pow_nonneg h_q0 term.e_q0)) (pow_nonneg h_s0 term.e_s0)) (pow_nonneg h_t0 term.e_t0)) (pow_nonneg h_r0 term.e_r0)) (pow_nonneg h_delta0 term.e_delta0)) (pow_nonneg h_beta0 term.e_beta0)) (pow_nonneg h_aj0 term.e_aj0)) (pow_nonneg h_g0 term.e_g0)) (pow_nonneg h_alpha0 term.e_alpha0)) (pow_nonneg h_bk0 term.e_bk0)) (pow_nonneg h_nu0 term.e_nu0)) (pow_nonneg h_h0 term.e_h0)) (pow_nonneg h_z0 term.e_z0)) (pow_nonneg h_x0 term.e_x0)) (pow_nonneg h_w0 term.e_w0)

end P21.Nonsymmetric.Chain.C10.TerminalCertificateData
