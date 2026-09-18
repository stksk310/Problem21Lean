/- Generated from the frozen 715-term table. -/
import Mathlib

namespace P21.Nonsymmetric.ChainCore.C9.LinearCertificateData

def tableSha256 : String := "9ba4fdcbdc1b5440785232e97e8cf8d729c3cf1254d87551d3a90d9abbff5916"
def termCount : Nat := 715
def constantTerm : Nat := 35

structure Variables where
  f : ℤ
  r : ℤ
  delta : ℤ
  beta : ℤ
  g : ℤ
  u : ℤ
  alpha : ℤ
  w : ℤ
  theta : ℤ
  eps : ℤ
  k : ℤ
  a_j : ℤ
  b_k : ℤ

structure Term where
  coefficient : Nat
  e_f : Nat
  e_r : Nat
  e_delta : Nat
  e_beta : Nat
  e_g : Nat
  e_u : Nat
  e_alpha : Nat
  e_w : Nat
  e_theta : Nat
  e_eps : Nat
  e_k : Nat
  e_a_j : Nat
  e_b_k : Nat

def evalTerm (y : Variables) (t : Term) : ℤ :=
  t.coefficient * y.f ^ t.e_f * y.r ^ t.e_r * y.delta ^ t.e_delta * y.beta ^ t.e_beta * y.g ^ t.e_g * y.u ^ t.e_u * y.alpha ^ t.e_alpha * y.w ^ t.e_w * y.theta ^ t.e_theta * y.eps ^ t.e_eps * y.k ^ t.e_k * y.a_j ^ t.e_a_j * y.b_k ^ t.e_b_k

theorem evalTerm_nonneg (y : Variables)
    (h_f : 0 ≤ y.f)
    (h_r : 0 ≤ y.r)
    (h_delta : 0 ≤ y.delta)
    (h_beta : 0 ≤ y.beta)
    (h_g : 0 ≤ y.g)
    (h_u : 0 ≤ y.u)
    (h_alpha : 0 ≤ y.alpha)
    (h_w : 0 ≤ y.w)
    (h_theta : 0 ≤ y.theta)
    (h_eps : 0 ≤ y.eps)
    (h_k : 0 ≤ y.k)
    (h_a_j : 0 ≤ y.a_j)
    (h_b_k : 0 ≤ y.b_k)
    (t : Term) : 0 ≤ evalTerm y t := by
  simp only [evalTerm]
  positivity

end P21.Nonsymmetric.ChainCore.C9.LinearCertificateData
