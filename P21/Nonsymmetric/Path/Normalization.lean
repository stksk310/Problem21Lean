import P21.Nonsymmetric.Path.Pair

namespace P21.Nonsymmetric
namespace PathInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

/-- The two no-PAIR central vectors, with every publication bound attached to
the named actual factorization that supplies its coefficients. -/
structure NoPairNormalization (P : PathInput s F D) where
  atA : g.ActualFactorization3 (P.qA + g.m)
  atB : g.ActualFactorization3 (P.qB + g.m)
  A_i_lt : atA.coeff 0 < D.rho 0
  A_j_lt : atA.coeff 1 < D.rho 1
  A_k_lt : atA.coeff 2 < P.alpha.toNat
  B_i_lt : atB.coeff 0 < P.beta.toNat
  B_j_lt : atB.coeff 1 < D.rho 1
  B_k_lt : atB.coeff 2 < D.rho 2

theorem no_pair_normalization (P : PathInput s F D) (hnp : P.NoPair)
    (C : P.CentralReturns) : Nonempty (NoPairNormalization P) := by
  let a := reduceCriticalCoordinate D C.atA 1
  let b := reduceCriticalCoordinate D C.atB 1
  have haJ : a.coeff 1 < D.rho 1 := reduceCriticalCoordinate_lt D C.atA 1
  have hbJ : b.coeff 1 < D.rho 1 := reduceCriticalCoordinate_lt D C.atB 1
  have haK : a.coeff 2 < P.alpha.toNat := hnp.A_k_lt P a
  have hbI : b.coeff 0 < P.beta.toNat := hnp.B_i_lt P b
  have halpha : P.alpha.toNat < D.a 2 := by
    have hc : (P.alpha.toNat : ℤ) = P.alpha :=
      Int.toNat_of_nonneg (by have := P.alpha_pos; omega)
    have hr := P.nu_range.1
    have he : P.alpha = (D.a 2 : ℤ) - P.nu := rfl
    omega
  have hbeta : P.beta.toNat < D.b 0 := by
    have hc : (P.beta.toNat : ℤ) = P.beta :=
      Int.toNat_of_nonneg (by have := P.beta_pos; omega)
    have hr := P.lambda_range.1
    have he : P.beta = (D.b 0 : ℤ) - P.lambda := rfl
    omega
  have haI : a.coeff 0 < D.rho 0 := by
    by_contra hh
    have hle : D.rho 0 ≤ a.coeff 0 := by omega
    let a' := replacePacketCopies D a 0 1 (by simpa using hle)
    have hk := replacePacketCopies_off_coeff D a 0 2 1 (by simpa using hle)
      (by decide)
    have hk' : a'.coeff 2 = a.coeff 2 + D.a 2 := by
      simpa [a', HerzogCriticalData.relationCoeff] using hk
    have := hnp.A_k_lt P a'
    omega
  have hbK : b.coeff 2 < D.rho 2 := by
    by_contra hh
    have hle : D.rho 2 ≤ b.coeff 2 := by omega
    let b' := replacePacketCopies D b 2 1 (by simpa using hle)
    have hi := replacePacketCopies_off_coeff D b 2 0 1 (by simpa using hle)
      (by decide)
    have hi' : b'.coeff 0 = b.coeff 0 + D.b 0 := by
      simpa [b', HerzogCriticalData.relationCoeff] using hi
    have := hnp.B_i_lt P b'
    omega
  exact ⟨⟨a, b, haI, haJ, haK, hbI, hbJ, hbK⟩⟩

end PathInput
end P21.Nonsymmetric
