import P21.Nonsymmetric.Chain.Setup
import P21.Nonsymmetric.ReturnLevels

namespace P21.Nonsymmetric
namespace ChainInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

/-- The actual Section 7 PFIBER factorization of the named element `P*n_i`. -/
structure PFiber (C : ChainInput s F D) where
  L : ℤ
  t : ℤ
  u : ℤ
  L_pos : 1 ≤ L
  t_nonneg : 0 ≤ t
  u_nonneg : 0 ≤ u
  equation : C.P * g.n 0 = L * g.m + (t + 1) * g.n 1 + (u + 1) * g.n 2
  actual : g.ActualFactorization4 (C.P * g.n 0)
  coeff_m : (actual.coeff 0 : ℤ) = L
  coeff_i : actual.coeff 1 = 0
  coeff_j : (actual.coeff 2 : ℤ) = t + 1
  coeff_k : (actual.coeff 3 : ℤ) = u + 1

private def matchedPair (C : ChainInput s F D) :
    MatchedPairData g F D C.qA C.qB where
  depth := C.lambda
  gapJ := C.gapJ
  gapK := C.alpha
  P := C.P
  R := C.R
  T := C.T
  depth_pos := by have := C.lambda_range.1; omega
  depth_a := C.lambda_range.2.1
  depth_b := C.lambda_range.2.2
  gapJ_nonneg := by have := C.scalar_ranges.2.2.1; omega
  gapK_nonneg := by have := C.scalar_ranges.2.2.2; omega
  P_eq := rfl
  R_eq := C.R_exact
  T_eq := C.T_exact
  R_lt := by simp [R]; have := C.mu_range.1; omega
  T_lt := by simp [T]; have := C.nu_range.1; omega
  qA_eq := rfl
  qB_eq := rfl
  compA := C.cA_exact
  compB := C.cB_exact
  W_eq := C.W_exact

theorem pfiber_exists (C : ChainInput s F D) (hF : s.semigroup.IsFrobenius F) :
    Nonempty C.PFiber := by
  obtain ⟨L, t, u, hL, ht, hu, _, _, he⟩ :=
    root_free_level_rigidity s hF C.matchedPair C.qA_actual C.qB_actual
  let coeff : Fin 4 → ℕ := ![L.toNat, 0, (t + 1).toNat, (u + 1).toNat]
  have hLc : (L.toNat : ℤ) = L := Int.toNat_of_nonneg hL.le
  have htc : ((t + 1).toNat : ℤ) = t + 1 := Int.toNat_of_nonneg (by omega)
  have huc : ((u + 1).toNat : ℤ) = u + 1 := Int.toNat_of_nonneg (by omega)
  let actual : g.ActualFactorization4 (C.P * g.n 0) := {
    coeff := coeff
    equation := by
      simp [value, Generators.all, Fin.sum_univ_succ, coeff, hLc, htc, huc]
      simpa [matchedPair, add_assoc] using he.symm }
  exact ⟨{
    L := L, t := t, u := u, L_pos := by omega, t_nonneg := ht, u_nonneg := hu,
    equation := he, actual := actual,
    coeff_m := by simp [actual, coeff, hLc],
    coeff_i := by rfl,
    coeff_j := by simp [actual, coeff, htc],
    coeff_k := by simp [actual, coeff, huc] }⟩

end ChainInput
end P21.Nonsymmetric
