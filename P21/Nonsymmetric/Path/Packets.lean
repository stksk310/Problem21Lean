import P21.Nonsymmetric.Path.Central

namespace P21.Nonsymmetric

variable {g : Generators}

private def packetSource (D : HerzogCriticalData g) (i : Fin 3) (k : ℕ) :
    Fin 3 → ℕ := fun j => if j = i then k * D.rho i else 0

private def packetTarget (D : HerzogCriticalData g) (i : Fin 3) (k : ℕ) :
    Fin 3 → ℕ := fun j => k * D.relationCoeff i j

/-- Replace `k` whole critical packets inside one named actual tail
factorization.  The output is definitionally tied to that same witness. -/
def replacePacketCopies (D : HerzogCriticalData g) {x : ℤ}
    (a : g.ActualFactorization3 x) (i : Fin 3) (k : ℕ)
    (hcontained : k * D.rho i ≤ a.coeff i) : g.ActualFactorization3 x := by
  let source := packetSource D i k
  let target := packetTarget D i k
  have hs : ∀ j, source j ≤ a.coeff j := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [source, packetSource] using hcontained
    · simp [source, packetSource, hji]
  have he : value g.n source = value g.n target := by
    have hr := D.relationCoeff_value i
    calc
      value g.n source = (k : ℤ) * (D.rho i : ℤ) * g.n i := by
        simp [source, packetSource, value, Nat.cast_mul]
      _ = (k : ℤ) * value g.n (D.relationCoeff i) := by rw [hr]; ring
      _ = value g.n target := by
        simp [target, packetTarget, value, Nat.cast_mul, Finset.mul_sum, mul_assoc]
  exact replaceWithinActualFactorization a source target hs he

theorem replacePacketCopies_self_coeff (D : HerzogCriticalData g) {x : ℤ}
    (a : g.ActualFactorization3 x) (i : Fin 3) (k : ℕ)
    (hcontained : k * D.rho i ≤ a.coeff i) :
    (replacePacketCopies D a i k hcontained).coeff i = a.coeff i - k * D.rho i := by
  simp only [replacePacketCopies, replaceWithinActualFactorization]
  simp only [packetSource, packetTarget, if_pos, D.relationCoeff_self,
    mul_zero, Nat.cast_zero, add_zero]
  change ((a.coeff i : ℤ) - (k * D.rho i : ℕ)).toNat =
    a.coeff i - k * D.rho i
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_sub_of_le (by exact_mod_cast hcontained)]
  rw [Nat.cast_sub hcontained]

/-- Normalize one coordinate by replacing the maximum number of whole
critical packets. -/
def reduceCriticalCoordinate (D : HerzogCriticalData g) {x : ℤ}
    (a : g.ActualFactorization3 x) (i : Fin 3) : g.ActualFactorization3 x :=
  replacePacketCopies D a i (a.coeff i / D.rho i) (by
    simpa [Nat.mul_comm] using Nat.mul_div_le (a.coeff i) (D.rho i))

theorem reduceCriticalCoordinate_self (D : HerzogCriticalData g) {x : ℤ}
    (a : g.ActualFactorization3 x) (i : Fin 3) :
    (reduceCriticalCoordinate D a i).coeff i = a.coeff i % D.rho i := by
  rw [reduceCriticalCoordinate, replacePacketCopies_self_coeff]
  rw [Nat.mod_eq_sub_mul_div]
  simp [Nat.mul_comm]

theorem reduceCriticalCoordinate_lt (D : HerzogCriticalData g) {x : ℤ}
    (a : g.ActualFactorization3 x) (i : Fin 3) :
    (reduceCriticalCoordinate D a i).coeff i < D.rho i := by
  rw [reduceCriticalCoordinate_self]
  exact Nat.mod_lt _ (D.rho_pos i)

end P21.Nonsymmetric
