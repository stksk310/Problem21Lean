import P21.Nonsymmetric.Path.PFree

namespace P21.Nonsymmetric
namespace PathInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

/-- Transport the two named normalized central factorizations through the
full PATH reversal.  The vectors themselves are permuted; no factorization
is reselected. -/
def NoPairNormalization.reverse (P : PathInput s F D)
    (N : NoPairNormalization P) : NoPairNormalization P.reverse where
  atA := by
    simpa [PathInput.reverse, relabel] using
      (relabelFactorization pathReversePerm N.atB)
  atB := by
    simpa [PathInput.reverse, relabel] using
      (relabelFactorization pathReversePerm N.atA)
  A_i_lt := by
    change N.atB.coeff 2 < D.rho 2
    exact N.B_k_lt
  A_j_lt := by
    change N.atB.coeff 1 < D.rho 1
    exact N.B_j_lt
  A_k_lt := by
    change N.atB.coeff 0 < P.beta.toNat
    exact N.B_i_lt
  B_i_lt := by
    change N.atA.coeff 2 < P.alpha.toNat
    exact N.A_k_lt
  B_j_lt := by
    change N.atA.coeff 1 < D.rho 1
    exact N.A_j_lt
  B_k_lt := by
    change N.atA.coeff 0 < D.rho 0
    exact N.A_i_lt

theorem NoPairNormalization.reverse_middle_lt (P : PathInput s F D)
    (N : NoPairNormalization P) (h : N.atB.coeff 1 < N.atA.coeff 1) :
    (N.reverse P).atA.coeff 1 < (N.reverse P).atB.coeff 1 := by
  change N.atB.coeff 1 < N.atA.coeff 1
  exact h

/-- The equal-middle seam is impossible.  Criticality is applied only to
the displayed pure-H relation after the two actual central equations have
cancelled their common `m` term. -/
theorem NoPairNormalization.middle_ne (P : PathInput s F D)
    (N : NoPairNormalization P) : N.atA.coeff 1 ≠ N.atB.coeff 1 := by
  intro heq
  have hrel0 := N.central_relation P
  rw [heq, sub_self, zero_mul, add_zero] at hrel0
  have hAc := N.Ac_pos P
  have hBc := N.Bc_pos P
  have hcrit0 := herzog_critical_le_int D (by decide : (0 : Fin 3) ≠ 1)
    (by decide : (0 : Fin 3) ≠ 2) (N.Ac P) 0 (N.Bc P)
    hAc (by omega) hBc.le (by simpa using hrel0)
  let v : ℤ := N.Bc P - D.a 2
  have hvpos : 0 < v := by
    have hp0 : 0 < g.n 0 := lt_trans s.m_pos (s.n_gt 0)
    have hp1 : 0 < g.n 1 := lt_trans s.m_pos (s.n_gt 1)
    have hp2 : 0 < g.n 2 := lt_trans s.m_pos (s.n_gt 2)
    have hz : v * g.n 2 =
        (N.Ac P - D.rho 0) * g.n 0 + (D.b 1 : ℤ) * g.n 1 := by
      dsimp [v]
      linear_combination -hrel0 + D.relation_zero
    have hnonneg : 0 ≤ (N.Ac P - D.rho 0) * g.n 0 :=
      mul_nonneg (by omega) hp0.le
    have hpositive : 0 < (D.b 1 : ℤ) * g.n 1 :=
      mul_pos (by exact_mod_cast D.b_pos 1) hp1
    nlinarith
  have hvlt : v < D.rho 2 := by
    have hk := N.B_k_lt
    have hnu := P.nu_range.1
    have hr2 : (D.rho 2 : ℤ) = D.a 2 + D.b 2 := by
      exact_mod_cast D.rho_eq 2
    have halpha : P.alpha = (D.a 2 : ℤ) - P.nu := rfl
    simp only [v, NoPairNormalization.Bc]
    omega
  have hz : v * g.n 2 =
      (N.Ac P - D.rho 0) * g.n 0 + (D.b 1 : ℤ) * g.n 1 := by
    dsimp [v]
    linear_combination -hrel0 + D.relation_zero
  have hcrit2 := herzog_critical_le_int D (by decide : (2 : Fin 3) ≠ 0)
    (by decide : (2 : Fin 3) ≠ 1) v (N.Ac P - D.rho 0) (D.b 1)
    hvpos (by omega) (by exact_mod_cast (D.b_pos 1).le) hz
  omega

/-- Publication P5.1: the two genuine central returns exhaust into PAIR,
the left PFREE kernel, or the formally transported right PFREE kernel. -/
theorem pair_or_pfree_or_dual (P : PathInput s F D) :
    Nonempty (Pair P) ∨ Nonempty (PFreeI P) ∨
      Nonempty (PFreeI P.reverse) := by
  classical
  by_cases hp : Nonempty (Pair P)
  · exact Or.inl hp
  · right
    have hnp : P.NoPair := hp
    obtain ⟨C⟩ := P.central_returns
    obtain ⟨N⟩ := P.no_pair_normalization hnp C
    rcases N.middle_trichotomy P with hlt | heq | hgt
    · exact Or.inl (P.pfree_of_middle_lt N hlt)
    · exact (N.middle_ne P heq).elim
    · exact Or.inr (P.reverse.pfree_of_middle_lt (N.reverse P)
        (N.reverse_middle_lt P hgt))

end PathInput
end P21.Nonsymmetric
