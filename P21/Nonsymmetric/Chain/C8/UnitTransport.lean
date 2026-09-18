import P21.Nonsymmetric.Chain.C8.UnitMultiplicity

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} (O : A.OneData E)

theorem unit_EB_equation (U : O.UnitParam) (hUj : (D.a 1 : ℤ)≤E.Uj) :
    K.chain.qB+g.n 0 = g.m+(Q E-(D.a 1 : ℤ)-1)*g.n 1+
      (E.Uk+(D.b 2 : ℤ))*g.n 2 := by
  have hea := E.EA_eq
  rw [U.Li_one, U.Uj_eq] at hea
  simp only [one_mul] at hea
  simp only [ChainInput.qA, ChainInput.qB, HerzogCriticalData.fA,
    HerzogCriticalData.fB]
  simp only [ChainInput.qA, HerzogCriticalData.fA] at hea
  linear_combination hea

/-- Genuine nonnegative level-one EB factorization transported from the
actual level-one EA return. -/
noncomputable def unit_EB_factorization (U : O.UnitParam)
    (hUj : (D.a 1 : ℤ)≤E.Uj) : g.ActualFactorization4 (K.chain.qB+g.n 0) := by
  have hq : 0≤Q E-(D.a 1 : ℤ)-1 := by
    have he := U.Uj_eq
    nlinarith
  have hk : 0≤E.Uk+(D.b 2 : ℤ) := by
    have := E.coeff_nonneg.2.1
    have hb := D.b_pos 2
    omega
  let coeff : Fin 4 → ℕ :=
    ![1,0,(Q E-(D.a 1 : ℤ)-1).toNat,(E.Uk+(D.b 2 : ℤ)).toNat]
  have hqN : ((Q E-(D.a 1 : ℤ)-1).toNat : ℤ)=Q E-(D.a 1 : ℤ)-1 :=
    Int.toNat_of_nonneg hq
  have hkN : ((E.Uk+(D.b 2 : ℤ)).toNat : ℤ)=E.Uk+(D.b 2 : ℤ) :=
    Int.toNat_of_nonneg hk
  exact {
    coeff := coeff
    equation := by
      simp only [value, Fin.sum_univ_four]
      dsimp [coeff, Generators.all]
      rw [hqN, hkN]
      have hall2 : (@Fin.cons 3 (fun _ => ℤ) g.m g.n) (2 : Fin 4)=g.n 1 := rfl
      have hall3 : (@Fin.cons 3 (fun _ => ℤ) g.m g.n) (3 : Fin 4)=g.n 2 := rfl
      rw [hall2, hall3]
      simpa [Generators.all, add_assoc] using (O.unit_EB_equation U hUj).symm }

theorem unit_EB_actual (U : O.UnitParam) (hUj : (D.a 1 : ℤ)≤E.Uj) :
    K.chain.qB+g.n 0∈g.Gamma :=
  ⟨(O.unit_EB_factorization U hUj).coeff,
    (O.unit_EB_factorization U hUj).equation⟩

end P21.Nonsymmetric.ChainCore.FirstFit.OneData
