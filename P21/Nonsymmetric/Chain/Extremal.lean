import P21.Nonsymmetric.Chain.PFiber

namespace P21.Nonsymmetric
namespace ChainInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

def hA (C : ChainInput s F D) : ℤ := C.qA + g.m

def hFactorSet (C : ChainInput s F D) : Set (Fin 3 → ℕ) :=
  {a | value g.n a = C.hA}

/-- A named maximal-i factorization of the same actual element `hA`. -/
structure MaxIFactorization (C : ChainInput s F D) where
  factorization : g.ActualFactorization3 C.hA
  maximal : ∀ a : g.ActualFactorization3 C.hA,
    a.coeff 0 ≤ factorization.coeff 0

namespace MaxIFactorization

def X {C : ChainInput s F D} (M : C.MaxIFactorization) : ℤ := M.factorization.coeff 0
def Y {C : ChainInput s F D} (M : C.MaxIFactorization) : ℤ := M.factorization.coeff 1
def Z {C : ChainInput s F D} (M : C.MaxIFactorization) : ℤ := M.factorization.coeff 2

theorem equation {C : ChainInput s F D} (M : C.MaxIFactorization) :
    C.hA = M.X * g.n 0 + M.Y * g.n 1 + M.Z * g.n 2 := by
  have h := M.factorization.equation.symm
  simpa [X, Y, Z, value, Fin.sum_univ_succ, add_assoc] using h

theorem coeff_nonneg {C : ChainInput s F D} (M : C.MaxIFactorization) :
    0 ≤ M.X ∧ 0 ≤ M.Y ∧ 0 ≤ M.Z := by
  exact ⟨Int.natCast_nonneg _, Int.natCast_nonneg _, Int.natCast_nonneg _⟩

end MaxIFactorization

private theorem hfactor_coord_bound (C : ChainInput s F D) (a : Fin 3 → ℕ)
    (ha : value g.n a = C.hA) (i : Fin 3) : a i ≤ C.hA.toNat := by
  have hp : ∀ j, 0 < g.n j := fun j => lt_trans s.m_pos (s.n_gt j)
  have he := ha
  rw [value_cyclic g a i] at he
  have h1 : 0 ≤ (a (next i) : ℤ) * g.n (next i) :=
    mul_nonneg (Int.natCast_nonneg _) (hp _).le
  have h2 : 0 ≤ (a (prev i) : ℤ) * g.n (prev i) :=
    mul_nonneg (Int.natCast_nonneg _) (hp _).le
  have hmul : (a i : ℤ) ≤ (a i : ℤ) * g.n i := by
    have hn : 0 ≤ g.n i - 1 := by have := hp i; omega
    nlinarith [mul_nonneg (Int.natCast_nonneg (a i)) hn]
  have hi : (a i : ℤ) ≤ C.hA := by
    nlinarith
  have hh : 0 ≤ C.hA := by
    have hm : 0 ≤ (a i : ℤ) * g.n i :=
      mul_nonneg (Int.natCast_nonneg _) (hp _).le
    nlinarith
  have hcast : (a i : ℤ) ≤ (C.hA.toNat : ℤ) := by
    rw [Int.toNat_of_nonneg hh]
    exact hi
  exact_mod_cast hcast

theorem hFactorSet_finite (C : ChainInput s F D) : C.hFactorSet.Finite := by
  classical
  refine (Set.finite_range
    (fun a : Fin 3 → Fin (C.hA.toNat + 1) => fun i => (a i : ℕ))).subset ?_
  intro a ha
  refine ⟨fun i => ⟨a i, Nat.lt_succ_iff.mpr (hfactor_coord_bound C a ha i)⟩, ?_⟩
  funext i
  rfl

theorem hFactorSet_nonempty (C : ChainInput s F D) : C.hFactorSet.Nonempty := by
  have hq := C.qA_actual
  have hmne : g.m ≠ 0 := ne_of_gt s.m_pos
  have hret := hq.1.2 g.m g.m_mem hmne
  change C.hA ∈ g.Gamma at hret
  obtain ⟨a⟩ := actual_iff_mem.mpr hret
  have hz : a.coeff 0 = 0 := by
    by_contra hn
    have hmem := actual_iff_mem.mp
      ⟨removeOne a 0 (Nat.pos_of_ne_zero hn)⟩
    apply hq.1.1
    change C.qA ∈ g.Gamma
    simpa [hA, Generators.all, Generators.Gamma] using hmem
  let b : Fin 3 → ℕ := fun i => a.coeff i.succ
  refine ⟨b, ?_⟩
  have he := a.equation
  simpa [hFactorSet, hA, b, value, Generators.all, Fin.sum_univ_succ, hz] using he

theorem max_i_exists (C : ChainInput s F D) : Nonempty C.MaxIFactorization := by
  classical
  let p : ℕ → Prop := fun x => ∃ a ∈ C.hFactorSet, a 0 = x
  obtain ⟨a, ha⟩ := C.hFactorSet_nonempty
  have hbound : ∀ x, p x → x ≤ C.hA.toNat := by
    rintro x ⟨b, hb, rfl⟩
    exact hfactor_coord_bound C b hb 0
  have hp : p (a 0) := ⟨a, ha, rfl⟩
  have hpmax : p (Nat.findGreatest p C.hA.toNat) :=
    Nat.findGreatest_spec (hbound _ hp) hp
  obtain ⟨b, hb, hbx⟩ := hpmax
  let factorization : g.ActualFactorization3 C.hA := ⟨b, hb⟩
  refine ⟨{ factorization := factorization, maximal := ?_ }⟩
  intro c
  have hc : p (c.coeff 0) := ⟨c.coeff, c.equation, rfl⟩
  have hle := Nat.le_findGreatest (hbound _ hc) hc
  simpa [factorization, hbx] using hle

private theorem P_pos (C : ChainInput s F D) : 1 ≤ C.P := by
  have := C.P_eq_a_beta
  have ha : (1 : ℤ) ≤ D.a 0 := by exact_mod_cast D.a_pos 0
  have hb := C.scalar_ranges.2.1
  omega

theorem X_cap (C : ChainInput s F D) (PF : C.PFiber) (M : C.MaxIFactorization) :
    M.X ≤ C.P - 1 := by
  by_contra hn
  have hXP : C.P ≤ M.X := by omega
  have hm := four_mem (g := g) (PF.L - 1) (M.X - C.P)
    (M.Y + PF.t + 1) (M.Z + PF.u + 1)
    (by have := PF.L_pos; omega) (by omega)
    (by have := M.coeff_nonneg; have := PF.t_nonneg; omega)
    (by have := M.coeff_nonneg; have := PF.u_nonneg; omega)
  apply C.qA_actual.1.1
  change C.qA ∈ g.Gamma
  convert hm using 1
  have hmax := M.equation
  have hpf := PF.equation
  simp only [hA] at hmax
  nlinarith

theorem Y_cap (C : ChainInput s F D) (M : C.MaxIFactorization) :
    M.Y ≤ (D.rho 1 : ℤ) - 1 := by
  by_contra hn
  have hYr : (D.rho 1 : ℤ) ≤ M.Y := by omega
  let coeff : Fin 3 → ℕ :=
    ![M.factorization.coeff 0 + D.a 0,
      M.factorization.coeff 1 - D.rho 1,
      M.factorization.coeff 2 + D.b 2]
  let b : g.ActualFactorization3 C.hA := {
    coeff := coeff
    equation := by
      have he := M.factorization.equation
      have hr := D.relation_one
      have hsub : ((M.factorization.coeff 1 - D.rho 1 : ℕ) : ℤ) = M.Y - D.rho 1 := by
        have hNat : D.rho 1 ≤ M.factorization.coeff 1 := by
          change (D.rho 1 : ℤ) ≤ (M.factorization.coeff 1 : ℤ) at hYr
          exact_mod_cast hYr
        rw [Nat.cast_sub hNat]
        rfl
      simp [coeff, value, Fin.sum_univ_succ, MaxIFactorization.X,
        MaxIFactorization.Y, MaxIFactorization.Z, hsub] at he ⊢
      linear_combination he - hr }
  have hmax := M.maximal b
  simp [b, coeff] at hmax
  have ha : 0 < D.a 0 := D.a_pos 0
  omega

theorem Z_cap (C : ChainInput s F D) (M : C.MaxIFactorization) :
    M.Z ≤ (D.rho 2 : ℤ) - 1 := by
  by_contra hn
  have hZr : (D.rho 2 : ℤ) ≤ M.Z := by omega
  let coeff : Fin 3 → ℕ :=
    ![M.factorization.coeff 0 + D.b 0,
      M.factorization.coeff 1 + D.a 1,
      M.factorization.coeff 2 - D.rho 2]
  let b : g.ActualFactorization3 C.hA := {
    coeff := coeff
    equation := by
      have he := M.factorization.equation
      have hr := D.relation_two
      have hsub : ((M.factorization.coeff 2 - D.rho 2 : ℕ) : ℤ) = M.Z - D.rho 2 := by
        have hNat : D.rho 2 ≤ M.factorization.coeff 2 := by
          change (D.rho 2 : ℤ) ≤ (M.factorization.coeff 2 : ℤ) at hZr
          exact_mod_cast hZr
        rw [Nat.cast_sub hNat]
        rfl
      simp [coeff, value, Fin.sum_univ_succ, MaxIFactorization.X,
        MaxIFactorization.Y, MaxIFactorization.Z, hsub] at he ⊢
      linear_combination he - hr }
  have hmax := M.maximal b
  simp [b, coeff] at hmax
  have hb : 0 < D.b 0 := D.b_pos 0
  omega

theorem max_i_box (C : ChainInput s F D) (PF : C.PFiber) (M : C.MaxIFactorization) :
    0 ≤ M.X ∧ M.X ≤ C.P - 1 ∧
    0 ≤ M.Y ∧ M.Y ≤ (D.rho 1 : ℤ) - 1 ∧
    0 ≤ M.Z ∧ M.Z ≤ (D.rho 2 : ℤ) - 1 := by
  obtain ⟨hX, hY, hZ⟩ := M.coeff_nonneg
  exact ⟨hX, C.X_cap PF M, hY, C.Y_cap M, hZ, C.Z_cap M⟩

end ChainInput
end P21.Nonsymmetric
