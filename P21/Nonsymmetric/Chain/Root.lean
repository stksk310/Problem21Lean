import P21.Nonsymmetric.Chain.Extremal

namespace P21.Nonsymmetric
namespace ChainInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

/-- ROOT0 together with the bounds before Frobenius-gap exclusion. -/
structure RootSeed (C : ChainInput s F D) where
  maxI : C.MaxIFactorization
  d : ℤ
  S : ℤ
  Croot : ℤ
  d_eq : d = C.P - 1 - maxI.X
  S_eq : S = maxI.Y - D.a 1 + 1
  Croot_eq : Croot = maxI.Z + 1
  root : g.m + d * g.n 0 = S * g.n 1 + Croot * g.n 2
  initial : 0 ≤ d ∧ d ≤ C.P - 1 ∧
    1 - D.a 1 ≤ S ∧ S ≤ D.b 1 ∧ 1 ≤ Croot ∧ Croot ≤ D.rho 2

/-- The complete ROOT-BOX and strictness package before orientation. -/
structure RootBox (C : ChainInput s F D) where
  d : ℤ
  S : ℤ
  Croot : ℤ
  root : g.m + d * g.n 0 = S * g.n 1 + Croot * g.n 2
  d_range : 1 ≤ d ∧ d ≤ C.lambda
  S_range : C.gapJ ≤ S ∧ S ≤ D.b 1
  C_range : C.alpha ≤ Croot ∧ Croot ≤ D.rho 2
  strict : C.gapJ + 1 ≤ S ∨ C.alpha + 1 ≤ Croot

def root_seed (C : ChainInput s F D) (PF : C.PFiber) (M : C.MaxIFactorization) :
    C.RootSeed := by
  obtain ⟨hX0, hX, hY0, hY, hZ0, hZ⟩ := C.max_i_box PF M
  have hr1 : (D.rho 1 : ℤ) = D.a 1 + D.b 1 := by exact_mod_cast D.rho_eq 1
  refine {
    maxI := M
    d := C.P - 1 - M.X
    S := M.Y - D.a 1 + 1
    Croot := M.Z + 1
    d_eq := rfl
    S_eq := rfl
    Croot_eq := rfl
    root := ?_
    initial := ?_ }
  · have hm := M.equation
    have hq := C.qA_exact
    simp only [hA] at hm
    linear_combination hm - hq
  · constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega

namespace RootSeed

variable {C : ChainInput s F D} (N : C.RootSeed)

theorem F_base :
    F = (C.P + N.d - 1) * g.n 0 + (C.R - N.S - 1) * g.n 1 +
      (C.T - N.Croot - 1) * g.n 2 := by
  have hw := C.W_exact
  have hr := N.root
  simp only [W] at hw
  linear_combination hw - hr

theorem F_S :
    F = (C.delta + N.d - 1) * g.n 0 + (C.gapJ - N.S - 1) * g.n 1 +
      ((D.rho 2 : ℤ) + C.T - N.Croot - 1) * g.n 2 := by
  have hb := N.F_base
  have hp := C.P_eq_b_delta
  have hR := C.R_exact
  rw [hp, hR] at hb
  linear_combination hb - D.relation_two

theorem S_lower (hF : s.semigroup.IsFrobenius F) : C.gapJ ≤ N.S := by
  by_contra hn
  have hS : N.S ≤ C.gapJ - 1 := by omega
  have he := N.F_S
  have hm := four_mem (g := g) 0 (C.delta + N.d - 1)
    (C.gapJ - N.S - 1) ((D.rho 2 : ℤ) + C.T - N.Croot - 1)
    (by omega)
    (by have := C.scalar_ranges.1; have := N.initial.1; omega)
    (by omega)
    (by
      have := N.initial.2.2.2.2.2
      have hT : 1 ≤ C.T := by rw [C.T_exact]; have := D.b_pos 2; have := C.scalar_ranges.2.2.2; omega
      omega)
  apply hF.1
  change F ∈ g.Gamma
  convert hm using 1
  simpa using he

theorem F_C :
    F = (C.beta + N.d - 1) * g.n 0 +
      ((D.rho 1 : ℤ) + C.R - N.S - 1) * g.n 1 +
      (C.alpha - N.Croot - 1) * g.n 2 := by
  have hb := N.F_base
  have hp := C.P_eq_a_beta
  have hT := C.T_exact
  rw [hp, hT] at hb
  linear_combination hb - D.relation_one

theorem C_lower (hF : s.semigroup.IsFrobenius F) : C.alpha ≤ N.Croot := by
  by_contra hn
  have hC : N.Croot ≤ C.alpha - 1 := by omega
  have he := N.F_C
  have hm := four_mem (g := g) 0 (C.beta + N.d - 1)
    ((D.rho 1 : ℤ) + C.R - N.S - 1) (C.alpha - N.Croot - 1)
    (by omega)
    (by have := C.scalar_ranges.2.1; have := N.initial.1; omega)
    (by
      have hS := N.initial.2.2.2.1
      have hR := C.R_exact
      have hr : (D.rho 1 : ℤ) = D.a 1 + D.b 1 := by exact_mod_cast D.rho_eq 1
      have ha : (1 : ℤ) ≤ D.a 1 := by exact_mod_cast D.a_pos 1
      have hg := C.scalar_ranges.2.2.1
      omega)
    (by omega)
  apply hF.1
  change F ∈ g.Gamma
  convert hm using 1
  simpa using he

theorem d_pos (hF : s.semigroup.IsFrobenius F) : 1 ≤ N.d := by
  have hS := N.S_lower hF
  have hC := N.C_lower hF
  have hg := C.scalar_ranges.2.2.1
  have ha := C.scalar_ranges.2.2.2
  by_contra hn
  have hd : N.d = 0 := by have := N.initial.1; omega
  have hj : 0 < g.n 1 := lt_trans s.m_pos (s.n_gt 1)
  have hk : 0 < g.n 2 := lt_trans s.m_pos (s.n_gt 2)
  have hSj : g.n 1 ≤ N.S * g.n 1 := by
    nlinarith [mul_nonneg (show 0 ≤ N.S - 1 by omega) hj.le]
  have hCk : 0 ≤ N.Croot * g.n 2 := mul_nonneg (by omega) hk.le
  have hm := N.root
  rw [hd] at hm
  have := s.n_gt 1
  nlinarith

theorem F_D :
    F = (N.d - C.lambda - 1) * g.n 0 +
      (C.R + D.b 1 - N.S - 1) * g.n 1 +
      (C.T + D.a 2 - N.Croot - 1) * g.n 2 := by
  have hb := N.F_base
  have hp' : C.P = (D.rho 0 : ℤ) - C.lambda := by simp [P]
  rw [hp'] at hb
  linear_combination hb + D.relation_zero

theorem d_upper (hF : s.semigroup.IsFrobenius F) : N.d ≤ C.lambda := by
  by_contra hn
  have hd : C.lambda + 1 ≤ N.d := by omega
  have hS := N.initial.2.2.2.1
  have hC := N.initial.2.2.2.2.2
  have hT := C.T_exact
  have ha : (1 : ℤ) ≤ D.a 2 := by exact_mod_cast D.a_pos 2
  have halpha := C.scalar_ranges.2.2.2
  have hr2 : (D.rho 2 : ℤ) = D.a 2 + D.b 2 := by exact_mod_cast D.rho_eq 2
  have he := N.F_D
  have hm := four_mem (g := g) 0 (N.d - C.lambda - 1)
    (C.R + D.b 1 - N.S - 1) (C.T + D.a 2 - N.Croot - 1)
    (by omega) (by omega)
    (by
      have hR : 1 ≤ C.R := by rw [C.R_exact]; have := D.a_pos 1; have := C.scalar_ranges.2.2.1; omega
      omega)
    (by omega)
  apply hF.1
  change F ∈ g.Gamma
  convert hm using 1
  simpa using he

theorem strict (hF : s.semigroup.IsFrobenius F) :
    C.gapJ + 1 ≤ N.S ∨ C.alpha + 1 ≤ N.Croot := by
  have hS := N.S_lower hF
  have hC := N.C_lower hF
  by_contra hn
  simp only [not_or, not_le] at hn
  have hSe : N.S = C.gapJ := by omega
  have hCe : N.Croot = C.alpha := by omega
  have hb := N.F_base
  have hR := C.R_exact
  have hT := C.T_exact
  have hP : 1 ≤ C.P := by
    rw [C.P_eq_a_beta]
    have := D.a_pos 0
    have := C.scalar_ranges.2.1
    omega
  have hd := N.d_pos hF
  have ha1 : (1 : ℤ) ≤ D.a 1 := by exact_mod_cast D.a_pos 1
  have hb2 : (1 : ℤ) ≤ D.b 2 := by exact_mod_cast D.b_pos 2
  have hm := four_mem (g := g) 0 (C.P + N.d - 1) (D.a 1 - 1) (D.b 2 - 1)
    (by omega) (by omega) (by omega) (by omega)
  apply hF.1
  change F ∈ g.Gamma
  convert hm using 1
  rw [hSe, hCe] at hb
  linear_combination hb + g.n 1 * hR + g.n 2 * hT

end RootSeed

def root_box (C : ChainInput s F D) (hF : s.semigroup.IsFrobenius F)
    (PF : C.PFiber) (M : C.MaxIFactorization) : C.RootBox := by
  let N := C.root_seed PF M
  have hS := N.S_lower hF
  have hC := N.C_lower hF
  exact {
    d := N.d
    S := N.S
    Croot := N.Croot
    root := N.root
    d_range := ⟨N.d_pos hF, N.d_upper hF⟩
    S_range := ⟨hS, N.initial.2.2.2.1⟩
    C_range := ⟨hC, N.initial.2.2.2.2.2⟩
    strict := N.strict hF }

end ChainInput
end P21.Nonsymmetric
