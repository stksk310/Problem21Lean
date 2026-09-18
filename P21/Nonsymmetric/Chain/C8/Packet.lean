import P21.Nonsymmetric.Chain.C8.FirstFit

namespace P21.Nonsymmetric
namespace ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

/-- The central `F+n_k` row.  It is a signed identity; in the strict case its
`n_k` coefficient is negative. -/
theorem centralFK (K : ChainCore s F D) :
    F + g.n 2 = (K.d+K.chain.beta-1)*g.n 0 +
      (K.chain.R+(D.rho 1 : ℤ)-K.S-1)*g.n 1 +
      (K.chain.alpha-K.Croot)*g.n 2 := by
  have hw := K.chain.W_exact
  have hr := K.root
  have h1 := D.relation_one
  simp only [W] at hw
  rw [K.chain.P_eq_a_beta, K.chain.T_exact] at hw
  linear_combination hw - hr - h1 + g.n 2

/-- The genuine zero-k upper face associated with the central signed row. -/
theorem centralFKUpper (K : ChainCore s F D) :
    F + (K.Croot-K.chain.alpha+1)*g.n 2 =
      (K.d+K.chain.beta-1)*g.n 0 +
      (K.chain.R+(D.rho 1 : ℤ)-K.S-1)*g.n 1 := by
  have h := K.centralFK
  linear_combination h + (K.Croot-K.chain.alpha)*g.n 2

namespace FirstFit

variable {K : ChainCore s F D} (A : K.FirstFit)

def DF : ℤ := K.d+K.chain.beta-1-A.I
def EF : ℤ := K.chain.R+(D.rho 1 : ℤ)-K.S-1-A.J
def chi : ℤ := K.Croot-K.chain.alpha+1-A.Xi

theorem DF_ge_beta : K.chain.beta ≤ A.DF := by
  have hi := A.I_bounds.2
  simp [DF]
  omega

theorem DF_pos : 0 < A.DF := by
  have hb := K.chain.scalar_ranges.2.1
  exact lt_of_lt_of_le hb A.DF_ge_beta

theorem EF_ge_aj : (D.a 1 : ℤ) ≤ A.EF := by
  have hj := A.J_upper
  have hR := K.chain.R_exact
  simp [EF]
  omega

theorem EF_pos : 0 < A.EF := lt_of_lt_of_le (by exact_mod_cast D.a_pos 1) A.EF_ge_aj

private theorem max_sub_max_neg (x : ℤ) : max x 0 - max (-x) 0 = x := by
  by_cases h : 0 ≤ x
  · simp [max_eq_left h, max_eq_right (by omega : -x ≤ 0)]
  · have hx : x ≤ 0 := by omega
    simp [max_eq_right hx, max_eq_left (by omega : 0 ≤ -x)]

/-- A same-element packet.  `left_actual` and `right_actual` are two actual
factorizations of the single named `upper`; the inequalities record that the
same `I*n_i+J*n_j` source is contained coefficientwise before removal. -/
structure Packet (hF : s.semigroup.IsFrobenius F) where
  upper : ℤ
  upper_eq : upper = F + A.Xi*g.n 2 + max A.chi 0*g.n 2
  same_upper : upper = F + (K.Croot-K.chain.alpha+1)*g.n 2 +
    max (-A.chi) 0*g.n 2
  left_actual : upper ∈ g.Gamma
  right_actual : upper ∈ g.Gamma
  common_i_left : 0 ≤ A.I
  common_j_left : 0 ≤ A.J
  common_i_right : A.I ≤ K.d+K.chain.beta-1
  common_j_right : A.J ≤ K.chain.R+(D.rho 1 : ℤ)-K.S-1
  removed : (A.N-1)*g.m + max A.chi 0*g.n 2 =
    A.DF*g.n 0+A.EF*g.n 1+max (-A.chi) 0*g.n 2

noncomputable def packet (hF : s.semigroup.IsFrobenius F) : A.Packet hF := by
  let U := F+A.Xi*g.n 2+max A.chi 0*g.n 2
  have hsame : U = F+(K.Croot-K.chain.alpha+1)*g.n 2+
      max (-A.chi) 0*g.n 2 := by
    dsimp [U]
    have hm := max_sub_max_neg A.chi
    simp [chi] at hm ⊢
    linear_combination hm * g.n 2
  have hleftEq : U = (A.N-1)*g.m+A.I*g.n 0+A.J*g.n 1+
      max A.chi 0*g.n 2 := by
    dsimp [U]
    have h := A.omegaHat_eq
    simp [omegaHat] at h
    linear_combination h
  have hrightEq : U = 0*g.m+(K.d+K.chain.beta-1)*g.n 0+
      (K.chain.R+(D.rho 1 : ℤ)-K.S-1)*g.n 1+max (-A.chi) 0*g.n 2 := by
    rw [hsame, K.centralFKUpper]
    ring
  have hN : 0 ≤ A.N-1 := by have := A.N_ge_two; omega
  have hL : U ∈ g.Gamma := by
    rw [hleftEq]
    exact four_mem (A.N-1) A.I A.J (max A.chi 0) hN
      A.I_bounds.1 A.J_nonneg (le_max_right _ _)
  have hR : U ∈ g.Gamma := by
    rw [hrightEq]
    exact four_mem 0 (K.d+K.chain.beta-1)
      (K.chain.R+(D.rho 1 : ℤ)-K.S-1) (max (-A.chi) 0)
      (by omega) (by have := A.DF_pos; have := A.I_bounds.1; simp [DF] at *; omega)
      (by have := A.EF_pos; have := A.J_nonneg; simp [EF] at *; omega)
      (le_max_right _ _)
  refine {
    upper := U
    upper_eq := rfl
    same_upper := hsame
    left_actual := hL
    right_actual := hR
    common_i_left := A.I_bounds.1
    common_j_left := A.J_nonneg
    common_i_right := ?_
    common_j_right := ?_
    removed := ?_ }
  · have := A.DF_pos; simp [DF] at *; omega
  · have := A.EF_pos; simp [EF] at *; omega
  · have hl := hleftEq
    have hr := hrightEq
    simp [DF, EF] at ⊢
    linear_combination hr - hl

/-- On the boundary the packet has no left k-source. -/
theorem boundary_packet (hF : s.semigroup.IsFrobenius F)
    (hb : K.Croot = K.chain.alpha) :
    (A.N-1)*g.m = A.DF*g.n 0+A.EF*g.n 1+(A.Xi-1)*g.n 2 := by
  have hx := A.Xi_pos hF
  have hp := (A.packet hF).removed
  have hc : A.chi = 1-A.Xi := by simp [chi, hb]
  rw [hc] at hp
  rw [max_eq_right (by omega : 1-A.Xi ≤ 0)] at hp
  have heq : -(1-A.Xi) = A.Xi-1 := by ring
  rw [heq, max_eq_left (by omega : 0 ≤ A.Xi-1)] at hp
  simp only [zero_mul, add_zero] at hp
  exact hp

private theorem q_gap_of_four {q l x y z : ℤ} (hq : q ∉ g.Gamma)
    (he : q=l*g.m+x*g.n 0+y*g.n 1+z*g.n 2)
    (hl : 0≤l) (hx : 0≤x) (hy : 0≤y) (hz : 0≤z) : False := by
  apply hq
  rw [he]
  exact four_mem l x y z hl hx hy hz

/-- Boundary insertion into the three named actual return representations. -/
theorem boundaryWall (E : K.Returns) (hF : s.semigroup.IsFrobenius F)
    (hb : K.Croot = K.chain.alpha) :
    max E.Li (max E.Lb E.Lj) + 2 ≤ A.N := by
  have hp := A.boundary_packet hF hb
  have hn := E.coeff_nonneg
  have hlevels := E.levels_pos
  have hxi := A.Xi_pos hF
  have hDF := A.DF_ge_beta
  have hEF := A.EF_ge_aj
  have hbeta := K.chain.scalar_ranges.2.1
  have haj : (1:ℤ) ≤ D.a 1 := by exact_mod_cast D.a_pos 1
  have hA : E.Li+2 ≤ A.N := by
    by_contra hh
    have he := E.EA_eq
    have hq := K.chain.qA_actual.1.1
    have eq : K.chain.qA = (E.Li-(A.N-1))*g.m+(A.DF-1)*g.n 0+
        (E.Uj+A.EF)*g.n 1+(E.Uk+A.Xi-1)*g.n 2 := by
      linear_combination he + hp
    exact q_gap_of_four hq eq (by omega) (by omega) (by omega) (by omega)
  have hB : E.Lb+2 ≤ A.N := by
    by_contra hh
    have he := E.EB_eq
    have hq := K.chain.qB_actual.1.1
    have eq : K.chain.qB = (E.Lb-(A.N-1))*g.m+(A.DF-1)*g.n 0+
        (E.Vj+A.EF)*g.n 1+(E.Vk+A.Xi-1)*g.n 2 := by
      linear_combination he + hp
    exact q_gap_of_four hq eq (by omega) (by omega) (by omega) (by omega)
  have hJ : E.Lj+2 ≤ A.N := by
    by_contra hh
    have he := E.Qj_eq
    have hq := K.chain.qJ_actual.1.1
    have eq : K.chain.qJ = (E.Lj-(A.N-1))*g.m+(E.Aj+A.DF)*g.n 0+
        (A.EF-1)*g.n 1+(E.Cj+A.Xi-1)*g.n 2 := by
      linear_combination he + hp
    exact q_gap_of_four hq eq (by omega) (by omega) (by omega) (by omega)
  omega

/-- The general T-window, deliberately scoped only to FI-A and FJ. -/
theorem windowWall (E : K.Returns) (hF : s.semigroup.IsFrobenius F)
    (hw : A.chi ≤ K.chain.T) : max E.Li E.Lj + 1 ≤ A.N := by
  have hp := (A.packet hF).removed
  have hn := E.coeff_nonneg
  have hDF := A.DF_pos
  have hEF := A.EF_pos
  have hsc := K.chain.scalar_ranges
  have hA : E.Li+1 ≤ A.N := by
    by_contra hh
    have he := K.FI_A E
    have eq : F = (E.Li-A.N)*g.m+(A.DF-1)*g.n 0+
        (E.Uj+K.chain.gapJ+A.EF)*g.n 1+
        (E.Uk+K.chain.T-A.chi)*g.n 2 := by
      have hm := max_sub_max_neg A.chi
      linear_combination he + hp - hm*g.n 2
    apply hF.1
    change F ∈ g.Gamma
    rw [eq]
    exact four_mem _ _ _ _ (by omega) (by omega) (by omega) (by omega)
  have hJ : E.Lj+1 ≤ A.N := by
    by_contra hh
    have he := K.FJ E
    have eq : F = (E.Lj-A.N)*g.m+(E.Aj+K.chain.delta+A.DF)*g.n 0+
        (A.EF-1)*g.n 1+(E.Cj+K.chain.T-A.chi)*g.n 2 := by
      have hm := max_sub_max_neg A.chi
      linear_combination he + hp - hm*g.n 2
    apply hF.1
    change F ∈ g.Gamma
    rw [eq]
    exact four_mem _ _ _ _ (by omega) (by omega) (by omega) (by omega)
  omega

end FirstFit
end ChainCore
end P21.Nonsymmetric
