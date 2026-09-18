import P21.Nonsymmetric.Chain.C8.Parameters

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} (O : A.OneData E)

def epsilon : ℤ := E.Li*K.Croot+O.x*(D.b 2 : ℤ)

def H0 : ℤ := E.Li*K.Croot+(O.x-1)*(D.b 2 : ℤ)-K.chain.alpha-E.Cj-1

/-- The exact EA packet identity used inside the same actual FJ representation. -/
theorem ea_packet :
    K.chain.delta*g.n 0+O.epsilon*g.n 2=E.Li*g.m+Q E*g.n 1 := by
  have hr := D.relation_one
  have hroot := K.root
  symm
  calc
    E.Li*g.m+Q E*g.n 1 =
        (E.Li*K.S+Q E)*g.n 1+E.Li*K.Croot*g.n 2-E.Li*K.d*g.n 0 := by
      linear_combination E.Li*hroot
    _ = O.x*(D.rho 1 : ℤ)*g.n 1+E.Li*K.Croot*g.n 2-
        (O.x*(D.a 0 : ℤ)-K.chain.delta)*g.n 0 := by
      rw [O.ea_S, O.ea_d]
      simp [Q]
    _ = K.chain.delta*g.n 0+O.epsilon*g.n 2 := by
      simp [epsilon]
      linear_combination O.x*hr

/-- General k-ceiling data; the formula deliberately retains `L*Croot-alpha`. -/
structure CeilingData : Prop where
  epsilon_lower : E.Cj+K.chain.T+1 ≤ O.epsilon
  H0_nonneg : 0 ≤ O.H0
  k_ceiling : (D.rho 2 : ℤ)=
    (E.Lj+E.Li)*K.Croot+(O.z+O.x-1)*(D.b 2 : ℤ)-K.chain.alpha-O.H0

theorem ceiling_data (hF : s.semigroup.IsFrobenius F) : O.CeilingData := by
  have hcoeff := E.coeff_nonneg
  have hlevels := E.levels_pos
  have hdelta := K.chain.scalar_ranges.1
  have hT : 1 ≤ K.chain.T := by
    rw [K.chain.T_exact]
    have hb : (1:ℤ) ≤ D.b 2 := by exact_mod_cast D.b_pos 2
    have ha := K.chain.scalar_ranges.2.2.2
    omega
  have heps : E.Cj+K.chain.T+1 ≤ O.epsilon := by
    by_contra hn
    have hle : O.epsilon ≤ E.Cj+K.chain.T := by omega
    have hFJ := K.FJ E
    have hp := O.ea_packet
    have heq : F=(E.Lj+E.Li-1)*g.m+E.Aj*g.n 0+
        (Q E-1)*g.n 1+(E.Cj+K.chain.T-O.epsilon)*g.n 2 := by
      linear_combination hFJ+hp-g.n 1-K.chain.delta*g.n 0-O.epsilon*g.n 2
    apply hF.1
    change F ∈ g.Gamma
    rw [heq]
    exact four_mem (E.Lj+E.Li-1) E.Aj (Q E-1)
      (E.Cj+K.chain.T-O.epsilon)
      (by omega) hcoeff.2.2.2.2.1 (by simp [Q]; omega) (by omega)
  have hH : 0 ≤ O.H0 := by
    have hid : O.H0=O.epsilon-(E.Cj+K.chain.T+1) := by
      rw [K.chain.T_exact]
      simp [epsilon, H0]
      ring
    rw [hid]
    omega
  have hk : (D.rho 2 : ℤ)=
      (E.Lj+E.Li)*K.Croot+(O.z+O.x-1)*(D.b 2 : ℤ)-K.chain.alpha-O.H0 := by
    have hq := O.qj_k
    simp [H0]
    linear_combination hq
  exact ⟨heps,hH,hk⟩

theorem boundary_k_ceiling (C : O.CeilingData) (hb : K.Croot=K.chain.alpha) :
    (D.rho 2 : ℤ)=(E.Lj+E.Li-1)*K.chain.alpha+
      (O.z+O.x-1)*(D.b 2 : ℤ)-O.H0 := by
  rw [C.k_ceiling, hb]
  ring

end P21.Nonsymmetric.ChainCore.FirstFit.OneData
