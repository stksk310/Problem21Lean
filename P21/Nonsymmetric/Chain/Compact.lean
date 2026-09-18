import P21.Nonsymmetric.Chain.Orientation

namespace P21.Nonsymmetric
namespace ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

def Delta0 (K : ChainCore s F D) : ℤ :=
  K.q0*K.S - D.rho 1 - K.chain.gapJ + 1
def A0 (K : ChainCore s F D) : ℤ := K.e0-K.chain.delta-1
def C0 (K : ChainCore s F D) : ℤ := D.a 2-K.q0*K.Croot-1
def tau0 (K : ChainCore s F D) : ℤ := D.rho 1-K.h*K.S

structure CompactData (K : ChainCore s F D) : Prop where
  oriented : K.J0 < 0
  Delta_pos : 1 ≤ K.Delta0
  A_nonneg : 0 ≤ K.A0
  C_nonneg : 0 ≤ K.C0
  tau_pos : 1 ≤ K.tau0
  sum_exact : K.Delta0+K.tau0 = K.S-K.chain.gapJ+1
  Delta_upper : K.Delta0 ≤ K.S-K.chain.gapJ

theorem compact_data (K : ChainCore s F D) (hJ : K.J0 < 0) : K.CompactData := by
  have E := K.euclidean
  have L := K.slopes
  have hD : 1 ≤ K.Delta0 := by
    simp [Delta0, J0] at ⊢ hJ
    omega
  have hCfit := K.J0_forces_k_fit hJ
  have hC : 0 ≤ K.C0 := by simp [C0]; omega
  have hqS : (D.rho 1 : ℤ) < K.q0*K.S := by
    simp [J0] at hJ
    have hg := K.chain.scalar_ranges.2.2.1
    omega
  have hr : (0 : ℤ) < D.rho 1 := by exact_mod_cast D.rho_pos 1
  have ha : (0 : ℤ) < D.a 0 := by exact_mod_cast D.a_pos 0
  have hqd : (D.a 0 : ℤ) < K.q0*K.d := by
    have hq := E.q0_pos
    have hslope : K.S*D.a 0 < K.d*D.rho 1 := by nlinarith [L.j_pos]
    have h1 := mul_lt_mul_of_pos_left hslope (show 0 < K.q0 by omega)
    have h2 := mul_lt_mul_of_pos_right hqS ha
    nlinarith
  have hA : 0 ≤ K.A0 := by
    simp [A0, e0, ChainInput.delta]
    omega
  have ht : 1 ≤ K.tau0 := by
    simp [tau0]
    have := K.hS_lt_rho
    omega
  have hsum : K.Delta0+K.tau0 = K.S-K.chain.gapJ+1 := by
    simp [Delta0, tau0, q0]
    ring
  have hu : K.Delta0 ≤ K.S-K.chain.gapJ := by omega
  exact ⟨hJ,hD,hA,hC,ht,hsum,hu⟩

theorem compact_equation (K : ChainCore s F D) (hJ : K.J0 < 0) :
    F + K.Delta0*g.n 1 = (K.q0-1)*g.m + (K.e0-1)*g.n 0 +
      (K.C0+K.chain.T)*g.n 2 := by
  have hf := K.completed_F K.q0 1
  have hv := K.second_coordinates
  have hr2 : (D.rho 2 : ℤ) = D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
  have hT := K.chain.T_exact
  have hDJ : K.Delta0 = -K.J0 := by simp [Delta0, J0]; ring
  have hK : K.K0 = K.C0+K.chain.T := by
    simp [K0, C0]
    nlinarith [hr2, hT]
  rw [hv] at hf
  simp at hf
  rw [hK] at hf
  calc
    F + K.Delta0*g.n 1 =
        ((K.q0-1)*g.m + (K.e0-1)*g.n 0 + K.J0*g.n 1 +
          (K.C0+K.chain.T)*g.n 2) + K.Delta0*g.n 1 :=
      congrArg (fun z : ℤ => z + K.Delta0*g.n 1) hf
    _ = (K.q0-1)*g.m + (K.e0-1)*g.n 0 +
          (K.C0+K.chain.T)*g.n 2 := by rw [hDJ]; ring

theorem compact_actual (K : ChainCore s F D) (hJ : K.J0 < 0) :
    F + K.Delta0*g.n 1 ∈ g.Gamma := by
  have C := K.compact_data hJ
  have E := K.euclidean
  have hT : 0 ≤ K.chain.T := by
    rw [K.chain.T_exact]
    have := D.b_pos 2; have := K.chain.scalar_ranges.2.2.2; omega
  have hq := E.q0_pos
  have he := E.e0_range.1
  have hC := C.C_nonneg
  have hm := four_mem (g := g) (K.q0-1) (K.e0-1) 0 (K.C0+K.chain.T)
    (by omega) (by omega) (by omega) (by omega)
  convert hm using 1
  simpa [add_assoc] using K.compact_equation hJ

theorem compact_contains_cJ (K : ChainCore s F D) (hJ : K.J0 < 0) :
    K.chain.delta ≤ K.e0-1 ∧ K.chain.T ≤ K.C0+K.chain.T := by
  have C := K.compact_data hJ
  have hA := C.A_nonneg
  have hC := C.C_nonneg
  simp [A0] at hA
  exact ⟨by omega, by omega⟩

theorem compact_return_equation (K : ChainCore s F D) (hJ : K.J0 < 0) :
    K.chain.qJ + K.Delta0*g.n 1 =
      K.q0*g.m + K.A0*g.n 0 + K.C0*g.n 2 := by
  have hc := K.chain.cJ_exact
  simp [complement, W] at hc
  have ho := K.compact_equation hJ
  simp [A0] at ⊢
  linear_combination ho - hc

theorem compact_return_actual (K : ChainCore s F D) (hJ : K.J0 < 0) :
    K.chain.qJ + K.Delta0*g.n 1 ∈ g.Gamma := by
  have C := K.compact_data hJ
  have E := K.euclidean
  have hq := E.q0_pos
  have hm := four_mem (g := g) K.q0 K.A0 0 K.C0
    (by omega) C.A_nonneg (by omega) C.C_nonneg
  convert hm using 1
  simpa [add_assoc] using K.compact_return_equation hJ

end ChainCore
end P21.Nonsymmetric
