import P21.Nonsymmetric.Chain.C8.TriangleEmpty

set_option maxHeartbeats 800000

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} (O : A.OneData E)

/-- Emptiness of the lattice triangle forces the first edge to be primitive. -/
theorem primitive_first_edge (hempty : O.EmptyTriangleStatement) : O.x.gcd E.Li = 1 := by
  have hx := O.x_pos
  have hLi := E.levels_pos.1
  let c : ℤ := (O.x.gcd E.Li : ℕ)
  have hcposNat : 0 < O.x.gcd E.Li := by
    rw [Int.gcd_eq_natAbs]
    exact Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr (by omega))
  have hcNat : 1 ≤ O.x.gcd E.Li := by omega
  have hc : 1 ≤ c := by
    dsimp [c]
    exact_mod_cast hcNat
  by_contra hne
  have hc2 : 2 ≤ c := by
    have : c ≠ 1 := by
      intro hc1
      apply hne
      dsimp [c] at hc1
      exact_mod_cast hc1
    omega
  let p := O.x / c
  let q := E.Li / c
  have hcx : c ∣ O.x := by
    dsimp [c]
    exact Int.gcd_dvd_left _ _
  have hcLi : c ∣ E.Li := by
    dsimp [c]
    exact Int.gcd_dvd_right _ _
  have hpx : p*c=O.x := by exact Int.ediv_mul_cancel hcx
  have hqLi : q*c=E.Li := by exact Int.ediv_mul_cancel hcLi
  have hbeta : O.baryBeta p q=0 := by
    simp [baryBeta]
    rw [← hpx, ← hqLi]
    ring
  have halpha_mul : c*O.baryAlpha p q=O.det := by
    simp [baryAlpha, det]
    rw [← hpx, ← hqLi]
    ring
  have hdet := O.det_pos
  have halpha_pos : 0 < O.baryAlpha p q := by
    by_contra hn
    have := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ c by omega) (show O.baryAlpha p q ≤ 0 by omega)
    nlinarith
  have halpha_lt : O.baryAlpha p q < O.det := by
    nlinarith [mul_pos (show 0 < c-1 by omega) halpha_pos]
  have hin : O.InTriangle p q := O.inTriangle_iff.mpr ⟨halpha_pos.le, by simp [hbeta], by
    simp [baryGamma, hbeta]
    omega⟩
  have hp_pos : 0 < p := by
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg (show p ≤ 0 by omega) (show 0 ≤ c by omega)
    nlinarith
  have hp_lt : p < O.x := by
    nlinarith [mul_pos (show 0 < p by omega) (show 0 < c-1 by omega)]
  have hnonvertex : ¬ O.IsVertex p q := by
    intro hv
    rcases hv with hO | hU | hV
    · omega
    · omega
    · have haz : O.baryAlpha p q=0 := by simp [baryAlpha, hV.1, hV.2]; ring
      omega
  exact hnonvertex (hempty p q hin)

private theorem pullback_beta (r s a b p q : ℤ)
    (hbez : r*O.x+s*E.Li=1)
    (hp : p=O.x*a-s*b) (hq : q=E.Li*a+r*b) : O.baryBeta p q=b := by
  simp [baryBeta, hp, hq]
  linear_combination b*hbez

private theorem pullback_alpha (r s k r0 a0 b p q : ℤ)
    (hv : r*O.z+s*E.Lj=k*O.det+r0)
    (hp : p=O.x*(a0+k*b)-s*b) (hq : q=E.Li*(a0+k*b)+r*b) :
    O.baryAlpha p q=O.det*a0-r0*b := by
  calc
    O.baryAlpha p q = O.det*(a0+k*b)-(r*O.z+s*E.Lj)*b := by
      simp [baryAlpha, det, hp, hq]
      ring
    _ = O.det*a0-r0*b := by rw [hv]; ring

/-- Explicit Bézout and shear normalization produces a nonvertex lattice point if `det ≥ 2`. -/
theorem det_one (hempty : O.EmptyTriangleStatement) : O.DetOneStatement := by
  have hdet := O.det_pos
  have hgcd := O.primitive_first_edge hempty
  let r : ℤ := Int.gcdA O.x E.Li
  let s0 : ℤ := Int.gcdB O.x E.Li
  have hbez : r*O.x+s0*E.Li=1 := by
    have h := Int.gcd_eq_gcd_ab O.x E.Li
    rw [hgcd] at h
    simpa [r, s0, mul_comm] using h.symm
  change O.det=1
  by_contra hne
  have hdet2 : 2 ≤ O.det := by omega
  let v1 : ℤ := r*O.z+s0*E.Lj
  let k : ℤ := v1/O.det
  let r0 : ℤ := v1%O.det
  have hr0_nonneg : 0 ≤ r0 := by
    dsimp [r0]
    exact Int.emod_nonneg _ (by omega)
  have hr0_lt : r0 < O.det := by
    have h := Int.emod_lt v1 (show O.det ≠ 0 by omega)
    rw [Int.natAbs_of_nonneg (show 0 ≤ O.det by omega)] at h
    exact h
  have hv1 : v1=k*O.det+r0 := by
    have h := Int.ediv_mul_add_emod v1 O.det
    dsimp [k, r0]
    omega
  by_cases hr0 : r0=0
  · let a0 : ℤ := 0
    let b0 : ℤ := 1
    let p : ℤ := O.x*(a0+k*b0)-s0*b0
    let q : ℤ := E.Li*(a0+k*b0)+r*b0
    have hb : O.baryBeta p q=b0 :=
      O.pullback_beta r s0 (a0+k*b0) b0 p q hbez rfl rfl
    have ha : O.baryAlpha p q=O.det*a0-r0*b0 :=
      O.pullback_alpha r s0 k r0 a0 b0 p q (by simpa [v1] using hv1) rfl rfl
    have ha0 : O.baryAlpha p q=0 := by simp [ha, a0, b0, hr0]
    have hb1 : O.baryBeta p q=1 := by simpa [b0] using hb
    have hin : O.InTriangle p q := O.inTriangle_iff.mpr ⟨by simp [ha0], by simp [hb1], by
      simp [baryGamma, ha0, hb1]
      omega⟩
    have hnonvertex : ¬ O.IsVertex p q := by
      intro hv
      rcases hv with hO | hU | hV
      · have : O.baryBeta p q=0 := by simp [baryBeta, hO.1, hO.2]
        omega
      · have : O.baryBeta p q=0 := by simp [baryBeta, hU.1, hU.2]; ring
        omega
      · have : O.baryBeta p q=O.det := by simp [baryBeta, det, hV.1, hV.2]; ring
        omega
    exact hnonvertex (hempty p q hin)
  · have hr0_pos : 1 ≤ r0 := by omega
    let a0 : ℤ := 1
    let b0 : ℤ := 1
    let p : ℤ := O.x*(a0+k*b0)-s0*b0
    let q : ℤ := E.Li*(a0+k*b0)+r*b0
    have hb : O.baryBeta p q=b0 :=
      O.pullback_beta r s0 (a0+k*b0) b0 p q hbez rfl rfl
    have ha : O.baryAlpha p q=O.det*a0-r0*b0 :=
      O.pullback_alpha r s0 k r0 a0 b0 p q (by simpa [v1] using hv1) rfl rfl
    have ha_pos : 1 ≤ O.baryAlpha p q := by simp [ha, a0, b0]; omega
    have hb1 : O.baryBeta p q=1 := by simpa [b0] using hb
    have hin : O.InTriangle p q := O.inTriangle_iff.mpr ⟨by omega, by simp [hb1], by
      simp [baryGamma, ha, hb1, a0, b0]
      omega⟩
    have hnonvertex : ¬ O.IsVertex p q := by
      intro hv
      rcases hv with hO | hU | hV
      · have : O.baryBeta p q=0 := by simp [baryBeta, hO.1, hO.2]
        omega
      · have : O.baryBeta p q=0 := by simp [baryBeta, hU.1, hU.2]; ring
        omega
      · have : O.baryBeta p q=O.det := by simp [baryBeta, det, hV.1, hV.2]; ring
        omega
    exact hnonvertex (hempty p q hin)

end P21.Nonsymmetric.ChainCore.FirstFit.OneData
