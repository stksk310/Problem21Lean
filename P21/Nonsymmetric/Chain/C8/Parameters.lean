import P21.Nonsymmetric.Chain.C8.DetOne

set_option maxHeartbeats 800000

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} (O : A.OneData E)

/-- The Section 8 slope numerator after determinant-one substitution. -/
def V : ℤ := a E*Q E-K.chain.delta*K.chain.gapJ+0*O.x

/-- Exact parameter identities obtained from EA-ONE, QJ-ONE and DET1. -/
structure ParamData : Prop where
  d_eq : K.d=O.x*a E+O.z*K.chain.delta
  S_eq : K.S=O.x*K.chain.gapJ+O.z*Q E
  ai_eq : (D.a 0 : ℤ)=E.Li*a E+E.Lj*K.chain.delta
  rhoj_eq : (D.rho 1 : ℤ)=E.Li*K.chain.gapJ+E.Lj*Q E
  bi_eq : (D.b 0 : ℤ)=E.Li*a E+(E.Lj-1)*K.chain.delta+K.chain.beta
  V_pos : 0 < O.V

theorem param_data (hdet : O.DetOneStatement) : O.ParamData := by
  have hdet1 : O.det=1 := hdet
  have hd := O.det_mul_d
  have hS : O.det*K.S=O.x*K.chain.gapJ+O.z*Q E := by
    simp [Q, det]
    linear_combination O.x*O.qj_S-O.z*O.ea_S
  have hdEq : K.d=O.x*a E+O.z*K.chain.delta := by rw [hdet1] at hd; simpa using hd
  have hSEq : K.S=O.x*K.chain.gapJ+O.z*Q E := by rw [hdet1] at hS; simpa using hS
  have hai : (D.a 0 : ℤ)=E.Li*a E+E.Lj*K.chain.delta := by
    have hx := O.x_pos
    have h := O.ea_d
    have hcross : O.x*E.Lj-O.z*E.Li=1 := hdet1
    rw [hdEq] at h
    have hc0 : 1+E.Li*O.z-O.x*E.Lj=0 := by linear_combination -hcross
    have hz : O.x*((D.a 0 : ℤ)-(E.Li*a E+E.Lj*K.chain.delta))=0 := by
      calc
        O.x*((D.a 0 : ℤ)-(E.Li*a E+E.Lj*K.chain.delta)) =
            (O.x*(D.a 0 : ℤ)-K.chain.delta-
              E.Li*(O.x*a E+O.z*K.chain.delta))+
            K.chain.delta*(1+E.Li*O.z-O.x*E.Lj) := by ring
        _ = 0 := by rw [h, hc0]; ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (by omega))
  have hrho : (D.rho 1 : ℤ)=E.Li*K.chain.gapJ+E.Lj*Q E := by
    have hx := O.x_pos
    have h := O.ea_S
    have hcross : O.x*E.Lj-O.z*E.Li=1 := hdet1
    rw [hSEq] at h
    have hc0 : 1+E.Li*O.z-O.x*E.Lj=0 := by linear_combination -hcross
    have hz : O.x*((D.rho 1 : ℤ)-(E.Li*K.chain.gapJ+E.Lj*Q E))=0 := by
      calc
        O.x*((D.rho 1 : ℤ)-(E.Li*K.chain.gapJ+E.Lj*Q E)) =
            (O.x*(D.rho 1 : ℤ)-Q E-
              E.Li*(O.x*K.chain.gapJ+O.z*Q E))+
            Q E*(1+E.Li*O.z-O.x*E.Lj) := by ring
        _ = 0 := by
          have h' : E.Li*(O.x*K.chain.gapJ+O.z*Q E)=O.x*(D.rho 1 : ℤ)-Q E := by
            simpa [Q] using h
          rw [h', hc0]
          ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (by omega))
  have hbi : (D.b 0 : ℤ)=E.Li*a E+(E.Lj-1)*K.chain.delta+K.chain.beta := by
    have ha0 := K.chain.a0_exact
    have hb0 := K.chain.b0_exact
    rw [hai] at ha0
    linear_combination hb0-ha0
  have hV : 0 < O.V := by
    have hslope := K.slopes.j_pos
    rw [hdEq, hSEq, hai, hrho] at hslope
    have hcross : O.x*E.Lj-O.z*E.Li=1 := hdet1
    have hid :
        (O.x*a E+O.z*K.chain.delta)*(E.Li*K.chain.gapJ+E.Lj*Q E)-
          (O.x*K.chain.gapJ+O.z*Q E)*(E.Li*a E+E.Lj*K.chain.delta) =
        (O.x*E.Lj-O.z*E.Li)*O.V := by simp [V]; ring
    rw [hid, hcross] at hslope
    simpa using hslope
  exact ⟨hdEq,hSEq,hai,hrho,hbi,hV⟩

/-- The exhaustive regular/level-one split forced by determinant one and `a_i>d`. -/
def LevelSplit : Prop :=
  (E.Li ≥ O.x+1 ∧ O.x+1 ≥ 2 ∧ E.Lj > O.z ∧ O.z ≥ 1) ∨
  (E.Li=1 ∧ O.x=1 ∧ E.Lj=O.z+1)

theorem level_split (hdet : O.DetOneStatement) (P : O.ParamData) : O.LevelSplit := by
  have hL := E.levels_pos.1
  have hM := E.levels_pos.2.2.1
  have hx := O.x_pos
  have hz := O.z_pos
  have ha := a_pos (K:=K) (E:=E)
  have hdelta := K.chain.scalar_ranges.1
  have hai_gt : K.d < (D.a 0 : ℤ) := by
    have hd := K.d_range.2
    have ha0 := K.chain.a0_exact
    have hdelta := K.chain.scalar_ranges.1
    omega
  have hcross : O.x*E.Lj-O.z*E.Li=1 := hdet
  rw [P.d_eq, P.ai_eq] at hai_gt
  by_cases hreg : O.x < E.Li
  · left
    have hMz : O.z < E.Lj := by
      by_contra hn
      have h1 := mul_le_mul_of_nonneg_left (show E.Lj ≤ O.z by omega) (show 0 ≤ O.x by omega)
      have h2 := mul_le_mul_of_nonneg_left (show O.x < E.Li by omega) (show 0 ≤ O.z by omega)
      nlinarith
    omega
  · right
    have hMgt : O.z < E.Lj := by
      by_contra hn
      have hLa := mul_nonpos_of_nonpos_of_nonneg (show E.Li-O.x ≤ 0 by omega)
        (show 0 ≤ a E by omega)
      have hMd := mul_nonpos_of_nonpos_of_nonneg (show E.Lj-O.z ≤ 0 by omega)
        (show 0 ≤ K.chain.delta by omega)
      nlinarith
    have hsum : O.x*(E.Lj-O.z)+O.z*(O.x-E.Li)=1 := by
      linear_combination hcross
    have hterm1 := mul_pos (show 0 < O.x by omega) (show 0 < E.Lj-O.z by omega)
    have hterm2 := mul_nonneg (show 0 ≤ O.z by omega) (show 0 ≤ O.x-E.Li by omega)
    have hx1 : O.x=1 := by nlinarith
    have hdiff : E.Lj-O.z=1 := by nlinarith
    have hLx : E.Li=O.x := by nlinarith
    omega

end P21.Nonsymmetric.ChainCore.FirstFit.OneData
