import P21.Nonsymmetric.Chain.C8.Triangle

set_option maxHeartbeats 800000

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} (O : A.OneData E)

def baryAlpha (p q : ℤ) : ℤ := E.Lj*p-O.z*q
def baryBeta (p q : ℤ) : ℤ := -E.Li*p+O.x*q
def baryGamma (p q : ℤ) : ℤ := O.det-O.baryAlpha p q-O.baryBeta p q

def Ipq (p q : ℤ) : ℤ := K.chain.delta-1+q*K.d-p*(D.a 0 : ℤ)+0*O.x
def Jpq (p q : ℤ) : ℤ := K.chain.gapJ-1+p*(D.rho 1 : ℤ)-q*K.S+0*O.x

theorem inTriangle_iff {p q : ℤ} : O.InTriangle p q ↔
    0 ≤ O.baryAlpha p q ∧ 0 ≤ O.baryBeta p q ∧ 0 ≤ O.baryGamma p q := by
  simp [InTriangle, baryAlpha, baryBeta, baryGamma]
  omega

theorem reconstruct_p (p q : ℤ) :
    O.det*p=O.x*O.baryAlpha p q+O.z*O.baryBeta p q := by
  simp [det, baryAlpha, baryBeta]
  ring

theorem reconstruct_q (p q : ℤ) :
    O.det*q=E.Li*O.baryAlpha p q+E.Lj*O.baryBeta p q := by
  simp [det, baryAlpha, baryBeta]
  ring

theorem I_barycentric (p q : ℤ) :
    O.det*(O.Ipq p q+1)=O.baryGamma p q*K.chain.delta+
      O.baryBeta p q*(E.Aj+K.chain.delta+1) := by
  simp [Ipq, baryGamma, baryAlpha, baryBeta, det]
  linear_combination
    (E.Lj*p-O.z*q)*O.ea_d + (-E.Li*p+O.x*q)*O.qj_d

theorem J_barycentric (p q : ℤ) :
    O.det*(O.Jpq p q+1)=O.baryGamma p q*K.chain.gapJ+
      O.baryAlpha p q*(Q E+K.chain.gapJ) := by
  simp [Jpq, baryGamma, baryAlpha, baryBeta, det, Q]
  linear_combination
    -(E.Lj*p-O.z*q)*O.ea_S - (-E.Li*p+O.x*q)*O.qj_S

private theorem triangle_nZeta_le {p q : ℤ}
    (hI : 0 ≤ K.chain.delta-1+q*K.d-p*(D.a 0 : ℤ)) : K.nZeta p ≤ q := by
  have hd0 := K.d_range.1
  have hd : 0 < K.d := by omega
  have hlt : p*(D.a 0 : ℤ)-K.chain.delta < q*K.d := by omega
  have hq := (Int.ediv_lt_iff_lt_mul hd).2 hlt
  simp [nZeta]
  omega

private theorem triangle_nZeta_mono {p r : ℤ} (h : p ≤ r) : K.nZeta p ≤ K.nZeta r := by
  rcases h.eq_or_lt with rfl | hlt
  · rfl
  · exact (K.nZeta_strict hlt).le

/-- A nonvertex closed-triangle lattice point gives an earlier fitting HRJ point. -/
theorem empty_triangle (hF : s.semigroup.IsFrobenius F)
    (hw : A.chi ≤ K.chain.T) : O.EmptyTriangleStatement := by
  intro p q hpq
  by_contra hvertex
  have hb := O.inTriangle_iff.mp hpq
  have ha0 := hb.1
  have hb0 := hb.2.1
  have hg0 := hb.2.2
  have hdet := O.det_pos
  have hdelta := K.chain.scalar_ranges.1
  have hgap := K.chain.scalar_ranges.2.2.1
  have ha := a_pos (K:=K) (E:=E)
  have hQ := Q_pos (K:=K) (E:=E)
  have hx := O.x_pos
  have hz := O.z_pos
  have hLi := E.levels_pos.1
  have hLj := E.levels_pos.2.2.1
  have hcoeff := E.coeff_nonneg
  have hAj : 0 ≤ E.Aj := hcoeff.2.2.2.2.1
  have hUj : 0 ≤ E.Uj := hcoeff.1
  have hIprod := O.I_barycentric p q
  have hJprod := O.J_barycentric p q
  have hI1 : 0 ≤ O.Ipq p q+1 := by
    by_contra hn
    have hl : O.det*(O.Ipq p q+1) < 0 := mul_neg_of_pos_of_neg (by omega) (by omega)
    have hr1 := mul_nonneg hg0 (show 0 ≤ K.chain.delta by omega)
    have hr2 := mul_nonneg hb0 (show 0 ≤ E.Aj+K.chain.delta+1 by omega)
    nlinarith
  have hJ1 : 0 ≤ O.Jpq p q+1 := by
    by_contra hn
    have hl : O.det*(O.Jpq p q+1) < 0 := mul_neg_of_pos_of_neg (by omega) (by omega)
    have hr1 := mul_nonneg hg0 (show 0 ≤ K.chain.gapJ by omega)
    have hr2 := mul_nonneg ha0 (show 0 ≤ Q E+K.chain.gapJ by omega)
    nlinarith
  have hIpos : 0 < O.Ipq p q+1 := by
    by_contra hn
    have hzero : O.Ipq p q+1=0 := by omega
    have hsum : O.baryGamma p q*K.chain.delta+O.baryBeta p q*(E.Aj+K.chain.delta+1)=0 := by
      rw [hzero] at hIprod
      simpa using hIprod.symm
    have hgprod : O.baryGamma p q*K.chain.delta=0 := by
      have h1 := mul_nonneg hg0 (show 0 ≤ K.chain.delta by omega)
      have h2 := mul_nonneg hb0 (show 0 ≤ E.Aj+K.chain.delta+1 by omega)
      omega
    have hbprod : O.baryBeta p q*(E.Aj+K.chain.delta+1)=0 := by omega
    have hgz : O.baryGamma p q=0 := (mul_eq_zero.mp hgprod).resolve_right (by omega)
    have hbz : O.baryBeta p q=0 := (mul_eq_zero.mp hbprod).resolve_right (by omega)
    have haz : O.baryAlpha p q=O.det := by simp [baryGamma] at hgz; omega
    have hp := O.reconstruct_p p q
    have hq := O.reconstruct_q p q
    rw [haz, hbz] at hp hq
    have hp0 : O.det*(p-O.x)=0 := by linear_combination hp
    have hq0 : O.det*(q-E.Li)=0 := by linear_combination hq
    have hpe : p=O.x := by have := (mul_eq_zero.mp hp0).resolve_left (by omega); omega
    have hqe : q=E.Li := by have := (mul_eq_zero.mp hq0).resolve_left (by omega); omega
    apply hvertex
    simp [IsVertex, hpe, hqe]
  have hJpos : 0 < O.Jpq p q+1 := by
    by_contra hn
    have hzero : O.Jpq p q+1=0 := by omega
    have hsum : O.baryGamma p q*K.chain.gapJ+O.baryAlpha p q*(Q E+K.chain.gapJ)=0 := by
      rw [hzero] at hJprod
      simpa using hJprod.symm
    have hgprod : O.baryGamma p q*K.chain.gapJ=0 := by
      have h1 := mul_nonneg hg0 (show 0 ≤ K.chain.gapJ by omega)
      have h2 := mul_nonneg ha0 (show 0 ≤ Q E+K.chain.gapJ by omega)
      omega
    have haprod : O.baryAlpha p q*(Q E+K.chain.gapJ)=0 := by omega
    have hgz : O.baryGamma p q=0 := (mul_eq_zero.mp hgprod).resolve_right (by omega)
    have haz : O.baryAlpha p q=0 := (mul_eq_zero.mp haprod).resolve_right (by omega)
    have hbz : O.baryBeta p q=O.det := by simp [baryGamma] at hgz; omega
    have hp := O.reconstruct_p p q
    have hq := O.reconstruct_q p q
    rw [haz, hbz] at hp hq
    have hp0 : O.det*(p-O.z)=0 := by linear_combination hp
    have hq0 : O.det*(q-E.Lj)=0 := by linear_combination hq
    have hpe : p=O.z := by have := (mul_eq_zero.mp hp0).resolve_left (by omega); omega
    have hqe : q=E.Lj := by have := (mul_eq_zero.mp hq0).resolve_left (by omega); omega
    apply hvertex
    simp [IsVertex, hpe, hqe]
  have hI : 0 ≤ O.Ipq p q := by omega
  have hJ : 0 ≤ O.Jpq p q := by omega
  have hpRec := O.reconstruct_p p q
  have hqRec := O.reconstruct_q p q
  have hpnonneg : 0 ≤ p := by
    by_contra hn
    have hl := mul_neg_of_pos_of_neg (show 0 < O.det by omega) (show p < 0 by omega)
    have hxa := mul_nonneg (show 0 ≤ O.x by omega) ha0
    have hzb := mul_nonneg (show 0 ≤ O.z by omega) hb0
    nlinarith
  have hqnonneg : 0 ≤ q := by
    by_contra hn
    have hl := mul_neg_of_pos_of_neg (show 0 < O.det by omega) (show q < 0 by omega)
    have hLa := mul_nonneg (show 0 ≤ E.Li by have := E.levels_pos.1; omega) ha0
    have hMb := mul_nonneg (show 0 ≤ E.Lj by have := E.levels_pos.2.2.1; omega) hb0
    nlinarith
  have hp_pos : 1 ≤ p := by
    by_contra hn
    have hpz : p=0 := by omega
    subst p
    simp only [mul_zero] at hpRec
    have hxa : O.x*O.baryAlpha 0 q=0 := by
      have h1 := mul_nonneg (show 0 ≤ O.x by omega) ha0
      have h2 := mul_nonneg (show 0 ≤ O.z by omega) hb0
      nlinarith
    have hzb : O.z*O.baryBeta 0 q=0 := by
      have h2 := mul_nonneg (show 0 ≤ O.z by omega) hb0
      nlinarith
    have haz : O.baryAlpha 0 q=0 := (mul_eq_zero.mp hxa).resolve_left (by omega)
    have hbz : O.baryBeta 0 q=0 := (mul_eq_zero.mp hzb).resolve_left (by omega)
    rw [haz, hbz] at hqRec
    have hqz : q=0 := by
      have hq0 : O.det*q=0 := by simpa using hqRec
      exact (mul_eq_zero.mp hq0).resolve_left (by omega)
    apply hvertex
    simp [IsVertex, hqz]
  have hq_pos : 1 ≤ q := by
    by_contra hn
    have hqz : q=0 := by omega
    subst q
    simp only [mul_zero] at hqRec
    have hLa : E.Li*O.baryAlpha p 0=0 := by
      have h1 := mul_nonneg (show 0 ≤ E.Li by have := E.levels_pos.1; omega) ha0
      have h2 := mul_nonneg (show 0 ≤ E.Lj by have := E.levels_pos.2.2.1; omega) hb0
      nlinarith
    have hMb : E.Lj*O.baryBeta p 0=0 := by
      have h2 := mul_nonneg (show 0 ≤ E.Lj by omega) hb0
      nlinarith
    have haz : O.baryAlpha p 0=0 := (mul_eq_zero.mp hLa).resolve_left (by have := E.levels_pos.1; omega)
    have hbz : O.baryBeta p 0=0 := (mul_eq_zero.mp hMb).resolve_left (by have := E.levels_pos.2.2.1; omega)
    rw [haz, hbz] at hpRec
    have hpz : p=0 := by
      have hp0 : O.det*p=0 := by simpa using hpRec
      exact (mul_eq_zero.mp hp0).resolve_left (by omega)
    apply hvertex
    simp [IsVertex, hpz]
  have hsum : O.baryAlpha p q+O.baryBeta p q ≤ O.det := by
    change 0 ≤ O.det-O.baryAlpha p q-O.baryBeta p q at hg0
    omega
  have hq_upper : q ≤ max E.Li E.Lj := by
    by_cases hLM : E.Li ≤ E.Lj
    · have h1 := mul_le_mul_of_nonneg_right hLM ha0
      have h2 := mul_le_mul_of_nonneg_left hsum (show 0 ≤ E.Lj by have := E.levels_pos.2.2.1; omega)
      have hprod : O.det*q ≤ O.det*E.Lj := by nlinarith
      have hqM : q ≤ E.Lj := by
        by_contra hn
        have := mul_pos (show 0 < O.det by omega) (show 0 < q-E.Lj by omega)
        nlinarith
      simpa [max_eq_right hLM] using hqM
    · have hML : E.Lj ≤ E.Li := by omega
      have h1 := mul_le_mul_of_nonneg_right hML hb0
      have h2 := mul_le_mul_of_nonneg_left hsum (show 0 ≤ E.Li by have := E.levels_pos.1; omega)
      have hprod : O.det*q ≤ O.det*E.Li := by nlinarith
      have hqL : q ≤ E.Li := by
        by_contra hn
        have := mul_pos (show 0 < O.det by omega) (show 0 < q-E.Li by omega)
        nlinarith
      simpa [max_eq_left hML] using hqL
  have hnle : K.nZeta p ≤ q := by
    apply triangle_nZeta_le (K:=K)
    simpa [Ipq] using hI
  have hjfit : 0 ≤ K.JZeta p := by
    have hS : 0 ≤ K.S := by have := K.S_strong; have := K.chain.scalar_ranges.2.2.1; omega
    simp [JZeta, Jpq] at hJ ⊢
    nlinarith [mul_nonneg (show 0 ≤ q-K.nZeta p by omega) hS]
  have hzle : A.zhat ≤ p := A.minimal p hp_pos hjfit
  have hNle : A.N ≤ q := by
    rw [A.N_eq]
    exact le_trans (triangle_nZeta_mono (K:=K) hzle) hnle
  have hwall := A.windowWall E hF hw
  omega

end P21.Nonsymmetric.ChainCore.FirstFit.OneData
