import P21.Nonsymmetric.Chain.C8.BoundarySync

set_option maxHeartbeats 800000

namespace P21.Nonsymmetric.ChainCore.FirstFit

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} (A : K.FirstFit)

/-- Boundary EB and the same Qj, kept separate from EA-specific `OneData`. -/
structure EBOneData (E : K.Returns) where
  anchor : A.zhat=A.zhat
  xb : ℤ
  z : ℤ
  xb_pos : 1 ≤ xb
  z_pos : 1 ≤ z
  eb_d : E.Lb*K.d=xb*(D.a 0 : ℤ)-K.chain.delta
  eb_S : E.Lb*K.S=xb*(D.rho 1 : ℤ)-(E.Vj+(D.a 1 : ℤ)+1)
  eb_k : (D.rho 2 : ℤ)-E.Vk-1=E.Lb*K.Croot+(xb-1)*(D.b 2 : ℤ)
  qj_d : E.Lj*K.d=z*(D.a 0 : ℤ)+(E.Aj+1)
  qj_S : E.Lj*K.S=z*(D.rho 1 : ℤ)+K.chain.gapJ
  qj_k : (D.rho 2 : ℤ)=E.Lj*K.Croot+E.Cj+1+z*(D.b 2 : ℤ)

noncomputable def ebOneData {E : K.Returns} (B : A.EBKernel E) (hy : B.y=1)
    (O : A.OneData E) : A.EBOneData E where
  anchor := rfl
  xb := B.x
  z := O.z
  xb_pos := B.x_pos
  z_pos := O.z_pos
  eb_d := by simpa [hy] using B.d_eq
  eb_S := by
    have h := B.S_eq
    rw [hy] at h
    simp at h
    nlinarith
  eb_k := by simpa [hy] using B.k_eq
  qj_d := O.qj_d
  qj_S := O.qj_S
  qj_k := O.qj_k

namespace EBOneData
variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns}

def detB (T : A.EBOneData E) : ℤ := T.xb*E.Lj-T.z*E.Lb

def Qb (E : K.Returns) : ℤ := E.Vj+(D.a 1 : ℤ)+1

theorem Qb_pos : 1 ≤ Qb E := by
  have hv := E.coeff_nonneg.2.2.1
  have ha : (1:ℤ) ≤ D.a 1 := by exact_mod_cast D.a_pos 1
  simp [Qb]
  omega

def InTriangle (T : A.EBOneData E) (p q : ℤ) : Prop :=
  0 ≤ E.Lj*p-T.z*q ∧ 0 ≤ -E.Lb*p+T.xb*q ∧
  (E.Lj*p-T.z*q)+(-E.Lb*p+T.xb*q) ≤ T.detB

def IsVertex (T : A.EBOneData E) (p q : ℤ) : Prop :=
  (p=0 ∧ q=0) ∨ (p=T.xb ∧ q=E.Lb) ∨ (p=T.z ∧ q=E.Lj)

def EBEmptyTriangleStatement (T : A.EBOneData E) : Prop :=
  ∀ p q : ℤ, InTriangle T p q → IsVertex T p q

theorem detB_mul_d (T : A.EBOneData E) :
    T.detB*K.d=T.xb*(E.Aj+1)+T.z*K.chain.delta := by
  simp [detB]
  linear_combination T.xb*T.qj_d-T.z*T.eb_d

theorem detB_pos (T : A.EBOneData E) : 1 ≤ T.detB := by
  have hd := K.d_range.1
  have ha := OneData.a_pos (K:=K) (E:=E)
  simp [OneData.a] at ha
  have hdelta := K.chain.scalar_ranges.1
  have hxb := T.xb_pos
  have hz := T.z_pos
  have hrhs : 0 < T.xb*(E.Aj+1)+T.z*K.chain.delta := by
    nlinarith [mul_pos (show 0<T.xb by omega) (show 0<E.Aj+1 by omega),
      mul_pos (show 0<T.z by omega) (show 0<K.chain.delta by omega)]
  by_contra h
  have hp : T.detB*K.d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
  rw [T.detB_mul_d] at hp
  omega
variable (T : A.EBOneData E)

def baryAlpha (p q : ℤ) : ℤ := E.Lj*p-T.z*q
def baryBeta (p q : ℤ) : ℤ := -E.Lb*p+T.xb*q
def baryGamma (p q : ℤ) : ℤ := T.detB-T.baryAlpha p q-T.baryBeta p q

def Ipq (p q : ℤ) : ℤ := K.chain.delta-1+q*K.d-p*(D.a 0 : ℤ)+0*T.xb
def Jpq (p q : ℤ) : ℤ := K.chain.gapJ-1+p*(D.rho 1 : ℤ)-q*K.S+0*T.xb

theorem inTriangle_iff {p q : ℤ} : InTriangle T p q ↔
    0 ≤ T.baryAlpha p q ∧ 0 ≤ T.baryBeta p q ∧ 0 ≤ T.baryGamma p q := by
  simp [InTriangle, baryAlpha, baryBeta, baryGamma]
  omega

theorem reconstruct_p (p q : ℤ) :
    T.detB*p=T.xb*T.baryAlpha p q+T.z*T.baryBeta p q := by
  simp [detB, baryAlpha, baryBeta]
  ring

theorem reconstruct_q (p q : ℤ) :
    T.detB*q=E.Lb*T.baryAlpha p q+E.Lj*T.baryBeta p q := by
  simp [detB, baryAlpha, baryBeta]
  ring

theorem I_barycentric (p q : ℤ) :
    T.detB*(T.Ipq p q+1)=T.baryGamma p q*K.chain.delta+
      T.baryBeta p q*(E.Aj+K.chain.delta+1) := by
  simp [Ipq, baryGamma, baryAlpha, baryBeta, detB]
  linear_combination
    (E.Lj*p-T.z*q)*T.eb_d + (-E.Lb*p+T.xb*q)*T.qj_d

theorem J_barycentric (p q : ℤ) :
    T.detB*(T.Jpq p q+1)=T.baryGamma p q*K.chain.gapJ+
      T.baryAlpha p q*(Qb E+K.chain.gapJ) := by
  simp [Jpq, baryGamma, baryAlpha, baryBeta, detB, Qb]
  linear_combination
    -(E.Lj*p-T.z*q)*T.eb_S - (-E.Lb*p+T.xb*q)*T.qj_S

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
theorem empty_triangleB (hF : s.semigroup.IsFrobenius F)
    (hb : K.Croot=K.chain.alpha) : EBEmptyTriangleStatement T := by
  intro p q hpq
  by_contra hvertex
  have hbar := T.inTriangle_iff.mp hpq
  have ha0 := hbar.1
  have hb0 := hbar.2.1
  have hg0 := hbar.2.2
  have hdet := T.detB_pos
  have hdelta := K.chain.scalar_ranges.1
  have hgap := K.chain.scalar_ranges.2.2.1
  have ha := OneData.a_pos (K:=K) (E:=E)
  have hQ := Qb_pos (K:=K) (E:=E)
  have hx := T.xb_pos
  have hz := T.z_pos
  have hLi := E.levels_pos.2.1
  have hLj := E.levels_pos.2.2.1
  have hcoeff := E.coeff_nonneg
  have hAj : 0 ≤ E.Aj := hcoeff.2.2.2.2.1
  have hUj : 0 ≤ E.Uj := hcoeff.1
  have hIprod := T.I_barycentric p q
  have hJprod := T.J_barycentric p q
  have hI1 : 0 ≤ T.Ipq p q+1 := by
    by_contra hn
    have hl : T.detB*(T.Ipq p q+1) < 0 := mul_neg_of_pos_of_neg (by omega) (by omega)
    have hr1 := mul_nonneg hg0 (show 0 ≤ K.chain.delta by omega)
    have hr2 := mul_nonneg hb0 (show 0 ≤ E.Aj+K.chain.delta+1 by omega)
    nlinarith
  have hJ1 : 0 ≤ T.Jpq p q+1 := by
    by_contra hn
    have hl : T.detB*(T.Jpq p q+1) < 0 := mul_neg_of_pos_of_neg (by omega) (by omega)
    have hr1 := mul_nonneg hg0 (show 0 ≤ K.chain.gapJ by omega)
    have hr2 := mul_nonneg ha0 (show 0 ≤ Qb E+K.chain.gapJ by omega)
    nlinarith
  have hIpos : 0 < T.Ipq p q+1 := by
    by_contra hn
    have hzero : T.Ipq p q+1=0 := by omega
    have hsum : T.baryGamma p q*K.chain.delta+T.baryBeta p q*(E.Aj+K.chain.delta+1)=0 := by
      rw [hzero] at hIprod
      simpa using hIprod.symm
    have hgprod : T.baryGamma p q*K.chain.delta=0 := by
      have h1 := mul_nonneg hg0 (show 0 ≤ K.chain.delta by omega)
      have h2 := mul_nonneg hb0 (show 0 ≤ E.Aj+K.chain.delta+1 by omega)
      omega
    have hbprod : T.baryBeta p q*(E.Aj+K.chain.delta+1)=0 := by omega
    have hgz : T.baryGamma p q=0 := (mul_eq_zero.mp hgprod).resolve_right (by omega)
    have hbz : T.baryBeta p q=0 := (mul_eq_zero.mp hbprod).resolve_right (by omega)
    have haz : T.baryAlpha p q=T.detB := by simp [baryGamma] at hgz; omega
    have hp := T.reconstruct_p p q
    have hq := T.reconstruct_q p q
    rw [haz, hbz] at hp hq
    have hp0 : T.detB*(p-T.xb)=0 := by linear_combination hp
    have hq0 : T.detB*(q-E.Lb)=0 := by linear_combination hq
    have hpe : p=T.xb := by have := (mul_eq_zero.mp hp0).resolve_left (by omega); omega
    have hqe : q=E.Lb := by have := (mul_eq_zero.mp hq0).resolve_left (by omega); omega
    apply hvertex
    simp [IsVertex, hpe, hqe]
  have hJpos : 0 < T.Jpq p q+1 := by
    by_contra hn
    have hzero : T.Jpq p q+1=0 := by omega
    have hsum : T.baryGamma p q*K.chain.gapJ+T.baryAlpha p q*(Qb E+K.chain.gapJ)=0 := by
      rw [hzero] at hJprod
      simpa using hJprod.symm
    have hgprod : T.baryGamma p q*K.chain.gapJ=0 := by
      have h1 := mul_nonneg hg0 (show 0 ≤ K.chain.gapJ by omega)
      have h2 := mul_nonneg ha0 (show 0 ≤ Qb E+K.chain.gapJ by omega)
      omega
    have haprod : T.baryAlpha p q*(Qb E+K.chain.gapJ)=0 := by omega
    have hgz : T.baryGamma p q=0 := (mul_eq_zero.mp hgprod).resolve_right (by omega)
    have haz : T.baryAlpha p q=0 := (mul_eq_zero.mp haprod).resolve_right (by omega)
    have hbz : T.baryBeta p q=T.detB := by simp [baryGamma] at hgz; omega
    have hp := T.reconstruct_p p q
    have hq := T.reconstruct_q p q
    rw [haz, hbz] at hp hq
    have hp0 : T.detB*(p-T.z)=0 := by linear_combination hp
    have hq0 : T.detB*(q-E.Lj)=0 := by linear_combination hq
    have hpe : p=T.z := by have := (mul_eq_zero.mp hp0).resolve_left (by omega); omega
    have hqe : q=E.Lj := by have := (mul_eq_zero.mp hq0).resolve_left (by omega); omega
    apply hvertex
    simp [IsVertex, hpe, hqe]
  have hI : 0 ≤ T.Ipq p q := by omega
  have hJ : 0 ≤ T.Jpq p q := by omega
  have hpRec := T.reconstruct_p p q
  have hqRec := T.reconstruct_q p q
  have hpnonneg : 0 ≤ p := by
    by_contra hn
    have hl := mul_neg_of_pos_of_neg (show 0 < T.detB by omega) (show p < 0 by omega)
    have hxa := mul_nonneg (show 0 ≤ T.xb by omega) ha0
    have hzb := mul_nonneg (show 0 ≤ T.z by omega) hb0
    nlinarith
  have hqnonneg : 0 ≤ q := by
    by_contra hn
    have hl := mul_neg_of_pos_of_neg (show 0 < T.detB by omega) (show q < 0 by omega)
    have hLa := mul_nonneg (show 0 ≤ E.Lb by have := E.levels_pos.1; omega) ha0
    have hMb := mul_nonneg (show 0 ≤ E.Lj by have := E.levels_pos.2.2.1; omega) hb0
    nlinarith
  have hp_pos : 1 ≤ p := by
    by_contra hn
    have hpz : p=0 := by omega
    subst p
    simp only [mul_zero] at hpRec
    have hxa : T.xb*T.baryAlpha 0 q=0 := by
      have h1 := mul_nonneg (show 0 ≤ T.xb by omega) ha0
      have h2 := mul_nonneg (show 0 ≤ T.z by omega) hb0
      nlinarith
    have hzb : T.z*T.baryBeta 0 q=0 := by
      have h2 := mul_nonneg (show 0 ≤ T.z by omega) hb0
      nlinarith
    have haz : T.baryAlpha 0 q=0 := (mul_eq_zero.mp hxa).resolve_left (by omega)
    have hbz : T.baryBeta 0 q=0 := (mul_eq_zero.mp hzb).resolve_left (by omega)
    rw [haz, hbz] at hqRec
    have hqz : q=0 := by
      have hq0 : T.detB*q=0 := by simpa using hqRec
      exact (mul_eq_zero.mp hq0).resolve_left (by omega)
    apply hvertex
    simp [IsVertex, hqz]
  have hq_pos : 1 ≤ q := by
    by_contra hn
    have hqz : q=0 := by omega
    subst q
    simp only [mul_zero] at hqRec
    have hLa : E.Lb*T.baryAlpha p 0=0 := by
      have h1 := mul_nonneg (show 0 ≤ E.Lb by have := E.levels_pos.1; omega) ha0
      have h2 := mul_nonneg (show 0 ≤ E.Lj by have := E.levels_pos.2.2.1; omega) hb0
      nlinarith
    have hMb : E.Lj*T.baryBeta p 0=0 := by
      have h2 := mul_nonneg (show 0 ≤ E.Lj by omega) hb0
      nlinarith
    have haz : T.baryAlpha p 0=0 := (mul_eq_zero.mp hLa).resolve_left (by have := E.levels_pos.1; omega)
    have hbz : T.baryBeta p 0=0 := (mul_eq_zero.mp hMb).resolve_left (by have := E.levels_pos.2.2.1; omega)
    rw [haz, hbz] at hpRec
    have hpz : p=0 := by
      have hp0 : T.detB*p=0 := by simpa using hpRec
      exact (mul_eq_zero.mp hp0).resolve_left (by omega)
    apply hvertex
    simp [IsVertex, hpz]
  have hsum : T.baryAlpha p q+T.baryBeta p q ≤ T.detB := by
    change 0 ≤ T.detB-T.baryAlpha p q-T.baryBeta p q at hg0
    omega
  have hq_upper : q ≤ max E.Lb E.Lj := by
    by_cases hLM : E.Lb ≤ E.Lj
    · have h1 := mul_le_mul_of_nonneg_right hLM ha0
      have h2 := mul_le_mul_of_nonneg_left hsum (show 0 ≤ E.Lj by have := E.levels_pos.2.2.1; omega)
      have hprod : T.detB*q ≤ T.detB*E.Lj := by nlinarith
      have hqM : q ≤ E.Lj := by
        by_contra hn
        have := mul_pos (show 0 < T.detB by omega) (show 0 < q-E.Lj by omega)
        nlinarith
      simpa [max_eq_right hLM] using hqM
    · have hML : E.Lj ≤ E.Lb := by omega
      have h1 := mul_le_mul_of_nonneg_right hML hb0
      have h2 := mul_le_mul_of_nonneg_left hsum (show 0 ≤ E.Lb by have := E.levels_pos.1; omega)
      have hprod : T.detB*q ≤ T.detB*E.Lb := by nlinarith
      have hqL : q ≤ E.Lb := by
        by_contra hn
        have := mul_pos (show 0 < T.detB by omega) (show 0 < q-E.Lb by omega)
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
  have hwall := A.boundaryWall E hF hb
  omega



def EBDetOneStatement (T : A.EBOneData E) : Prop := T.detB=1

/-- Emptiness of the lattice triangle forces the first edge to be primitive. -/
theorem primitive_first_edgeB (hempty : EBEmptyTriangleStatement T) : T.xb.gcd E.Lb = 1 := by
  have hx := T.xb_pos
  have hLi := E.levels_pos.2.1
  let c : ℤ := (T.xb.gcd E.Lb : ℕ)
  have hcposNat : 0 < T.xb.gcd E.Lb := by
    rw [Int.gcd_eq_natAbs]
    exact Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr (by omega))
  have hcNat : 1 ≤ T.xb.gcd E.Lb := by omega
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
  let p := T.xb / c
  let q := E.Lb / c
  have hcx : c ∣ T.xb := by
    dsimp [c]
    exact Int.gcd_dvd_left _ _
  have hcLi : c ∣ E.Lb := by
    dsimp [c]
    exact Int.gcd_dvd_right _ _
  have hpx : p*c=T.xb := by exact Int.ediv_mul_cancel hcx
  have hqLi : q*c=E.Lb := by exact Int.ediv_mul_cancel hcLi
  have hbeta : T.baryBeta p q=0 := by
    simp [baryBeta]
    rw [← hpx, ← hqLi]
    ring
  have halpha_mul : c*T.baryAlpha p q=T.detB := by
    simp [baryAlpha, detB]
    rw [← hpx, ← hqLi]
    ring
  have hdet := T.detB_pos
  have halpha_pos : 0 < T.baryAlpha p q := by
    by_contra hn
    have := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ c by omega) (show T.baryAlpha p q ≤ 0 by omega)
    nlinarith
  have halpha_lt : T.baryAlpha p q < T.detB := by
    nlinarith [mul_pos (show 0 < c-1 by omega) halpha_pos]
  have hin : InTriangle T p q := T.inTriangle_iff.mpr ⟨halpha_pos.le, by simp [hbeta], by
    simp [baryGamma, hbeta]
    omega⟩
  have hp_pos : 0 < p := by
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg (show p ≤ 0 by omega) (show 0 ≤ c by omega)
    nlinarith
  have hp_lt : p < T.xb := by
    nlinarith [mul_pos (show 0 < p by omega) (show 0 < c-1 by omega)]
  have hnonvertex : ¬ IsVertex T p q := by
    intro hv
    rcases hv with hO | hU | hV
    · omega
    · omega
    · have haz : T.baryAlpha p q=0 := by simp [baryAlpha, hV.1, hV.2]; ring
      omega
  exact hnonvertex (hempty p q hin)

private theorem pullback_beta (r s a b p q : ℤ)
    (hbez : r*T.xb+s*E.Lb=1)
    (hp : p=T.xb*a-s*b) (hq : q=E.Lb*a+r*b) : T.baryBeta p q=b := by
  simp [baryBeta, hp, hq]
  linear_combination b*hbez

private theorem pullback_alpha (r s k r0 a0 b p q : ℤ)
    (hv : r*T.z+s*E.Lj=k*T.detB+r0)
    (hp : p=T.xb*(a0+k*b)-s*b) (hq : q=E.Lb*(a0+k*b)+r*b) :
    T.baryAlpha p q=T.detB*a0-r0*b := by
  calc
    T.baryAlpha p q = T.detB*(a0+k*b)-(r*T.z+s*E.Lj)*b := by
      simp [baryAlpha, detB, hp, hq]
      ring
    _ = T.detB*a0-r0*b := by rw [hv]; ring

/-- Explicit Bézout and shear normalization produces a nonvertex lattice point if `det ≥ 2`. -/
theorem det_oneB (hempty : EBEmptyTriangleStatement T) : EBDetOneStatement T := by
  have hdet := T.detB_pos
  have hgcd := T.primitive_first_edgeB hempty
  let r : ℤ := Int.gcdA T.xb E.Lb
  let s0 : ℤ := Int.gcdB T.xb E.Lb
  have hbez : r*T.xb+s0*E.Lb=1 := by
    have h := Int.gcd_eq_gcd_ab T.xb E.Lb
    rw [hgcd] at h
    simpa [r, s0, mul_comm] using h.symm
  change T.detB=1
  by_contra hne
  have hdet2 : 2 ≤ T.detB := by omega
  let v1 : ℤ := r*T.z+s0*E.Lj
  let k : ℤ := v1/T.detB
  let r0 : ℤ := v1%T.detB
  have hr0_nonneg : 0 ≤ r0 := by
    dsimp [r0]
    exact Int.emod_nonneg _ (by omega)
  have hr0_lt : r0 < T.detB := by
    have h := Int.emod_lt v1 (show T.detB ≠ 0 by omega)
    rw [Int.natAbs_of_nonneg (show 0 ≤ T.detB by omega)] at h
    exact h
  have hv1 : v1=k*T.detB+r0 := by
    have h := Int.ediv_mul_add_emod v1 T.detB
    dsimp [k, r0]
    omega
  by_cases hr0 : r0=0
  · let a0 : ℤ := 0
    let b0 : ℤ := 1
    let p : ℤ := T.xb*(a0+k*b0)-s0*b0
    let q : ℤ := E.Lb*(a0+k*b0)+r*b0
    have hb : T.baryBeta p q=b0 :=
      T.pullback_beta r s0 (a0+k*b0) b0 p q hbez rfl rfl
    have ha : T.baryAlpha p q=T.detB*a0-r0*b0 :=
      T.pullback_alpha r s0 k r0 a0 b0 p q (by simpa [v1] using hv1) rfl rfl
    have ha0 : T.baryAlpha p q=0 := by simp [ha, a0, b0, hr0]
    have hb1 : T.baryBeta p q=1 := by simpa [b0] using hb
    have hin : InTriangle T p q := T.inTriangle_iff.mpr ⟨by simp [ha0], by simp [hb1], by
      simp [baryGamma, ha0, hb1]
      omega⟩
    have hnonvertex : ¬ IsVertex T p q := by
      intro hv
      rcases hv with hO | hU | hV
      · have : T.baryBeta p q=0 := by simp [baryBeta, hO.1, hO.2]
        omega
      · have : T.baryBeta p q=0 := by simp [baryBeta, hU.1, hU.2]; ring
        omega
      · have : T.baryBeta p q=T.detB := by simp [baryBeta, detB, hV.1, hV.2]; ring
        omega
    exact hnonvertex (hempty p q hin)
  · have hr0_pos : 1 ≤ r0 := by omega
    let a0 : ℤ := 1
    let b0 : ℤ := 1
    let p : ℤ := T.xb*(a0+k*b0)-s0*b0
    let q : ℤ := E.Lb*(a0+k*b0)+r*b0
    have hb : T.baryBeta p q=b0 :=
      T.pullback_beta r s0 (a0+k*b0) b0 p q hbez rfl rfl
    have ha : T.baryAlpha p q=T.detB*a0-r0*b0 :=
      T.pullback_alpha r s0 k r0 a0 b0 p q (by simpa [v1] using hv1) rfl rfl
    have ha_pos : 1 ≤ T.baryAlpha p q := by simp [ha, a0, b0]; omega
    have hb1 : T.baryBeta p q=1 := by simpa [b0] using hb
    have hin : InTriangle T p q := T.inTriangle_iff.mpr ⟨by omega, by simp [hb1], by
      simp [baryGamma, ha, hb1, a0, b0]
      omega⟩
    have hnonvertex : ¬ IsVertex T p q := by
      intro hv
      rcases hv with hO | hU | hV
      · have : T.baryBeta p q=0 := by simp [baryBeta, hO.1, hO.2]
        omega
      · have : T.baryBeta p q=0 := by simp [baryBeta, hU.1, hU.2]; ring
        omega
      · have : T.baryBeta p q=T.detB := by simp [baryBeta, detB, hV.1, hV.2]; ring
        omega
    exact hnonvertex (hempty p q hin)

end EBOneData
end P21.Nonsymmetric.ChainCore.FirstFit
