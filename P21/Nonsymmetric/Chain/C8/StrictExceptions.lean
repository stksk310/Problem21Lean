import P21.Nonsymmetric.Chain.C8.StrictIdentities

set_option maxHeartbeats 1200000

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} (O : A.OneData E)

def EX1 (O : A.OneData E) : Prop :=
  E.Li=2 ∧ O.x=1 ∧ E.Lj=2*O.z+1 ∧ Q E=2 ∧
    K.chain.gapJ=1 ∧ (D.a 1 : ℤ)=1 ∧ 1≤O.z

def EX2 (O : A.OneData E) : Prop :=
  E.Li=2 ∧ O.x=1 ∧ O.z=1 ∧ E.Lj=3 ∧ Q E=3 ∧
    K.chain.gapJ=1 ∧ (D.a 1 : ℤ)=1

def EX3 (O : A.OneData E) : Prop :=
  E.Li=3 ∧ O.x=2 ∧ O.z=1 ∧ E.Lj=2 ∧ Q E=2 ∧
    K.chain.gapJ=1 ∧ (D.a 1 : ℤ)=1

/-- Exact symbolic classification of the negative `a` coefficient. -/
theorem Ea_negative_exceptions (hdet : O.DetOneStatement)
    (hreg : E.Li≥O.x+1 ∧ E.Lj>O.z ∧ O.x≥1 ∧ O.z≥1)
    (hQ2 : 2≤Q E) (hEa : O.Ea<0) : O.EX1 ∨ O.EX2 ∨ O.EX3 := by
  change O.x*E.Lj-O.z*E.Li=1 at hdet
  have hL : 2≤E.Li := by omega
  have hM : 2≤E.Lj := by omega
  have hg : 1≤K.chain.gapJ := K.chain.scalar_ranges.2.2.1
  have haj : (1:ℤ)≤D.a 1 := by exact_mod_cast D.a_pos 1
  have hc0 : 0≤((E.Li-1)*(E.Lj-1)-1)*(Q E-2) := by
    apply mul_nonneg
    · nlinarith [mul_nonneg (show 0≤E.Li-2 by omega) (show 0≤E.Lj-2 by omega)]
    · omega
  have hc1 : 0≤E.Li^2*(K.chain.gapJ-1) := mul_nonneg (sq_nonneg _) (by omega)
  have hc2 : 0≤E.Li*((D.a 1 : ℤ)-1) := mul_nonneg (by omega) (by omega)
  have hLle : E.Li≤3 := by
    by_contra hn
    have hc3 : 0≤(E.Li-2)*E.Lj-E.Li := by
      nlinarith [mul_nonneg (show 0≤E.Li-4 by omega) (show 0≤E.Lj-2 by omega)]
    simp only [Ea] at hEa
    nlinarith
  rcases (show E.Li=2 ∨ E.Li=3 by omega) with hL2 | hL3
  · have hx : O.x=1 := by omega
    rw [hx, hL2] at hdet
    have hMform : E.Lj=2*O.z+1 := by omega
    have hp : 0≤(E.Lj-2)*(Q E-2) := mul_nonneg (by omega) (by omega)
    have hg1 : K.chain.gapJ=1 := by
      simp only [Ea, hL2] at hEa
      by_contra hn
      have : 2≤K.chain.gapJ := by omega
      nlinarith
    have haj1 : (D.a 1 : ℤ)=1 := by
      simp only [Ea, hL2, hg1] at hEa
      by_contra hn
      have : (2:ℤ)≤D.a 1 := by omega
      nlinarith
    have hsmall : (E.Lj-2)*(Q E-2)<2 := by
      norm_num [Ea, hL2, hg1, haj1] at hEa
      nlinarith
    by_cases hQ : Q E=2
    · left
      exact ⟨hL2,hx,hMform,hQ,hg1,haj1,hreg.2.2.2⟩
    · right; left
      have hQ3 : 3≤Q E := by omega
      have hprodpos : 0<(E.Lj-2)*(Q E-2) := mul_pos (by omega) (by omega)
      have hprod : (E.Lj-2)*(Q E-2)=1 := by omega
      have hM3 : E.Lj=3 := by
        by_contra hn
        have hge : 2≤E.Lj-2 := by omega
        have hh : 0≤(E.Lj-3)*(Q E-2) := mul_nonneg (by omega) (by omega)
        nlinarith
      have hQeq : Q E=3 := by
        rw [hM3] at hprod
        norm_num at hprod ⊢
        omega
      have hz1 : O.z=1 := by omega
      exact ⟨hL2,hx,hz1,hM3,hQeq,hg1,haj1⟩
  · right; right
    have hM2 : E.Lj=2 := by
      simp only [Ea, hL3] at hEa
      by_contra hn
      have hM3 : 3≤E.Lj := by omega
      nlinarith
    have hx2 : O.x=2 := by
      rw [hL3, hM2] at hdet
      omega
    rw [hx2, hL3, hM2] at hdet
    have hz1 : O.z=1 := by
      omega
    have hQeq : Q E=2 := by
      simp only [Ea, hL3, hM2] at hEa
      omega
    have hg1 : K.chain.gapJ=1 := by
      simp only [Ea, hL3, hM2, hQeq] at hEa
      omega
    have haj1 : (D.a 1 : ℤ)=1 := by
      simp only [Ea, hL3, hM2, hQeq, hg1] at hEa
      omega
    exact ⟨hL3,hx2,hz1,hM2,hQeq,hg1,haj1⟩

end P21.Nonsymmetric.ChainCore.FirstFit.OneData
