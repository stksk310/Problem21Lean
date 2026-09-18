import P21.Nonsymmetric.Chain.C8.BoundaryMultiplicity

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} (O : A.OneData E)

def Aa (O : A.OneData E) : ℤ :=
  (E.Li-1)*(E.Lj-1)*(Q E-2)+E.Li^2*(K.chain.gapJ-1)+
    E.Li*((D.a 1 : ℤ)-1)+(E.Li-2)*E.Lj+2

def Adelta (O : A.OneData E) : ℤ :=
  E.Lj*(E.Lj-1)*(Q E-2)+(E.Li*E.Lj+E.Lj-1)*(K.chain.gapJ-1)+
    E.Lj*((D.a 1 : ℤ)-1)+E.Lj^2+E.Lj-1

def Ba (O : A.OneData E) : ℤ :=
  (O.z*(E.Li-1)-O.x+1)*(Q E-2)+E.Li*O.x*(K.chain.gapJ-1)+
    O.x*((D.a 1 : ℤ)-1)+O.z*(E.Li-O.x-1)+(O.z-1)*(O.x-1)+1

def Bdelta (O : A.OneData E) : ℤ :=
  (O.x*E.Lj+O.z-1)*(K.chain.gapJ-1)+O.z*(E.Lj-1)*(Q E-2)+
    O.z*((D.a 1 : ℤ)-1)+O.z*E.Lj

theorem CA_decomposition (P : O.ParamData) :
    O.CA=a E*O.Aa+K.chain.delta*O.Adelta+
      K.chain.beta*(D.rho 1 : ℤ) := by
  simp only [CA, Kcal, P0, V, Aa, Adelta]
  rw [P.ai_eq, P.rhoj_eq, P.bi_eq]
  ring

theorem CB_decomposition (P : O.ParamData) :
    O.CB=a E*O.Ba+K.chain.delta*O.Bdelta+
      K.chain.beta*(K.S-1) := by
  simp only [CB, Dj, P0, V, Ba, Bdelta]
  rw [P.d_eq, P.S_eq, P.ai_eq, P.bi_eq]
  ring

theorem boundary_coefficient_positive (P : O.ParamData)
    (hreg : E.Li≥O.x+1 ∧ O.x+1≥2 ∧ E.Lj>O.z ∧ O.z≥1)
    (hQ2 : 2≤Q E) :
    0 < O.Aa ∧ 0 < O.Adelta ∧ 0 < O.Ba ∧ 0 < O.Bdelta := by
  have hL : 2≤E.Li := by omega
  have hM : 2≤E.Lj := by omega
  have hx : 1≤O.x := by omega
  have hz : 1≤O.z := by omega
  have hg : 1≤K.chain.gapJ := K.chain.scalar_ranges.2.2.1
  have haj : (1:ℤ)≤D.a 1 := by exact_mod_cast D.a_pos 1
  have hzcoef_eq : O.z*(E.Li-1)-O.x+1 =
      O.x*(O.z-1)+1+O.z*(E.Li-O.x-1) := by ring
  have hzcoef : 1≤O.z*(E.Li-1)-O.x+1 := by
    rw [hzcoef_eq]
    have h1 : 0≤O.x*(O.z-1) := mul_nonneg (by omega) (by omega)
    have h2 : 0≤O.z*(E.Li-O.x-1) := mul_nonneg (by omega) (by omega)
    omega
  have hAa1 : 0≤(E.Li-1)*(E.Lj-1)*(Q E-2) :=
    mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
  have hAa2 : 0≤E.Li^2*(K.chain.gapJ-1) := mul_nonneg (sq_nonneg _) (by omega)
  have hAa3 : 0≤E.Li*((D.a 1 : ℤ)-1) := mul_nonneg (by omega) (by omega)
  have hAa4 : 0≤(E.Li-2)*E.Lj := mul_nonneg (by omega) (by omega)
  have hAd1 : 0≤E.Lj*(E.Lj-1)*(Q E-2) :=
    mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
  have hAd2 : 0≤(E.Li*E.Lj+E.Lj-1)*(K.chain.gapJ-1) := by
    apply mul_nonneg <;> nlinarith [mul_pos (show 0<E.Li by omega) (show 0<E.Lj by omega)]
  have hAd3 : 0≤E.Lj*((D.a 1 : ℤ)-1) := mul_nonneg (by omega) (by omega)
  have hAd4 : 0<E.Lj^2+E.Lj-1 := by nlinarith [sq_nonneg (E.Lj-1)]
  have hBa1 : 0≤(O.z*(E.Li-1)-O.x+1)*(Q E-2) :=
    mul_nonneg (by omega) (by omega)
  have hBa2 : 0≤E.Li*O.x*(K.chain.gapJ-1) :=
    mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
  have hBa3 : 0≤O.x*((D.a 1 : ℤ)-1) := mul_nonneg (by omega) (by omega)
  have hBa4 : 0≤O.z*(E.Li-O.x-1) := mul_nonneg (by omega) (by omega)
  have hBa5 : 0≤(O.z-1)*(O.x-1) := mul_nonneg (by omega) (by omega)
  have hBd1 : 0≤(O.x*E.Lj+O.z-1)*(K.chain.gapJ-1) := by
    apply mul_nonneg <;> nlinarith [mul_pos (show 0<O.x by omega) (show 0<E.Lj by omega)]
  have hBd2 : 0≤O.z*(E.Lj-1)*(Q E-2) :=
    mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
  have hBd3 : 0≤O.z*((D.a 1 : ℤ)-1) := mul_nonneg (by omega) (by omega)
  have hBd4 : 0<O.z*E.Lj := mul_pos (by omega) (by omega)
  simp only [Aa, Adelta, Ba, Bdelta]
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

theorem CA_CB_pos (P : O.ParamData)
    (hreg : E.Li≥O.x+1 ∧ O.x+1≥2 ∧ E.Lj>O.z ∧ O.z≥1)
    (hQ2 : 2≤Q E) : 0 < O.CA ∧ 0 < O.CB := by
  obtain ⟨hAa,hAd,hBa,hBd⟩ := O.boundary_coefficient_positive P hreg hQ2
  have ha : 0<a E := a_pos (K:=K) (E:=E)
  have hd : 0<K.chain.delta := by have := K.chain.scalar_ranges.1; omega
  have hb : 0<K.chain.beta := by have := K.chain.scalar_ranges.2.1; omega
  have hr : 0<(D.rho 1 : ℤ) := by exact_mod_cast D.rho_pos 1
  have hS : 1≤K.S := by
    have := K.S_strong
    have := K.chain.scalar_ranges.2.2.1
    omega
  rw [O.CA_decomposition P, O.CB_decomposition P]
  constructor
  · have h1 := mul_pos ha hAa
    have h2 := mul_pos hd hAd
    have h3 := mul_pos hb hr
    nlinarith
  · have h1 := mul_pos ha hBa
    have h2 := mul_pos hd hBd
    have h3 := mul_nonneg (le_of_lt hb) (show 0≤K.S-1 by omega)
    nlinarith

end P21.Nonsymmetric.ChainCore.FirstFit.OneData
