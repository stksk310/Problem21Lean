import P21.Nonsymmetric.Chain.C8.StrictExceptions

set_option maxHeartbeats 1200000

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} (O : A.OneData E)

theorem Edelta_pos
    (hreg : E.Li≥O.x+1 ∧ E.Lj>O.z ∧ O.x≥1 ∧ O.z≥1)
    (hQ2 : 2≤Q E) : 0<O.Edelta := by
  have hL : 2≤E.Li := by omega
  have hM : 2≤E.Lj := by omega
  have hg := K.chain.scalar_ranges.2.2.1
  have haj : (1:ℤ)≤D.a 1 := by exact_mod_cast D.a_pos 1
  have h1 : 0≤E.Lj*(E.Lj-1)*(Q E-2) :=
    mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
  have h2 : 0≤(E.Li*E.Lj+E.Lj)*(K.chain.gapJ-1) :=
    mul_nonneg (by nlinarith [mul_pos (show 0<E.Li by omega) (show 0<E.Lj by omega)]) (by omega)
  have h3 : 0≤E.Lj*((D.a 1 : ℤ)-1) := mul_nonneg (by omega) (by omega)
  have h4 : 0<E.Lj^2 := sq_pos_of_pos (by omega)
  simp only [Edelta]
  nlinarith

theorem CA_sub_P0_pos_regular (hdet : O.DetOneStatement) (P : O.ParamData)
    (hreg : E.Li≥O.x+1 ∧ E.Lj>O.z ∧ O.x≥1 ∧ O.z≥1)
    (hQ2 : 2≤Q E) (hnot : ¬O.EX1 ∧ ¬O.EX2 ∧ ¬O.EX3) :
    0<O.CA-O.P0 := by
  have hEa : 0≤O.Ea := by
    by_contra hn
    have hex := O.Ea_negative_exceptions hdet hreg hQ2 (by omega)
    rcases hex with h1 | h2 | h3
    · exact hnot.1 h1
    · exact hnot.2.1 h2
    · exact hnot.2.2 h3
  have hEd := O.Edelta_pos hreg hQ2
  have ha : 0<a E := a_pos (K:=K) (E:=E)
  have hd : 0<K.chain.delta := by have := K.chain.scalar_ranges.1; omega
  have hb : 0<K.chain.beta := by have := K.chain.scalar_ranges.2.1; omega
  have hr : (0:ℤ)<D.rho 1 := by exact_mod_cast D.rho_pos 1
  rw [O.CA_sub_P0_decomposition P]
  have h1 := mul_nonneg (le_of_lt ha) hEa
  have h2 := mul_pos hd hEd
  have h3 := mul_pos hb hr
  nlinarith

theorem Aprime_Bprime_pos (P : O.ParamData)
    (hreg : E.Li≥O.x+1 ∧ E.Lj>O.z ∧ O.x≥1 ∧ O.z≥1)
    (hQ1 : 1≤Q E) : 0<O.Aprime ∧ 0<O.Bprime := by
  have hL : 2≤E.Li := by omega
  have hM : 2≤E.Lj := by omega
  have hg := K.chain.scalar_ranges.2.2.1
  have haj : (1:ℤ)≤D.a 1 := by exact_mod_cast D.a_pos 1
  have hr : (1:ℤ)≤D.rho 1 := by exact_mod_cast D.rho_pos 1
  have ha : 0<a E := a_pos (K:=K) (E:=E)
  have hd : 0<K.chain.delta := by have := K.chain.scalar_ranges.1; omega
  have hb : 0<K.chain.beta := by have := K.chain.scalar_ranges.2.1; omega
  have hS : 1≤K.S := by have := K.S_strong; have := K.chain.scalar_ranges.2.2.1; omega
  have hLM : 0≤(E.Li-1)*E.Lj-E.Li := by
    nlinarith [mul_nonneg (show 0≤E.Li-2 by omega) (show 0≤E.Lj-2 by omega)]
  have hzcoef : 1≤O.z*(E.Li-1)-O.x+1 := by
    have heq : O.z*(E.Li-1)-O.x+1=
        O.x*(O.z-1)+1+O.z*(E.Li-O.x-1) := by ring
    rw [heq]
    have h1 := mul_nonneg (show 0≤O.x by omega) (show 0≤O.z-1 by omega)
    have h2 := mul_nonneg (show 0≤O.z by omega) (show 0≤E.Li-O.x-1 by omega)
    omega
  have hAc : 0<E.Li^2*K.chain.gapJ+((E.Li-1)*E.Lj-E.Li)*Q E+
      E.Li*(D.a 1 : ℤ) := by
    have h1 := mul_pos (sq_pos_of_pos (show 0<E.Li by omega)) (show 0<K.chain.gapJ by omega)
    have h2 := mul_nonneg hLM (show 0≤Q E by omega)
    have h3 := mul_pos (show 0<E.Li by omega) (show (0:ℤ)<D.a 1 by omega)
    nlinarith
  have hAd : 0<(E.Lj-1)*(D.rho 1 : ℤ)+E.Lj*(D.a 1 : ℤ)+
      (E.Lj+E.Li)*K.chain.gapJ := by
    have h1 := mul_pos (show 0<E.Lj-1 by omega) (show (0:ℤ)<D.rho 1 by omega)
    have h2 := mul_pos (show 0<E.Lj by omega) (show (0:ℤ)<D.a 1 by omega)
    have h3 := mul_pos (show 0<E.Lj+E.Li by omega) (show 0<K.chain.gapJ by omega)
    nlinarith
  have hBc : 0<O.x*(D.a 1 : ℤ)+E.Li*O.x*K.chain.gapJ+
      (O.z*(E.Li-1)-O.x+1)*Q E := by
    have h1 := mul_pos (show 0<O.x by omega) (show (0:ℤ)<D.a 1 by omega)
    have h2 := mul_pos (mul_pos (show 0<E.Li by omega) (show 0<O.x by omega))
      (show 0<K.chain.gapJ by omega)
    have h3 := mul_pos (show 0<O.z*(E.Li-1)-O.x+1 by omega) (show 0<Q E by omega)
    nlinarith
  have hBd : 0<O.z*(D.a 1 : ℤ)+(E.Lj-1)*K.S+
      (O.z+O.x-1)*K.chain.gapJ := by
    have h1 := mul_pos (show 0<O.z by omega) (show (0:ℤ)<D.a 1 by omega)
    have h2 := mul_nonneg (show 0≤E.Lj-1 by omega) (show 0≤K.S by omega)
    have h3 := mul_pos (show 0<O.z+O.x-1 by omega) (show 0<K.chain.gapJ by omega)
    nlinarith
  rw [O.Aprime_decomposition P, O.Bprime_decomposition P]
  constructor
  · nlinarith [mul_pos ha hAc, mul_pos hd hAd, mul_pos hb (show (0:ℤ)<D.rho 1 by omega)]
  · nlinarith [mul_pos ha hBc, mul_pos hd hBd, mul_pos hb (show 0<K.S by omega)]

theorem Ecoeff_identity :
    O.Ecoeff-(E.Li-O.x-3)=
      (E.Li-2)*(E.Lj-2)+(E.Li-1)*(O.z-1) := by
  simp [Ecoeff]
  ring

end P21.Nonsymmetric.ChainCore.FirstFit.OneData
