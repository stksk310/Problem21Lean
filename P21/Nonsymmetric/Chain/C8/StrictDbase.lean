import P21.Nonsymmetric.Chain.C8.StrictPositivity

set_option maxHeartbeats 1200000

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} (O : A.OneData E)

def DbaseA (O : A.OneData E) : ℤ :=
  (E.Li+O.x)*(D.a 1 : ℤ)+E.Li*(E.Li+O.x)*K.chain.gapJ+O.Ecoeff*Q E

private theorem Dbase_pos_of_a (P : O.ParamData)
    (hreg : E.Li≥O.x+1 ∧ E.Lj>O.z ∧ O.x≥1 ∧ O.z≥1)
    (hA : 0<O.DbaseA) : 0<O.Dbase := by
  have hL : 2≤E.Li := by omega
  have hM : 2≤E.Lj := by omega
  have hg := K.chain.scalar_ranges.2.2.1
  have haj : (1:ℤ)≤D.a 1 := by exact_mod_cast D.a_pos 1
  have hr : (1:ℤ)≤D.rho 1 := by exact_mod_cast D.rho_pos 1
  have hS : 1≤K.S := by have := K.S_strong; have := K.chain.scalar_ranges.2.2.1; omega
  have ha : 0<a E := a_pos (K:=K) (E:=E)
  have hd : 0<K.chain.delta := by have := K.chain.scalar_ranges.1; omega
  have hb : 0<K.chain.beta := by have := K.chain.scalar_ranges.2.1; omega
  have hD : 0<(E.Lj-1)*(D.rho 1 : ℤ)+(E.Lj+O.z)*(D.a 1 : ℤ)+
      (E.Lj-1)*K.S+(2*(E.Lj+E.Li)+O.z+O.x-2)*K.chain.gapJ := by
    have h1 := mul_pos (show 0<E.Lj-1 by omega) (show (0:ℤ)<D.rho 1 by omega)
    have h2 := mul_pos (show 0<E.Lj+O.z by omega) (show (0:ℤ)<D.a 1 by omega)
    have h3 := mul_pos (show 0<E.Lj-1 by omega) (show 0<K.S by omega)
    have h4 := mul_pos (show 0<2*(E.Lj+E.Li)+O.z+O.x-2 by omega)
      (show 0<K.chain.gapJ by omega)
    nlinarith
  have hB : 0<(D.rho 1 : ℤ)+K.S := by omega
  rw [O.Dbase_decomposition P]
  change 0<a E*O.DbaseA+K.chain.delta*_
    +K.chain.beta*((D.rho 1 : ℤ)+K.S)
  nlinarith [mul_pos ha hA, mul_pos hd hD, mul_pos hb hB]

theorem Dbase_pos_q_one (P : O.ParamData)
    (hreg : E.Li≥O.x+1 ∧ E.Lj>O.z ∧ O.x≥1 ∧ O.z≥1)
    (hQ : Q E=1) : 0<O.Dbase := by
  have hL : 2≤E.Li := by omega
  have hx : 1≤O.x := hreg.2.2.1
  have hM : 2≤E.Lj := by omega
  have hz : 1≤O.z := hreg.2.2.2
  have hg := K.chain.scalar_ranges.2.2.1
  have haj : (1:ℤ)≤D.a 1 := by exact_mod_cast D.a_pos 1
  have heq := O.Ecoeff_identity
  have hp1 : 0≤(E.Li-2)*(E.Lj-2) := mul_nonneg (by omega) (by omega)
  have hp2 : 0≤(E.Li-1)*(O.z-1) := mul_nonneg (by omega) (by omega)
  have hEco : E.Li-O.x-3≤O.Ecoeff := by nlinarith
  have hbase : 0<(E.Li+O.x)*(E.Li+1)-2 := by
    nlinarith [mul_pos (show 0<E.Li+O.x by omega) (show 0<E.Li+1 by omega)]
  have hA : 0<O.DbaseA := by
    simp only [DbaseA, hQ, mul_one]
    have h1 : 0≤(E.Li+O.x)*((D.a 1 : ℤ)-1) := mul_nonneg (by omega) (by omega)
    have h2 : 0≤E.Li*(E.Li+O.x)*(K.chain.gapJ-1) :=
      mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
    nlinarith
  exact O.Dbase_pos_of_a P hreg hA

theorem DbaseA_EX1 (h : O.EX1) : O.DbaseA=2*O.z+3 := by
  rcases h with ⟨hL,hx,hM,hQ,hg,haj,hz⟩
  simp [DbaseA, Ecoeff, hL, hx, hM, hQ, hg, haj]
  ring

theorem DbaseA_EX2 (h : O.EX2) : O.DbaseA=3 := by
  rcases h with ⟨hL,hx,hz,hM,hQ,hg,haj⟩
  norm_num [DbaseA, Ecoeff, hL, hx, hz, hM, hQ, hg, haj]

theorem DbaseA_EX3 (h : O.EX3) : O.DbaseA=16 := by
  rcases h with ⟨hL,hx,hz,hM,hQ,hg,haj⟩
  norm_num [DbaseA, Ecoeff, hL, hx, hz, hM, hQ, hg, haj]

theorem Dbase_pos_exception (P : O.ParamData)
    (h : O.EX1 ∨ O.EX2 ∨ O.EX3) : 0<O.Dbase := by
  rcases h with h1 | h2 | h3
  · have hreg : E.Li≥O.x+1 ∧ E.Lj>O.z ∧ O.x≥1 ∧ O.z≥1 := by
      rcases h1 with ⟨hL,hx,hM,hQ,hg,haj,hz⟩
      omega
    have hA := O.DbaseA_EX1 h1
    apply O.Dbase_pos_of_a P hreg
    omega
  · have hreg : E.Li≥O.x+1 ∧ E.Lj>O.z ∧ O.x≥1 ∧ O.z≥1 := by
      rcases h2 with ⟨hL,hx,hz,hM,hQ,hg,haj⟩
      omega
    have hA := O.DbaseA_EX2 h2
    apply O.Dbase_pos_of_a P hreg
    omega
  · have hreg : E.Li≥O.x+1 ∧ E.Lj>O.z ∧ O.x≥1 ∧ O.z≥1 := by
      rcases h3 with ⟨hL,hx,hz,hM,hQ,hg,haj⟩
      omega
    have hA := O.DbaseA_EX3 h3
    apply O.Dbase_pos_of_a P hreg
    omega

end P21.Nonsymmetric.ChainCore.FirstFit.OneData
