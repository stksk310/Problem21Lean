import P21.Nonsymmetric.Chain.C8.StrictDbase

set_option maxHeartbeats 1200000

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} (O : A.OneData E)

/-- C8.9 STRICT-WINDOW: no strict-root survivor can have `Li ≥ 2` while
the first-fit packet remains inside the window. -/
theorem strict_window (O : A.OneData E) (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) (hstrict : K.chain.alpha<K.Croot)
    (hw : A.chi≤K.chain.T) (hLi : 2≤E.Li) : False := by
  have hempty := O.empty_triangle hF hw
  have hdet : O.DetOneStatement := O.det_one hempty
  have P : O.ParamData := O.param_data hdet
  have C : O.CeilingData := O.ceiling_data hF
  have hreg := O.strict_regular hdet P hLi
  have hQ1 : 1≤Q E := Q_pos (K:=K) (E:=E)
  have hgamma : 1≤O.gamma := by simp [gamma]; omega
  have halpha : 1≤K.chain.alpha := K.chain.scalar_ranges.2.2.2
  have hbk : (1:ℤ)≤D.b 2 := by exact_mod_cast D.b_pos 2
  have hH := C.H0_nonneg
  have hP0 := O.P0_pos P
  have hV := P.V_pos
  have hAB := O.Aprime_Bprime_pos P hreg hQ1
  obtain ⟨sigma,hsigma,hni,hnj,hnk,hm⟩ := O.cross_product_scale hF hc
  have contradict_k (hDb : 0<O.Dbase) : False := by
    have hid := O.strict_k hdet C P
    have h0 : 0≤O.H0*O.V := mul_nonneg hH (le_of_lt hV)
    have h1 : 0≤(K.chain.alpha-1)*(O.V+O.Aprime) :=
      mul_nonneg (by omega) (by nlinarith [hAB.1])
    have h2 : 0≤(O.gamma-1)*O.Aprime := mul_nonneg (by omega) (le_of_lt hAB.1)
    have h3 : 0≤((D.b 2 : ℤ)-1)*O.Bprime := mul_nonneg (by omega) (le_of_lt hAB.2)
    have hmk : O.Kcal<O.mhat := by nlinarith
    have hs := mul_lt_mul_of_pos_left hmk hsigma
    have hmgt : g.n 2<g.m := by rw [hnk, hm]; exact hs
    exact (not_lt_of_ge (s.n_gt 2).le) hmgt
  by_cases hQ : Q E=1
  · exact contradict_k (O.Dbase_pos_q_one P hreg hQ)
  · have hQ2 : 2≤Q E := by omega
    by_cases hex : O.EX1 ∨ O.EX2 ∨ O.EX3
    · exact contradict_k (O.Dbase_pos_exception P hex)
    · have hnot : ¬O.EX1 ∧ ¬O.EX2 ∧ ¬O.EX3 := by tauto
      have hsub := O.CA_sub_P0_pos_regular hdet P hreg hQ2 hnot
      have hreg' : E.Li≥O.x+1 ∧ O.x+1≥2 ∧ E.Lj>O.z ∧ O.z≥1 := by omega
      have hcoeff := O.CA_CB_pos P hreg' hQ2
      have hid := O.strict_j hdet C P
      have h0 : 0≤O.H0*O.P0 := mul_nonneg hH (le_of_lt hP0)
      have h1 : 0<K.chain.alpha*O.CA := mul_pos (by omega) hcoeff.1
      have h2 : 0<O.gamma*(O.CA-O.P0) := mul_pos (by omega) hsub
      have h3 : 0<(D.b 2 : ℤ)*O.CB := mul_pos (by omega) hcoeff.2
      have hmj : O.Jcal<O.mhat := by nlinarith
      have hs := mul_lt_mul_of_pos_left hmj hsigma
      have hmgt : g.n 1<g.m := by rw [hnj, hm]; exact hs
      exact (not_lt_of_ge (s.n_gt 1).le) hmgt

end P21.Nonsymmetric.ChainCore.FirstFit.OneData
