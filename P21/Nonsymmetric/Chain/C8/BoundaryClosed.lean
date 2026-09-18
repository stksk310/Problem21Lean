import P21.Nonsymmetric.Chain.C8.PositiveCoefficients

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} (O : A.OneData E)

/-- Appendix §8.8: the boundary `Croot = alpha` contradicts multiplicity. -/
theorem boundary_ne (O : A.OneData E) (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) (hw : A.chi≤K.chain.T) :
    K.Croot≠K.chain.alpha := by
  intro hb
  have hempty := O.empty_triangle hF hw
  have hdet : O.DetOneStatement := O.det_one hempty
  have P : O.ParamData := O.param_data hdet
  have C : O.CeilingData := O.ceiling_data hF
  have hsplit : O.LevelSplit := O.level_split hdet P
  have hreg := O.boundary_regular hb C hsplit
  obtain ⟨B,hSync⟩ := O.boundary_sync hF hb hdet P
  have hcoeff := O.CA_CB_pos P hreg hSync.Q_ge_two
  have hP0 := O.P0_pos P
  have hbound := O.bound_mult hb hdet C P
  have hH := C.H0_nonneg
  have halpha : 0<K.chain.alpha := by
    have := K.chain.scalar_ranges.2.2.2
    omega
  have hbk : (0:ℤ)<D.b 2 := by exact_mod_cast D.b_pos 2
  have hterm0 : 0≤O.H0*O.P0 := mul_nonneg hH (le_of_lt hP0)
  have htermA : 0<K.chain.alpha*O.CA := mul_pos halpha hcoeff.1
  have htermB : 0<(D.b 2 : ℤ)*O.CB := mul_pos hbk hcoeff.2
  have hmhat : O.Jcal<O.mhat := by nlinarith
  obtain ⟨sigma,hsigma,hni,hnj,hnk,hm⟩ := O.cross_product_scale hF hc
  have hscaled : sigma*O.Jcal<sigma*O.mhat := mul_lt_mul_of_pos_left hmhat hsigma
  have hmgt : g.n 1<g.m := by rw [hnj, hm]; exact hscaled
  exact (not_lt_of_ge (s.n_gt 1).le) hmgt

/-- The surviving boundary coordinate is strictly above `alpha`. -/
theorem Croot_gt_alpha (O : A.OneData E) (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) (hw : A.chi≤K.chain.T) :
    K.chain.alpha<K.Croot := by
  have hne := O.boundary_ne hF hc hw
  have hlow := K.C_lower
  omega

end P21.Nonsymmetric.ChainCore.FirstFit.OneData
