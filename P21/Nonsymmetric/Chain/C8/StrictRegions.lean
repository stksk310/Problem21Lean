import P21.Nonsymmetric.Chain.C8.StrictWindow

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} (O : A.OneData E)

/-- The strict finite band is empty. -/
theorem strict_closed_band (O : A.OneData E) (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) (hlambda : K.d<K.chain.lambda)
    (hstrict : K.chain.alpha<K.Croot)
    (hupper : K.Croot≤(D.b 2 : ℤ)+2*K.chain.alpha) : False := by
  have hXi := A.Xi_pos hF
  have hw : A.chi≤K.chain.T := by
    rw [K.chain.T_exact]
    simp only [FirstFit.chi]
    omega
  have hlevel := K.Li_level E
  have hLi : 2≤E.Li := by
    have hd := K.d_range.1
    have hLp := E.levels_pos.1
    by_contra hn
    have hL1 : E.Li=1 := by omega
    rw [hL1, one_mul] at hlevel
    omega
  exact O.strict_window hF hc hstrict hw hLi

/-- Exact source-shortage inequalities passed to Section 9. -/
structure DeepBounds (O : A.OneData E) : Prop where
  chi_gt : K.chain.T<A.chi
  chi_le : A.chi≤K.Croot-K.chain.alpha
  Xi_pos : 1≤A.Xi
  Xi_le : A.Xi≤K.Croot-(D.b 2 : ℤ)-2*K.chain.alpha
  C_deep : (D.b 2 : ℤ)+2*K.chain.alpha+1≤K.Croot

theorem deep_bounds (O : A.OneData E) (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) (hstrict : K.chain.alpha<K.Croot)
    (hLi : 2≤E.Li) : O.DeepBounds := by
  have hXi := A.Xi_pos hF
  have hchi : A.chi≤K.Croot-K.chain.alpha := by
    simp only [FirstFit.chi]
    omega
  have hgt : K.chain.T<A.chi := by
    by_contra hn
    exact O.strict_window hF hc hstrict (by omega) hLi
  have hT := K.chain.T_exact
  have hXiUpper : A.Xi≤K.Croot-(D.b 2 : ℤ)-2*K.chain.alpha := by
    simp only [FirstFit.chi] at hgt
    omega
  have hCdeep : (D.b 2 : ℤ)+2*K.chain.alpha+1≤K.Croot := by omega
  exact ⟨hgt,hchi,hXi,hXiUpper,hCdeep⟩

end P21.Nonsymmetric.ChainCore.FirstFit.OneData
