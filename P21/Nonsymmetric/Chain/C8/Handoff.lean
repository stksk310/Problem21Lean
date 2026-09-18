import P21.Nonsymmetric.Chain.C8.UnitTransport

namespace P21.Nonsymmetric.ChainCore.FirstFit

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns}

namespace OneData

/-- The surviving level-one branch inside the packet window. -/
structure RegionU (O : A.OneData E) : Prop where
  unit : O.UnitParam
  firstPoint : O.UnitFirstPoint
  compact : K.Delta0=(O.z-1)*Q E+1 ∧ K.tau0=Q E
  Du_pos : 0<O.Du
  Q_gt_R : K.chain.R<Q E
  Uj_ge : (D.a 1 : ℤ)≤E.Uj
  EB_actual : K.chain.qB+g.n 0∈g.Gamma
  caps : K.Caps E

theorem regionU (O : A.OneData E) (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) (hstrict : K.chain.alpha<K.Croot)
    (hw : A.chi≤K.chain.T) : O.RegionU := by
  let U := O.unit_param hF hc hstrict hw
  let FP := O.unit_first_point U
  have hDu := O.unit_Du_pos U FP hF hc
  have hQR := O.unit_Q_gt_R U FP hDu
  have hUj := O.unit_Uj_ge_aj U hQR
  exact ⟨U,FP,O.unit_compact U,hDu,hQR,hUj,O.unit_EB_actual U hUj,K.caps E hF⟩

/-- Every actual missing-i return in the unit window has level one.  This is
not a uniqueness assumption: each chosen return of level at least two is
excluded independently by STRICT-WINDOW. -/
theorem every_EA_level_one (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) (hstrict : K.chain.alpha<K.Croot)
    (hw : A.chi≤K.chain.T) (E' : K.Returns) : E'.Li=1 := by
  have hpos := E'.levels_pos.1
  by_contra hne
  have hLi : 2≤E'.Li := by omega
  let O' := A.oneData E' hF hw
  exact O'.strict_window hF hc hstrict hw hLi

end OneData

/-- The source-shortage branch.  It retains the unconditional pure-H kernels,
rather than asserting their coefficients are one.  EA/Qj ONE, DET1 and PARAM
are packet-window conclusions and cannot be transported across `T < chi`.

The first fit, returns and CORE are preserved by the structure parameters;
the fields retain the actual packet and the C7 data needed downstream. -/
structure RegionD (A : K.FirstFit) (E : K.Returns)
    (hF : s.semigroup.IsFrobenius F) where
  strict : K.chain.alpha<K.Croot
  chi_gt : K.chain.T<A.chi
  chi_le : A.chi≤K.Croot-K.chain.alpha
  Xi_pos : 1≤A.Xi
  Xi_le : A.Xi≤K.Croot-(D.b 2 : ℤ)-2*K.chain.alpha
  C_deep : (D.b 2 : ℤ)+2*K.chain.alpha+1≤K.Croot
  packet : A.Packet hF
  ea_kernel : A.EAKernel E
  qj_kernel : A.QJKernel E
  caps : K.Caps E
  slopes : K.Slopes

noncomputable def regionD (A : K.FirstFit) (E : K.Returns)
    (hF : s.semigroup.IsFrobenius F) (hstrict : K.chain.alpha<K.Croot)
    (hgt : K.chain.T<A.chi) : A.RegionD E hF := by
  have hXi := A.Xi_pos hF
  have hchi : A.chi≤K.Croot-K.chain.alpha := by
    simp only [FirstFit.chi]
    omega
  have hT := K.chain.T_exact
  have hXiUpper : A.Xi≤K.Croot-(D.b 2 : ℤ)-2*K.chain.alpha := by
    simp only [FirstFit.chi] at hgt
    omega
  have hCdeep : (D.b 2 : ℤ)+2*K.chain.alpha+1≤K.Croot := by omega
  exact ⟨hstrict,hgt,hchi,hXi,hXiUpper,hCdeep,A.packet hF,A.eaKernel E,
    A.qjKernel E (K.caps E hF),K.caps E hF,K.slopes⟩

/-- Boundary elimination is used only after deriving its own window from
`Croot = alpha`; no strict theorem is imported into that boundary. -/
theorem Croot_gt_alpha (A : K.FirstFit) (E : K.Returns)
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m) :
    K.chain.alpha<K.Croot := by
  have hle := K.C_lower
  by_contra hn
  have hb : K.Croot=K.chain.alpha := by omega
  have hXi := A.Xi_pos hF
  have hT : 1≤K.chain.T := by
    rw [K.chain.T_exact]
    have hbk : (1:ℤ)≤D.b 2 := by exact_mod_cast D.b_pos 2
    have ha := K.chain.scalar_ranges.2.2.2
    omega
  have hw : A.chi≤K.chain.T := by
    simp only [FirstFit.chi]
    omega
  let O := A.oneData E hF hw
  exact O.boundary_ne hF hc hw hb

/-- Exact C8 handoff.  ONE/DET1/PARAM are constructed only in the U branch,
where WINDOW-WALL is available. -/
theorem c8_handoff (A : K.FirstFit) (E : K.Returns)
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m) :
    (∃ O : A.OneData E, O.RegionU) ∨ Nonempty (A.RegionD E hF) := by
  have hstrict := A.Croot_gt_alpha E hF hc
  by_cases hw : A.chi≤K.chain.T
  · left
    let O := A.oneData E hF hw
    exact ⟨O,O.regionU hF hc hstrict hw⟩
  · right
    exact ⟨A.regionD E hF hstrict (by omega)⟩

theorem handoff_disjoint (A : K.FirstFit) (E : K.Returns)
    (hF : s.semigroup.IsFrobenius F) :
    ¬ ((∃ O : A.OneData E, O.RegionU) ∧ Nonempty (A.RegionD E hF)) := by
  rintro ⟨⟨O,hU⟩,⟨hD⟩⟩
  exact (not_lt_of_ge hU.unit.window) hD.chi_gt

/-- Regression form of the four publication entries. -/
theorem branch_table (A : K.FirstFit) (E : K.Returns)
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m) :
    K.Croot≠K.chain.alpha ∧
    (K.chain.alpha<K.Croot → A.chi≤K.chain.T → 2≤E.Li → False) ∧
    ((A.chi≤K.chain.T → ∃ O : A.OneData E, O.RegionU) ∧
      (K.chain.T<A.chi → Nonempty (A.RegionD E hF))) := by
  have hstrict := A.Croot_gt_alpha E hF hc
  constructor
  · omega
  constructor
  · intro _ hw hLi
    let O := A.oneData E hF hw
    exact O.strict_window hF hc hstrict hw hLi
  constructor
  · intro hw
    let O := A.oneData E hF hw
    exact ⟨O,O.regionU hF hc hstrict hw⟩
  · intro hgt
    exact ⟨A.regionD E hF hstrict hgt⟩

end P21.Nonsymmetric.ChainCore.FirstFit
