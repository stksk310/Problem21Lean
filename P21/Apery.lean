import P21.PseudoFrobenius

namespace P21.NumericalSemigroup
variable (S : NumericalSemigroup)

theorem apery_le {F m w : ℤ} (hF : S.IsFrobenius F) (hw : w ∈ S.Apery m) :
    w ≤ F + m := by have := hF.2 hw.2; omega

theorem apery_finite {F m : ℤ} (hF : S.IsFrobenius F) : (S.Apery m).Finite := by
  exact (Set.finite_Icc 0 (F + m)).subset fun _ hw =>
    ⟨S.nonneg _ hw.1, S.apery_le hF hw⟩

theorem zero_mem_apery {m : ℤ} (hm : 0 < m) : 0 ∈ S.Apery m := by
  refine ⟨S.carrier.zero_mem, ?_⟩
  intro h
  have := S.nonneg _ h
  omega

theorem W_mem_apery {F m : ℤ} (hF : S.IsFrobenius F) (hm : 0 < m) :
    F + m ∈ S.Apery m := by
  exact ⟨S.mem_of_gt_frobenius hF (by omega), by simpa [Gap] using hF.1⟩

theorem pf_add_m_mem_apery {m q : ℤ} (hm : m ∈ S.carrier) (hm0 : m ≠ 0)
    (hq : q ∈ S.PF) : q + m ∈ S.Apery m :=
  ⟨hq.2 m hm hm0, by simpa using hq.1⟩

theorem apery_lower {m x y : ℤ} (hx : x ∈ S.carrier) (hy : y ∈ S.Apery m)
    (hxy : S.Le x y) : x ∈ S.Apery m := by
  refine ⟨hx, ?_⟩
  intro h
  apply hy.2
  convert S.carrier.add_mem h hxy using 1; unfold Le at hxy; ring

theorem pf_iff_maximal_apery {m q : ℤ} (hm : m ∈ S.carrier) (hm0 : m ≠ 0) :
    q ∈ S.PF ↔ S.Maximal (S.Apery m) (q + m) := by
  constructor
  · intro hq
    refine ⟨S.pf_add_m_mem_apery hm hm0 hq, ?_⟩
    intro y hy hle
    by_contra hn
    have hne : y - (q + m) ≠ 0 := by omega
    have h := hq.2 _ hle hne
    apply hy.2
    convert h using 1; ring
  · rintro ⟨ha, hmax⟩
    refine ⟨by simpa using ha.2, ?_⟩
    intro s hs hs0
    by_contra hgap
    have ha' : q + m + s ∈ S.Apery m :=
      ⟨S.carrier.add_mem ha.1 hs, by simpa [add_sub_right_comm] using hgap⟩
    have he := hmax _ ha' (by simpa [Le] using hs)
    omega

def A0 (F m : ℤ) : Set ℤ := {w | w ∈ S.Apery m ∧ F + m - w ∈ S.Apery m}
def A1 (F m : ℤ) : Set ℤ := S.Apery m \ S.A0 F m
def iota (_S : NumericalSemigroup) (F m w : ℤ) : ℤ := F + m + m - w

theorem complement_mem_apery {F m w : ℤ} (hF : S.IsFrobenius F)
    (hw : w ∈ S.Apery m) (hb : F + m - w ∈ S.carrier) :
    F + m - w ∈ S.Apery m := by
  refine ⟨hb, ?_⟩
  intro h
  apply hF.1
  convert S.carrier.add_mem hw.1 h using 1; ring

/-- C2.2: the two alternatives hold exclusively. -/
theorem exact_two_layers {F m w : ℤ} (hF : S.IsFrobenius F) (hm : 0 < m)
    (hmin : ∀ x ∈ S.carrier, x ≠ 0 → m ≤ x) (hc : S.Canonical F m)
    (hw : w ∈ S.Apery m) :
    (F + m - w ∈ S.Apery m ∧ S.iota F m w ∉ S.Apery m) ∨
    (F + m - w ∉ S.Apery m ∧ S.iota F m w ∈ S.Apery m) := by
  have hb : S.iota F m w ∈ S.carrier := by
    by_cases hz : w = 0
    · subst w
      apply S.mem_of_gt_frobenius hF
      dsimp [iota]; omega
    · have hx0 : 0 ≤ w - m := by have := hmin w hw.1 hz; omega
      convert S.canonical_all_nonnegative_gaps hF hc hx0 hw.2 using 1; dsimp [iota]; ring
  have he : S.iota F m w - m = F + m - w := by dsimp [iota]; ring
  by_cases h : F + m - w ∈ S.carrier
  · refine Or.inl ⟨S.complement_mem_apery hF hw h, ?_⟩
    intro hi
    apply hi.2
    rwa [he]
  · refine Or.inr ⟨fun h' => h h'.1, hb, ?_⟩
    rwa [he]

theorem a0_lower {F m x y : ℤ} (hF : S.IsFrobenius F) (hx : x ∈ S.Apery m)
    (hy : y ∈ S.A0 F m) (hxy : S.Le x y) : x ∈ S.A0 F m := by
  refine ⟨hx, S.complement_mem_apery hF hx ?_⟩
  convert S.carrier.add_mem hy.2.1 hxy using 1; ring

theorem a1_upper {F m x y : ℤ} (hF : S.IsFrobenius F) (hx : x ∈ S.A1 F m)
    (hy : y ∈ S.Apery m) (hxy : S.Le x y) : y ∈ S.A1 F m :=
  ⟨hy, fun h => hx.2 (S.a0_lower hF hx.1 h hxy)⟩

theorem iota_involutive (F m w : ℤ) : S.iota F m (S.iota F m w) = w := by
  dsimp [iota]; ring

theorem iota_order_reverse (F m x y : ℤ) :
    S.Le (S.iota F m y) (S.iota F m x) ↔ S.Le x y := by
  unfold Le iota
  have he : (F + m + m - x) - (F + m + m - y) = y - x := by ring
  rw [he]

theorem iota_mem_a1 {F m w : ℤ} (hF : S.IsFrobenius F) (hm : 0 < m)
    (hmin : ∀ x ∈ S.carrier, x ≠ 0 → m ≤ x) (hc : S.Canonical F m)
    (hw : w ∈ S.A1 F m) : S.iota F m w ∈ S.A1 F m := by
  obtain h | h := S.exact_two_layers hF hm hmin hc hw.1
  · exact False.elim (hw.2 ⟨hw.1, h.1⟩)
  · refine ⟨h.2, ?_⟩
    intro h0
    apply hw.1.2
    convert h0.2.1 using 1; dsimp [iota]; ring

theorem pf_add_m_mem_a1 {F m q : ℤ} (hF : S.IsFrobenius F)
    (hm : m ∈ S.carrier) (hm0 : m ≠ 0) (hq : q ∈ S.Q F) : q + m ∈ S.A1 F m := by
  refine ⟨S.pf_add_m_mem_apery hm hm0 hq.1, ?_⟩
  intro h0
  have ht := S.q_lt_frobenius hF hq
  have hd : F - q ∈ S.carrier := by convert h0.2.1 using 1; ring
  have hf := hq.1.2 (F - q) hd (by omega)
  apply hF.1
  convert hf using 1; ring

theorem complement_of_q_mem_apery {F m q : ℤ} (hF : S.IsFrobenius F)
    (hc : S.Canonical F m) (hq : q ∈ S.Q F) : F + m - q ∈ S.Apery m := by
  refine ⟨hc q hq.1, ?_⟩
  intro h
  have ht := S.q_lt_frobenius hF hq
  have hd : F - q ∈ S.carrier := by convert h using 1; ring
  have hf := hq.1.2 (F - q) hd (by omega)
  apply hF.1
  convert hf using 1; ring

theorem maximal_a1_iff {F m w : ℤ} (hF : S.IsFrobenius F)
    (hm : m ∈ S.carrier) (hmpos : 0 < m) :
    S.Maximal (S.A1 F m) w ↔ w - m ∈ S.Q F := by
  have hm0 : m ≠ 0 := by omega
  constructor
  · rintro ⟨hw, hmax⟩
    have ha : S.Maximal (S.Apery m) w := ⟨hw.1, fun y hy hle =>
      hmax y (S.a1_upper hF hw hy hle) hle⟩
    have hp : w - m ∈ S.PF := (S.pf_iff_maximal_apery hm hm0).mpr (by simpa using ha)
    refine ⟨hp, ?_⟩
    intro he
    have he' : w - m = F := he
    apply hw.2
    refine ⟨hw.1, ?_⟩
    have hz : F + m - w = 0 := by omega
    rw [hz]
    exact S.zero_mem_apery hmpos
  · intro hq
    have hw := S.pf_add_m_mem_a1 hF hm hm0 hq
    have hmax := (S.pf_iff_maximal_apery hm hm0).mp hq.1
    refine ⟨by simpa using hw, ?_⟩
    intro y hy hle
    have := hmax.2 y hy.1 (by simpa using hle)
    simpa using this

theorem minimal_iff_iota_maximal {F m w : ℤ} (hF : S.IsFrobenius F) (hm : 0 < m)
    (hmin : ∀ x ∈ S.carrier, x ≠ 0 → m ≤ x) (hc : S.Canonical F m) :
    S.Minimal (S.A1 F m) w ↔ S.Maximal (S.A1 F m) (S.iota F m w) := by
  constructor
  · rintro ⟨hw, hlow⟩
    refine ⟨S.iota_mem_a1 hF hm hmin hc hw, ?_⟩
    intro y hy hle
    have hy' := S.iota_mem_a1 hF hm hmin hc hy
    have hord : S.Le (S.iota F m y) w := by
      simpa [S.iota_involutive] using
        (S.iota_order_reverse F m (S.iota F m w) y).mpr hle
    have he := hlow (S.iota F m y) hy' hord
    have := congrArg (S.iota F m) he
    simpa [S.iota_involutive] using this
  · rintro ⟨hw, hhigh⟩
    have hw' := S.iota_mem_a1 hF hm hmin hc hw
    refine ⟨by simpa [S.iota_involutive] using hw', ?_⟩
    intro y hy hle
    have hy' := S.iota_mem_a1 hF hm hmin hc hy
    have hord := (S.iota_order_reverse F m y w).mpr hle
    have he := hhigh (S.iota F m y) hy' hord
    have := congrArg (S.iota F m) he
    simpa [S.iota_involutive] using this

theorem minimal_a1_iff {F m w : ℤ} (hF : S.IsFrobenius F)
    (hm : m ∈ S.carrier) (hmpos : 0 < m)
    (hmin : ∀ x ∈ S.carrier, x ≠ 0 → m ≤ x) (hc : S.Canonical F m) :
    S.Minimal (S.A1 F m) w ↔ F + m - w ∈ S.Q F := by
  rw [S.minimal_iff_iota_maximal hF hmpos hmin hc, S.maximal_a1_iff hF hm hmpos]
  have he : S.iota F m w - m = F + m - w := by dsimp [iota]; ring
  rw [he]

theorem maximal_a1_set {F m : ℤ} (hF : S.IsFrobenius F)
    (hm : m ∈ S.carrier) (hmpos : 0 < m) :
    {w | S.Maximal (S.A1 F m) w} = (fun q => q + m) '' S.Q F := by
  ext w
  rw [Set.mem_ofPred_eq, S.maximal_a1_iff hF hm hmpos]
  constructor
  · intro h; exact ⟨w - m, h, by ring⟩
  · rintro ⟨q, hq, rfl⟩; simpa using hq

theorem minimal_a1_set {F m : ℤ} (hF : S.IsFrobenius F)
    (hm : m ∈ S.carrier) (hmpos : 0 < m)
    (hmin : ∀ x ∈ S.carrier, x ≠ 0 → m ≤ x) (hc : S.Canonical F m) :
    {w | S.Minimal (S.A1 F m) w} = (fun q => F + m - q) '' S.Q F := by
  ext w
  rw [Set.mem_ofPred_eq, S.minimal_a1_iff hF hm hmpos hmin hc]
  constructor
  · intro h; exact ⟨F + m - w, h, by ring⟩
  · rintro ⟨q, hq, rfl⟩; convert hq using 1; ring

theorem minimal_a1_card {F m : ℤ} (hF : S.IsFrobenius F)
    (hm : m ∈ S.carrier) (hmpos : 0 < m)
    (hmin : ∀ x ∈ S.carrier, x ≠ 0 → m ≤ x) (hc : S.Canonical F m) :
    {w | S.Minimal (S.A1 F m) w}.ncard = (S.Q F).ncard ∧
    (S.Q F).ncard + 1 = S.type := by
  constructor
  · rw [S.minimal_a1_set hF hm hmpos hmin hc]
    exact Set.ncard_image_of_injective _ (by intro a b h; dsimp at h; omega)
  · exact (S.type_eq_q_card_add_one hF hm (by omega)).symm

end P21.NumericalSemigroup
