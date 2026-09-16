import P21.Symmetric.StableCore

namespace P21.Symmetric

def tailIntersection (g : Generators) (r : ℤ) : Set ℤ :=
  {c | c ∈ g.H ∧ c + r ∈ g.H}

/-- The bridge is a disjoint insertion: the distinguished point is not Apéry. -/
theorem minimal_bridge {g : Generators} (s : g.Setting) (J I : Set ℤ)
    (hsub : J ⊆ g.Gamma) (hmin : IsLeast J g.m)
    (hIH : ∀ c, c ∈ I ↔ c ∈ J ∧ c ∈ g.H) :
    {c | idealMin g.Gamma J c} =
      insert g.m {c | idealMin g.H I c ∧ c ∈ s.semigroup.Apery g.m} := by
  ext c
  constructor
  · rintro ⟨hc, hlow⟩
    by_cases he : c = g.m
    · exact Or.inl he
    · apply Or.inr
      have hAp : c ∈ s.semigroup.Apery g.m := by
        refine ⟨hsub hc, ?_⟩
        intro h
        exact he (hlow g.m hmin.1 h).symm
      have hcH := s.apery_in_tail hAp
      refine ⟨⟨(hIH c).mpr ⟨hc, hcH⟩, ?_⟩, hAp⟩
      intro b hb hcb
      exact hlow b ((hIH b).mp hb).1 (g.h_subset_gamma hcb)
  · rintro (rfl | ⟨⟨hcI, hlow⟩, hAp⟩)
    · refine ⟨hmin.1, ?_⟩
      intro b hb hmb
      have h1 := hmin.2 hb
      have h2 := s.semigroup.nonneg _ hmb
      omega
    · refine ⟨((hIH c).mp hcI).1, ?_⟩
      intro b hb hcb
      have hbG := hsub hb
      have hbAp : b ∈ s.semigroup.Apery g.m :=
        s.semigroup.apery_lower hbG hAp hcb
      have hdAp : c - b ∈ s.semigroup.Apery g.m :=
        s.semigroup.apery_lower hcb hAp (by
          change c - (c - b) ∈ g.Gamma
          simpa using hbG)
      exact hlow b ((hIH b).mpr ⟨hb, s.apery_in_tail hbAp⟩)
        (s.apery_in_tail hdAp)

theorem distinguished_not_raw_apery {g : Generators} (s : g.Setting) (I : Set ℤ) :
    g.m ∉ {c | idealMin g.H I c ∧ c ∈ s.semigroup.Apery g.m} := by
  intro h
  exact h.2.2 (by simp)

theorem idealMin_shift {g : Generators} {r c : ℤ} :
    idealMin g.Gamma (shiftedCore g r) c ↔
      idealMin g.Gamma (stableCore g) (c + r) := by
  constructor
  · rintro ⟨hc, hlow⟩
    refine ⟨hc, ?_⟩
    intro b hb hd
    have hbJ : b - r ∈ shiftedCore g r := by
      change b - r + r ∈ stableCore g
      simpa using hb
    have he := hlow (b - r) hbJ (by convert hd using 1; ring)
    omega
  · rintro ⟨hc, hlow⟩
    refine ⟨hc, ?_⟩
    intro b hb hd
    have he := hlow (b + r) hb (by convert hd using 1; ring)
    omega

theorem min_shiftedCore_iff_pf {g : Generators} (s : g.Setting) {F f c : ℤ}
    (hsym : SymmetricAt g.H f) :
    idealMin g.Gamma (shiftedCore g (f - F - g.m)) c ↔
      F + g.m - c ∈ s.semigroup.PF := by
  rw [idealMin_shift, pf_iff_min_stableCore s hsym]
  have he : c + (f - F - g.m) = f - (F + g.m - c) := by ring
  rw [he]

theorem tailIntersection_iff_shiftedCore {g : Generators} (s : g.Setting) {F f c : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hsym : SymmetricAt g.H f) :
    c ∈ tailIntersection g (f - F - g.m) ↔
      c ∈ shiftedCore g (f - F - g.m) ∧ c ∈ g.H := by
  constructor
  · rintro ⟨hcH, hcr⟩
    refine ⟨?_, hcH⟩
    intro n
    cases n with
    | zero => simpa using hcr
    | succ n =>
      have hn := stable_walk s hF hsym (n + 1) (by omega)
      convert g.H.add_mem hcH hn using 1; ring
  · rintro ⟨hcJ, hcH⟩
    exact ⟨hcH, stableCore_subset_tail hcJ⟩

theorem exact_bridge {g : Generators} (s : g.Setting) {F f : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hcan : s.semigroup.Canonical F g.m)
    (hsym : SymmetricAt g.H f) :
    {c | idealMin g.Gamma (shiftedCore g (f - F - g.m)) c} =
      insert g.m {c | idealMin g.H (tailIntersection g (f - F - g.m)) c ∧
        c ∈ s.semigroup.Apery g.m} :=
  minimal_bridge s _ _ (shiftedCore_subset_gamma s hF hcan hsym)
    (shiftedCore_isLeast s hF hsym) (fun _ => tailIntersection_iff_shiftedCore s hF hsym)

theorem min_shiftedCore_set {g : Generators} (s : g.Setting) {F f : ℤ}
    (hsym : SymmetricAt g.H f) :
    {c | idealMin g.Gamma (shiftedCore g (f - F - g.m)) c} =
      (fun q => F + g.m - q) '' s.semigroup.PF := by
  ext c
  rw [Set.mem_ofPred_eq, min_shiftedCore_iff_pf s hsym]
  constructor
  · intro hc
    exact ⟨F + g.m - c, hc, by ring⟩
  · rintro ⟨q, hq, rfl⟩
    simpa using hq

theorem type_bridge {g : Generators} (s : g.Setting) {F f : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hcan : s.semigroup.Canonical F g.m)
    (hsym : SymmetricAt g.H f) :
    s.semigroup.type = 1 +
      {c | idealMin g.H (tailIntersection g (f - F - g.m)) c ∧
        c ∈ s.semigroup.Apery g.m}.ncard := by
  have hcard : {c | idealMin g.Gamma (shiftedCore g (f - F - g.m)) c}.ncard =
      s.semigroup.type := by
    rw [min_shiftedCore_set s hsym]
    exact Set.ncard_image_of_injective _ (by intro a b h; dsimp at h; omega)
  have hfinite : {c | idealMin g.Gamma (shiftedCore g (f - F - g.m)) c}.Finite := by
    rw [min_shiftedCore_set s hsym]
    exact s.semigroup.all_pf_finite.image _
  rw [exact_bridge s hF hcan hsym] at hcard hfinite
  rw [Set.ncard_insert_of_notMem (distinguished_not_raw_apery s _)
    (hfinite.subset (Set.subset_insert _ _))] at hcard
  omega

end P21.Symmetric
