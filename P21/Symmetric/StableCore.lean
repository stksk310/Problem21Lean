import P21

/-! Publication §3.2: symmetry on integers, the stable core, and its gap duality. -/
namespace P21.Symmetric

/-- Integer Frobenius symmetry, including negative integers. -/
def SymmetricAt (H : AddSubmonoid ℤ) (f : ℤ) : Prop :=
  ∀ t : ℤ, t ∉ H ↔ f - t ∈ H

/-- All nonnegative translates are required, including the zeroth translate. -/
def stableCore (g : Generators) : Set ℤ :=
  {a | ∀ n : ℕ, a + (n : ℤ) * g.m ∈ g.H}

/-- Translation `J = K - r`, expressed without choosing witnesses. -/
def shiftedCore (g : Generators) (r : ℤ) : Set ℤ :=
  {c | c + r ∈ stableCore g}

/-- A minimal ideal generator with respect to the semigroup order. -/
def idealMin (S : AddSubmonoid ℤ) (I : Set ℤ) (a : ℤ) : Prop :=
  a ∈ I ∧ ∀ b ∈ I, a - b ∈ S → b = a

variable {g : Generators}

/-- The decomposition is extracted from natural coefficients of an actual factorization. -/
theorem mem_gamma_iff_tail_add (t : ℤ) :
    t ∈ g.Gamma ↔ ∃ a ∈ g.H, ∃ n : ℕ, t = a + (n : ℤ) * g.m := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨value g.n (fun i => c i.succ), ⟨_, rfl⟩, c 0, ?_⟩
    have he : value g.all c = (c 0 : ℤ) * g.m + value g.n (fun i => c i.succ) := by
      simp [value, Generators.all, Fin.sum_univ_succ]
    rw [← hc, he]
    ring
  · rintro ⟨a, ⟨c, hc⟩, n, rfl⟩
    exact ⟨Fin.cons n c, by rw [g.value_cons, hc]; ring⟩

theorem stableCore_subset_tail : stableCore g ⊆ g.H := by
  intro a ha
  simpa using ha 0

/-- GAP-K, with exactly the publication's universal stable quantifier. -/
theorem gap_iff_stableCore {f t : ℤ} (hsym : SymmetricAt g.H f) :
    t ∉ g.Gamma ↔ f - t ∈ stableCore g := by
  constructor
  · intro ht n
    have hn : t - (n : ℤ) * g.m ∉ g.H := by
      intro h
      apply ht
      exact (mem_gamma_iff_tail_add t).2 ⟨_, h, n, by ring⟩
    convert (hsym _).1 hn using 1; ring
  · intro ht hg
    obtain ⟨a, ha, n, he⟩ := (mem_gamma_iff_tail_add t).1 hg
    have hb : f - a ∈ g.H := by
      convert ht n using 1; rw [he]; ring
    exact ((hsym a).2 hb) ha

/-- Closure by every element of Gamma, rather than just the displayed generators. -/
theorem stableCore_add_gamma {a b : ℤ} (ha : a ∈ stableCore g) (hb : b ∈ g.Gamma) :
    a + b ∈ stableCore g := by
  obtain ⟨c, hc, k, rfl⟩ := (mem_gamma_iff_tail_add b).1 hb
  intro n
  convert g.H.add_mem (ha (k + n)) hc using 1; push_cast; ring

theorem stableCore_isLeast (s : g.Setting) {F f : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hsym : SymmetricAt g.H f) :
    IsLeast (stableCore g) (f - F) := by
  refine ⟨(gap_iff_stableCore hsym).1 hF.1, ?_⟩
  intro a ha
  have hgap : f - a ∉ g.Gamma := (gap_iff_stableCore hsym).2 (by
    convert ha using 1; ring)
  have := hF.2 hgap
  omega

theorem m_not_mem_tail (s : g.Setting) : g.m ∉ g.H := by
  rintro ⟨a, ha⟩
  exact s.minimal 0 (Fin.cons 0 a) (by simp) (by
    change value g.all (Fin.cons 0 a) = g.m
    simpa [g.value_cons] using ha)

theorem stableCore_zero_not_mem (s : g.Setting) : 0 ∉ stableCore g := by
  intro h
  exact m_not_mem_tail s (by simpa using h 1)

theorem stableCore_mem_gt_m (s : g.Setting) {a : ℤ} (ha : a ∈ stableCore g) :
    g.m < a := by
  have ht := stableCore_subset_tail ha
  have ha0 : 0 ≤ a := s.semigroup.nonneg a (g.h_subset_gamma ht)
  have hne : a ≠ 0 := by intro he; subst a; exact stableCore_zero_not_mem s ha
  obtain ⟨i, hi⟩ := Generators.Setting.support_nonempty ht (by omega)
  have hp := s.semigroup.nonneg _ (g.h_subset_gamma hi)
  have := s.n_gt i
  omega

theorem stableCore_min_gt_m (s : g.Setting) {F f : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hsym : SymmetricAt g.H f) :
    g.m < f - F := stableCore_mem_gt_m s (stableCore_isLeast s hF hsym).1

theorem stable_shift_pos (s : g.Setting) {F f : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hsym : SymmetricAt g.H f) :
    0 < f - F - g.m := by
  have := stableCore_min_gt_m s hF hsym
  omega

/-- FS: every positive-index point of the one fixed stable walk belongs to H. -/
theorem stable_walk (s : g.Setting) {F f : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hsym : SymmetricAt g.H f)
    (n : ℕ) (hn : 1 ≤ n) :
    f - F - g.m + (n : ℤ) * g.m ∈ g.H := by
  have h := (stableCore_isLeast s hF hsym).1 (n - 1)
  have he : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  convert h using 1; rw [he]; ring

/-- The gap complement gives precisely the minimal K-generators. -/
theorem pf_iff_min_stableCore (s : g.Setting) {f q : ℤ}
    (hsym : SymmetricAt g.H f) :
    q ∈ s.semigroup.PF ↔ idealMin g.Gamma (stableCore g) (f - q) := by
  classical
  constructor
  · intro hq
    refine ⟨(gap_iff_stableCore hsym).1 hq.1, ?_⟩
    intro b hb hd
    by_contra hne
    have hd0 : f - q - b ≠ 0 := by omega
    have hm := hq.2 (f - q - b) hd hd0
    have hgap : f - b ∉ g.Gamma := (gap_iff_stableCore hsym).2 (by
      convert hb using 1; ring)
    apply hgap
    change q + (f - q - b) ∈ g.Gamma at hm
    convert hm using 1; ring
  · rintro ⟨hk, hmin⟩
    refine ⟨(gap_iff_stableCore hsym).2 hk, ?_⟩
    intro a ha ha0
    change a ∈ g.Gamma at ha
    by_contra hgap
    change q + a ∉ g.Gamma at hgap
    have hb := (gap_iff_stableCore hsym).1 hgap
    have he := hmin (f - (q + a)) hb (by convert ha using 1; ring)
    apply ha0
    omega

/-- CAN extends from minimal generators to all of J via M1's gap-to-PF theorem. -/
theorem shiftedCore_subset_gamma (s : g.Setting) {F f : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hcan : s.semigroup.Canonical F g.m)
    (hsym : SymmetricAt g.H f) :
    shiftedCore g (f - F - g.m) ⊆ g.Gamma := by
  intro c hc
  change c + (f - F - g.m) ∈ stableCore g at hc
  change c ∈ g.Gamma
  have hgap : f - (c + (f - F - g.m)) ∉ g.Gamma :=
    (gap_iff_stableCore hsym).2 (by convert hc using 1; ring)
  obtain ⟨q, hq, hd⟩ := s.semigroup.gap_below_pf hF hgap
  have hm := g.Gamma.add_mem (hcan q hq) hd
  convert hm using 1; ring

theorem shiftedCore_isLeast (s : g.Setting) {F f : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hsym : SymmetricAt g.H f) :
    IsLeast (shiftedCore g (f - F - g.m)) g.m := by
  have hh := stableCore_isLeast s hF hsym
  refine ⟨?_, ?_⟩
  · change g.m + (f - F - g.m) ∈ stableCore g
    convert hh.1 using 1; ring
  · intro c hc
    have := hh.2 hc
    change f - F ≤ c + (f - F - g.m) at this
    omega

/-- Identifying an independently named least stable element recovers `F = f - h`. -/
theorem frobenius_eq_sub_core_min (s : g.Setting) {F f h : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hsym : SymmetricAt g.H f)
    (hh : IsLeast (stableCore g) h) : F = f - h := by
  have hc := stableCore_isLeast s hF hsym
  have h₁ := hh.2 hc.1
  have h₂ := hc.2 hh.1
  omega

/-- Symmetry's center is a genuine gap of the tail. -/
theorem symmetricAt_f_not_mem {f : ℤ} (hsym : SymmetricAt g.H f) : f ∉ g.H := by
  exact (hsym f).2 (by simp)

/-- With the publication's nonnegative generators, every tail gap is at most f. -/
theorem symmetricAt_gap_le (s : g.Setting) {f t : ℤ}
    (hsym : SymmetricAt g.H f) (ht : t ∉ g.H) : t ≤ f := by
  have hn := s.semigroup.nonneg _ (g.h_subset_gamma ((hsym t).1 ht))
  omega

end P21.Symmetric



