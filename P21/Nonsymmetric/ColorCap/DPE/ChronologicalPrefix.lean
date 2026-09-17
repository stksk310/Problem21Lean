import P21.Nonsymmetric.ColorCap.DPE.SuccessfulPrefix

namespace P21.Nonsymmetric.ColorCap

/-- Every non-first-color occurrence has a genuine immediately preceding row-zero firing. -/
def ProperNonzeroPredecessors (l : List (Fin 3)) : Prop :=
  ∀ a i b, l = a ++ i :: b → i ≠ 0 → ∃ p, a = p ++ [0]

theorem ProperNonzeroPredecessors.prefix {l p : List (Fin 3)}
    (hp : ProperNonzeroPredecessors l) (hpl : p <+: l) :
    ProperNonzeroPredecessors p := by
  intro a i b hs hi
  obtain ⟨tail, ht⟩ := hpl
  apply hp a i (b ++ tail) _ hi
  rw [← ht, hs]
  simp [List.append_assoc]

theorem ProperNonzeroPredecessors.count_le_zero {l : List (Fin 3)}
    (hp : ProperNonzeroPredecessors l) (r : Fin 3) (hr : r ≠ 0) :
    l.count r ≤ l.count 0 := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | h n ih =>
    cases l using List.reverseRecOn with
    | nil => simp
    | append_singleton a i =>
      have hpa : ProperNonzeroPredecessors a := hp.prefix (by simp)
      have halen : a.length < n := by simp at hn; omega
      by_cases hi : i = 0
      · subst i
        have hle := ih a.length halen hpa rfl
        simp [List.count_append, Ne.symm hr]
        omega
      · by_cases hir : i = r
        · subst i
          obtain ⟨p, ha⟩ := hp a r [] (by simp) hr
          have hpp : ProperNonzeroPredecessors p := hpa.prefix (by rw [ha]; simp)
          have hplen : p.length < n := by simp [ha] at hn; omega
          have hle := ih p.length hplen hpp rfl
          rw [ha]
          simp [List.count_append, Ne.symm hr]
          omega
        · have hle := ih a.length halen hpa rfl
          simp [List.count_append, hi, hir]
          exact hle

theorem ProperNonzeroPredecessors.count_lt_zero_of_last_zero
    {l a : List (Fin 3)} (hp : ProperNonzeroPredecessors l)
    (hlast : l = a ++ [0]) (r : Fin 3) (hr : r ≠ 0) :
    l.count r < l.count 0 := by
  have hpa : ProperNonzeroPredecessors a := hp.prefix ⟨[0], hlast.symm⟩
  have hle := hpa.count_le_zero r hr
  rw [hlast]
  simp [List.count_append, Ne.symm hr]
  omega

/-- Provenance for the arithmetic count attached to the `h`-th actual
nonzero firing.  `source` is the genuine chronological state immediately
before that firing; `N` is its row-zero count plus one. -/
def CrossingWitness (l : List (Fin 3)) (r : Fin 3) (h : ℕ) (N : ℤ) : Prop :=
  ∃ source tail : List (Fin 3),
    l = source ++ r :: tail ∧
    source.count r = h - 1 ∧
    N = (source.count 0 : ℤ) + 1

theorem CrossingWitness.at_last {l : List (Fin 3)} {r : Fin 3} {N : ℤ}
    (hw : CrossingWitness l r (l.count r) N) (hr : r ≠ 0)
    {a : List (Fin 3)} (hlast : l = a ++ [r]) :
    N = (l.count 0 : ℤ) + 1 := by
  obtain ⟨source, tail, hsplit, hcount, hN⟩ := hw
  have htailCount : tail.count r = 0 := by
    have hc := congrArg (fun z : List (Fin 3) => z.count r) hsplit
    simp at hc
    omega
  have htail : tail = [] := by
    by_contra hn
    have hg := congrArg List.getLast? (hsplit.symm.trans hlast)
    have ht : (r :: tail).getLast? = some r := by
      simpa [List.getLast?_append] using hg
    rw [List.getLast?_eq_some_iff] at ht
    obtain ⟨ys, hys⟩ := ht
    cases ys with
    | nil =>
        simp at hys
        exact hn hys
    | cons z zs =>
        simp at hys
        have hm : r ∈ tail := by rw [hys.2]; simp
        rw [List.count_eq_zero] at htailCount
        exact htailCount hm
  subst tail
  rw [hsplit]
  simp [hr] at hN ⊢
  exact hN

/-- The `h`-th occurrence is split from the original list, preserving its exact prefix. -/
theorem nth_occurrence_split {α : Type*} [DecidableEq α] (r : α) :
    ∀ (l : List α) (h : ℕ), 1 ≤ h → h ≤ l.count r →
      ∃ a b, l = a ++ r :: b ∧ a.count r = h - 1 := by
  intro l
  induction l with
  | nil => intro h hh hc; simp at hc; omega
  | cons x xs ih =>
      intro h hh hc
      by_cases hx : x = r
      · subst x
        by_cases he : h = 1
        · subst h
          exact ⟨[],xs,rfl,by simp⟩
        · have hh' : 1 ≤ h-1 := by omega
          have hc' : h-1 ≤ xs.count r := by simp at hc; omega
          obtain ⟨a,b,hab,hcount⟩ := ih (h-1) hh' hc'
          refine ⟨r::a,b,?_,?_⟩
          · simp [hab]
          · simp [hcount]
            omega
      · have hc' : h ≤ xs.count r := by simpa [hx] using hc
        obtain ⟨a,b,hab,hcount⟩ := ih h hh hc'
        refine ⟨x::a,b,?_,?_⟩
        · simp [hab]
        · simpa [hx] using hcount

theorem occurrence_source_ends_zero (l : List (Fin 3)) (r : Fin 3)
    (hp : ProperNonzeroPredecessors l) (hr : r ≠ 0)
    {h : ℕ} (hh : 1 ≤ h) (hc : h ≤ l.count r) :
    ∃ p b, l = (p ++ [0]) ++ r :: b ∧ (p ++ [0]).count r = h-1 := by
  obtain ⟨a,b,hab,hcount⟩ := nth_occurrence_split r l h hh hc
  obtain ⟨p,rfl⟩ := hp a r b hab hr
  exact ⟨p,b,hab,hcount⟩

theorem count_eq_zero_of_members {l : List (Fin 3)} {a b c : Fin 3}
    (hmem : ∀ i ∈ l, i = a ∨ i = b) (hc : c ≠ a) (hc' : c ≠ b) :
    l.count c = 0 := by
  rw [List.count_eq_zero]
  intro hm
  rcases hmem c hm with h | h <;> contradiction

/-- Select the prefix ending at the `k`-th actual row-zero firing. -/
theorem prefix_at_zero_count (l : List (Fin 3)) (k : ℕ)
    (hk : 1 ≤ k) (hkl : k ≤ l.count 0) :
    ∃ p, p <+: l ∧ p.count 0 = k ∧ ∃ a, p = a ++ [0] := by
  obtain ⟨a, b, hab, hcount⟩ := nth_occurrence_split 0 l k hk hkl
  refine ⟨a ++ [0], ?_, ?_, a, rfl⟩
  · refine ⟨b, ?_⟩
    simpa [List.append_assoc] using hab.symm
  · simp [hcount]
    omega

/-- The finite-list actuality lemma behind Appendix B.2.4.2.

The upper prefix is either the source of the `K`-th successful crossing
(`K < Q`) or the current terminal row-zero run (`K = Q`).  For `K = 1`
no predecessor crossing is requested: the selected state lies directly on
the initial row-zero run. -/
theorem shifted_prefix_actual (l : List (Fin 3)) (r : Fin 3)
    (K target : ℕ) (hK : 1 ≤ K)
    (upper : List (Fin 3)) (hupper : upper <+: l)
    (hupperR : upper.count r = K - 1)
    (htarget0 : 1 ≤ target) (htargetUpper : target ≤ upper.count 0)
    (hlower : K = 1 ∨ ∃ lower, lower <+: l ∧
      lower.count r = K - 1 ∧ lower.count 0 < target) :
    ∃ p, p <+: l ∧ p.count 0 = target ∧ p.count r = K - 1 ∧
      ∃ a, p = a ++ [0] := by
  obtain ⟨p, hpUpper, hp0, a, ha⟩ := prefix_at_zero_count upper target htarget0 htargetUpper
  have hpL : p <+: l := hpUpper.trans hupper
  have hpRle : p.count r ≤ K - 1 := by
    rw [← hupperR]
    exact hpUpper.count_le r
  have hpRge : K - 1 ≤ p.count r := by
    rcases hlower with hK1 | ⟨lower, hlowerL, hlowerR, hlower0⟩
    · omega
    · rcases List.prefix_or_prefix_of_prefix hlowerL hpL with hlu | hpl
      · rw [← hlowerR]
        exact hlu.count_le r
      · have := hpl.count_le 0
        omega
  exact ⟨p, hpL, hp0, by omega, a, ha⟩

/-- If two comparable prefixes have the same nonzero-row count but the later
one has another row-zero firing, the actual next label after the earlier
prefix is row zero. -/
theorem prefix_continues_zero {l p upper : List (Fin 3)} {r : Fin 3}
    (hp : p <+: upper) (hupper : upper <+: l)
    (hcolors : ∀ i ∈ l, i = 0 ∨ i = r)
    (hr : r ≠ 0) (hcountR : p.count r = upper.count r)
    (hcount0 : p.count 0 < upper.count 0) :
    p ++ [0] <+: l := by
  obtain ⟨tail, htail⟩ := hp
  have htailne : tail ≠ [] := by
    intro he
    subst tail
    simp at htail
    subst upper
    omega
  cases tail with
  | nil => contradiction
  | cons i rest =>
      have hi : i = 0 ∨ i = r := by
        apply hcolors i
        apply hupper.sublist.mem
        rw [← htail]
        simp
      have hi0 : i = 0 := by
        rcases hi with h | h
        · exact h
        · subst i
          rw [← htail] at hcountR
          simp at hcountR
      subst i
      refine (show p ++ [0] <+: upper from ⟨rest, ?_⟩).trans hupper
      simpa [List.append_assoc] using htail

end P21.Nonsymmetric.ColorCap
