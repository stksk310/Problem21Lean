import P21.Nonsymmetric.ColorCap.BoxPaths

namespace P21.Nonsymmetric.ColorCap

/-- RES places consecutive integers strictly on either side of the Farey corridor. -/
theorem crossing_separator (x A B v h N : ℤ) (hx : 0 < x) (hB : 0 < B)
    (_hE0 : 0 < N*x-h*A) (hEx : N*x-h*A < x)
    (_hU0 : 0 < h*v-(N-1)*B) (hUB : h*v-(N-1)*B < B) :
    ¬ ∃ k : ℤ, h*A ≤ k*x ∧ k*B ≤ h*v := by
  rintro ⟨k,hleft,hright⟩
  have hk : N ≤ k := by
    by_contra hn
    have hkn : k ≤ N-1 := by omega
    have := mul_le_mul_of_nonneg_right hkn hx.le
    nlinarith
  have := mul_le_mul_of_nonneg_right hk hB.le
  nlinarith

/-- The separator rule is derived for the whole chronological successful prefix. -/
theorem successful_prefix_separator (x A B v : ℤ) (q : ℕ) (N : ℕ → ℤ)
    (hx : 0 < x) (hB : 0 < B)
    (hres : ∀ h : ℕ, 1 ≤ h → h ≤ q →
      0 < N h*x-(h : ℤ)*A ∧ N h*x-(h : ℤ)*A < x ∧
      0 < (h : ℤ)*v-(N h-1)*B ∧ (h : ℤ)*v-(N h-1)*B < B) :
    ∀ h : ℕ, 1 ≤ h → h ≤ q →
      ¬ ∃ k : ℤ, (h : ℤ)*A ≤ k*x ∧ k*B ≤ (h : ℤ)*v := by
  intro h hh hq
  obtain ⟨hE0,hEx,hU0,hUB⟩ := hres h hh hq
  exact crossing_separator x A B v h (N h) hx hB hE0 hEx hU0 hUB

/-- Two successful residue coordinates cannot both weakly increase. -/
theorem prefix_residue_antichain (x A B v : ℤ) (q : ℕ) (N : ℕ → ℤ)
    (hsep : ∀ h : ℕ, 1 ≤ h → h ≤ q →
      ¬ ∃ k : ℤ, (h : ℤ)*A ≤ k*x ∧ k*B ≤ (h : ℤ)*v)
    (i j : ℕ) (hij : i < j) (hjq : j ≤ q) :
    N j*x-(j : ℤ)*A < N i*x-(i : ℤ)*A ∨
      (j : ℤ)*v-(N j-1)*B < (i : ℤ)*v-(N i-1)*B := by
  by_contra hn
  push Not at hn
  apply hsep (j-i) (by omega) (by omega)
  refine ⟨N j-N i,?_,?_⟩
  all_goals
    rw [Nat.cast_sub (by omega : i ≤ j)]
    nlinarith [hn.1,hn.2]

end P21.Nonsymmetric.ColorCap


namespace P21.Nonsymmetric.ColorCap

/-- Exact finite slot counting, including a terminal point outside one residue range. -/
theorem residue_slot_bound {α : Type*} (s : Finset α) (E U : α → ℤ)
    (e u emax umax : ℤ) (hE : ∀ i ∈ s, E i ≤ emax) (hU : ∀ i ∈ s, U i ≤ umax)
    (hEinj : Set.InjOn E (s : Set α)) (hUinj : Set.InjOn U (s : Set α))
    (hcover : ∀ i ∈ s, e < E i ∨ u < U i) :
    s.card ≤ (emax-e).toNat + (umax-u).toNat := by
  classical
  let left := s.filter (fun i => e < E i)
  let right := s.filter (fun i => ¬ e < E i)
  have hleft : left.card ≤ (Finset.Ioc e emax).card := by
    apply Finset.card_le_card_of_injOn E
    · intro i hi
      obtain ⟨his,he⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_Ioc.mpr ⟨he,hE i his⟩
    · intro i hi j hj heq
      exact hEinj (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 heq
  have hright : right.card ≤ (Finset.Ioc u umax).card := by
    apply Finset.card_le_card_of_injOn U
    · intro i hi
      obtain ⟨his,he⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_Ioc.mpr ⟨(hcover i his).resolve_left he,hU i his⟩
    · intro i hi j hj heq
      exact hUinj (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 heq
  have hsum : left.card+right.card = s.card := Finset.card_filter_add_card_filter_not _
  rw [Int.card_Ioc] at hleft hright
  omega

end P21.Nonsymmetric.ColorCap

namespace P21.Nonsymmetric.ColorCap

/-- Each residue coordinate is distinct along a successful prefix, not only the pair. -/
theorem prefix_residue_distinct (x A B v : ℤ) (q : ℕ) (N : ℕ → ℤ)
    (hx : 0 < x) (hB : 0 < B) (hcorridor : A*B < x*v)
    (hsep : ∀ h : ℕ, 1 ≤ h → h ≤ q →
      ¬ ∃ k : ℤ, (h : ℤ)*A ≤ k*x ∧ k*B ≤ (h : ℤ)*v)
    (i j : ℕ) (hij : i < j) (hjq : j ≤ q) :
    N i*x-(i : ℤ)*A ≠ N j*x-(j : ℤ)*A ∧
      (i : ℤ)*v-(N i-1)*B ≠ (j : ℤ)*v-(N j-1)*B := by
  have hijz : 0 < (j : ℤ)-i := by
    have hz : (i : ℤ) < j := by exact_mod_cast hij
    omega
  have hprod := mul_pos hijz (sub_pos.mpr hcorridor)
  constructor
  · intro he
    apply hsep (j-i) (by omega) (by omega)
    refine ⟨N j-N i,?_,?_⟩
    · rw [Nat.cast_sub (by omega : i ≤ j)]
      nlinarith
    · rw [Nat.cast_sub (by omega : i ≤ j)]
      have heB := congrArg (fun z : ℤ => z*B) he
      by_contra hn
      have hbad := mul_pos hx (show 0 < (N j-N i)*B-((j : ℤ)-i)*v by omega)
      nlinarith
  · intro he
    apply hsep (j-i) (by omega) (by omega)
    refine ⟨N j-N i,?_,?_⟩
    · rw [Nat.cast_sub (by omega : i ≤ j)]
      have hex := congrArg (fun z : ℤ => z*x) he
      by_contra hn
      have hbad := mul_pos hB (show 0 < ((j : ℤ)-i)*A-(N j-N i)*x by omega)
      nlinarith
    · rw [Nat.cast_sub (by omega : i ≤ j)]
      nlinarith

end P21.Nonsymmetric.ColorCap


