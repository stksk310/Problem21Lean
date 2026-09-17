import P21.External.SymmetricThreeGenerator

/-! Numerical tail foundations obtained from symmetry alone, without CAN or Q. -/
namespace P21.Symmetric.Classification

variable {g : Generators}

theorem tail_generator_pos (s : g.Setting) (i : Fin 3) : 0 < g.n i :=
  lt_trans s.m_pos (s.n_gt i)

theorem tail_nonneg (s : g.Setting) {x : ℤ} (hx : x ∈ g.H) : 0 ≤ x :=
  generated_nonneg (fun i => (tail_generator_pos s i).le) hx

theorem tail_minimal (s : g.Setting) : g.TailMinimal :=
  g.tail_minimal s.minimal

theorem tail_cofinite (s : g.Setting) (hsym : SymmetricTail g) :
    ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H := by
  obtain ⟨f, hf⟩ := hsym
  refine ⟨f + 1, ?_⟩
  intro x hx
  by_contra hn
  have := symmetricAt_gap_le s hf hn
  omega

def tailSemigroup (s : g.Setting) (hsym : SymmetricTail g) : NumericalSemigroup where
  carrier := g.H
  nonneg := fun _ hx => tail_nonneg s hx
  cofinite := tail_cofinite s hsym

theorem tail_common_divisor_dvd_one (s : g.Setting) (hsym : SymmetricTail g)
    {d : ℤ} (hd : ∀ i, d ∣ g.n i) : d ∣ 1 := by
  obtain ⟨B, hB⟩ := tail_cofinite s hsym
  have h0 := divisor_of_generated hd (hB B le_rfl)
  have h1 := divisor_of_generated hd (hB (B + 1) (by omega))
  have := dvd_sub h1 h0
  simpa using this

theorem tail_gcd_eq_one (s : g.Setting) (hsym : SymmetricTail g) : g.tailGcd = 1 := by
  have hd : ∀ i, (g.tailGcd : ℤ) ∣ g.n i := by
    intro i
    rw [Int.natCast_dvd]
    fin_cases i
    · exact Nat.gcd_dvd_left _ _
    · exact dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
    · exact dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)
  have h := tail_common_divisor_dvd_one s hsym hd
  have hn : g.tailGcd ∣ 1 := by exact_mod_cast h
  exact Nat.eq_one_of_dvd_one hn

theorem value_permuted_three (p : Equiv.Perm (Fin 3)) (a : Fin 3 → ℕ) :
    value g.n a = (a (p 0) : ℤ) * g.n (p 0) +
      (a (p 1) : ℤ) * g.n (p 1) + (a (p 2) : ℤ) * g.n (p 2) := by
  have h := Equiv.sum_comp p (fun i => (a i : ℤ) * g.n i)
  simpa [value, Fin.sum_univ_succ, add_assoc] using h.symm

/-- Consecutive actual tail elements give Bezout coefficients after any permutation. -/
theorem tail_bezout (s : g.Setting) (hsym : SymmetricTail g)
    (p : Equiv.Perm (Fin 3)) : ∃ α β γ : ℤ,
    α * g.n (p 0) + β * g.n (p 1) + γ * g.n (p 2) = 1 := by
  obtain ⟨B, hB⟩ := tail_cofinite s hsym
  obtain ⟨a, ha⟩ := hB B le_rfl
  obtain ⟨b, hb⟩ := hB (B + 1) (by omega)
  rw [value_permuted_three p a] at ha
  rw [value_permuted_three p b] at hb
  refine ⟨(b (p 0) : ℤ) - a (p 0), (b (p 1) : ℤ) - a (p 1),
    (b (p 2) : ℤ) - a (p 2), ?_⟩
  linear_combination hb - ha

theorem symmetric_frobenius (s : g.Setting) {f : ℤ} (hs : SymmetricAt g.H f) :
    (tailSemigroup s ⟨f, hs⟩).IsFrobenius f := by
  refine ⟨?_, ?_⟩
  · change f ∉ g.H
    apply (hs f).2
    simp
  · intro t ht
    exact symmetricAt_gap_le s hs ht

/-- A local Apéry predicate for the actual tail, independent of choosing f. -/
def TailApery (g : Generators) (i : Fin 3) (a : ℤ) : Prop :=
  a ∈ g.H ∧ a - g.n i ∉ g.H

theorem symmetry_apery_top (s : g.Setting) {f : ℤ} (hs : SymmetricAt g.H f)
    (i : Fin 3) : TailApery g i (f + g.n i) := by
  constructor
  · by_contra hg
    have := symmetricAt_gap_le s hs hg
    have := tail_generator_pos s i
    omega
  · have hf : f ∉ g.H := (hs f).2 (by simp)
    simpa using hf

theorem symmetry_apery_complement {f a : ℤ} (hs : SymmetricAt g.H f)
    (i : Fin 3) (ha : TailApery g i a) : TailApery g i (f + g.n i - a) := by
  constructor
  · have h := (hs (a - g.n i)).1 ha.2
    convert h using 1; ring
  · have h : f - a ∉ g.H := by
      intro hm
      exact ((hs a).2 hm) ha.1
    simpa only [show f + g.n i - a - g.n i = f - a by ring] using h

theorem symmetry_apery_complement_iff {f a : ℤ} (hs : SymmetricAt g.H f)
    (i : Fin 3) : TailApery g i a ↔ TailApery g i (f + g.n i - a) := by
  constructor
  · exact symmetry_apery_complement hs i
  · intro ha
    have h := symmetry_apery_complement hs i ha
    simpa only [show f + g.n i - (f + g.n i - a) = a by ring] using h

theorem symmetry_apery_le_top (s : g.Setting) {f a : ℤ}
    (hs : SymmetricAt g.H f) {i : Fin 3} (ha : TailApery g i a) :
    a ≤ f + g.n i := by
  have := tail_nonneg s (symmetry_apery_complement hs i ha).1
  omega

/-- Every actual representation of an Apéry element has zero distinguished coordinate. -/
theorem apery_actual_zero {a : ℤ} {i : Fin 3} (ha : TailApery g i a)
    (A : g.ActualFactorization3 a) : A.coeff i = 0 := by
  by_contra hn
  have hp : 0 < A.coeff i := Nat.pos_of_ne_zero hn
  exact ha.2 (actual_iff_mem.mp ⟨removeOne A i hp⟩)

end P21.Symmetric.Classification
