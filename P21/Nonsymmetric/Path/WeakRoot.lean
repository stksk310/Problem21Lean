import P21.Nonsymmetric.Path.Split

namespace P21.Nonsymmetric
namespace PathInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

/-- A signed weak root.  This structure intentionally has no semigroup
membership coercion: its negative `n₀` coefficient is part of the data. -/
structure WeakRoot (P : PathInput s F D) where
  d : ℤ
  S : ℤ
  e : ℤ
  d_pos : 1 ≤ d
  d_le : d ≤ (D.a 0 : ℤ) - 1
  S_pos : 1 ≤ S
  e_ge : P.alpha ≤ e
  equation : g.m = -d * g.n 0 + S * g.n 1 + e * g.n 2

/-- Convert an explicitly coefficientwise nonnegative four-generator
identity into genuine semigroup membership. -/
theorem gamma_of_coordinates (g : Generators) (x k a b c : ℤ)
    (hk : 0 ≤ k) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (he : x = k * g.m + a * g.n 0 + b * g.n 1 + c * g.n 2) :
    x ∈ g.Gamma := by
  refine ⟨![k.toNat, a.toNat, b.toNat, c.toNat], ?_⟩
  simpa [Generators.all, value, Fin.sum_univ_succ,
    Int.toNat_of_nonneg hk, Int.toNat_of_nonneg ha,
    Int.toNat_of_nonneg hb, Int.toNat_of_nonneg hc, add_assoc] using he.symm

theorem Pair.root_identity (P : PathInput s F D) (p : Pair P) :
    g.m = ((p.X : ℤ) - D.a 0 + 1) * g.n 0 +
      ((p.H0 : ℤ) + 1) * g.n 1 +
      ((p.Z : ℤ) - D.b 2 + 1) * g.n 2 := by
  have he := p.equationA
  have hq := P.qA_eq
  have hT := P.T_eq
  have ha : (P.alpha.toNat : ℤ) = P.alpha :=
    Int.toNat_of_nonneg (by have := P.alpha_pos; omega)
  simp [value, Fin.sum_univ_succ, Nat.cast_add, ha] at he
  rw [hT] at hq
  linear_combination he - hq

def Pair.t0 (D : HerzogCriticalData g) (p : Pair P) : ℤ :=
  D.rho 1 - p.H0 - 1

theorem Pair.t0_relation (P : PathInput s F D) (p : Pair P) :
    p.t0 D * g.n 1 + g.m =
      ((p.X : ℤ) + 1) * g.n 0 + ((p.Z : ℤ) + 1) * g.n 2 := by
  have hr := p.root_identity P
  simp only [Pair.t0]
  linear_combination hr + D.relation_one

theorem Pair.t0_bounds (P : PathInput s F D) (p : Pair P) :
    1 ≤ p.t0 D ∧ p.t0 D < D.rho 1 := by
  have he := p.t0_relation P
  have hm := s.m_pos
  have hn0 := s.n_gt 0
  have hn2 := s.n_gt 2
  have hX : 0 ≤ (p.X : ℤ) := Int.natCast_nonneg _
  have hZ : 0 ≤ (p.Z : ℤ) := Int.natCast_nonneg _
  constructor
  · by_contra h
    have hn1 := lt_trans s.m_pos (s.n_gt 1)
    have : p.t0 D * g.n 1 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) hn1.le
    nlinarith
  · simp only [Pair.t0]
    omega

theorem Pair.qA_gap_identity (P : PathInput s F D) (p : Pair P) :
    P.qA = g.m + ((D.a 0 : ℤ) - p.X - 2) * g.n 0 +
      (p.t0 D - 1) * g.n 1 + (P.T - p.Z - 2) * g.n 2 := by
  have hr := p.root_identity P
  have hq := P.qA_eq
  have ht := P.T_eq
  have hrho : (D.rho 1 : ℤ) = D.a 1 + D.b 1 := by
    exact_mod_cast D.rho_eq 1
  simp only [Pair.t0]
  linear_combination hq - hr - D.relation_one

theorem Pair.qB_gap_identity (P : PathInput s F D) (p : Pair P) :
    P.qB = g.m + (P.P0 - p.X - 2) * g.n 0 +
      (p.t0 D - 1) * g.n 1 + ((D.b 2 : ℤ) - p.Z - 2) * g.n 2 := by
  have hr := p.root_identity P
  have hq := P.qB_eq
  simp only [Pair.t0]
  linear_combination hq - hr - D.relation_one

theorem Pair.A_disjunction (P : PathInput s F D) (p : Pair P) :
    (D.a 0 : ℤ) - 1 ≤ p.X ∨ P.T - 1 ≤ p.Z := by
  by_contra h
  push_neg at h
  have ht := p.t0_bounds P
  have hmem := gamma_of_coordinates g P.qA 1
    ((D.a 0 : ℤ) - p.X - 2) (p.t0 D - 1) (P.T - p.Z - 2)
    (by omega) (by omega) (by omega) (by omega) (by
      simpa using p.qA_gap_identity P)
  exact (P.actual 1).1.1 hmem

theorem Pair.B_disjunction (P : PathInput s F D) (p : Pair P) :
    P.P0 - 1 ≤ p.X ∨ (D.b 2 : ℤ) - 1 ≤ p.Z := by
  by_contra h
  push_neg at h
  have ht := p.t0_bounds P
  have hmem := gamma_of_coordinates g P.qB 1
    (P.P0 - p.X - 2) (p.t0 D - 1) ((D.b 2 : ℤ) - p.Z - 2)
    (by omega) (by omega) (by omega) (by omega) (by
      simpa using p.qB_gap_identity P)
  exact (P.actual 2).1.1 hmem

theorem Pair.not_middle_quadrant (P : PathInput s F D) (p : Pair P) :
    ¬ ((D.a 0 : ℤ) - 1 ≤ p.X ∧ (D.b 2 : ℤ) - 1 ≤ p.Z) := by
  rintro ⟨hX, hZ⟩
  apply P21.Symmetric.m_not_mem_tail s
  have hr := p.root_identity P
  have hx : (((p.X : ℤ) - D.a 0 + 1).toNat : ℤ) =
      (p.X : ℤ) - D.a 0 + 1 := Int.toNat_of_nonneg (by omega)
  have hh : (((p.H0 : ℤ) + 1).toNat : ℤ) = (p.H0 : ℤ) + 1 :=
    Int.toNat_of_nonneg (by omega)
  have hz : (((p.Z : ℤ) - D.b 2 + 1).toNat : ℤ) =
      (p.Z : ℤ) - D.b 2 + 1 := Int.toNat_of_nonneg (by omega)
  have h0 := g.H.nsmul_mem (generator_mem g.n 0)
    ((p.X : ℤ) - D.a 0 + 1).toNat
  have h1 := g.H.nsmul_mem (generator_mem g.n 1) ((p.H0 : ℤ) + 1).toNat
  have h2 := g.H.nsmul_mem (generator_mem g.n 2)
    ((p.Z : ℤ) - D.b 2 + 1).toNat
  have hsum := g.H.add_mem h0 (g.H.add_mem h1 h2)
  simp only [nsmul_eq_mul] at hsum
  rw [hx, hh, hz] at hsum
  rw [hr]
  simpa [add_assoc] using hsum

/-- The exact two surviving PAIR ports before choosing an orientation. -/
theorem Pair.strong_port (P : PathInput s F D) (p : Pair P) :
    ((p.X : ℤ) ≤ D.a 0 - 2 ∧ P.T - 1 ≤ p.Z) ∨
    (P.P0 - 1 ≤ p.X ∧ (p.Z : ℤ) ≤ D.b 2 - 2) := by
  have hA := p.A_disjunction P
  have hB := p.B_disjunction P
  have hM := p.not_middle_quadrant P
  rcases hA with hAi | hAk
  · rcases hB with hBi | hBk
    · exact Or.inr ⟨hBi, by
        by_contra hz
        apply hM
        exact ⟨hAi, by omega⟩⟩
    · exact (hM ⟨hAi, hBk⟩).elim
  · rcases hB with hBi | hBk
    · exact Or.inr ⟨hBi, by
        have hP := P.P0_eq
        have hb := P.beta_pos
        by_contra hz
        apply hM
        exact ⟨by omega, by omega⟩⟩
    · exact Or.inl ⟨by
        by_contra hx
        apply hM
        exact ⟨by omega, hBk⟩, hAk⟩

theorem Pair.weak_root_of_left (P : PathInput s F D) (p : Pair P)
    (hleft : (p.X : ℤ) ≤ D.a 0 - 2 ∧ P.T - 1 ≤ p.Z) :
    Nonempty (WeakRoot P) := by
  refine ⟨{
    d := (D.a 0 : ℤ) - 1 - p.X
    S := (p.H0 : ℤ) + 1
    e := (p.Z : ℤ) - D.b 2 + 1
    d_pos := by omega
    d_le := by omega
    S_pos := by omega
    e_ge := by have := P.T_eq; omega
    equation := ?_ }⟩
  have hr := p.root_identity P
  linear_combination hr

/-- A genuine PAIR transported through the full PATH reversal.  Its actual
coefficient vectors are exchanged and permuted, with `X` and `Z` swapped. -/
def Pair.reverse (P : PathInput s F D) (p : Pair P) : Pair P.reverse where
  X := p.Z
  H0 := p.H0
  Z := p.X
  equationA := by
    have he := p.equationB
    simp [PathInput.reverse, PathInput.alpha, PathInput.beta,
      pathReverseHerzog, pathReversePerm, relabel, value,
      Fin.sum_univ_succ, add_comm, add_left_comm, add_assoc] at he ⊢
    linear_combination he
  equationB := by
    have he := p.equationA
    simp [PathInput.reverse, PathInput.alpha, PathInput.beta,
      pathReverseHerzog, pathReversePerm, relabel, value,
      Fin.sum_univ_succ, add_comm, add_left_comm, add_assoc] at he ⊢
    linear_combination he

theorem Pair.reverse_left_of_right (P : PathInput s F D) (p : Pair P)
    (hright : P.P0 - 1 ≤ p.X ∧ (p.Z : ℤ) ≤ D.b 2 - 2) :
    (((p.reverse P).X : ℤ) ≤ (pathReverseHerzog D).a 0 - 2 ∧
      P.reverse.T - 1 ≤ (p.reverse P).Z) := by
  have hT : P.reverse.T = P.P0 := by
    simp [PathInput.T, PathInput.P0, PathInput.reverse,
      pathReverseHerzog, pathReversePerm]
  simp only [Pair.reverse]
  constructor
  · simpa [pathReverseHerzog, pathReversePerm] using hright.2
  · rw [hT]
    exact hright.1

/-- Every genuine PAIR produces a weak root in one of the two formally
related PATH orientations. -/
theorem Pair.weak_root_or_dual (P : PathInput s F D) (p : Pair P) :
    Nonempty (WeakRoot P) ∨ Nonempty (WeakRoot P.reverse) := by
  rcases p.strong_port P with hleft | hright
  · exact Or.inl (p.weak_root_of_left P hleft)
  · exact Or.inr ((p.reverse P).weak_root_of_left P.reverse
      (p.reverse_left_of_right P hright))

end PathInput
end P21.Nonsymmetric
