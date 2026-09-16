import P21.NumericalSemigroup

namespace P21

structure Generators where
  m : ℤ
  n : Fin 3 → ℤ

namespace Generators
def all (g : Generators) : Fin 4 → ℤ := Fin.cons g.m g.n
def Gamma (g : Generators) : AddSubmonoid ℤ := generated g.all
def H (g : Generators) : AddSubmonoid ℤ := generated g.n
abbrev ActualFactorization4 (g : Generators) (x : ℤ) := ActualFactorization g.all x
abbrev ActualFactorization3 (g : Generators) (x : ℤ) := ActualFactorization g.n x
def Minimal (g : Generators) : Prop :=
  ∀ i : Fin 4, ∀ a : Fin 4 → ℕ, a i = 0 → value g.all a ≠ g.all i
def TailMinimal (g : Generators) : Prop :=
  ∀ i : Fin 3, ∀ a : Fin 3 → ℕ, a i = 0 → value g.n a ≠ g.n i
def OffDirection (g : Generators) (i : Fin 3) (x : ℤ) : Prop :=
  ∃ a : g.ActualFactorization3 x, a.coeff i = 0
def D (g : Generators) (c : ℤ) : Set (Fin 3) := {i | c - g.n i ∈ g.H}
def SH (g : Generators) (q : ℤ) : Set (Fin 3) := {i | q + g.n i ∈ g.H}
def tailGcd (g : Generators) : ℕ :=
  Nat.gcd (g.n 0).natAbs (Nat.gcd (g.n 1).natAbs (g.n 2).natAbs)

theorem value_cons (g : Generators) (a : ℕ) (b : Fin 3 → ℕ) :
    value g.all (Fin.cons a b) = (a : ℤ) * g.m + value g.n b := by
  simp [value, all, Fin.sum_univ_succ]

theorem h_subset_gamma (g : Generators) : g.H ≤ g.Gamma := by
  rintro x ⟨a, rfl⟩
  exact ⟨Fin.cons 0 a, by simp [g.value_cons]⟩

theorem m_mem (g : Generators) : g.m ∈ g.Gamma := generator_mem g.all 0
theorem n_mem (g : Generators) (i : Fin 3) : g.n i ∈ g.Gamma :=
  g.h_subset_gamma (generator_mem g.n i)

theorem tail_minimal (g : Generators) (hg : g.Minimal) : g.TailMinimal := by
  intro i a hi he
  apply hg i.succ (Fin.cons 0 a) (by simpa using hi)
  change value g.all (Fin.cons 0 a) = g.n i
  simpa [g.value_cons] using he

/-- Exactly the publication hypotheses, with redundant edim wording represented by
an indexed irredundant four-generator family (injectivity is proved below). -/
structure Setting (g : Generators) where
  m_pos : 0 < g.m
  n_gt : ∀ i, g.m < g.n i
  minimal : g.Minimal
  multiplicity : ∀ x ∈ g.Gamma, x ≠ 0 → g.m ≤ x
  cofinite : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.Gamma

def Setting.semigroup {g : Generators} (s : g.Setting) : NumericalSemigroup where
  carrier := g.Gamma
  nonneg := fun _ hx => generated_nonneg (by
    intro i; refine Fin.cases ?_ (fun j => ?_) i
    · exact s.m_pos.le
    · exact (lt_trans s.m_pos (s.n_gt j)).le) hx
  cofinite := s.cofinite

theorem minimal_injective (g : Generators) (hg : g.Minimal) : Function.Injective g.all := by
  classical
  intro i j he
  by_contra hn
  exact hg i (fun k => if k = j then 1 else 0) (by simp [hn]) (by simp [value, he])

theorem minimal_four_distinct (g : Generators) (hg : g.Minimal) :
    (Set.range g.all).ncard = 4 := by
  rw [Set.ncard_range_of_injective (g.minimal_injective hg)]
  simp

end Generators

/-- Unproved publication target, NOT a theorem. PF ranges over all integer gaps. -/
def P21MainStatement : Prop :=
  ∀ (g : Generators) (s : g.Setting) (F : ℤ),
    s.semigroup.IsFrobenius F → s.semigroup.Canonical F g.m → s.semigroup.type ≤ 4

end P21
