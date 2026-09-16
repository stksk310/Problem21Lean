import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.Data.Set.Card
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Actual coefficients are natural numbers; all values and signed algebra are integers. -/
namespace P21

def value {k : ℕ} (g : Fin k → ℤ) (a : Fin k → ℕ) : ℤ :=
  ∑ i, (a i : ℤ) * g i

structure ActualFactorization {k : ℕ} (g : Fin k → ℤ) (x : ℤ) where
  coeff : Fin k → ℕ
  equation : value g coeff = x

def generated {k : ℕ} (g : Fin k → ℤ) : AddSubmonoid ℤ where
  carrier := {x | ∃ a : Fin k → ℕ, value g a = x}
  zero_mem' := ⟨fun _ => 0, by simp [value]⟩
  add_mem' := by
    rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨fun i => a i + b i, by simp [value, add_mul, Finset.sum_add_distrib]⟩

theorem actual_iff_mem {k : ℕ} {g : Fin k → ℤ} {x : ℤ} :
    Nonempty (ActualFactorization g x) ↔ x ∈ generated g := by
  constructor
  · rintro ⟨a⟩; exact ⟨a.coeff, a.equation⟩
  · rintro ⟨a, h⟩; exact ⟨⟨a, h⟩⟩

theorem generator_mem {k : ℕ} (g : Fin k → ℤ) (i : Fin k) : g i ∈ generated g := by
  classical
  exact ⟨fun j => if j = i then 1 else 0, by simp [value]⟩

theorem generated_nonneg {k : ℕ} {g : Fin k → ℤ} (hg : ∀ i, 0 ≤ g i)
    {x : ℤ} (hx : x ∈ generated g) : 0 ≤ x := by
  obtain ⟨a, rfl⟩ := hx
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Int.natCast_nonneg _) (hg i)

/-- Replacement consumes a source contained in THIS named actual factorization.
The residual is constructed in integers and converted only with proved nonnegativity. -/
def replaceWithinActualFactorization {k : ℕ} {g : Fin k → ℤ} {x : ℤ}
    (a : ActualFactorization g x) (source target : Fin k → ℕ)
    (contained : ∀ i, source i ≤ a.coeff i)
    (replacement : value g source = value g target) : ActualFactorization g x where
  coeff i := ((a.coeff i : ℤ) - source i + target i).toNat
  equation := by
    have hn i : 0 ≤ (a.coeff i : ℤ) - source i + target i := by
      have := contained i
      omega
    simp only [value, Int.toNat_of_nonneg (hn _)]
    simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    change value g a.coeff - value g source + value g target = x
    rw [replacement, a.equation]
    ring

/-- Remove one copy from the supplied witness, retaining same-factorization provenance. -/
def removeOne {k : ℕ} {g : Fin k → ℤ} {x : ℤ}
    (a : ActualFactorization g x) (i : Fin k) (hi : 0 < a.coeff i) :
    ActualFactorization g (x - g i) where
  coeff j := ((a.coeff j : ℤ) - if j = i then 1 else 0).toNat
  equation := by
    have hn j : 0 ≤ (a.coeff j : ℤ) - if j = i then 1 else 0 := by
      split_ifs with h
      · subst j; omega
      · omega
    simp only [value, Int.toNat_of_nonneg (hn _), sub_mul, Finset.sum_sub_distrib]
    simpa [value] using congrArg (fun z => z - g i) a.equation

/-- Integer group representation: this type provides no semigroup membership API. -/
structure SignedRepresentation {k : ℕ} (g : Fin k → ℤ) (x : ℤ) where
  coeff : Fin k → ℤ
  equation : ∑ i, coeff i * g i = x

/-- Future criticality interfaces use only three tail coordinates. -/
structure SignedRelation3 (n : Fin 3 → ℤ) where
  coeff : Fin 3 → ℤ
  equation : ∑ i, coeff i * n i = 0

end P21
