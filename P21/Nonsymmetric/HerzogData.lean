import P21.Symmetric.Classification.CriticalRelations
import P21.External.SymmetricThreeGenerator

namespace P21.Nonsymmetric
open Symmetric.Classification

/-- Positive critical cycle, with actual least positive critical multipliers. -/
structure HerzogCriticalData (g : Generators) where
  a : Fin 3 → ℕ
  b : Fin 3 → ℕ
  rho : Fin 3 → ℕ
  a_pos : ∀ i, 0 < a i
  b_pos : ∀ i, 0 < b i
  rho_eq : ∀ i, rho i = a i + b i
  relation_zero : (rho 0 : ℤ) * g.n 0 = (b 1 : ℤ) * g.n 1 + (a 2 : ℤ) * g.n 2
  relation_one : (rho 1 : ℤ) * g.n 1 = (a 0 : ℤ) * g.n 0 + (b 2 : ℤ) * g.n 2
  relation_two : (rho 2 : ℤ) * g.n 2 = (b 0 : ℤ) * g.n 0 + (a 1 : ℤ) * g.n 1
  critical : ∀ i, CriticalRelation g i
  coeff_rho : ∀ i, (critical i).coeff = rho i

namespace HerzogCriticalData
variable {g : Generators} (D : HerzogCriticalData g)

def fA : ℤ := (D.rho 0 - 1 : ℤ) * g.n 0 + (D.a 1 - 1 : ℤ) * g.n 1 - g.n 2
def fB : ℤ := (D.rho 0 - 1 : ℤ) * g.n 0 - g.n 1 + (D.b 2 - 1 : ℤ) * g.n 2

theorem rho_pos (i : Fin 3) : 0 < D.rho i := by
  rw [D.rho_eq]; exact Nat.add_pos_left (D.a_pos i) _

theorem critical_minimal (i : Fin 3) (c : ℕ) (hc : 0 < c)
    (u : Fin 3 → ℕ) (hu : u i = 0)
    (he : (c : ℤ) * g.n i = value g.n u) : D.rho i ≤ c := by
  rw [← D.coeff_rho]
  exact (D.critical i).minimal c hc u hu he
end HerzogCriticalData

/-- PF on the actual tail, independently of a choice of cofiniteness witness. -/
def TailPF (g : Generators) : Set ℤ :=
  {q | q ∉ g.H ∧ ∀ t ∈ g.H, t ≠ 0 → q + t ∈ g.H}

/-- Full publication input; existence is a separate classification obligation. -/
structure NonsymmetricHerzogData (g : Generators) extends HerzogCriticalData g where
  distinct : toHerzogCriticalData.fA ≠ toHerzogCriticalData.fB
  pf_exact : TailPF g = {toHerzogCriticalData.fA, toHerzogCriticalData.fB}

/-- Exact standard theorem target, proved by `herzog_classification` downstream. -/
def HerzogClassificationStatement : Prop := ∀ (g : Generators), g.Setting →
  (∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H) →
  ¬ Symmetric.SymmetricTail g → Nonempty (NonsymmetricHerzogData g)

end P21.Nonsymmetric


