import P21.Nonsymmetric.HerzogCoordinates
import Mathlib.Tactic.DeriveFintype

set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 1024

namespace P21.Nonsymmetric

/-- Labels record just a row's direction and its Herzog color. -/
inductive RowLabel where
  | singleton : Fin 3 → RowLabel
  | arm : Bool → Fin 3 → RowLabel
  | corner : Bool → RowLabel
  deriving DecidableEq, Fintype

namespace RowLabel
def S := singleton
def A := arm false
def B := arm true
def revDir (i : Fin 3) : Fin 3 := ![0,2,1] i
def reverse : RowLabel → RowLabel
  | singleton i => singleton (revDir i)
  | arm c i => arm (!c) (revDir i)
  | corner c => corner (!c)

def path (i : Fin 3) : Finset RowLabel := {S i,B i,A (prev i),S (prev i)}
def typeII (i : Fin 3) : Finset RowLabel := {S i,A i,B (next i),A (prev i)}
def chain (i : Fin 3) : Finset RowLabel := {B (next i),A i,B i,A (prev i)}

/-- Local geometric constraints plus the three-arm exclusion. The latter is
conditional on the two explicit ColorCap residuals. This finite lemma consumes
constraints, not any assumption on the size of Q. -/
def Compatible (t : Finset RowLabel) : Prop :=
  t.card = 4 ∧
  (¬ (corner false ∈ t ∧ corner true ∈ t)) ∧
  (∀ c i, corner c ∈ t → S i ∉ t ∧ arm c i ∉ t) ∧
  (∀ c, ¬ (arm c 0 ∈ t ∧ arm c 1 ∈ t ∧ arm c 2 ∈ t)) ∧
  (¬ (S 0 ∈ t ∧ S 1 ∈ t ∧ S 2 ∈ t)) ∧
  (∀ i, A i ∈ t → B i ∈ t →
    (∀ j, S j ∉ t) ∧ A (next i) ∉ t ∧ B (prev i) ∉ t) ∧
  (∀ i, A i ∈ t → A (prev i) ∈ t → S (next i) ∉ t) ∧
  (∀ i, B i ∈ t → B (next i) ∈ t → S (prev i) ∉ t) ∧
  (∀ c i j, i ≠ j → arm c i ∈ t → arm c j ∈ t →
    ∀ k l, k ≠ l → ¬ (S k ∈ t ∧ S l ∈ t)) ∧
  (∀ i, B i ∈ t → A (prev i) ∈ t → S (next i) ∉ t) ∧
  (∀ i, A i ∈ t → B (prev i) ∈ t → S i ∉ t ∧ S (prev i) ∉ t)

def Terminal (t : Finset RowLabel) : Prop :=
  ∃ i, t = path i ∨ t = typeII i ∨ t = chain i ∨
    t = (path i).image reverse ∨ t = (typeII i).image reverse ∨
    t = (chain i).image reverse

instance (t : Finset RowLabel) : Decidable (Compatible t) := by
  unfold Compatible
  infer_instance
instance (t : Finset RowLabel) : Decidable (Terminal t) := by unfold Terminal; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Exhaustive finite classification of four distinct labels; checked by
Lean's kernel evaluator, with no native evaluation or unchecked oracle. -/
theorem four_labels_classification : ∀ t : Finset RowLabel, Compatible t → Terminal t := by
  decide

end RowLabel
end P21.Nonsymmetric
