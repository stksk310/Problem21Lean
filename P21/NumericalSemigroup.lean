import P21.Factorization
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.SuccPred

namespace P21

/-- Integer realization of a cofinite additive submonoid of the nonnegative integers. -/
structure NumericalSemigroup where
  carrier : AddSubmonoid ℤ
  nonneg : ∀ x ∈ carrier, 0 ≤ x
  cofinite : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ carrier

namespace NumericalSemigroup
variable (S : NumericalSemigroup)

def Gap : Set ℤ := {x | x ∉ S.carrier}
def IsFrobenius (F : ℤ) : Prop := IsGreatest S.Gap F
def PF : Set ℤ := {q | q ∉ S.carrier ∧
  ∀ s ∈ S.carrier, s ≠ 0 → q + s ∈ S.carrier}
noncomputable def type : ℕ := S.PF.ncard
def Apery (m : ℤ) : Set ℤ := {w | w ∈ S.carrier ∧ w - m ∉ S.carrier}
def Le (x y : ℤ) : Prop := y - x ∈ S.carrier
def Canonical (F m : ℤ) : Prop := ∀ q ∈ S.PF, F + m - q ∈ S.carrier
def Q (F : ℤ) : Set ℤ := S.PF \ {F}
def Maximal (A : Set ℤ) (x : ℤ) : Prop := x ∈ A ∧ ∀ y ∈ A, S.Le x y → y = x
def Minimal (A : Set ℤ) (x : ℤ) : Prop := x ∈ A ∧ ∀ y ∈ A, S.Le y x → y = x

theorem le_refl (x : ℤ) : S.Le x x := by simp [Le]
theorem le_trans {x y z : ℤ} (hxy : S.Le x y) (hyz : S.Le y z) : S.Le x z := by
  have := S.carrier.add_mem hxy hyz
  convert this using 1; simp [Le] at *
theorem le_antisymm {x y : ℤ} (hxy : S.Le x y) (hyx : S.Le y x) : x = y := by
  have := S.nonneg _ hxy
  have := S.nonneg _ hyx
  omega

theorem exists_frobenius : ∃ F, S.IsFrobenius F := by
  obtain ⟨B, hB⟩ := S.cofinite
  apply BddAbove.exists_isGreatest_of_nonempty
  · exact ⟨B, fun x hx => le_of_lt (lt_of_not_ge fun h => hx (hB x h))⟩
  · exact ⟨-1, fun h => by have := S.nonneg _ h; omega⟩

theorem frobenius_mem_pf {F : ℤ} (hF : S.IsFrobenius F) : F ∈ S.PF := by
  refine ⟨hF.1, ?_⟩
  intro s hs hn
  by_contra hg
  have := hF.2 hg
  have := S.nonneg _ hs
  omega

theorem mem_of_gt_frobenius {F x : ℤ} (hF : S.IsFrobenius F) (hx : F < x) :
    x ∈ S.carrier := by
  by_contra h
  exact (not_le_of_gt hx) (hF.2 h)

theorem pf_finite {F m : ℤ} (hF : S.IsFrobenius F) (hm : m ∈ S.carrier) (hm0 : m ≠ 0) :
    S.PF.Finite := by
  apply (Set.finite_Icc (-m) F).subset
  intro q hq
  exact ⟨by have := S.nonneg _ (hq.2 m hm hm0); omega, hF.2 hq.1⟩

theorem q_lt_frobenius {F q : ℤ} (hF : S.IsFrobenius F) (hq : q ∈ S.Q F) : q < F := by
  have hle := hF.2 hq.1.1
  have hne : q ≠ F := hq.2
  omega

theorem type_eq_q_card_add_one {F m : ℤ} (hF : S.IsFrobenius F)
    (hm : m ∈ S.carrier) (hm0 : m ≠ 0) : S.type = (S.Q F).ncard + 1 := by
  exact (Set.ncard_sdiff_singleton_add_one (S.frobenius_mem_pf hF)
    (S.pf_finite hF hm hm0)).symm

end NumericalSemigroup
end P21
