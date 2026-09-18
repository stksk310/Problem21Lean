import P21.Nonsymmetric.Path.Exclusion
import P21.Nonsymmetric.ColorCap.FullColorCap

namespace P21.Nonsymmetric

/-- The selected terminal alternatives remaining after PATH exclusion. -/
def SelectedTerminalAfterPath {g : Generators} (s : g.Setting) (F : ℤ)
    (D : HerzogCriticalData g) (rows : FourDistinctActualQRows s F) : Prop :=
  (∃ P : TypeIIInput s F D, P.values = selectedValues rows) ∨
  (∃ P : ChainInput s F D, P.values = selectedValues rows)

/-- The frozen orientation wrapper with its PATH disjunct removed. -/
def TerminalInputAfterPath {g : Generators} (s : g.Setting) (F : ℤ)
    (D : HerzogCriticalData g) (rows : FourDistinctActualQRows s F) : Prop :=
  (∃ i, SelectedTerminalAfterPath (relabelSetting s (rotatePerm i)) F
    (rotateHerzog D i) (relabelFourRows (rotatePerm i) rows)) ∨
  (∃ i, SelectedTerminalAfterPath
    (relabelSetting (relabelSetting s reversePerm) (rotatePerm i)) F
    (rotateHerzog (reverseHerzog D) i)
    (relabelFourRows (rotatePerm i) (relabelFourRows reversePerm rows)))

theorem selected_terminal_after_path {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (D : HerzogCriticalData g)
    (rows : FourDistinctActualQRows s F) (h : SelectedTerminal s F D rows) :
    SelectedTerminalAfterPath s F D rows := by
  rcases h with hp | ht | hc
  · obtain ⟨P, _⟩ := hp
    exact (P.impossible hF).elim
  · exact Or.inl ht
  · exact Or.inr hc

theorem terminal_input_after_path {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (D : HerzogCriticalData g)
    (rows : FourDistinctActualQRows s F) (h : TerminalInputExists s F D rows) :
    TerminalInputAfterPath s F D rows := by
  rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
  · left
    refine ⟨i, selected_terminal_after_path _ ?_ _ _ hi⟩
    rw [relabel_semigroup]
    exact hF
  · right
    refine ⟨i, selected_terminal_after_path _ ?_ _ _ hi⟩
    have hrev : (relabelSetting s reversePerm).semigroup.IsFrobenius F := by
      rw [relabel_semigroup]
      exact hF
    rw [relabel_semigroup]
    exact hrev

/-- Residual-free selected-four extraction with PATH removed. -/
theorem nonsymmetric_selected_four_after_path
    {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hns : ¬ P21.Symmetric.SymmetricTail g) (rows : FourDistinctActualQRows s F) :
    ∃ D : NonsymmetricHerzogData g,
      TerminalInputAfterPath s F D.toHerzogCriticalData rows := by
  obtain ⟨D, hD⟩ := nonsymmetric_selected_four s hF hc hns rows
  exact ⟨D, terminal_input_after_path s hF D.toHerzogCriticalData rows hD⟩

/-- The cardinality wrapper retains the same selected rows and leaves only
TYPE II or CHAIN in either frozen orientation. -/
theorem nonsymmetric_Q_ge_four_after_path
    {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hns : ¬ P21.Symmetric.SymmetricTail g) (hcard : 4 ≤ (s.semigroup.Q F).ncard) :
    ∃ (D : NonsymmetricHerzogData g) (rows : FourDistinctActualQRows s F),
      TerminalInputAfterPath s F D.toHerzogCriticalData rows := by
  obtain ⟨D, rows, hD⟩ := nonsymmetric_Q_ge_four s hF hc hns hcard
  exact ⟨D, rows, terminal_input_after_path s hF D.toHerzogCriticalData rows hD⟩

end P21.Nonsymmetric
