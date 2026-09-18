import P21.Nonsymmetric.TypeII.Exclusion
import P21.Nonsymmetric.Path.Integration

namespace P21.Nonsymmetric

/-- The selected terminal alternative after eliminating TYPE II. -/
def SelectedTerminalAfterTypeII {g : Generators} (s : g.Setting) (F : ℤ)
    (D : HerzogCriticalData g) (rows : FourDistinctActualQRows s F) : Prop :=
  ∃ C : ChainInput s F D, C.values = selectedValues rows

/-- The frozen two-orientation wrapper with only CHAIN remaining. -/
def TerminalInputAfterTypeII {g : Generators} (s : g.Setting) (F : ℤ)
    (D : HerzogCriticalData g) (rows : FourDistinctActualQRows s F) : Prop :=
  (∃ i, SelectedTerminalAfterTypeII (relabelSetting s (rotatePerm i)) F
    (rotateHerzog D i) (relabelFourRows (rotatePerm i) rows)) ∨
  (∃ i, SelectedTerminalAfterTypeII
    (relabelSetting (relabelSetting s reversePerm) (rotatePerm i)) F
    (rotateHerzog (reverseHerzog D) i)
    (relabelFourRows (rotatePerm i) (relabelFourRows reversePerm rows)))

theorem selected_terminal_after_typeII {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (D : HerzogCriticalData g)
    (rows : FourDistinctActualQRows s F) (h : SelectedTerminalAfterPath s F D rows) :
    SelectedTerminalAfterTypeII s F D rows := by
  rcases h with ⟨T, _⟩ | hC
  · exact (T.impossible hF).elim
  · exact hC

theorem terminal_input_after_typeII {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (D : HerzogCriticalData g)
    (rows : FourDistinctActualQRows s F) (h : TerminalInputAfterPath s F D rows) :
    TerminalInputAfterTypeII s F D rows := by
  rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
  · left
    refine ⟨i, selected_terminal_after_typeII _ ?_ _ _ hi⟩
    rw [relabel_semigroup]
    exact hF
  · right
    refine ⟨i, selected_terminal_after_typeII _ ?_ _ _ hi⟩
    have hrev : (relabelSetting s reversePerm).semigroup.IsFrobenius F := by
      rw [relabel_semigroup]
      exact hF
    rw [relabel_semigroup]
    exact hrev

/-- Residual-free selected-four extraction with only CHAIN remaining. -/
theorem nonsymmetric_selected_four_after_typeII
    {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hns : ¬ P21.Symmetric.SymmetricTail g) (rows : FourDistinctActualQRows s F) :
    ∃ D : NonsymmetricHerzogData g,
      TerminalInputAfterTypeII s F D.toHerzogCriticalData rows := by
  obtain ⟨D, hD⟩ := nonsymmetric_selected_four_after_path s hF hc hns rows
  exact ⟨D, terminal_input_after_typeII s hF D.toHerzogCriticalData rows hD⟩

/-- Cardinality wrapper preserving the selected four rows and leaving CHAIN only. -/
theorem nonsymmetric_Q_ge_four_after_typeII
    {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hns : ¬ P21.Symmetric.SymmetricTail g) (hcard : 4 ≤ (s.semigroup.Q F).ncard) :
    ∃ (D : NonsymmetricHerzogData g) (rows : FourDistinctActualQRows s F),
      TerminalInputAfterTypeII s F D.toHerzogCriticalData rows := by
  obtain ⟨D, rows, hD⟩ := nonsymmetric_Q_ge_four_after_path s hF hc hns hcard
  exact ⟨D, rows, terminal_input_after_typeII s hF D.toHerzogCriticalData rows hD⟩

end P21.Nonsymmetric
