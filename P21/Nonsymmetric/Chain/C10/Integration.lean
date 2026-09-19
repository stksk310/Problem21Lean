import P21.Nonsymmetric.Chain.C10.ChainClosure
import P21.Nonsymmetric.TypeII.Integration

namespace P21.Nonsymmetric

theorem selected_terminal_after_chain_impossible
    {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    {rows : FourDistinctActualQRows s F}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (h : SelectedTerminalAfterTypeII s F D rows) : False := by
  obtain ⟨C, _⟩ := h
  exact C.impossible hF hc

theorem terminal_input_after_chain_impossible
    {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    {rows : FourDistinctActualQRows s F}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (h : TerminalInputAfterTypeII s F D rows) : False := by
  rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
  · apply selected_terminal_after_chain_impossible ?_ ?_ hi
    · rw [relabel_semigroup]
      exact hF
    · rw [relabel_semigroup]
      change s.semigroup.Canonical F g.m
      exact hc
  · let sr : (relabel g reversePerm).Setting :=
      relabelSetting (g := g) s reversePerm
    let si : (relabel (relabel g reversePerm) (rotatePerm i)).Setting :=
      relabelSetting (g := relabel g reversePerm) sr (rotatePerm i)
    have hF' : si.semigroup.IsFrobenius F := by
      change (relabelSetting (g := relabel g reversePerm) sr
        (rotatePerm i)).semigroup.IsFrobenius F
      rw [relabel_semigroup]
      change (relabelSetting (g := g) s reversePerm).semigroup.IsFrobenius F
      rw [relabel_semigroup]
      exact hF
    have hc' : si.semigroup.Canonical F
        (relabel (relabel g reversePerm) (rotatePerm i)).m := by
      change (relabelSetting (g := relabel g reversePerm) sr
        (rotatePerm i)).semigroup.Canonical F
          (relabel (relabel g reversePerm) (rotatePerm i)).m
      rw [relabel_semigroup]
      change (relabelSetting (g := g) s reversePerm).semigroup.Canonical F g.m
      rw [relabel_semigroup]
      change s.semigroup.Canonical F g.m
      exact hc
    exact selected_terminal_after_chain_impossible hF' hc' hi

theorem nonsymmetric_selected_four_impossible_after_chain
    {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hns : ¬ P21.Symmetric.SymmetricTail g) (rows : FourDistinctActualQRows s F) : False := by
  obtain ⟨D, hD⟩ := nonsymmetric_selected_four_after_typeII s hF hc hns rows
  exact terminal_input_after_chain_impossible hF hc hD

theorem nonsymmetric_Q_ge_four_impossible_after_chain
    {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hns : ¬ P21.Symmetric.SymmetricTail g) (hcard : 4 ≤ (s.semigroup.Q F).ncard) : False := by
  obtain ⟨D, rows, hD⟩ := nonsymmetric_Q_ge_four_after_typeII s hF hc hns hcard
  exact terminal_input_after_chain_impossible hF hc hD

end P21.Nonsymmetric
