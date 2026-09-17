import P21.Nonsymmetric.SelectedExtraction

open P21 P21.Nonsymmetric

-- End-to-end conditional selected-four statement. Neither compatibility,
-- tail cofiniteness, Herzog data, nor a terminal configuration is a premise.
example (hm : ColorCap.MinimumOneStatement) (hd : ColorCap.BoxPositiveExitStatement)
    (g : Generators) (s : g.Setting) (F : ℤ)
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hn : ¬ P21.Symmetric.SymmetricTail g) (rows : FourDistinctActualQRows s F) :
    ∃ D : NonsymmetricHerzogData g, TerminalInputExists s F D.toHerzogCriticalData rows :=
  nonsymmetric_selected_four_of_colorcap_residuals hm hd s hF hc hn rows

-- Q≥4 remains a lower bound on the ambient set, never an equality assumption.
example (hm : ColorCap.MinimumOneStatement) (hd : ColorCap.BoxPositiveExitStatement)
    (g : Generators) (s : g.Setting) (F : ℤ)
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hn : ¬ P21.Symmetric.SymmetricTail g) (hcard : 4 ≤ (s.semigroup.Q F).ncard) :
    ∃ (D : NonsymmetricHerzogData g) (rows : FourDistinctActualQRows s F),
      TerminalInputExists s F D.toHerzogCriticalData rows :=
  nonsymmetric_Q_ge_four_of_colorcap_residuals hm hd s hF hc hn hcard

-- Relabeling changes generator coordinates, never the four selected values.
example (g : Generators) (s : g.Setting) (F : ℤ) (rows : FourDistinctActualQRows s F)
    (e : Equiv.Perm (Fin 3)) : selectedValues (relabelFourRows e rows) = selectedValues rows :=
  selectedValues_relabel rows e
