import P21.Nonsymmetric.Chain.C10

namespace P21.Nonsymmetric

example {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    (K : ChainCore s F D) (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) : False := K.impossible hF hc

example {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    (C : ChainInput s F D) (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) : False := C.impossible hF hc

example {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    {rows : FourDistinctActualQRows s F}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (h : SelectedTerminalAfterTypeII s F D rows) : False :=
  selected_terminal_after_chain_impossible hF hc h

example {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    {rows : FourDistinctActualQRows s F}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (h : TerminalInputAfterTypeII s F D rows) : False :=
  terminal_input_after_chain_impossible hF hc h

example {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hns : ¬ P21.Symmetric.SymmetricTail g) (rows : FourDistinctActualQRows s F) : False :=
  nonsymmetric_selected_four_impossible_after_chain s hF hc hns rows

example {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hns : ¬ P21.Symmetric.SymmetricTail g) (hcard : 4 ≤ (s.semigroup.Q F).ncard) : False :=
  nonsymmetric_Q_ge_four_impossible_after_chain s hF hc hns hcard

end P21.Nonsymmetric
