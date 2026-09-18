import P21.Nonsymmetric.Chain.C8

namespace P21.Nonsymmetric

open ChainCore

example {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    {K : ChainCore s F D} (A : K.FirstFit) (E : K.Returns)
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m) :
    (∃ O : A.OneData E, O.RegionU) ∨ Nonempty (A.RegionD E hF) :=
  A.c8_handoff E hF hc

example {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns}
    (O : A.OneData E) (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) (hstrict : K.chain.alpha<K.Croot)
    (hw : A.chi≤K.chain.T) : E.Li=1 :=
  ChainCore.FirstFit.OneData.every_EA_level_one hF hc hstrict hw E

example {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    {K : ChainCore s F D} (A : K.FirstFit) (E : K.Returns)
    (hF : s.semigroup.IsFrobenius F) :
    ¬ ((∃ O : A.OneData E, O.RegionU) ∧ Nonempty (A.RegionD E hF)) :=
  A.handoff_disjoint E hF

end P21.Nonsymmetric
