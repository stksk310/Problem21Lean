import P21.Nonsymmetric.Chain

namespace P21.Nonsymmetric

example {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    (K : ChainCore s F D) :
    K.h*g.m + K.tau0*g.n 1 =
      ((D.a 0 : ℤ)-K.h*K.d)*g.n 0 +
      ((D.b 2 : ℤ)+K.h*K.Croot)*g.n 2 := K.shift_new

example {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    (K : ChainCore s F D) (E : K.Returns) :
    E.Uj ≤ K.tau0-1 ∧ E.Vj ≤ K.tau0-1 := K.tau_caps E

-- C7 deliberately exposes an interface and no CHAIN impossibility theorem.
#check ChainCore.FK_strong

end P21.Nonsymmetric
