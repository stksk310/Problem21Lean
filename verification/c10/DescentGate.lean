import P21.Nonsymmetric.Chain.C10.SeedClosure

namespace P21.Nonsymmetric

example {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    (X : EuclideanState s F D) : F ∈ g.Gamma := X.f_mem

example {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    (seed : EuclideanSeed s F D) : False := seed.impossible

end P21.Nonsymmetric
