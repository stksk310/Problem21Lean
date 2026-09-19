import P21.Nonsymmetric.Chain.C10.Descent
import P21.Nonsymmetric.Chain.C10.Projection

namespace P21.Nonsymmetric
namespace EuclideanSeed

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

theorem impossible (seed : EuclideanSeed s F D) : False := by
  exact seed.frobenius.1 seed.toState.f_mem

end EuclideanSeed
end P21.Nonsymmetric
