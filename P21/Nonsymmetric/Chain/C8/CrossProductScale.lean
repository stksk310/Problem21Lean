import P21.Nonsymmetric.Chain.C8.BoundaryFullSync
import P21.Nonsymmetric.PrimitiveGenerators
import P21.Tail

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} (O : A.OneData E)

/-- The three publication cross-product coordinates, in the oriented `i,j,k` order. -/
def Ical (O : A.OneData E) : ℤ := (D.rho 1 : ℤ)*D.rho 2-(D.a 1 : ℤ)*D.b 2

def Jcal (O : A.OneData E) : ℤ := (D.a 0 : ℤ)*D.rho 2+(D.b 0 : ℤ)*D.b 2

def Kcal (O : A.OneData E) : ℤ := (D.b 0 : ℤ)*D.rho 1+(D.a 0 : ℤ)*D.a 1

/-- The ROOT multiplicity after removing the common positive generator scale. -/
def mhat : ℤ := -K.d*O.Ical+K.S*O.Jcal+K.Croot*O.Kcal

/-- Scale-aware primitive-generator interface.  The positive scale is produced
from the frozen primitive-generator theorem; it is not an added hypothesis. -/
theorem cross_product_scale (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) :
    ∃ sigma : ℤ, 0 < sigma ∧
      g.n 0=sigma*O.Ical ∧ g.n 1=sigma*O.Jcal ∧ g.n 2=sigma*O.Kcal ∧
      g.m=sigma*O.mhat := by
  have hQ : (s.semigroup.Q F).Nonempty :=
    ⟨K.chain.qJ, K.chain.actual 0⟩
  have hcof := s.tail_cofinite hF hc hQ
  have hp : ∀ i, 0 < g.n i := fun i => lt_trans s.m_pos (s.n_gt i)
  obtain ⟨hi,hj,hk⟩ := primitive_generator_minors D hp hcof
  refine ⟨1, by norm_num, ?_, ?_, ?_, ?_⟩
  · simpa [Ical] using hi
  · simpa [Jcal] using hj
  · simpa [Kcal, add_comm] using hk
  · simp only [one_mul]
    simp only [mhat, Ical, Jcal, Kcal]
    linear_combination K.root - hi*K.d + hj*K.S + hk*K.Croot

end P21.Nonsymmetric.ChainCore.FirstFit.OneData
