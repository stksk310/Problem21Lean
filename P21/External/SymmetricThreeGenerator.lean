import P21.Symmetric.GlueNormalForm

namespace P21.Symmetric

/-- Integer Frobenius symmetry of the actual tail; no classification is built in. -/
def SymmetricTail (g : Generators) : Prop := ∃ f : ℤ, SymmetricAt g.H f

/-- A target proposition recording precisely the external direction still required.
It is not supplied as a theorem or an axiom. The Setting supplies positivity and
irredundancy; symmetry supplies cofiniteness of the integer tail. -/
def SymmetricThreeGeneratorGluingStatement : Prop :=
  ∀ (g : Generators), g.Setting → SymmetricTail g → Nonempty (SymmetricGlueData g)

theorem glue_data_symmetric_tail {g : Generators} (D : SymmetricGlueData g) :
    SymmetricTail g := ⟨D.frobenius, D.symmetry⟩

end P21.Symmetric
