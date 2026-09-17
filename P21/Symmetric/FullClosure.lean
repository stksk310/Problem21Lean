import P21.External.SymmetricThreeGeneratorProof
import P21.Symmetric.Closure

namespace P21.Symmetric

/-- Full S3: integer symmetry of the minimally generated tail supplies the
normal form required by the frozen internal type bound. -/
theorem symmetric_tail_type_le_four
    (g : Generators) (setting : g.Setting) (F : ℤ)
    (hF : setting.semigroup.IsFrobenius F)
    (hcan : setting.semigroup.Canonical F g.m)
    (hsym : SymmetricTail g) : setting.semigroup.type ≤ 4 := by
  obtain ⟨G⟩ := symmetric_three_generator_gluing g setting hsym
  exact symmetric_tail_from_glue_data g setting F hF hcan G

end P21.Symmetric
