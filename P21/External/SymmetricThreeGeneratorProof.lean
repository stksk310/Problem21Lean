import P21.Symmetric.Classification.GlueExistence

namespace P21.Symmetric

/-- The previously external three-generator classification, proved from the
unchanged Setting and integer Frobenius symmetry hypotheses. -/
theorem symmetric_three_generator_gluing : SymmetricThreeGeneratorGluingStatement := by
  intro g setting hsym
  exact Classification.glue_exists_of_symmetric g setting hsym

end P21.Symmetric
