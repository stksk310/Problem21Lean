import P21.Symmetric.BranchIIActual
import P21.External.SymmetricThreeGenerator

namespace P21.Symmetric

/-- The complete internal S3 closure. The gluing normal form is an explicit input;
its production from symmetry alone remains the separate external obligation. -/
theorem symmetric_tail_from_glue_data (g : Generators) (setting : g.Setting) (F : ℤ)
    (hF : setting.semigroup.IsFrobenius F)
    (hcan : setting.semigroup.Canonical F g.m) (G : SymmetricGlueData g) :
    setting.semigroup.type ≤ 4 := by
  by_contra htype
  obtain ⟨R⟩ := G.exists_raw4 setting hF hcan (by omega)
  obtain ⟨e, μ, he, hed, hm⟩ := G.normal_form_exists g.m
  rcases R.split hF hcan hm with hI | hII
  · exact R.branchI_excluded hF hcan he hed hm hI
  · exact R.branchII_excluded hF hcan he hed hm hII

end P21.Symmetric
