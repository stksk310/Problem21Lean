# C7 source of truth

1. `reference_inputs/P21_Journal_of_Algebra_Submission_Manuscript_FINAL_20260916.pdf`, Section 7.
2. `reference_inputs/P21_MANUSCRIPT_EN_FINAL_20260908_v1.zip`, Section 7 sources.
3. `reference_inputs/P21_FINAL_FROZEN_VERIFICATION_EDITION_20260907.zip`, maintained CORE proof.
4. Frozen Lean source at commit `6a1e395736e442bcda33c0da282220c98a444c76`.

The publication controls mathematical scope.  Existing Lean declarations are
used only through their actual-factorization interfaces.  Signed identities do
not imply semigroup membership; every membership proof names nonnegative
coefficients.  Strict-region results explicitly require
`chain.alpha < Croot`.
