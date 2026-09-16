import P21.Symmetric.StableCore

namespace P21.Symmetric.Regression
variable {g : Generators} (s : g.Setting) {F f : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hsym : SymmetricAt g.H f)

example (t : ℤ) : t ∉ g.Gamma ↔ ∀ n : ℕ, f - t + (n : ℤ) * g.m ∈ g.H :=
  gap_iff_stableCore hsym

example : f - F - g.m + (1 : ℤ) * g.m ∈ g.H :=
  stable_walk s hF hsym 1 (by omega)

example : 0 < f - F - g.m := stable_shift_pos s hF hsym

example (hcan : s.semigroup.Canonical F g.m) :
    shiftedCore g (f - F - g.m) ⊆ g.Gamma :=
  shiftedCore_subset_gamma s hF hcan hsym

example (q : ℤ) : q ∈ s.semigroup.PF ↔ idealMin g.Gamma (stableCore g) (f - q) :=
  pf_iff_min_stableCore s hsym

#print axioms gap_iff_stableCore
#print axioms stableCore_isLeast
#print axioms stableCore_mem_gt_m
#print axioms stable_walk
#print axioms stableCore_add_gamma
#print axioms pf_iff_min_stableCore
#print axioms shiftedCore_subset_gamma
#print axioms shiftedCore_isLeast
end P21.Symmetric.Regression
