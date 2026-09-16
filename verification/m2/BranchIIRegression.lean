import P21.Symmetric.BranchIIActual
namespace P21.Symmetric.BranchII.Regression
-- The N=1 case cannot enter the previous-stable-point argument.
example {d s e : ℤ} (hd : 0 < d) (hs : 0 ≤ s) (hsd : s < d)
    (he : 0 < e) (hed : e < d) (hek : d-s ≤ e) (hphase : 2*e ≤ d+1) :
    epsilon d s e 1 ≠ 1 := by
  intro h
  have := (epsilon_one_predecessor hd hs hsd he hed hek hphase (by omega) h).1
  omega
#print axioms k1_aux_pos
#print axioms k1_reduces_to_branchI
#print axioms k0_e0_impossible
#print axioms crosscore_phase
#print axioms complement_add_tau
#print axioms epsilon_one_predecessor
#print axioms crosscore_shift_mem
end P21.Symmetric.BranchII.Regression

namespace P21.Symmetric.Regression
example {g : Generators} {G : SymmetricGlueData g} {s : g.Setting} {F e μ : ℤ}
    (R : Raw4Data G s F) (hF : s.semigroup.IsFrobenius F)
    (hcan : s.semigroup.Canonical F g.m) (he : 0 ≤ e) (hed : e < G.d)
    (hm : g.m=e*G.w+G.d*μ) :
    (μ+((G.d-1-R.s+e)/G.d)*G.w)-R.rho-G.two.u-G.two.v ∉ G.two.T :=
  R.branchII_excluded hF hcan he hed hm
#print axioms BranchIIActual.actual_fs
#print axioms BranchIIActual.actual_complement_gap
#print axioms BranchIIActual.k0_excluded
#print axioms BranchIIActual.k1_excluded
#print axioms Raw4Data.branchII_excluded
end P21.Symmetric.Regression
