import P21.Nonsymmetric.Chain.C9

namespace P21.Nonsymmetric

example {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns}
    (O : A.OneData E) (U : O.RegionU)
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m) : False :=
  U.impossible hF hc

example {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns}
    (hF : s.semigroup.IsFrobenius F) (RD : A.RegionD E hF) (hJ : K.J0 < 0)
    (hc : s.semigroup.Canonical F g.m) : K.h = 1 ∧ A.N = A.zhat + 1 :=
  RD.linear_first_survivor hJ hc

example {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    (X : EuclideanSeed s F D) :
    1 ≤ X.p ∧ 1 ≤ X.q ∧ 1 ≤ X.v ∧ 1 ≤ X.t ∧
      X.p * X.t - X.q * X.v = 1 ∧ X.M < X.L ∧
      0 < X.theta * X.chi - X.Epar * X.Hp :=
  ⟨X.p_pos, X.q_pos, X.v_pos, X.t_pos, X.det_one, X.L_gt_M,
    X.packet_det_pos⟩

example {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    (K : ChainCore s F D) (A : K.FirstFit) (E : K.Returns)
    (hJ : K.J0 < 0) (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) : Nonempty (EuclideanSeed s F D) :=
  K.c9_handoff A E hJ hF hc

end P21.Nonsymmetric
