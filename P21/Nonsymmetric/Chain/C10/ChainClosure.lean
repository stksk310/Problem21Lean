import P21.Nonsymmetric.Chain.C10.SeedClosure
import P21.Nonsymmetric.Chain.C9.Handoff
import P21.Nonsymmetric.Chain.Orientation
import P21.Nonsymmetric.Chain.Root

namespace P21.Nonsymmetric

namespace ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

theorem impossible (K : ChainCore s F D)
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m) : False := by
  cases K.orientIntrinsic hF with
  | direct hJ =>
      obtain ⟨seed⟩ := K.c9_handoff K.firstFit K.returns hJ hF hc
      exact seed.impossible
  | reversed h hJ =>
      let Kr := K.reverseCore h
      have hF' : (relabelSetting s reversePerm).semigroup.IsFrobenius F := by
        rw [relabel_semigroup]
        exact hF
      have hc' : (relabelSetting s reversePerm).semigroup.Canonical F
          (relabel g reversePerm).m := by
        rw [relabel_semigroup]
        change s.semigroup.Canonical F g.m
        exact hc
      obtain ⟨seed⟩ := Kr.c9_handoff Kr.firstFit Kr.returns hJ hF' hc'
      exact seed.impossible

end ChainCore

namespace ChainInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

theorem impossible (C : ChainInput s F D)
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m) : False := by
  let PF := Classical.choice (C.pfiber_exists hF)
  let M := Classical.choice C.max_i_exists
  let RB := C.root_box hF PF M
  cases C.to_oriented_core RB with
  | direct K => exact K.impossible hF hc
  | reversed K =>
      have hF' : (relabelSetting s reversePerm).semigroup.IsFrobenius F := by
        rw [relabel_semigroup]
        exact hF
      have hc' : (relabelSetting s reversePerm).semigroup.Canonical F
          (relabel g reversePerm).m := by
        rw [relabel_semigroup]
        change s.semigroup.Canonical F g.m
        exact hc
      exact K.impossible hF' hc'

end ChainInput
end P21.Nonsymmetric
