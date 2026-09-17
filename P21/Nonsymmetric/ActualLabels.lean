import P21.Nonsymmetric.FourRowCombinatorics
import P21.Nonsymmetric.RowAtlas
import P21.Nonsymmetric.Singletons

namespace P21.Nonsymmetric

/-- A label names an actual support pattern or the exact Herzog corner. -/
def Realizes {g : Generators} (D : HerzogCriticalData g) (q : ℤ) : RowLabel → Prop
  | .singleton i => IsSingleton g q i
  | .arm false i => IsArmA D q i
  | .arm true i => IsArmB D q i
  | .corner false => q = D.fA
  | .corner true => q = D.fB

theorem actual_label_exists {g : Generators} (s : g.Setting) {F q : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g) (hq : q ∈ s.semigroup.Q F) :
    ∃ l, Realizes D.toHerzogCriticalData q l := by
  rcases actual_row_atlas s hF hc D hq with ⟨i,hs⟩ | ⟨i,ha | hb⟩ | (ha | hb)
  · exact ⟨.singleton i,hs⟩
  · exact ⟨.arm false i,ha⟩
  · exact ⟨.arm true i,hb⟩
  · exact ⟨.corner false,ha⟩
  · exact ⟨.corner true,hb⟩

theorem equal_label_equal_row {g : Generators} (s : g.Setting) {F q r : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (hq : q ∈ s.semigroup.Q F) (hr : r ∈ s.semigroup.Q F)
    {l : RowLabel} (ha : Realizes D q l) (hb : Realizes D r l) : q = r := by
  cases l with
  | singleton i => exact singletons_same_direction s hF hc hq hr ha hb
  | arm c i =>
    cases c
    · exact same_A_arm_unique D hq hr ha hb
    · exact same_B_arm_unique D hq hr ha hb
  | corner c => cases c <;> exact ha.trans hb.symm

/-- No compatibility conclusion is stored in this witness. -/
structure ActualLabeling {g : Generators} {s : g.Setting} {F : ℤ}
    (D : HerzogCriticalData g) (rows : FourDistinctActualQRows s F) where
  label : Fin 4 → RowLabel
  realizes : ∀ i, Realizes D (rows.row i).q (label i)

theorem actual_labeling_exists {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g) (rows : FourDistinctActualQRows s F) :
    Nonempty (ActualLabeling D.toHerzogCriticalData rows) := by
  classical
  choose label hl using fun i => actual_label_exists s hF hc D (rows.row i).mem
  exact ⟨⟨label,hl⟩⟩

namespace ActualLabeling
variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
  {rows : FourDistinctActualQRows s F}

def labels (L : ActualLabeling D rows) : Finset RowLabel := Finset.univ.image L.label

theorem label_injective (L : ActualLabeling D rows)
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m) :
    Function.Injective L.label := by
  intro i j he
  apply rows.distinct
  exact equal_label_equal_row s hF hc D (rows.row i).mem (rows.row j).mem
    (L.realizes i) (he ▸ L.realizes j)

theorem labels_card (L : ActualLabeling D rows)
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m) : L.labels.card = 4 := by
  rw [labels,Finset.card_image_of_injective _ (L.label_injective hF hc)]
  decide

theorem mem_labels (L : ActualLabeling D rows) {l : RowLabel} (hl : l ∈ L.labels) :
    ∃ i, L.label i = l ∧ Realizes D (rows.row i).q l := by
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hl
  exact ⟨i,hi,hi ▸ L.realizes i⟩

end ActualLabeling
end P21.Nonsymmetric
