import P21.Nonsymmetric.ActualClassification
import P21.Nonsymmetric.Extraction

namespace P21.Nonsymmetric
namespace ActualLabeling
variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
  {rows : FourDistinctActualQRows s F}

noncomputable def pick (L : ActualLabeling D rows) (l : RowLabel) (h : l ∈ L.labels) : Fin 4 :=
  Classical.choose (L.mem_labels h)

theorem pick_label (L : ActualLabeling D rows) (l : RowLabel) (h : l ∈ L.labels) :
    L.label (L.pick l h) = l := (Classical.choose_spec (L.mem_labels h)).1

theorem pick_realizes (L : ActualLabeling D rows) (l : RowLabel) (h : l ∈ L.labels) :
    Realizes D (rows.row (L.pick l h)).q l := (Classical.choose_spec (L.mem_labels h)).2

/-- Selecting all four distinct labels only reorders the original actual rows. -/
theorem pick_permutation (L : ActualLabeling D rows) (ls : Fin 4 → RowLabel)
    (hinj : Function.Injective ls) (hmem : ∀ i, ls i ∈ L.labels) :
    Function.Bijective (fun i => L.pick (ls i) (hmem i)) := by
  have hi : Function.Injective (fun i => L.pick (ls i) (hmem i)) := by
    intro i j he
    dsimp only at he
    apply hinj
    rw [← L.pick_label (ls i) (hmem i), ← L.pick_label (ls j) (hmem j), he]
  exact ⟨hi,Finite.surjective_of_injective hi⟩

end ActualLabeling

/-- Exact selected values are retained; the ambient Q remains unchanged. -/
def selectedValues {g : Generators} {s : g.Setting} {F : ℤ}
    (rows : FourDistinctActualQRows s F) : Set ℤ := Set.range (fun i => (rows.row i).q)

def PathInput.values {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    (P : PathInput s F D) : Set ℤ := Set.range (![P.qL,P.qA,P.qB,P.qR] : Fin 4 → ℤ)
def TypeIIInput.values {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    (P : TypeIIInput s F D) : Set ℤ :=
  Set.range (![P.qS,D.fA-P.lambda*g.n 0,D.fB-P.mu*g.n 1,D.fA-P.nu*g.n 2] : Fin 4 → ℤ)
def ChainInput.values {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    (P : ChainInput s F D) : Set ℤ :=
  Set.range (![D.fB-P.mu*g.n 1,D.fA-P.lambda*g.n 0,D.fB-P.lambda*g.n 0,D.fA-P.nu*g.n 2] : Fin 4 → ℤ)

def SelectedTerminal {g : Generators} (s : g.Setting) (F : ℤ) (D : HerzogCriticalData g)
    (rows : FourDistinctActualQRows s F) : Prop :=
  (∃ P : PathInput s F D, P.values = selectedValues rows) ∨
  (∃ P : TypeIIInput s F D, P.values = selectedValues rows) ∨
  (∃ P : ChainInput s F D, P.values = selectedValues rows)

/-- Four actual rows with the same ordered labels have the same values. -/
theorem realized_values_eq {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (rows : FourDistinctActualQRows s F)
    (L : ActualLabeling D rows) (ls : Fin 4 → RowLabel)
    (hi : Function.Injective ls) (hm : ∀ i, ls i ∈ L.labels)
    (v : Fin 4 → ℤ) (hv : ∀ i, v i ∈ s.semigroup.Q F)
    (hr : ∀ i, Realizes D (v i) (ls i)) : Set.range v = selectedValues rows := by
  have he (i) : v i = (rows.row (L.pick (ls i) (hm i))).q :=
    equal_label_equal_row s hF hc D (hv i) (rows.row _).mem (hr i) (L.pick_realizes _ _)
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨_,(he i).symm⟩
  · rintro ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := (L.pick_permutation ls hi hm).2 i
    dsimp only at hj
    exact ⟨j,by rw [he,hj]⟩


theorem ordered_realization {g : Generators} {s : g.Setting} {F : ℤ}
    {D : HerzogCriticalData g} {rows : FourDistinctActualQRows s F}
    (L : ActualLabeling D rows) (ls : Fin 4 → RowLabel)
    (hi : Function.Injective ls) (hm : ∀ i, ls i ∈ L.labels) :
    ∃ v : Fin 4 → ℤ, (∀ i, v i ∈ s.semigroup.Q F) ∧ Function.Injective v ∧
      ∀ i, Realizes D (v i) (ls i) := by
  refine ⟨fun i => (rows.row (L.pick (ls i) (hm i))).q,fun i => (rows.row _).mem,?_,?_⟩
  · exact rows.distinct.comp (L.pick_permutation ls hi hm).1
  · exact fun i => L.pick_realizes _ _

theorem selected_path_normalized {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (rows : FourDistinctActualQRows s F)
    (L : ActualLabeling D rows) (he : L.labels = RowLabel.path 0) : SelectedTerminal s F D rows := by
  let ls : Fin 4 → RowLabel := ![RowLabel.S 0,RowLabel.A 2,RowLabel.B 0,RowLabel.S 2]
  have hi : Function.Injective ls := by decide
  have hm : ∀ i, ls i ∈ L.labels := by intro i; rw [he]; fin_cases i <;> simp [ls,RowLabel.path,prev]
  obtain ⟨v,hv,hvi,hr⟩ := ordered_realization L ls hi hm
  have hsL : IsSingleton g (v 0) 0 := hr 0
  have hsR : IsSingleton g (v 3) 2 := hr 3
  obtain ⟨n,hn,hna,en⟩ := (hr 1 : IsArmA D (v 1) 2)
  obtain ⟨l,hl,hlb,el⟩ := (hr 2 : IsArmB D (v 2) 0)
  have ev : v = ![v 0,D.fA-n*g.n 2,D.fB-l*g.n 0,v 3] := by
    funext i; fin_cases i <;> simp [en,el]
  rw [ev] at hv hvi
  obtain ⟨P⟩ := path_exact_input s hF hc D l n (v 0) (v 3) hl (by omega) hn (by omega) hv hvi hsL hsR
  left
  refine ⟨P, realized_values_eq s hF hc D rows L ls hi hm _ P.actual ?_⟩
  intro i; fin_cases i
  · exact P.left_singleton
  · exact ⟨P.nu,P.nu_range.1,by have := P.nu_range.2; omega,P.A_eq⟩
  · exact ⟨P.lambda,P.lambda_range.1,by have := P.lambda_range.2; omega,P.B_eq⟩
  · exact P.right_singleton

theorem selected_typeII_normalized {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (rows : FourDistinctActualQRows s F)
    (L : ActualLabeling D rows) (he : L.labels = RowLabel.typeII 0) : SelectedTerminal s F D rows := by
  let ls : Fin 4 → RowLabel := ![RowLabel.S 0,RowLabel.A 0,RowLabel.B 1,RowLabel.A 2]
  have hi : Function.Injective ls := by decide
  have hm : ∀ i, ls i ∈ L.labels := by intro i; rw [he]; fin_cases i <;> simp [ls,RowLabel.typeII,next,prev]
  obtain ⟨v,hv,hvi,hr⟩ := ordered_realization L ls hi hm
  have hs : IsSingleton g (v 0) 0 := hr 0
  obtain ⟨l,hl,hla,el⟩ := (hr 1 : IsArmA D (v 1) 0)
  obtain ⟨m,hm',hmb,em⟩ := (hr 2 : IsArmB D (v 2) 1)
  obtain ⟨n,hn,hna,en⟩ := (hr 3 : IsArmA D (v 3) 2)
  have ev : v = ![v 0,D.fA-l*g.n 0,D.fB-m*g.n 1,D.fA-n*g.n 2] := by
    funext i; fin_cases i <;> simp [en,el,em]
  rw [ev] at hv hvi
  obtain ⟨P⟩ := typeII_exact_input s hF hc D l m n (v 0) hl (by omega) hm' (by omega) hn (by omega) hv hvi hs
  right; left
  refine ⟨P, realized_values_eq s hF hc D rows L ls hi hm _ P.actual ?_⟩
  intro i; fin_cases i
  · exact P.singleton
  · exact ⟨P.lambda,P.lambda_range.1,by have := P.lambda_range.2.1; omega,rfl⟩
  · exact ⟨P.mu,P.mu_range.1,by have := P.mu_range.2; omega,rfl⟩
  · exact ⟨P.nu,P.nu_range.1,by have := P.nu_range.2; omega,rfl⟩

theorem selected_chain_normalized {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (rows : FourDistinctActualQRows s F)
    (L : ActualLabeling D rows) (he : L.labels = RowLabel.chain 0) : SelectedTerminal s F D rows := by
  let ls : Fin 4 → RowLabel := ![RowLabel.B 1,RowLabel.A 0,RowLabel.B 0,RowLabel.A 2]
  have hi : Function.Injective ls := by decide
  have hm : ∀ i, ls i ∈ L.labels := by intro i; rw [he]; fin_cases i <;> simp [ls,RowLabel.chain,next,prev]
  obtain ⟨v,hv,hvi,hr⟩ := ordered_realization L ls hi hm
  obtain ⟨m,hm',hmb,em⟩ := (hr 0 : IsArmB D (v 0) 1)
  obtain ⟨l,hl,hla,el⟩ := (hr 1 : IsArmA D (v 1) 0)
  obtain ⟨r,hr',hrb,er⟩ := (hr 2 : IsArmB D (v 2) 0)
  obtain ⟨n,hn,hna,en⟩ := (hr 3 : IsArmA D (v 3) 2)
  have ev : v = ![D.fB-m*g.n 1,D.fA-l*g.n 0,D.fB-r*g.n 0,D.fA-n*g.n 2] := by
    funext i; fin_cases i <;> simp [en,el,em,er]
  rw [ev] at hv hvi
  obtain ⟨P⟩ := chain_exact_input_independent s hF hc D l r m n hl (by omega) hr' (by omega)
    hm' (by omega) hn (by omega) hv hvi
  right; right
  refine ⟨P, realized_values_eq s hF hc D rows L ls hi hm _ P.actual ?_⟩
  intro i; fin_cases i
  · exact ⟨P.mu,P.mu_range.1,by have := P.mu_range.2; omega,rfl⟩
  · exact ⟨P.lambda,P.lambda_range.1,by have := P.lambda_range.2.1; omega,rfl⟩
  · exact ⟨P.lambda,P.lambda_range.1,by have := P.lambda_range.2.2; omega,rfl⟩
  · exact ⟨P.nu,P.nu_range.1,by have := P.nu_range.2; omega,rfl⟩

namespace RowLabel
def rotateBack (i : Fin 3) : RowLabel → RowLabel
  | .singleton j => .singleton ((rotatePerm i).symm j)
  | .arm c j => .arm c ((rotatePerm i).symm j)
  | .corner c => .corner c

theorem reverse_reverse (l : RowLabel) : reverse (reverse l) = l := by
  cases l with
  | singleton i => fin_cases i <;> rfl
  | arm c i => cases c <;> fin_cases i <;> rfl
  | corner c => cases c <;> rfl

theorem rotate_path (i : Fin 3) : (path i).image (rotateBack i) = path 0 := by fin_cases i <;> decide
theorem rotate_typeII (i : Fin 3) : (typeII i).image (rotateBack i) = typeII 0 := by fin_cases i <;> decide
theorem rotate_chain (i : Fin 3) : (chain i).image (rotateBack i) = chain 0 := by fin_cases i <;> decide
end RowLabel

theorem realizes_rotate {g : Generators} (D : HerzogCriticalData g) (i : Fin 3)
    {q : ℤ} {l : RowLabel} (h : Realizes D q l) :
    Realizes (rotateHerzog D i) q (RowLabel.rotateBack i l) := by
  cases l with
  | singleton j =>
    change IsSingleton (relabel g (rotatePerm i)) q ((rotatePerm i).symm j)
    rw [relabel_singleton_iff,Equiv.apply_symm_apply]
    exact h
  | arm c j =>
    cases c
    · change IsArmA (rotateHerzog D i) q ((rotatePerm i).symm j)
      rw [rotate_isArmA,Equiv.apply_symm_apply]; exact h
    · change IsArmB (rotateHerzog D i) q ((rotatePerm i).symm j)
      rw [rotate_isArmB,Equiv.apply_symm_apply]; exact h
  | corner c => cases c <;> simpa [Realizes,RowLabel.rotateBack] using h

theorem realizes_reverse {g : Generators} (D : HerzogCriticalData g)
    {q : ℤ} {l : RowLabel} (h : Realizes D q l) :
    Realizes (reverseHerzog D) q (RowLabel.reverse l) := by
  cases l with
  | singleton j =>
    change IsSingleton (relabel g reversePerm) q (reversePerm j)
    rw [relabel_singleton_iff,reversePerm_self]; exact h
  | arm c j =>
    cases c
    · change IsArmB (reverseHerzog D) q (reversePerm j)
      rw [reverse_isArmB,reversePerm_self]; exact h
    · change IsArmA (reverseHerzog D) q (reversePerm j)
      rw [reverse_isArmA,reversePerm_self]; exact h
  | corner c => cases c <;> simpa [Realizes,RowLabel.reverse] using h

namespace ActualLabeling
variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
  {rows : FourDistinctActualQRows s F}
def rotate (L : ActualLabeling D rows) (i : Fin 3) :
    ActualLabeling (rotateHerzog D i) (relabelFourRows (rotatePerm i) rows) where
  label t := RowLabel.rotateBack i (L.label t)
  realizes t := realizes_rotate D i (L.realizes t)
def reverse (L : ActualLabeling D rows) :
    ActualLabeling (reverseHerzog D) (relabelFourRows reversePerm rows) where
  label t := RowLabel.reverse (L.label t)
  realizes t := realizes_reverse D (L.realizes t)

theorem rotate_labels (L : ActualLabeling D rows) (i : Fin 3) :
    (L.rotate i).labels = L.labels.image (RowLabel.rotateBack i) := by
  simp only [labels,rotate,Finset.image_image]
  rfl

theorem reverse_labels (L : ActualLabeling D rows) :
    L.reverse.labels = L.labels.image RowLabel.reverse := by
  simp only [labels,reverse,Finset.image_image]
  rfl

theorem reverse_image_labels (L : ActualLabeling D rows) (t : Finset RowLabel)
    (h : L.labels = t.image RowLabel.reverse) : L.reverse.labels = t := by
  rw [reverse_labels,h,Finset.image_image]
  simp [Function.comp_def,RowLabel.reverse_reverse]
end ActualLabeling

/-- The two allowed orientations: cyclic relabeling, or genuine reversal followed
by cyclic relabeling. Every terminal package retains exactly the selected values. -/
def TerminalInputExists {g : Generators} (s : g.Setting) (F : ℤ) (D : HerzogCriticalData g)
    (rows : FourDistinctActualQRows s F) : Prop :=
  (∃ i, SelectedTerminal (relabelSetting s (rotatePerm i)) F (rotateHerzog D i)
    (relabelFourRows (rotatePerm i) rows)) ∨
  (∃ i, SelectedTerminal (relabelSetting (relabelSetting s reversePerm) (rotatePerm i)) F
    (rotateHerzog (reverseHerzog D) i)
    (relabelFourRows (rotatePerm i) (relabelFourRows reversePerm rows)))

theorem selected_normalized {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (rows : FourDistinctActualQRows s F)
    (L : ActualLabeling D rows)
    (he : L.labels = RowLabel.path 0 ∨ L.labels = RowLabel.typeII 0 ∨ L.labels = RowLabel.chain 0) :
    SelectedTerminal s F D rows := by
  rcases he with he | he | he
  · exact selected_path_normalized s hF hc D rows L he
  · exact selected_typeII_normalized s hF hc D rows L he
  · exact selected_chain_normalized s hF hc D rows L he

theorem selected_rotated {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (rows : FourDistinctActualQRows s F)
    (L : ActualLabeling D rows) (i : Fin 3)
    (he : L.labels = RowLabel.path i ∨ L.labels = RowLabel.typeII i ∨ L.labels = RowLabel.chain i) :
    SelectedTerminal (relabelSetting s (rotatePerm i)) F (rotateHerzog D i)
      (relabelFourRows (rotatePerm i) rows) := by
  apply selected_normalized (relabelSetting s (rotatePerm i))
    (by rw [relabel_semigroup]; exact hF) (by rw [relabel_semigroup]; exact hc)
    (rotateHerzog D i) _ (L.rotate i)
  rw [L.rotate_labels]
  rcases he with h | h | h
  · exact Or.inl (by rw [h,RowLabel.rotate_path])
  · exact Or.inr (Or.inl (by rw [h,RowLabel.rotate_typeII]))
  · exact Or.inr (Or.inr (by rw [h,RowLabel.rotate_chain]))

/-- Terminal label classification is converted to the exact actual input,
without assuming a complement identity, synchronized depth, or scalar box. -/
theorem actual_terminal_input_exists {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (rows : FourDistinctActualQRows s F)
    (L : ActualLabeling D rows) (ht : RowLabel.Terminal L.labels) : TerminalInputExists s F D rows := by
  obtain ⟨i,h | h | h | h | h | h⟩ := ht
  · exact Or.inl ⟨i,selected_rotated s hF hc D rows L i (Or.inl h)⟩
  · exact Or.inl ⟨i,selected_rotated s hF hc D rows L i (Or.inr (Or.inl h))⟩
  · exact Or.inl ⟨i,selected_rotated s hF hc D rows L i (Or.inr (Or.inr h))⟩
  all_goals
    right
    refine ⟨i,selected_rotated (relabelSetting s reversePerm)
      (by rw [relabel_semigroup]; exact hF) (by rw [relabel_semigroup]; exact hc)
      (reverseHerzog D) (relabelFourRows reversePerm rows) L.reverse i ?_⟩
  · exact Or.inl (L.reverse_image_labels _ h)
  · exact Or.inr (Or.inl (L.reverse_image_labels _ h))
  · exact Or.inr (Or.inr (L.reverse_image_labels _ h))

@[simp] theorem selectedValues_relabel {g : Generators} {s : g.Setting} {F : ℤ}
    (rows : FourDistinctActualQRows s F) (e : Equiv.Perm (Fin 3)) :
    selectedValues (relabelFourRows e rows) = selectedValues rows := rfl


/-- Conditional selected-four G4: its only unproved mathematical inputs are
exactly the explicitly named MINBOX and positive-exit statements. -/
theorem selected_four_terminal_of_colorcap_residuals
    (hminimum : ColorCap.MinimumOneStatement) (hdpe : ColorCap.BoxPositiveExitStatement)
    {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g) (rows : FourDistinctActualQRows s F) :
    TerminalInputExists s F D.toHerzogCriticalData rows := by
  obtain ⟨L⟩ := actual_labeling_exists s hF hc D rows
  exact actual_terminal_input_exists s hF hc D.toHerzogCriticalData rows L
    (actual_labels_terminal hminimum hdpe s hF hc D rows L)

/-- Any selected four actual rows obtain their own exact terminal input;
Herzog data and tail cofiniteness are derived rather than assumed. -/
theorem nonsymmetric_selected_four_of_colorcap_residuals
    (hminimum : ColorCap.MinimumOneStatement) (hdpe : ColorCap.BoxPositiveExitStatement)
    {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hns : ¬ P21.Symmetric.SymmetricTail g) (rows : FourDistinctActualQRows s F) :
    ∃ D : NonsymmetricHerzogData g, TerminalInputExists s F D.toHerzogCriticalData rows := by
  obtain ⟨D⟩ := nonsymmetric_herzog_exists g s
    (s.tail_cofinite hF hc ⟨(rows.row 0).q,(rows.row 0).mem⟩) hns
  exact ⟨D,selected_four_terminal_of_colorcap_residuals hminimum hdpe s hF hc D rows⟩

/-- Cardinality at least four supplies a selection; it does not replace full Q
by a four-element set. Both unresolved ColorCap obligations remain explicit. -/
theorem nonsymmetric_Q_ge_four_of_colorcap_residuals
    (hminimum : ColorCap.MinimumOneStatement) (hdpe : ColorCap.BoxPositiveExitStatement)
    {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hns : ¬ P21.Symmetric.SymmetricTail g) (hcard : 4 ≤ (s.semigroup.Q F).ncard) :
    ∃ (D : NonsymmetricHerzogData g) (rows : FourDistinctActualQRows s F),
      TerminalInputExists s F D.toHerzogCriticalData rows := by
  obtain ⟨rows⟩ := select_four_actual_rows s hF hc hcard
  obtain ⟨D,hD⟩ := nonsymmetric_selected_four_of_colorcap_residuals hminimum hdpe s hF hc hns rows
  exact ⟨D,rows,hD⟩

end P21.Nonsymmetric
