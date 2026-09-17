import P21.Nonsymmetric.ColorCap.DPE.Exhaustion
import P21.Nonsymmetric.ColorCap.MinimumOneProof
import P21.Nonsymmetric.SelectedExtraction

namespace P21.Nonsymmetric.ColorCap

/-- Residual-free THREE-ARM exclusion, obtained by composing the proved
MINBOX and DPE statements with the frozen reduction. -/
theorem three_arms_impossible
    (g : Generators) (s : g.Setting)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (D : HerzogCriticalData g) (colorA : Bool)
    (depth : Point) (hdepth : ∀ i, 1 ≤ depth i)
    (hcap : ∀ i, depth i < (if colorA then (D.a i : ℤ) else (D.b i : ℤ)))
    (harms : ∀ i, (if colorA then D.fA else D.fB) - depth i * g.n i ∈
      s.semigroup.PF) : False :=
  three_arms_impossible_of_residuals minimum_one_proved box_positive_exit_proved
    g s hcof D colorA depth hdepth hcap harms

end P21.Nonsymmetric.ColorCap

namespace P21.Nonsymmetric

/-- Residual-free actual color-A three-arm exclusion. -/
theorem actual_three_A_excluded_residual_free
    {g : Generators} (s : g.Setting) {F : ℤ} (D : NonsymmetricHerzogData g)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (ha : ∀ i, ∃ q, q ∈ s.semigroup.Q F ∧ IsArmA D.toHerzogCriticalData q i) : False :=
  actual_three_A_excluded ColorCap.minimum_one_proved ColorCap.box_positive_exit_proved
    s D hcof ha

/-- Residual-free actual color-B three-arm exclusion. -/
theorem actual_three_B_excluded_residual_free
    {g : Generators} (s : g.Setting) {F : ℤ} (D : NonsymmetricHerzogData g)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (ha : ∀ i, ∃ q, q ∈ s.semigroup.Q F ∧ IsArmB D.toHerzogCriticalData q i) : False :=
  actual_three_B_excluded ColorCap.minimum_one_proved ColorCap.box_positive_exit_proved
    s D hcof ha

/-- Residual-free COLOR-CAP compatibility theorem. -/
theorem actual_labels_compatible_residual_free
    {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g) (rows : FourDistinctActualQRows s F)
    (L : ActualLabeling D.toHerzogCriticalData rows) : RowLabel.Compatible L.labels :=
  actual_labels_compatible ColorCap.minimum_one_proved ColorCap.box_positive_exit_proved
    s hF hc D rows L

/-- Residual-free COLOR-CAP terminal classification. -/
theorem actual_labels_terminal_residual_free
    {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g) (rows : FourDistinctActualQRows s F)
    (L : ActualLabeling D.toHerzogCriticalData rows) : RowLabel.Terminal L.labels :=
  actual_labels_terminal ColorCap.minimum_one_proved ColorCap.box_positive_exit_proved
    s hF hc D rows L

/-- Residual-free terminal extraction for four selected actual rows. -/
theorem selected_four_terminal
    {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g) (rows : FourDistinctActualQRows s F) :
    TerminalInputExists s F D.toHerzogCriticalData rows :=
  selected_four_terminal_of_colorcap_residuals ColorCap.minimum_one_proved
    ColorCap.box_positive_exit_proved s hF hc D rows

/-- Residual-free selected-four extraction from nonsymmetry. -/
theorem nonsymmetric_selected_four
    {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hns : ¬ P21.Symmetric.SymmetricTail g) (rows : FourDistinctActualQRows s F) :
    ∃ D : NonsymmetricHerzogData g, TerminalInputExists s F D.toHerzogCriticalData rows :=
  nonsymmetric_selected_four_of_colorcap_residuals ColorCap.minimum_one_proved
    ColorCap.box_positive_exit_proved s hF hc hns rows

/-- Residual-free selected-four extraction from the cardinality lower bound. -/
theorem nonsymmetric_Q_ge_four
    {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hns : ¬ P21.Symmetric.SymmetricTail g) (hcard : 4 ≤ (s.semigroup.Q F).ncard) :
    ∃ (D : NonsymmetricHerzogData g) (rows : FourDistinctActualQRows s F),
      TerminalInputExists s F D.toHerzogCriticalData rows :=
  nonsymmetric_Q_ge_four_of_colorcap_residuals ColorCap.minimum_one_proved
    ColorCap.box_positive_exit_proved s hF hc hns hcard

end P21.Nonsymmetric
