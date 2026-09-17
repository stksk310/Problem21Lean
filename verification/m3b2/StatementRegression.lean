import P21.Nonsymmetric.ColorCap.FullColorCap

open P21 P21.Nonsymmetric P21.Nonsymmetric.ColorCap

-- The authoritative frozen statement is used without an added hypothesis.
example : BoxPositiveExitStatement := box_positive_exit_proved

-- MINBOX and DPE have disappeared from the THREE-ARM interface.
example (g : Generators) (s : g.Setting)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (D : HerzogCriticalData g) (colorA : Bool)
    (depth : Point) (hdepth : ∀ i, 1 ≤ depth i)
    (hcap : ∀ i, depth i < (if colorA then (D.a i : ℤ) else (D.b i : ℤ)))
    (harms : ∀ i, (if colorA then D.fA else D.fB) - depth i * g.n i ∈
      s.semigroup.PF) : False :=
  three_arms_impossible g s hcof D colorA depth hdepth hcap harms

#check actual_labels_terminal_residual_free
#check selected_four_terminal
#check nonsymmetric_selected_four
#check nonsymmetric_Q_ge_four

#print BoxPositiveExitStatement
#print axioms box_positive_exit_proved
#print axioms three_arms_impossible
#print axioms actual_labels_terminal_residual_free
#print axioms nonsymmetric_Q_ge_four
