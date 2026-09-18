import P21.Nonsymmetric.TypeII.Integration

namespace P21.Nonsymmetric

-- The main theorem has only the exact frozen input and Frobenius hypothesis.
example {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    (T : TypeIIInput s F D) (hF : s.semigroup.IsFrobenius F) : False :=
  T.impossible hF

-- Actual return provenance retains the full nonnegative factorization,
-- returned-direction zero, and positive m-level.
#check PathInput.ActualReturn.factorization
#check PathInput.ActualReturn.direction_zero
#check PathInput.ActualReturn.level_pos
#check TypeIIInput.singleton_n1_return
#check TypeIIInput.singleton_n2_return

-- Signed identities remain equations; membership is supplied separately.
#check TypeIIInput.JR
#check TypeIIInput.KR
#check TypeIIInput.actual_of_coordinates

-- Every sign region and both uniform caps have named gates.
#check TypeIIInput.cap_of_eta_pos
#check TypeIIInput.cap_of_theta_pos
#check TypeIIInput.cap_zero_zero
#check TypeIIInput.impossible_eta_zero_theta_neg
#check TypeIIInput.impossible_theta_zero_eta_neg
#check TypeIIInput.impossible_eta_theta_neg
#check TypeIIInput.uniform_i_cap

-- Criticality is downstream of the pure-H equal-level relation only.
#check TypeIIInput.equal_level_relation
#check TypeIIInput.impossible_equal_levels
#check TypeIIInput.ABS_L
#check TypeIIInput.ABS_R

-- The terminal proposition contains CHAIN only and preserves selected values.
example {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    {rows : FourDistinctActualQRows s F}
    (h : SelectedTerminalAfterTypeII s F D rows) :
    ∃ C : ChainInput s F D, C.values = selectedValues rows := h

#check terminal_input_after_typeII
#check nonsymmetric_selected_four_after_typeII
#check nonsymmetric_Q_ge_four_after_typeII

end P21.Nonsymmetric
