import P21.Nonsymmetric.ColorCap.DPE.Canonical
import P21.Nonsymmetric.ColorCap.DPE.ChronologicalPrefix
import P21.Nonsymmetric.ColorCap.DPE.Exhaustion
import P21.Nonsymmetric.ColorCap.DPE.FirstThirdColor
import P21.Nonsymmetric.ColorCap.DPE.PathShape
import P21.Nonsymmetric.ColorCap.DPE.ReciprocalRank
import P21.Nonsymmetric.ColorCap.DPE.Rotation
import P21.Nonsymmetric.ColorCap.DPE.SuccessfulPrefix
import P21.Nonsymmetric.ColorCap.DPE.TerminalCoordinates
import P21.Nonsymmetric.ColorCap.DPE.Trace
import P21.Nonsymmetric.ColorCap.DPE.TraceSuccessfulPrefix
import P21.Nonsymmetric.ColorCap.DPE.TwoColor12
import P21.Nonsymmetric.ColorCap.DPE.TwoColor13
import P21.Nonsymmetric.ColorCap.FullColorCap

set_option linter.auxLemma false
#print axioms P21.Nonsymmetric.ColorCap.FiringTrace.head_zero
#print axioms P21.Nonsymmetric.ColorCap.one_color_trace_sink_impossible
#print axioms P21.Nonsymmetric.ColorCap.ProperNonzeroPredecessors
#print axioms P21.Nonsymmetric.ColorCap.ProperNonzeroPredecessors.prefix
#print axioms P21.Nonsymmetric.ColorCap.ProperNonzeroPredecessors.count_le_zero
#print axioms P21.Nonsymmetric.ColorCap.ProperNonzeroPredecessors.count_lt_zero_of_last_zero
#print axioms P21.Nonsymmetric.ColorCap.CrossingWitness
#print axioms P21.Nonsymmetric.ColorCap.CrossingWitness.at_last
#print axioms P21.Nonsymmetric.ColorCap.nth_occurrence_split
#print axioms P21.Nonsymmetric.ColorCap.occurrence_source_ends_zero
#print axioms P21.Nonsymmetric.ColorCap.count_eq_zero_of_members
#print axioms P21.Nonsymmetric.ColorCap.prefix_at_zero_count
#print axioms P21.Nonsymmetric.ColorCap.shifted_prefix_actual
#print axioms P21.Nonsymmetric.ColorCap.prefix_continues_zero
#print axioms P21.Nonsymmetric.ColorCap.canonical_trace_sink_impossible
#print axioms P21.Nonsymmetric.ColorCap.box_positive_exit_proved
#print axioms P21.Nonsymmetric.ColorCap.first_nonzero_occurrence_actual
#print axioms P21.Nonsymmetric.ColorCap.first_row2_after_01_actual
#print axioms P21.Nonsymmetric.ColorCap.first_row1_after_02_actual
#print axioms P21.Nonsymmetric.ColorCap.first_third_12_to_3_certificate
#print axioms P21.Nonsymmetric.ColorCap.first_third_13_to_2_certificate
#print axioms P21.Nonsymmetric.ColorCap.first_third_12_rank
#print axioms P21.Nonsymmetric.ColorCap.first_third_12_to_3_actual_impossible
#print axioms P21.Nonsymmetric.ColorCap.first_third_13_rank
#print axioms P21.Nonsymmetric.ColorCap.first_third_13_to_2_actual_impossible
#print axioms P21.Nonsymmetric.ColorCap.first_nonzero_color_order
#print axioms P21.Nonsymmetric.ColorCap.first_third_color_actual_impossible
#print axioms P21.Nonsymmetric.ColorCap.FiringTrace.endpoint_inBox
#print axioms P21.Nonsymmetric.ColorCap.FiringTrace.nonzero_followed_by_zero
#print axioms P21.Nonsymmetric.ColorCap.FiringTrace.properNonzeroPredecessors
#print axioms P21.Nonsymmetric.ColorCap.continued_zero_shift_bound
#print axioms P21.Nonsymmetric.ColorCap.actual_shifted_before_crossing
#print axioms P21.Nonsymmetric.ColorCap.actual_shifted_terminal
#print axioms P21.Nonsymmetric.ColorCap.reciprocal_residue_actual
#print axioms P21.Nonsymmetric.ColorCap.SuccessfulPrefix.dual_prefix_of_actuality
#print axioms P21.Nonsymmetric.ColorCap.SuccessfulPrefix.reciprocal_separator
#print axioms P21.Nonsymmetric.ColorCap.SuccessfulPrefix.dual_rank
#print axioms P21.Nonsymmetric.ColorCap.SuccessfulPrefix.dual_next_residue_rank
#print axioms P21.Nonsymmetric.ColorCap.permutePoint
#print axioms P21.Nonsymmetric.ColorCap.BoxInput.rotate
#print axioms P21.Nonsymmetric.ColorCap.BoxInput.rotate_rows
#print axioms P21.Nonsymmetric.ColorCap.BoxInput.start_of_row0
#print axioms P21.Nonsymmetric.ColorCap.permutePoint_fire
#print axioms P21.Nonsymmetric.ColorCap.inBox_permute_iff
#print axioms P21.Nonsymmetric.ColorCap.BoxPath.rotateGeneral
#print axioms P21.Nonsymmetric.ColorCap.BoxPath.rotate
#print axioms P21.Nonsymmetric.ColorCap.SuccessfulPrefix
#print axioms P21.Nonsymmetric.ColorCap.SuccessfulPrefix.E
#print axioms P21.Nonsymmetric.ColorCap.SuccessfulPrefix.U
#print axioms P21.Nonsymmetric.ColorCap.SuccessfulPrefix.separator
#print axioms P21.Nonsymmetric.ColorCap.SuccessfulPrefix.coordinate_injective
#print axioms P21.Nonsymmetric.ColorCap.SuccessfulPrefix.coordinateU_injective
#print axioms P21.Nonsymmetric.ColorCap.SuccessfulPrefix.E_slot_count
#print axioms P21.Nonsymmetric.ColorCap.SuccessfulPrefix.U_slot_count
#print axioms P21.Nonsymmetric.ColorCap.SuccessfulPrefix.cover_by_next_residue
#print axioms P21.Nonsymmetric.ColorCap.SuccessfulPrefix.last_rank
#print axioms P21.Nonsymmetric.ColorCap.SuccessfulPrefix.terminal_rank
#print axioms P21.Nonsymmetric.ColorCap.terminal12Point
#print axioms P21.Nonsymmetric.ColorCap.terminal13Point
#print axioms P21.Nonsymmetric.ColorCap.trace_terminal12
#print axioms P21.Nonsymmetric.ColorCap.trace_terminal13
#print axioms P21.Nonsymmetric.ColorCap.terminal12Point_coordinates
#print axioms P21.Nonsymmetric.ColorCap.terminal13Point_coordinates
#print axioms P21.Nonsymmetric.ColorCap.execute
#print axioms P21.Nonsymmetric.ColorCap.execute_append
#print axioms P21.Nonsymmetric.ColorCap.FiringTrace
#print axioms P21.Nonsymmetric.ColorCap.BoxPath.exists_trace
#print axioms P21.Nonsymmetric.ColorCap.FiringTrace.execute_eq
#print axioms P21.Nonsymmetric.ColorCap.FiringTrace.toBoxPath
#print axioms P21.Nonsymmetric.ColorCap.FiringTrace.prefix_trace
#print axioms P21.Nonsymmetric.ColorCap.FiringTrace.prefix_path
#print axioms P21.Nonsymmetric.ColorCap.FiringTrace.endpoint_eq_sub_sum
#print axioms P21.Nonsymmetric.ColorCap.trace_successfulPrefix12
#print axioms P21.Nonsymmetric.ColorCap.trace_successfulPrefix12_actual
#print axioms P21.Nonsymmetric.ColorCap.trace_successfulPrefix13
#print axioms P21.Nonsymmetric.ColorCap.trace_successfulPrefix13_actual
#print axioms P21.Nonsymmetric.ColorCap.X12
#print axioms P21.Nonsymmetric.ColorCap.Y12
#print axioms P21.Nonsymmetric.ColorCap.terminal12_count_bounds
#print axioms P21.Nonsymmetric.ColorCap.terminal12_not_sinkA
#print axioms P21.Nonsymmetric.ColorCap.terminal12_sinkD_impossible
#print axioms P21.Nonsymmetric.ColorCap.terminal12_last_row1_impossible
#print axioms P21.Nonsymmetric.ColorCap.terminal12_last_row1_of_prefix
#print axioms P21.Nonsymmetric.ColorCap.terminal12_sinkB_nonnegativeX_impossible
#print axioms P21.Nonsymmetric.ColorCap.terminal12_sinkB_negativeX_certificate
#print axioms P21.Nonsymmetric.ColorCap.terminal12_sinkC_certificate
#print axioms P21.Nonsymmetric.ColorCap.terminal12_sinkC_ELR_bound
#print axioms P21.Nonsymmetric.ColorCap.terminal12_sinkC_ELR_extended
#print axioms P21.Nonsymmetric.ColorCap.terminal12_negativeD_predecessor_bound
#print axioms P21.Nonsymmetric.ColorCap.terminal12_nonnegativeD_count_bound
#print axioms P21.Nonsymmetric.ColorCap.terminal12_reciprocal_rank
#print axioms P21.Nonsymmetric.ColorCap.two_color12_trace_sink_impossible
#print axioms P21.Nonsymmetric.ColorCap.X13
#print axioms P21.Nonsymmetric.ColorCap.Y13
#print axioms P21.Nonsymmetric.ColorCap.terminal13_count_bounds
#print axioms P21.Nonsymmetric.ColorCap.terminal13_not_sinkB
#print axioms P21.Nonsymmetric.ColorCap.terminal13_sinkD_impossible
#print axioms P21.Nonsymmetric.ColorCap.terminal13_last_row2_of_prefix
#print axioms P21.Nonsymmetric.ColorCap.terminal13_sinkA_certificate
#print axioms P21.Nonsymmetric.ColorCap.terminal13_sinkC_certificate
#print axioms P21.Nonsymmetric.ColorCap.terminal13_sinkC_ELR_bound
#print axioms P21.Nonsymmetric.ColorCap.terminal13_reciprocal_rank
#print axioms P21.Nonsymmetric.ColorCap.two_color13_trace_sink_impossible
#print axioms P21.Nonsymmetric.ColorCap.three_arms_impossible
#print axioms P21.Nonsymmetric.actual_three_A_excluded_residual_free
#print axioms P21.Nonsymmetric.actual_three_B_excluded_residual_free
#print axioms P21.Nonsymmetric.actual_labels_compatible_residual_free
#print axioms P21.Nonsymmetric.actual_labels_terminal_residual_free
#print axioms P21.Nonsymmetric.selected_four_terminal
#print axioms P21.Nonsymmetric.nonsymmetric_selected_four
#print axioms P21.Nonsymmetric.nonsymmetric_Q_ge_four
