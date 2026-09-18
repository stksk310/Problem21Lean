import P21.Nonsymmetric.Path.Integration

-- Frozen input and actual provenance gates.
#check P21.Nonsymmetric.PathInput
#check P21.Nonsymmetric.PathInput.ActualReturn.factorization
#check P21.Nonsymmetric.PathInput.Pair.equationA
#check P21.Nonsymmetric.PathInput.Pair.equationB
#check P21.Nonsymmetric.PathInput.no_pair_normalization
#check P21.Nonsymmetric.PathInput.reverse

-- Signed-root and strictly decreasing normalization gates.
#check P21.Nonsymmetric.PathInput.WeakRoot.equation
#check P21.Nonsymmetric.PathInput.WeakRoot.step
#check P21.Nonsymmetric.PathInput.WeakRoot.step_measure
#check P21.Nonsymmetric.PathInput.WeakRoot.normalize
#check P21.Nonsymmetric.PathInput.NormalizedRoot.endpoint_level_two
#check P21.Nonsymmetric.PathInput.NormalizedRoot.F_absorption

-- PFREE sign, unit, FIX-J, PIN, and opposite endpoint gates.
#check P21.Nonsymmetric.PathInput.PFreeI.right_i_equation
#check P21.Nonsymmetric.PathInput.PFreeI.right_j_equation
#check P21.Nonsymmetric.PathInput.PFreeI.i_fabs
#check P21.Nonsymmetric.PathInput.PFreeI.j_fabs
#check P21.Nonsymmetric.PathInput.PFreeI.u_cert
#check P21.Nonsymmetric.PathInput.PFreeI.x_cert
#check P21.Nonsymmetric.PathInput.PFreeI.F0_pos
#check P21.Nonsymmetric.PathInput.PFreeI.left_j_caps
#check P21.Nonsymmetric.PathInput.PFreeI.fix_j
#check P21.Nonsymmetric.PathInput.PFreeI.unit_eq
#check P21.Nonsymmetric.PathInput.PFreeI.pin
#check P21.Nonsymmetric.PathInput.PFreeI.roots
#check P21.Nonsymmetric.PathInput.PFreeI.impossible

-- Exhaustion, formal dual transport, and selected-value preservation gates.
#check P21.Nonsymmetric.PathInput.pair_or_pfree_or_dual
#check P21.Nonsymmetric.PathInput.impossible
#check P21.Nonsymmetric.SelectedTerminalAfterPath
#check P21.Nonsymmetric.TerminalInputAfterPath
#check P21.Nonsymmetric.terminal_input_after_path
#check P21.Nonsymmetric.nonsymmetric_selected_four_after_path
#check P21.Nonsymmetric.nonsymmetric_Q_ge_four_after_path
