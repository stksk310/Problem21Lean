# M3 statement map

The publication PDF controls the section numbers below. Full declaration
names and source positions are in `verification/m3/DECLARATIONS.json`.
`AXIOM_SUMMARY.json` in the evidence additionally inventories every generated
helper, constructor, projection and instance below `P21.Nonsymmetric`.

| Publication / requirement | Main Lean result | Scope |
|---|---|---|
| §2.2.2 positive least critical cycle | `herzog_critical_exists` | Proved from setting, tail cofiniteness and nonsymmetry |
| §2.2.2 exact two tail PF values | `herzog_classification` | Proved, exact gap/return PF predicate |
| §2.2.2 primitive generators | `nonsymmetric_herzog_primitive_exists` | Same Herzog witness plus all three primitive formulas |
| §4.1 six-arm atlas | `six_arm_atlas`, `actual_row_atlas` | Proved for actual tail gaps / Q rows |
| §4.2 actual complement bounds | `complement_antichain`, `arm_complement_pair`, `singleton_W_cap` | Proved; support inclusion only |
| §4.3 critical box | `critical_box_unique` | Proved; every coordinate strictly subcritical |
| §4.3 integer kernel basis | `integer_kernel_basis` | Proved unique integer coordinates, not just rational span |
| §4.4 corners | `corner_A_singleton_excluded`, `corner_B_singleton_excluded`, `both_corners_excluded` | Proved |
| §4.5 matched-pair package | `matched_pair_sync`, `matched_pair_data` | Proved with nonnegative, possibly zero gaps |
| §4.6–4.10 independent positive-m levels | `minimal_return_exists`, `four_return_caps`, `unequal_levels_impossible`, `equal_level_matching`, `root_free_level_rigidity` | Proved; m cancels before pure-tail criticality |
| §4.10 coexistence | `matched_pair_excludes_A_one`, `matched_pair_excludes_B_two`, `matched_pair_no_singleton` | Proved; arbitrary singleton direction |
| §4.11 same color | `same_color_complement_cases`, `actual_AA_cyclic`, `actual_BB_cyclic` | Exact two cases and actual singleton exclusions |
| §4.12 mixed colors | `mixed_right_complement_geometry`, `mixed_left_complement_geometry`, `actual_BA_excludes_middle`, `actual_AB_excludes_endpoints` | Both orientations; zero shared coefficient retained |
| §4.13 three singletons | `three_singletons_force_Q_three` | Full ambient Q has cardinality three |
| §4.14 / Appendix B color cap | `ColorCap.three_arms_impossible_of_residuals` | Conditional on exactly MINBOX and DPE |
| §4.15 finite case split | `RowLabel.four_labels_classification` | Kernel-checked compatible-label theorem |
| §4.15 actual selected rows | `actual_labels_compatible`, `actual_labels_terminal` | All compatibility facts derived, conditional only on MINBOX/DPE |
| §4.16.1 saturation | `singleton_saturation`, `singleton_saturation_last` | Proved from actual BOX-W and singleton caps |
| §4.16.2 CHAIN | `chain_exact_input`, `chain_exact_input_independent` | Exact normalized scalar extraction |
| §4.16.3 TYPE II | `typeII_exact_input` | Includes derived lambda ≤ b0 and singleton saturation |
| §4.16.4 PATH | `path_exact_input` | Both endpoint rays, positive R and exact ladder |
| Full selected-four composition | `nonsymmetric_selected_four_of_colorcap_residuals` | Any selected four actual rows; preserves their values; explicit two residuals |
| Q≥4 wrapper | `nonsymmetric_Q_ge_four_of_colorcap_residuals` | Derives selection, cofiniteness and Herzog data; explicit two residuals |

All abbreviated names in this table have prefix `P21.Nonsymmetric.`. The
normalized extraction theorems do not assume their complement identities;
they derive them from the actual row configuration. Their existence for an
arbitrary selection follows from the conditional final composition. This
distinction is preserved in the regression tests and delivery status.
