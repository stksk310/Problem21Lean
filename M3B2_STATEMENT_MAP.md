# M3B2 statement map

| Publication/interface | Lean declaration | Scope |
|---|---|---|
| Chronological firing data | `ColorCap.FiringTrace`, `BoxPath.exists_trace` | Trace reconstructs the actual endpoint and every prefix state |
| START / proper predecessor | `FiringTrace.head_zero`, `properNonzeroPredecessors` | Derived after genuine cyclic rotation of the first firing |
| Successful PREFIX and LR/ELR | declarations in `SuccessfulPrefix`, `ChronologicalPrefix` | Actual successful crossings only |
| Shifted-gap actuality | declarations in `TraceSuccessfulPrefix`, `ReciprocalRank` | Dual residues map back to actual original prefixes; explicit `K_s = 1` run |
| B.16 | `one_color_trace_sink_impossible` | Frozen one-color exclusion reused |
| B.17 | `two_color12_trace_sink_impossible` | Full `{1,2}` exhaustion, including `X = 0` and predecessor/PREFIX |
| B.18 | `two_color13_trace_sink_impossible` | Independent `{1,3}` exhaustion |
| B.19 | `first_third_12_to_3_actual_impossible`, `first_third_13_to_2_actual_impossible`, `first_third_color_actual_impossible` | First third color taken from the actual trace |
| B.20 | `canonical_trace_sink_impossible` | One/two/three-color exhaustion |
| Exact DPE | `box_positive_exit_proved` | Original `BoxPositiveExitStatement`, zero extra assumptions |
| THREE-ARM | `three_arms_impossible` | Frozen MINBOX and proved DPE composed |
| COLOR-CAP | `actual_labels_compatible_residual_free`, `actual_labels_terminal_residual_free` | Residual-free actual label classification |
| Selected four | `selected_four_terminal`, `nonsymmetric_selected_four`, `nonsymmetric_Q_ge_four` | Residual-free terminal input extraction |

`verification/m3b2/DECLARATIONS.json` is the complete public declaration
inventory for new M3B2 mathematical modules.
