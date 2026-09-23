# Section 11 final statement map

| Section 11 step | Lean declaration | Frozen input |
|---|---|---|
| Exclude `Q(F)` cardinality at least four | `P21.q_ge_four_impossible` | `P21.Symmetric.symmetric_tail_type_le_four`; `P21.Nonsymmetric.nonsymmetric_Q_ge_four_impossible_after_chain` |
| Bound `Q(F)` by three | `P21.q_card_le_three` | `P21.q_ge_four_impossible` |
| Convert the `Q(F)` bound to type at most four | `P21.type_le_four` | `P21.NumericalSemigroup.type_eq_q_card_add_one` |
| Prove the publication target | `P21.main_theorem : P21MainStatement` | `P21.type_le_four` |

The symmetric branch uses the frozen direct type bound. The nonsymmetric branch receives the monotone hypothesis `4 ≤ (s.semigroup.Q F).ncard` exactly as exposed by C10. No firing order, exact-cardinality assumption, or new branch mathematics is introduced here.

