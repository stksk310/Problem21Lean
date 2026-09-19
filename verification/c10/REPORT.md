# C10 Euclidean Descent Verification Report

The C10 implementation closes the terminal SAME-W replacement, the nonterminal Euclidean color exchange, strong induction over the type-changing state, and the full CHAIN integration through the nonsymmetric selected-four and `Q≥4` wrappers.

Public closure declarations:

- `P21.Nonsymmetric.EuclideanState.f_mem`
- `P21.Nonsymmetric.EuclideanSeed.impossible`
- `P21.Nonsymmetric.ChainCore.impossible`
- `P21.Nonsymmetric.ChainInput.impossible`
- `P21.Nonsymmetric.selected_terminal_after_chain_impossible`
- `P21.Nonsymmetric.terminal_input_after_chain_impossible`
- `P21.Nonsymmetric.nonsymmetric_selected_four_impossible_after_chain`
- `P21.Nonsymmetric.nonsymmetric_Q_ge_four_impossible_after_chain`

The local gate is `powershell -File verification/c10/verify.ps1`. It checks the frozen source manifest rooted at C9 commit `50d65c7982aebe67856cb85e81771d0452d62fec`, regenerates the 3234-term certificate in memory, rejects proof-debt tokens and reverse dependencies, builds the root, runs all C10 gates and axiom reports, and runs the M1/M2A/M2B/M3A/M3B1/M3B2/P5/T6/C7/C8/C9 regression entrypoints.

The only inherited axioms permitted by the project audit are `propext`, `Classical.choice`, and `Quot.sound`. The final local and GitHub run identifiers are recorded with the delivery evidence after CI completes.

Local full verification on 2026-09-20: **PASS**. All eight C10 gates and all eleven historical regression entrypoints completed with exit code 0; the axiom report listed only the three permitted inherited axioms.
