# M3A nonsymmetric local geometry candidate

**Reduced scope under the user's request §37. STD_HERZOG is proved.
STD_WHITE / MINBOX and unconditional COLOR-CAP remain OPEN. FULL G4 is OPEN.**

This branch adds only new mathematical modules under `P21/Nonsymmetric`.
All 49 preexisting Lean files and the original M2A/M2B verification sources
are protected by a 103-file byte baseline at commit
`9a9e01c401a934cfca2da15026986b0ecf83ff4f`.

The proved core includes primitive generator formulas and the exact two tail pseudo-Frobenius elements,
six-arm atlas, actual complement critical boxes, saturated integer kernel,
singleton caps and full-Q three-singleton collapse, matched-pair depth and
independently minimized positive-m-level synchronization, same/mixed-color
geometry, genuine relabeling, and exact normalized PATH/TYPE II/CHAIN inputs.
No terminal exclusion from Sections 5–10 is imported or asserted.

Appendix B is partially formalized. The two remaining obligations are actual
Lean propositions, not axioms or fields claiming a theorem:

- `P21.Nonsymmetric.ColorCap.MinimumOneStatement`
- `P21.Nonsymmetric.ColorCap.BoxPositiveExitStatement`

`three_arms_impossible_of_residuals` proves the both-color reduction with these
two hypotheses visibly present. See `M3_EXTERNAL_INPUT_REPORT.md` for the exact
gap and `M3_STATEMENT_MAP.md` for theorem-level scope. The compatible-label
finite case split is kernel checked. Its actual-row integration and exact
terminal extraction are proved end to end by
`nonsymmetric_selected_four_of_colorcap_residuals`, with precisely those two
remaining mathematical inputs. This is a conditional classification; it does
not close unconditional G4.

## Reproduce

Use the unchanged `lean-toolchain` and `lake-manifest.json`.

```text
python3 verification/m3/verify.py --fresh
python3 ci/m3_audit.py suite
```

The first command requires an empty project `.lake/build`, builds the root,
every frozen module and every M3 module, checks all namespace declarations'
kernel axioms, and runs exact statement regressions. The second runs the
unmodified M1, M2A and M2B suites in three separate archived source copies;
only pinned third-party dependencies are shared.

GitHub workflow `P21 Lean M3 Audit` performs clean Linux verification, compares
all executable sources with both the ZIP and exact Git commit, and publishes
`P21_M3_TRUE_AUDIT_EVIDENCE`. This is reproducibility evidence for a candidate,
not an independent audit ruling. Final run identifiers and artifact digest
are recorded in the separate post-run `HANDOFF_RECEIPT_M3.json`.
