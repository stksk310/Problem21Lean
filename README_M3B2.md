# M3B2 DPE / ColorCap

This milestone proves the existing `BoxPositiveExitStatement` with no added
mathematical hypothesis:

```lean
P21.Nonsymmetric.ColorCap.box_positive_exit_proved :
  P21.Nonsymmetric.ColorCap.BoxPositiveExitStatement
```

The proof follows Appendix B.16--B.20 on an actual chronological `FiringTrace`.
It includes shifted-gap actuality (including `K_s = 1` without a fictitious
crossing), the complete `{1,2}` and `{1,3}` terminal cases, both first-third
color orientations, and cyclic normalization of the actual first firing.

`FullColorCap.lean` composes this theorem with the frozen
`minimum_one_proved`. Its THREE-ARM, actual COLOR-CAP, and selected-four
terminal extraction wrappers no longer take MINBOX or DPE hypotheses. This
does not prove FULL G4 or the later terminal branch exclusions.

All 87 mathematical Lean files present at base
`9c9a1b6f76f78a2927b12bf8a0663dfdc29ea7a1` are byte protected. M3B2 adds 14
mathematical modules and does not edit an old one.

Reproduce from an empty `.lake/build` with:

```text
python3 verification/m3b2/verify.py --fresh
python3 ci/m3b2_audit.py suite
```

The GitHub workflow is `.github/workflows/m3b2-audit.yml`; its evidence
artifact is named `P21_M3B2_TRUE_AUDIT_EVIDENCE`.
