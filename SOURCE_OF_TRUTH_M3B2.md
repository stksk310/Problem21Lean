# M3B2 source of truth

The immutable implementation base is
`9c9a1b6f76f78a2927b12bf8a0663dfdc29ea7a1`.

The mathematical authority is the submitted manuscript
`P21_Journal_of_Algebra_Submission_Manuscript_FINAL_20260916.pdf`, Appendix
B.16--B.20. The repository navigation copy is
`verification/m3/source/appendixB-readable.md`, sections A2.6--A2.10. The
verification edition and supplement under `reference_inputs/` are supporting
navigation sources.

The authoritative formal target remains the byte-protected definition in
`P21/Nonsymmetric/ColorCap/ThreeArms.lean`:

```lean
def BoxPositiveExitStatement : Prop :=
  ∀ (D : BoxInput) (t : ℕ) (u : Point), BoxPath D.upper D.rows t D.x u →
    (∀ i, ¬ InBox D.upper (fire D.rows i u)) →
    ∃ i, ∀ j, 1 ≤ fire D.rows i u j
```

Lean declarations and kernel reports determine formal scope. Prose and
external computations do not supply theorem premises.
