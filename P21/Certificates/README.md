# Future static certificates

No polynomial certificate is imported into the Lean proof graph at this milestone.
The original `P21_supplement_v1.zip` is preserved under `reference_inputs/`.

| Future source | Data | Published specification |
|---|---|---|
| Appendix D.1, `fr-A4.1`, `fr-C8.4.5`–`fr-C8.4.6` | `I_FIT_POSITIVE_COEFFICIENTS.json` | 715 monomials, constant 35 |
| Appendix D.2, `fr-A4.2`, `fr-E8.4` | `TERMINAL_POSITIVITY_COEFFICIENTS.json` | 3234 monomials, degree 7, constant 63 |

The counts above are source specifications, not results of a certificate proof in
this project. A later module must prove identities and coefficient nonnegativity
from the static data. Neither source verifier output nor a coefficient count is
accepted as a substitute for a Lean theorem. See the preserved certificate map in
`source_excerpts/MANUSCRIPT_CERTIFICATE_MAP.md`.
