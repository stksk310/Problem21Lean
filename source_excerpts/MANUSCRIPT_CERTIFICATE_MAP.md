# Manuscript ↔ certificate map

| Manuscript location | Role | Publication artifact | Expected check |
|---|---|---|---|
| Appendix D §D.1, label `fr-A4.1`; main text `fr-C8.4.5`–`fr-C8.4.6` | Linear i-fit positivity | `coefficient_tables/I_FIT_POSITIVE_COEFFICIENTS.json` | 715 monomials, constant 35 |
| Appendix D §D.2, label `fr-A4.2`; main text `fr-E8.4`, `fr-E8.4.2`–`fr-E8.4.3` | Terminal Euclidean i-fit positivity | `coefficient_tables/TERMINAL_POSITIVITY_COEFFICIENTS.json` | 3,234 monomials, total degree 7, constant 63 |
| Appendix D §D.3–D.7 | notation, defining expressions, variable shifts, reproducibility | this supplement plus manuscript | paths/hashes and scripts agree |

The verifier scripts are retained byte-for-byte from the frozen verification edition. Each script is stored with the exact companion table path it expects, under `verification_scripts/LINEAR/` or `verification_scripts/EUCLIDEAN/`. The canonical publication copies of the tables are duplicated under `coefficient_tables/`; SHA-256 proves the duplicates are identical.
