# M3B1 sources and immutable base

Base commit: `258d74ac941796c62bb45cc177f22a7396319413`.
The user authorizes treating this M3A state as the immutable starting point.
The agent does not issue a new independent audit determination.

1. Publication PDF:
   `reference_inputs/P21_Journal_of_Algebra_Submission_Manuscript_FINAL_20260916.pdf`
   (at the parent workspace). SHA256:
   `40f128453206c54800a5e3df1ec18a945a5a0836469df1de2fac9fb307354346`.
   Appendix B.1-B.7; PDF pages 80-83 (printed 79-82) were rendered and checked
   for the socle matrices, LAT/AGE/Z, BA/AP and BB/BP equations.
2. Verification-edition ZIP:
   `reference_inputs/P21_FINAL_FROZEN_VERIFICATION_EDITION_20260907.zip`.
   SHA256: `f98436c59bf735444e75cc0a133a8ac128ba7c69c049e97da9593a3aeab64bc8`.
   Relevant member: `APPENDICES/A2_COLOR_CAP.md` under its archive root.
3. Preserved readable excerpts:
   `verification/m3/source/appendixB-readable.md` and `frozen-color-cap.md`.
4. Corrected scope: `verification/m3/REVIEW_CORRECTION_MINBOX.md` and the
   unchanged `ColorCap/Residuals.lean` definition. Tail cofiniteness is essential.
5. White proof strategy: Khan and Rogers, *An Exposition of White's
   Characterization of Empty Lattice Tetrahedra*,
   <https://arxiv.org/abs/1610.01981>. The finite floor-jump support argument is
   proved symbolically in Lean; the citation is not a logical dependency.

Exact PDF/ZIP hashes and extracted PDF page text are in
`verification/m3b1/SOURCE_CHECK.json`. Pinned mathlib search and source
comparison are in `MATHLIB_WHITE_SEARCH.md`. Lean types and kernel evidence
control what is formally proved; no prose citation supplies a proof term.
