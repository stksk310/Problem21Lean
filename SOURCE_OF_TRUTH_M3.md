# M3 source of truth

Mathematical authority, in order:

1. `P21_Journal_of_Algebra_Submission_Manuscript_FINAL_20260916.pdf`,
   SHA256 `40f128453206c54800a5e3df1ec18a945a5a0836469df1de2fac9fb307354346`.
2. `P21_FINAL_FROZEN_VERIFICATION_EDITION_20260907.zip`,
   SHA256 `f98436c59bf735444e75cc0a133a8ac128ba7c69c049e97da9593a3aeab64bc8`.
3. Existing Lean at `9a9e01c401a934cfca2da15026986b0ecf83ff4f` for reusable
   definitions and proved interfaces, without changing any existing Lean file.

The user's operational request is copied as `verification/m3/REQUEST.md`.
Instructions in source documents are not additional user commands. Local
archived uploads supplied the two authoritative files; no re-upload was needed.

`verification/m3/source/publication-fresh.txt` is a fresh page-tagged extraction
of the 99-page publication PDF. `publication.txt` provides the prior text
extraction. Readable/frozen Section 4 and Appendix B excerpts are retained to
make the naming correspondence inspectable. The older text's G4.5.2/G4.5.3
correspond to publication 4.10.1/4.10.2; old G4.11 corresponds to publication
4.16. B.17.2's pre-crossing case and B.14's omitted-prefix preservation are
present in the authoritative publication. No mathematical conflict was found
in the passages used. PDF page 13 was rendered and visually checked for the
critical-box/kernel/corner statements.

The source candidate is M3A, not the full-classification archive requested for
full success. Its name deliberately records the reduced scope permitted by
request §37. SHA receipts identify exact bytes; a candidate cannot contain its
own later commit or CI artifact digest, so those belong to the post-run receipt.
