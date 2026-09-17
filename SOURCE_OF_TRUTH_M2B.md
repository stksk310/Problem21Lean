# M2B source of truth

1. The current user specification is `verification/m2b/REQUEST.md`.
2. The authoritative frozen input is Git commit
   `a0ec51cf93326b6f8dbf22647cfeecf81a931bd8` in
   https://github.com/stksk310/Problem21Lean, including M1 and M2A.
3. Publication wording is `P21_Journal_of_Algebra_Submission_Manuscript_FINAL_20260916.pdf`,
   especially Sections 2.2.1 and 3. The unchanged text extraction remains under
   `source_excerpts/m2/publication.txt`. The manuscript source ZIP is navigation;
   the earlier frozen verification edition is provenance, not executable instructions.
4. The new public target is exactly the old
   `P21.Symmetric.SymmetricThreeGeneratorGluingStatement` definition. FullClosure
   uses its new proof followed by the frozen M2A internal theorem.
5. `verification/m2b/FROZEN_SHA256.json` records every protected file, independently
   checked against Git in CI. Dependency revisions remain those of the frozen manifest.

The authoritative source audit promotion of M2A was supplied by the user. M2B
remains a candidate for independent audit. Older candidate documents and logs
are preserved as history; new M2B reports describe the current extension.

No source manuscript, external reference or theorem citation is treated as a
Lean axiom. The new classification is established by actual Lean proof terms.
Signed Bezout relations are used for divisibility only. Every semigroup
membership construction retains nonnegative actual coefficient witnesses.
