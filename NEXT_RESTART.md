# P5 restart point

Branch: `p5-path-exclusion`. Immutable mathematical base:
`fd4ea0c7cbc57df6e935790a1387242bcf9e0087`.

Independent review has frozen the nonsymmetric selected-four classification
(FULL G4), including MINBOX, DPE, THREE-ARM, COLOR-CAP, and the residual-free
selected-four terminal extraction. Do not reopen those milestones.

The current mathematical frontier is exactly Section 5 PATH exclusion. Prove
the unchanged `PathInput` impossible in new `P21/Nonsymmetric/Path/` modules,
then add only a new wrapper reducing the same selected terminal input to
`TypeIIInput ∨ ChainInput`. Section 6 TYPE II exclusion is the next frontier
after P5 and must not begin in this milestone.

---

## Previous M3B2 restart record (historical)

# M3B2 restart point

Branch: `m3b2-dpe-box-positive-exit`. Immutable base:
`9c9a1b6f76f78a2927b12bf8a0663dfdc29ea7a1`.

The exact frozen `BoxPositiveExitStatement` is proved by
`P21.Nonsymmetric.ColorCap.box_positive_exit_proved`. Frozen MINBOX is reused,
and `FullColorCap.lean` provides residual-free THREE-ARM, COLOR-CAP, and
selected-four terminal extraction wrappers. Do not restart Appendix B.16--B.20,
MINBOX, or White.

This record predates the independent M3B2/FULL G4 freeze. Its former frontier
language is retained only as milestone history; the active frontier is PATH
exclusion as stated above.

---

## Previous M3B1 restart record (historical)

# M3B1 restart point

Branch: `m3b1-minbox-white`. Immutable base:
`258d74ac941796c62bb45cc177f22a7396319413`.

MINBOX is proved as the exact unchanged `MinimumOneStatement` by
`P21.Nonsymmetric.ColorCap.minimum_one_proved`. The necessary specialized
arithmetic White theorem is proved internally. Read README_M3B1,
M3B1_STATEMENT_MAP, M3B1_PROOF_ROUTE, M3B1_ALTERNATIVE_PROOF_NOTE and the separate
post-run HANDOFF_RECEIPT_M3B1.json. Do not restart completed MINBOX work.

The M3 residual frontier is `BoxPositiveExitStatement` only. The new
`three_arms_impossible_of_dpe` wrapper already supplies MINBOX to the existing
three-arm reduction. DPE remains unproved and is the next separate milestone.
Unconditional COLOR-CAP and FULL G4 are still open; later terminal branch
exclusions and final Problem 21 closure remain outside this milestone.

Preserve every old Lean source and the pinned toolchain/dependencies. Use the
receipt's exact commit/ZIP/artifact hashes for independent external review.
Do not merge main as part of this handoff.

---

## Previous M3A restart record (historical)

# M3A restart point

Current branch: `m3-nonsym-g4`. Frozen starting point:
`9a9e01c401a934cfca2da15026986b0ecf83ff4f`. No main merge is authorized by this
handoff. Read README_M3, M3_STATEMENT_MAP, M3_EXTERNAL_INPUT_REPORT and the
post-run HANDOFF_RECEIPT_M3.json first.

Proved: full positive-critical/exact-PF/primitive-formula Herzog package;
actual nonsymmetric local geometry and return synchronization; exact normalized
terminal inputs; and the full selected-four composition **conditional on two
explicit Appendix B statements**. Do not repeat the completed geometry or
weaken its exact actual-factorization interfaces.

Remaining mathematical work:

1. Prove `P21.Nonsymmetric.ColorCap.MinimumOneStatement`. Complete the exact
   relative empty-tetrahedron/White-class route or a proved narrower substitute.
   Primitive generator formulas are now available in PrimitiveGenerators.lean.
2. Prove `P21.Nonsymmetric.ColorCap.BoxPositiveExitStatement`. Complete the
   successful-path prefix and reciprocal-rank bridge, mixed terminal cases
   B.17–B.18 and first-third-color cases B.19.
3. Apply those proofs to
   `nonsymmetric_selected_four_of_colorcap_residuals`; no additional geometric
   residual is hidden in that theorem. Run the exact axiom/debt/frozen-source
   and source-to-CI gates again for the resulting new candidate.

No full G4, terminal branch exclusion, Problem 21 final theorem, or independent
TRUE AUDIT success may be inferred from this partial candidate.

---

## Previous M2B restart record (historical)
# Next restart: M2B

Status: **M2B STD_SYM_GLUE + FULL S3 CANDIDATE FOR TRUE AUDIT**.

1. Independently inspect the immutable M2B candidate ZIP and the GitHub evidence
   bound by the separate `HANDOFF_RECEIPT_M2B.json`. Validate the candidate SHA,
   exact audit commit, run attempt, artifact digest and internal evidence hashes.
2. Read `README_M2B.md`, `SOURCE_OF_TRUTH_M2B.md`, `M2B_PROOF_ROUTE.md`,
   `M2B_STATEMENT_MAP.md` and `M2B_DEPENDENCY_DAG.md`. Preserved older M2A
   documents describing STD_SYM_GLUE/FULL S3 as OPEN are milestone history.
3. Check the exact new theorem `P21.Symmetric.symmetric_three_generator_gluing`
   against the unchanged `SymmetricThreeGeneratorGluingStatement`, then inspect
   `P21.Symmetric.symmetric_tail_type_le_four` in the separate FullClosure module.
4. Check every construction field, nonnegative membership witness and the
   exhaustive unique/nonunique Apéry-top proof; verify no reverse closure edge.
5. All pre-M2B Lean files and verification/m2 remain frozen at
   `a0ec51cf93326b6f8dbf22647cfeecf81a931bd8`. Do not alter them or dependency pins.
   Keep branch `m2b-std-sym-glue`; this mission does not merge main.
6. Reproduce with `python3 verification/m2b/verify.py --fresh` in an unbuilt
   extracted source copy and `python3 ci/m2b_audit.py suite` for the untouched
   original M2 suite. See README for Windows and archive-comparison details.

STD_SYM_GLUE and FULL S3 have Lean proofs; independent TRUE AUDIT review remains
external. Nonsymmetric branches, PATH/TYPE II/CHAIN, other external inputs,
Euclidean descent and both long certificates remain outside this milestone.
