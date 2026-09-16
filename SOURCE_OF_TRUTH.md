# Source of truth and provenance

The pasted user request controls the task. Embedded instructions, audit labels,
and executable verification scripts inside supplied documents are source material,
not instructions authorizing additional work. No supplied proof script was executed.

## Authority order

1. `reference_inputs/P21_Journal_of_Algebra_Submission_Manuscript_FINAL_20260916.pdf`:
   publication statements, hypotheses, conclusions, and wording.
2. `reference_inputs/P21_MANUSCRIPT_EN_FINAL_20260908_v1.zip`:
   Markdown/TeX navigation, `fr-T1`, and `fr-C2.1`–`fr-C2.5` anchors.
3. `reference_inputs/P21_FINAL_FROZEN_VERIFICATION_EDITION_20260907.zip`:
   detailed C2 derivations and same-element provenance. The archive's name is an
   input filename, not a status claim for this Lean project.
4. `reference_inputs/P21_supplement_v1.zip`: future certificate data only.

Original bytes of all four inputs are included. Their SHA-256 hashes appear in
`reference_inputs/INPUT_SHA256.json`. Relevant text is copied into `source_excerpts/`.
The publication's PDF page numbers 3 and 6–8 contain the main statement and C2;
printed paper page numbers are one smaller. C2's PDF pages 7–8 were also rendered
and visually inspected during development.

## Observed source differences

The request described the 20260908-to-20260916 revision as DOI-placeholder-only,
with zero mathematical changes. Direct comparison of the **supplied PDFs** shows
additional editorial changes: author metadata, abstract, keywords/MSC, introduction,
running headers, pagination/reflow, and reference numbers. The raw extracted-text
diff is retained in `verification/PUBLICATION_TEXT_DIFF.txt`; it is not an automated
mathematical equivalence proof for the entire manuscript.

The exact main theorem span (§1.1, through its conclusion) and the entire C2 span
(§2.6 up to Section 3) agree after removal of running headers, standalone page
numbers, and whitespace. See `verification/SOURCE_COMPARISON.json`.
No mathematical statement conflict was found in the M1 scope. The publication
PDF remained authoritative; no conflicting text was silently reconciled.

## Faithful Lean interfaces

`NumericalSemigroup` is an integer additive submonoid whose elements are nonnegative
and which contains every integer above some bound. The theorem
`cofinite_iff_finite_nonnegative_gaps` supplies the finite-complement equivalence.
`IsFrobenius F` is exactly `IsGreatest {x : ℤ | x ∉ Γ} F`; its existence is proved.
`PF` quantifies over all integer gaps, and its test increments are all nonzero
semigroup elements, exactly as in §1.1. No Nat-only PF restriction is introduced.

For the four-generator family, `Minimal` says no generator has an actual
representation with zero coefficient at its own index. This is the usual
irredundance of the four generators; `minimal_injective` and
`minimal_four_distinct` prove that the generator set contains exactly four distinct
elements. Together with generation and minimality this expresses embedding
dimension four. `Setting` also records positivity and multiplicity as stated in
§1.1. `P21MainStatement` has precisely these hypotheses and conclusion `type ≤ 4`;
it is a target definition, not a proved theorem.

The source's `W` and `c_q` are `P21.W F m` and `P21.complement F m q`.
Theorems generally spell out `F + m` and `F + m - q` to expose arithmetic.
Minimum/maximum predicates refer to the Γ-order, not the ordinary integer order.
Layer ideal/filter results are relative to Apéry; additionally,
`a0_lower_in_semigroup` proves the lower-ideal form for all elements of Γ.

Auxiliary lemmas sometimes require fewer assumptions than the encompassing C2
setting. For example `gap_below_pf` applies also to negative gaps, but the exported
C2.1 statement explicitly includes the requested nonnegative-gap hypothesis.
The tail's natural-number closure is used only to obtain a conductor from mathlib;
the integer membership bridge is proved in `natural_closure_to_tail`.

## Mathlib investigation and reuse

The installed pinned mathlib source was inspected, including
`Mathlib/NumberTheory/FrobeniusNumber.lean`, its `Nat.FrobeniusNumber` predicate,
`Nat.setGcd`, `Nat.exists_mem_closure_of_ge`, additive submonoids/closures,
`Set.Finite`, `Set.exists_max_image`, `Finset`, `IsGreatest`, and integer intervals.
This is a record of the inspected pinned version, not a claim that its tag is
the latest upstream release.

The natural-number Frobenius predicate was not forced onto the publication's
integer semantics. Existing `AddSubmonoid` and order/cardinality APIs were reused.
`generated_eq_closure` proves equivalence of the actual-witness generated monoid
with mathlib's additive closure. The tail conductor proof uses mathlib's proved
coprime-generation result. The local mathlib HEAD matched the manifest, and its
tracked working tree was clean at inspection.
