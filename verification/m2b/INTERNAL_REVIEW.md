# M2B internal mathematical source review

Status: no material mathematical defect found in the source inspected. This is an internal review, not a TRUE AUDIT declaration or a claim of completed kernel/CI verification.

## Scope and method

Read `REQUEST.md`, all eight new `P21/Symmetric/Classification/*.lean` modules, `P21/External/SymmetricThreeGeneratorProof.lean`, `P21/Symmetric/FullClosure.lean`, and `verification/m2b/Regression.lean` directly. Checked the relevant frozen definitions of `Setting`, actual factorization, generated monoid, `SymmetricAt`, `SymmetricTail`, `TwoGeneratorData.T`, and `SymmetricGlueData`, together with the frozen two-generator representation-difference and Frobenius-symmetry proofs. The reference base is `a0ec51cf93326b6f8dbf22647cfeecf81a931bd8`.

No Lean build was launched in this review; the primary agent was running the serial build. Existing verification reports were not used as evidence for mathematical correctness. Only this review document was written by the reviewer.

## Findings

1. **Exact public scope.** `symmetric_three_generator_gluing` has the frozen `SymmetricThreeGeneratorGluingStatement` as its declared type. Its proof introduces only `g`, `Setting`, and `SymmetricTail`. The latter remains integer gap symmetry, not a definition containing glue data. No canonical assumption, supplied special pair, critical relation, or target-existence premise enters the public proof.

2. **Tail foundations.** Positivity and irredundancy come from `Setting`. Symmetry bounds every gap and gives cofiniteness. Consecutive tail members give both the common-divisor-divides-one result and the three-generator Bezout witness. These arguments do not use the canonical/Q-dependent tail results.

3. **Exhaustive dichotomy.** `glue_exists_of_symmetric` first obtains an actual natural-coefficient factorization of `f + n_0`. Its distinguished coefficient is zero because removing one copy would represent the Frobenius gap. Classical case analysis then tests uniqueness among all nonnegative integer pair representations. Failure supplies an actual second nonnegative representation distinct from the first. The two branches cover all cases without assuming gluing.

4. **Multiple-representation branch.** Primitive pair quotients are formed using the actual pair gcd. Coprimality gives a nonzero integral representation shift; one representation then contains at least the primitive least-common-multiple block. Subtracting that block leaves an actual member of the tail. The Apéry gap passes down to the block. If the omitted generator were outside the primitive two-generator monoid, frozen two-generator Frobenius symmetry would give a nonnegative representation of its complement. Scaling that representation, adding the two scaled generators and `(d - 1)` copies of the omitted generator gives the forbidden Apéry predecessor. Thus the asserted primitive membership is actual nonnegative membership, not a signed Bezout conclusion.

5. **Unique-representation branch.** Symmetric Apéry complementation forces every nonnegative pair representation of an Apéry element into the rectangle bounded by the top coefficients. Conversely, points in that rectangle lie below the top in semigroup order and remain Apéry. Uniqueness at the top proves injectivity of rectangle values. The cardinality proof supplies a bijection between the actual Apéry set and all residues modulo the positive distinguished generator, including surjectivity via a least natural representative. A separate finite rectangle bijection therefore proves `n_0 = (A + 1) * (B + 1)`; it does not merely count representations with possible collisions.

6. **Boundary and determinant step.** Apéry reduction yields nonnegative coefficients for the two first exterior rectangle points. A zero reduction quotient would place an exterior point inside the rectangle; a positive coefficient on its original axis would violate an interior Apéry gap. The resulting inward coefficients satisfy the strict rectangle bounds. The determinant annihilates both remaining generators modulo the distinguished generator; the explicitly derived three-generator Bezout identity proves divisibility by that distinguished generator. The determinant is positive and at most the rectangle cardinality. Divisibility and `x = L*M` force `a*b = 0`. Each zero case produces the stated integral decomposition, and the boundary quotients used in the membership witness are positive.

7. **All gluing fields.** `decomposition_glue_data` constructs the frozen structure directly. Positivity of the scaled generators implies positive primitive quotients. Quotient one contradicts tail minimality; scale one contradicts minimality using the supplied nonnegative primitive expression. Thus `u,v,d >= 2` are proved, not assumed at the public boundary. A common divisor of `d,w` divides all three actual generators and hence one. Primitive coprimality in the rectangle branch is established by the same common-divisor argument. All reorderings are `Equiv.Perm (Fin 3)` values built from swaps/refl/composition, with explicit coordinate identities. No repeated-index tuple is substituted for a permutation.

8. **Auxiliary critical relations.** `CriticalRelation` includes natural off-direction coefficients, positivity, exact equality, and least-positive minimality. Existence is proved from positivity by a pair product relation and `Nat.find`; it needs neither the target result nor a supplied relation. Minimality excludes coefficient one. This module is auxiliary to the selected direct Apéry proof and is imported by the regression file, not used to disguise an unproved rigidity hypothesis.

9. **Closure and dependency direction.** `FullClosure` obtains the new glue data and applies the unchanged M2A `symmetric_tail_from_glue_data`. Its hypotheses are exactly `Setting`, Frobenius, canonical, and symmetric tail. The inspected import graph has classification below the public glue theorem and `FullClosure` above it. No classification proof refers to the full S3 theorem. Reusing the frozen two-generator theorem and glue-data structure is not reuse of the three-generator target.

10. **Regression coverage.** The regression file checks the definitional integer-symmetry meaning, existence and lower bounds for critical coefficients, the exact public gluing type, all gluing arithmetic/membership/permutation fields, and the full S3 type. These examples invoke proved declarations rather than introduce the target as an assumption. They are theorem-level interface regressions, not independent alternative proofs or computational example coverage.

## Limits and remaining verification

- Source review found no strengthening, circularity, missing nonnegative witness, invalid cardinality step, or determinant/permutation defect.
- A direct token search in the reviewed new Lean files found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `native_decide`, or `run_tac`. This is not a replacement for the designated scanner and transitive axiom inspection.
- The working-tree diff against the base showed no modification of existing Lean files at review time, but this review did not perform the required byte-level frozen inventory check.
- Successful elaboration, fresh builds, complete declaration axiom reports, frozen byte integrity, clean CI, and candidate/archive identity remain obligations of the primary verification workflow. This document makes no assertion that those obligations have completed.
- The review applies to the source read in this working session. Any later mathematical edits require renewed inspection of their affected reasoning.
