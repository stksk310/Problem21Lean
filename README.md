# P21 Lean

**Formalization status: COMPLETE**

This repository contains the Lean 4 formalization of Numerical Semigroup
Problem 21. The symmetric and nonsymmetric branches, including PATH, TYPE II,
and CHAIN, are closed. No mathematical branches remain open.

The final API is:

```lean
P21.q_ge_four_impossible
P21.q_card_le_three
P21.type_le_four
P21.main_theorem : P21MainStatement
```

The main statement is:

```lean
def P21MainStatement : Prop :=
  ∀ (g : Generators) (s : g.Setting) (F : ℤ),
    s.semigroup.IsFrobenius F →
    s.semigroup.Canonical F g.m →
    s.semigroup.type ≤ 4
```

It formalizes the type bound

```text
canonical minimally four-generated numerical semigroup
→ type ≤ 4
```

## Frozen release

The permanent audited snapshot is
[v1.0.0](https://github.com/stksk310/Problem21Lean/releases/tag/v1.0.0),
whose annotated tag peels to the exact commit:

```text
13026bdd4ac72dc892415c456fb8e780c3ec62dc
```

Release assets:

- [Final candidate ZIP](https://github.com/stksk310/Problem21Lean/releases/download/v1.0.0/P21_LEAN_FINAL_MAIN_THEOREM_CANDIDATE_20260923.zip)
- [Final TRUE-audit evidence](https://github.com/stksk310/Problem21Lean/releases/download/v1.0.0/P21_FINAL_TRUE_AUDIT_EVIDENCE.zip)
- [SHA-256 checksums](https://github.com/stksk310/Problem21Lean/releases/download/v1.0.0/SHA256SUMS.txt)
- [Release provenance](https://github.com/stksk310/Problem21Lean/releases/download/v1.0.0/RELEASE_PROVENANCE.txt)

The final audit is bound to
[GitHub Actions run 35892930280](https://github.com/stksk310/Problem21Lean/actions/runs/35892930280).
The release candidate SHA-256 is:

```text
3341da0f47da0b91d01cd76ca1ec6d786d66fb31c487420d8ad48776aed4d14e
```

## Permanent archive and DOI

The independently audited frozen formalization is permanently archived on
Zenodo.

- **Exact v1.0.0 DOI:** [10.5281/zenodo.22928464](https://doi.org/10.5281/zenodo.22928464)
- **All-versions DOI:** [10.5281/zenodo.22928463](https://doi.org/10.5281/zenodo.22928463)

The exact v1.0.0 DOI refers to the frozen archival snapshot corresponding to:

```text
Git tag:
v1.0.0

Audited commit:
13026bdd4ac72dc892415c456fb8e780c3ec62dc

Permanent archive SHA-256:
1bf73c94faf5c60607cd70e20fc1adbff18dd861634b3d71a7546f52dbc8dabd
```

For reproducible citation of the frozen formal proof, cite the exact v1.0.0
DOI:

```text
10.5281/zenodo.22928464
```

## Pinned environment

```text
Lean         v4.34.0-rc1
Lean commit  3447a668783dbce1a8fdb97101dd067687b2b418
mathlib      de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
Lake         5.0.0
SymPy        1.14.0
```

## Reproduction

With the pinned Lean toolchain and dependencies available:

```bash
lake build
lake build P21.MainTheorem
lake env lean verification/final/MainStatementGate.lean
```

Inspect the final theorem and its axioms in Lean:

```lean
#print P21.main_theorem
#print axioms P21.main_theorem
```

The final theorem depends only on Lean/mathlib's standard axioms:

```text
propext
Classical.choice
Quot.sound
```

There are no project-specific axioms and no `sorry`, `admit`, or `sorryAx`
proof debt in the final theorem assembly.

## Generated certificates

The nonsymmetric closure includes two generated certificate families:

```text
C9 LINEAR
28 identities
715 positive monomials
constant 35

C10 EUCLIDEAN
35 identities
3234 positive monomials
constant 63
```

Their Python verifiers are auxiliary consistency checks. The Lean kernel proof
is authoritative.

The `v1.0.0` tag is immutable. Any future mathematical Lean-source change
requires a new version and a new independent audit.
