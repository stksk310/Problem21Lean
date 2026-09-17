# P21 LEAN — M2B `STD_SYM_GLUE` / FULL S3 CLOSURE

Numerical Semigroup Problem 21 Lean formalization project を継続する。

このmissionでは、M2Aで唯一OPENとして残った standard external input

```text
STD_SYM_GLUE
```

をLean内で実証明し、そのままM2Aと接続して

```text
FULL S3 — symmetric tail ⇒ type ≤ 4
```

まで閉じることをprimary targetとする。

今回は最初から

```text
proof implementation
→ local Lean verification
→ GitHub branch push
→ clean GitHub Actions CI
→ evidence artifact
→ single candidate ZIP
```

まで一つのmissionとして完遂する。

---

# 0. AUTHORITATIVE FROZEN STATE

Repository:

```text
https://github.com/stksk310/Problem21Lean
```

現在のM2A audit target:

```text
branch:
m2-symmetric-tail

commit:
a0ec51cf93326b6f8dbf22647cfeecf81a931bd8
```

正式FROZEN ledger:

```text
M1 — FOUNDATION + C2
TRUE AUDIT PASS / FROZEN

M2A — INTERNAL SYMMETRIC CLOSURE
TRUE AUDIT PASS / FROZEN
```

M2Aの最終定理:

```lean
P21.Symmetric.symmetric_tail_from_glue_data
    (g : P21.Generators)
    (setting : g.Setting)
    (F : ℤ)
    (hF : setting.semigroup.IsFrobenius F)
    (hcan : setting.semigroup.Canonical F g.m)
    (G : P21.Symmetric.SymmetricGlueData g) :
    setting.semigroup.type ≤ 4
```

これはFROZEN入力として使用してよい。

---

# 1. IMMUTABILITY — EXISTING MATHEMATICAL SOURCE IS FROZEN

commit

```text
a0ec51cf93326b6f8dbf22647cfeecf81a931bd8
```

に存在する**全既存 project-owned `.lean` source**をFROZENとする。

特に以下を変更禁止:

```text
P21/*.lean
P21/Symmetric/*.lean
P21/External/SymmetricThreeGenerator.lean
verification/m2/*
lean-toolchain
lakefile.toml
lake-manifest.json
```

`P21/External/SymmetricThreeGenerator.lean` のOPEN definitionも変更しない。

M2Bは**新規moduleのみ**で証明を追加すること。

FROZEN sourceに変更が必要なら黙って変更せず、

```text
FROZEN API EXTENSION REQUIRED
```

としてexact requirementを報告する。

---

# 2. NEW BRANCH

M2A FROZEN commitからbranchを作る。

推奨:

```text
m2b-std-sym-glue
```

base:

```text
a0ec51cf93326b6f8dbf22647cfeecf81a931bd8
```

mainへmergeしない。

TRUE AUDIT PASSまではbranchを保持する。

---

# 3. EXACT OPEN TARGET

既存definition:

```lean
def P21.Symmetric.SymmetricThreeGeneratorGluingStatement : Prop :=
  ∀ (g : P21.Generators),
    g.Setting →
    P21.Symmetric.SymmetricTail g →
    Nonempty (P21.Symmetric.SymmetricGlueData g)
```

今回まず証明すべきものはexactly:

```lean
theorem symmetric_three_generator_gluing :
    P21.Symmetric.SymmetricThreeGeneratorGluingStatement := by
  ...
```

hypothesis strengthening禁止。

特に追加してはいけない仮定:

```text
canonical
Q nonempty
pseudo-Frobenius cardinality
pairwise coprime generators
already complete intersection
already gluing
existence of a special pair
critical relation supplied externally
```

これらが必要ならすべて`Setting + SymmetricTail`からLean内で導くこと。

---

# 4. SOURCE MATHEMATICS

publicationが使用するexact standard resultは:

after permuting the minimally three-generated symmetric tail generators,

```math
H = ⟨du,dv,w⟩
```

with

```math
d,u,v ≥ 2,
gcd(u,v)=1,
gcd(d,w)=1,
w∈⟨u,v⟩.
```

これをLeanの既存

```lean
SymmetricGlueData g
```

へconstructする。

既存structureは:

```text
perm : Equiv.Perm (Fin 3)
two  : TwoGeneratorData
d    : ℤ
w    : ℤ

d_ge_two : 2 ≤ d
coprime   : Int.gcd d w = 1
w_mem     : w ∈ two.T

x_eq : g.n (perm 0) = d * two.u
y_eq : g.n (perm 1) = d * two.v
z_eq : g.n (perm 2) = w
```

`TwoGeneratorData` already contains:

```text
u ≥ 2
v ≥ 2
gcd(u,v)=1
```

したがってM2Bのformal targetとpublication normal formは一致している。

---

# 5. DO NOT AXIOMATIZE THE EXTERNAL THEOREM

絶対禁止:

```lean
axiom symmetric_three_generator_gluing ...
```

```lean
theorem symmetric_three_generator_gluing := by
  sorry
```

```lean
opaque symmetric_three_generator_gluing ...
```

またbibliographic theoremを

```text
“standardなので使用”
```

としてLeanのassumptionにしてはならない。

今回の目的はまさに、そのstandard theorem自体をLean kernelの中へ持ち込むことである。

---

# 6. PROOF-ROUTE POLICY

最初に短いroute auditを行う。

調査対象:

```text
pinned mathlib
existing P21 structures
available commutative-monoid / gcd / AddSubmonoid results
finite factorization / minimal relation APIs
```

ただし長時間の一般論探索に逃げない。

優先順位:

```text
A. theorem-specific direct classification of symmetric 3-generated numerical semigroups
B. narrowly scoped complete-intersection / gluing proof sufficient only for edim=3
C. broad general complete-intersection theory
```

推奨は **A**。

CはYAGNI。
Delormeの一般gluing classification全体をformalizeする必要はない。

---

# 7. REFERENCE FORM OF THE CLASSIFICATION

proof design上は、次の古典的equivalent formを利用してよい。

after permutation every symmetric embedding-dimension-three numerical semigroup has generators

```math
⟨a m₁,\; a m₂,\; b m₁+c m₂⟩
```

where conceptually:

```math
m₁,m₂ > 1,
gcd(m₁,m₂)=1,
a≥2,
b,c≥0,
b+c≥2,
gcd(a,bm₁+cm₂)=1.
```

これが証明できれば

```text
d = a
u = m₁
v = m₂
w = b m₁ + c m₂
```

として`SymmetricGlueData`を構成できる。

ただし、このclassification statement自体を仮定してはならない。

必要な方向をLeanで証明すること。

---

# 8. RECOMMENDED DIRECT FORMALIZATION SPINE

以下は推奨DAG。
より短く厳密なrouteが見つかれば変更可だが、各数学義務を消してはならない。

```text
Setting + SymmetricTail
        │
        ▼
Tail is an actual minimally 3-generated numerical semigroup
        │
        ▼
critical multiples / minimal pair relations
        │
        ▼
symmetric edim-3 relation rigidity
        │
        ▼
some pair has common gcd d > 1
        │
        ▼
x = d u, y = d v, gcd(u,v)=1
        │
        ▼
w ∈ ⟨u,v⟩
        │
        ▼
gcd(d,w)=1
        │
        ▼
u,v,d ≥ 2
        │
        ▼
SymmetricGlueData
```

---

# 9. FIRST FOUNDATION — TAIL IS A NUMERICAL SEMIGROUP

From

```text
g.Setting
+
SymmetricTail g
```

derive explicitly:

```text
all tail generators positive
g.H ⊆ ℕ inside ℤ
g.H minimally generated by the three tail generators
tail is cofinite
gcd of the three tail generators = 1
```

Do not use M1's canonical/Q-dependent tail-gcd theorem if its hypotheses are unavailable.

Here symmetry itself should supply the necessary cofiniteness/Frobenius bound.

Reuse existing:

```lean
SymmetricAt
symmetricAt_gap_le
```

where appropriate.

Prove a local numerical-semigroup package if useful.

---

# 10. CRITICAL MULTIPLES

For each tail generator `n_i`, define or obtain the least positive integer

```math
c_i > 0
```

such that

```math
c_i n_i ∈ ⟨n_j,n_k⟩.
```

Required:

```text
existence
positivity
minimality
actual nonnegative two-generator witness
```

Existence should follow from tail cofiniteness / finite residues.

Do not use a signed relation as the witness.

Suggested local abstraction:

```lean
structure CriticalRelation (g : Generators) (i : Fin 3) where
  coeff : ℕ
  coeff_pos : 0 < coeff
  otherCoeff : Fin 3 → ℕ
  zero_self : otherCoeff i = 0
  equality :
    coeff * g.n i = value g.n otherCoeff
  minimal :
    ...
```

Adapt to existing P21 factorization types if cleaner.

---

# 11. SYMMETRIC THREE-GENERATOR RIGIDITY — CORE NEW LEMMA

This is the mathematical heart.

Prove, from symmetry plus minimal three-generation, the exact relation pattern needed to obtain the gluing pair.

Equivalent acceptable forms include:

### Form A

after a permutation,

```math
c_1 n_1 = c_2 n_2
```

with the third critical relation

```math
c_3 n_3 = r_1 n_1+r_2 n_2.
```

### Form B

after a permutation, two generators have a nontrivial common divisor `d>1`
and the third generator belongs to the semigroup generated by their primitive quotients.

### Form C

directly obtain

```math
n_i=d u,\quad n_j=d v,\quad n_k=w,
```

with all `SymmetricGlueData` fields.

Choose the route that yields the smallest auditable Lean dependency.

Do not package the desired conclusion into an intermediate structure and assume its existence.

---

# 12. HOW TO PROVE THE RIGIDITY

Use the classical edim-3 symmetric/complete-intersection argument only to the extent necessary.

Acceptable strategies:

## Strategy 1 — critical-relation / Betti route

Develop only the tiny amount of minimal-relation theory required to prove:

```text
symmetric 3-generated
⇒ two critical Betti relations coincide
⇒ gluing pair exists
```

No general Betti-element library required.

## Strategy 2 — unique factorization graph route

For the three critical multiples, analyze their actual factorization supports and use Frobenius symmetry to rule out the nonsymmetric three-cycle pattern.

If this reproduces the classical Herzog dichotomy directly, this is highly desirable.

## Strategy 3 — narrowly scoped complete-intersection route

Formalize:

```text
symmetric edim 3 ⇒ complete intersection
```

only in the exact three-generator setting, then prove the corresponding two-relation presentation forces the desired gluing data.

Do not formalize arbitrary embedding dimension.

---

# 13. FORBIDDEN CIRCULARITY

M2B must not use:

```text
M2A symmetric_tail_from_glue_data
```

to prove existence of glue data.

That theorem is direction

```text
GlueData → type ≤ 4
```

and may only be used **after** M2B is proved.

Likewise

```lean
glue_data_symmetric_tail
```

is the reverse easy direction

```text
GlueData → SymmetricTail
```

and cannot establish existence.

Explicitly include a dependency check showing:

```text
symmetric_three_generator_gluing
```

does not depend on

```text
symmetric_tail_from_glue_data
```

in a circular way.

---

# 14. CONSTRUCTION OF `d,u,v,w`

Once the appropriate pair is found, construct actual integers:

```math
d = gcd(x,y),
u = x/d,
v = y/d,
w = z.
```

or an equivalent directly obtained decomposition.

Prove:

```math
x = d u
y = d v
gcd(u,v)=1
```

with exact integer divisibility lemmas.

Avoid unsafe integer division reasoning.
Every quotient identity must have divisibility proof attached.

---

# 15. PROVE `d ≥ 2`

Need:

```math
2 ≤ d.
```

Do not simply infer from “nontrivial gluing”.

Lean proof must establish `d ≠ 1` from the symmetric critical-relation structure plus minimality.

If the direct classification route supplies `a≥2`, map that proof explicitly.

---

# 16. PROVE `u,v ≥ 2`

`TwoGeneratorData` requires:

```math
2 ≤ u
2 ≤ v.
```

These are not optional.

Derive them from minimality of the original three tail generators.

For example, if `u=1`, show the corresponding generator/decomposition makes another generator redundant.

All redundancy contradictions must use actual nonnegative representations.

---

# 17. PROVE `w ∈ ⟨u,v⟩`

This is a hard gate.

Need an actual witness:

```math
∃ a b : ℤ,
  0 ≤ a ∧
  0 ≤ b ∧
  w = a*u+b*v
```

or equivalent `w ∈ TwoGeneratorData.T`.

A divisibility or group-membership argument is insufficient.

Do not confuse

```text
w ∈ ℤ⟨u,v⟩
```

with

```text
w ∈ ⟨u,v⟩.
```

The proof must preserve nonnegative coefficients.

---

# 18. PROVE `gcd(d,w)=1`

Derive this from the actual numerical-semigroup gcd-one property:

```math
gcd(du,dv,w)=1
```

and `gcd(u,v)=1`.

No canonical hypothesis required.

Produce a reusable arithmetic lemma if useful:

```text
gcd(d*u, d*v, w)=1
and gcd(u,v)=1
⇒ gcd(d,w)=1.
```

---

# 19. PERMUTATION DATA

Construct a genuine:

```lean
Equiv.Perm (Fin 3)
```

identifying the selected pair and remaining generator.

Do not handle the permutation only by informal `wlog`.

All three generator equations:

```lean
x_eq
y_eq
z_eq
```

must be Lean equalities.

Finite case splits over `Fin 3` are acceptable.

---

# 20. BUILD `TwoGeneratorData`

Construct:

```lean
TwoGeneratorData
```

with:

```text
u
v
u_ge_two
v_ge_two
coprime
```

Then construct:

```lean
SymmetricGlueData g
```

with all fields.

At this point prove:

```lean
theorem symmetric_three_generator_gluing :
    SymmetricThreeGeneratorGluingStatement
```

with zero additional hypotheses.

---

# 21. FULL S3 CONNECTION

After M2B theorem is complete, add a separate new module, for example:

```text
P21/Symmetric/FullClosure.lean
```

Do not modify M2A's existing `Closure.lean`.

Prove:

```lean
theorem symmetric_tail_type_le_four
    (g : Generators)
    (setting : g.Setting)
    (F : ℤ)
    (hF : setting.semigroup.IsFrobenius F)
    (hcan : setting.semigroup.Canonical F g.m)
    (hsym : SymmetricTail g) :
    setting.semigroup.type ≤ 4 := by
  obtain ⟨G⟩ :=
    symmetric_three_generator_gluing g setting hsym
  exact symmetric_tail_from_glue_data g setting F hF hcan G
```

Use actual namespace/API names.

This theorem should match publication S3 scope.

---

# 22. SUCCESS STATES

## Full success

If both:

```text
STD_SYM_GLUE proved
FULL S3 theorem proved
```

then status:

```text
M2B STD_SYM_GLUE + FULL S3
CANDIDATE FOR TRUE AUDIT
```

Do NOT say FROZEN.

## Partial success

If the full theorem cannot be closed, do not axiomatize.

Instead return:

```text
M2B BEST REDUCTION
NOT YET ELIGIBLE FOR FROZEN
```

with the smallest precise remaining Lean proposition.

The remaining proposition must be substantially smaller than the original theorem if progress was made.

---

# 23. RECOMMENDED NEW FILE LAYOUT

Prefer new files only, e.g.

```text
P21/Symmetric/Classification/
  TailNumericalSemigroup.lean
  CriticalRelations.lean
  SymmetricRigidity.lean
  GcdDecomposition.lean
  GlueExistence.lean

P21/External/
  SymmetricThreeGeneratorProof.lean

P21/Symmetric/
  FullClosure.lean
```

Keep files focused.

Do not force this exact layout if a cleaner decomposition emerges.

---

# 24. TEST / REGRESSION OBLIGATIONS

Add theorem-level regression checks for at least:

```text
SymmetricTail alone does not encode GlueData definitionally
critical coefficients are positive
selected pair really has d>1
primitive quotients are coprime
u,v≥2
w membership uses nonnegative coefficients
gcd(d,w)=1
permutation equations are exact
STD_SYM_GLUE theorem has no canonical hypothesis
full S3 theorem has publication-equivalent hypotheses
```

No tests may assume the target theorem.

---

# 25. PROOF DEBT FIREWALL

Project-owned Lean code must contain no:

```text
sorry
admit
axiom
sorryAx
unsafe
```

and no project-specific opaque escape.

Inspect also:

```text
native_decide
run_tac
```

if used as proof shortcuts.

Ordinary proven `opaque` library internals are not the issue;
new project-specific uninspected escape hatches are forbidden.

---

# 26. AXIOM AUDIT

Run `#print axioms` or the existing automated checker over:

```text
all new M2B declarations
symmetric_three_generator_gluing
symmetric_tail_type_le_four
```

Allowed only:

```text
propext
Classical.choice
Quot.sound
```

Project-specific axiom count:

```text
0
```

---

# 27. FROZEN SOURCE INTEGRITY

Compare every pre-existing project-owned Lean file against:

```text
a0ec51cf93326b6f8dbf22647cfeecf81a931bd8
```

Expected:

```text
ALL PRE-M2B LEAN SOURCES BYTE-IDENTICAL
```

New `.lean` files are allowed.

Any pre-existing Lean source changed:

```text
FROZEN_SOURCE_CHANGED: YES
```

and candidate is not eligible for TRUE AUDIT under this mission.

---

# 28. LOCAL VERIFICATION BEFORE PUSH

Run fresh local verification.

At minimum:

```bash
lake build
```

plus explicit build of:

```text
all 16 M2A modules
all new M2B modules
FullClosure module
```

Run:

```text
existing M2 verification suite
new M2B verification suite
proof-debt scanner
scanner regression tests
axiom checker
frozen integrity checker
```

All must pass before GitHub push.

---

# 29. SINGLE DELIVERY ZIP

Produce:

```text
P21_LEAN_M2B_STD_SYM_GLUE_FULL_S3_CANDIDATE_20260917.zip
```

or current date if necessary.

Include:

```text
complete reproducible project snapshot
new Lean source
README_M2B.md
SOURCE_OF_TRUTH_M2B.md
M2B_DEPENDENCY_DAG.md
M2B_STATEMENT_MAP.md
M2B_PROOF_ROUTE.md
FROZEN_SOURCE_INTEGRITY_REPORT.txt
BUILD_LOCAL_LOG.txt
AXIOM_REPORT_M2B.txt
PROOF_DEBT_REPORT_M2B.txt
CODEX_SELF_CHECK_M2B.md
NEXT_RESTART.md
```

If partial:

```text
M2B_REMAINING_OBLIGATION.md
```

must contain the exact remaining theorem.

---

# 30. GITHUB PUSH — INTEGRATED WORKFLOW

After local success, push the same exact source to:

```text
repository:
https://github.com/stksk310/Problem21Lean

branch:
m2b-std-sym-glue
```

Do not merge main.

Record exact commit:

```text
AUDIT_TARGET_COMMIT=<40-char SHA>
```

Candidate ZIP source and GitHub source must be hash-identical.

---

# 31. GITHUB ACTIONS

Create:

```text
.github/workflows/m2b-audit.yml
```

name:

```text
P21 Lean M2B Audit
```

Run in clean Ubuntu GitHub-hosted runner.

Use exact existing:

```text
lean-toolchain
lake-manifest.json
```

No dependency upgrades.

Third-party mathlib cache allowed.

No project-owned compiled cache.

---

# 32. REQUIRED CI CHECKS

CI must independently run:

```text
1. checkout exact audit commit
2. frozen pre-M2B source integrity
3. candidate ZIP/source integrity
4. install pinned Lean toolchain
5. dependency revision check
6. fresh root lake build
7. explicit build all M2A modules
8. explicit build all M2B modules
9. explicit build FullClosure
10. proof-debt scan
11. scanner regression tests
12. axiom inspection
13. existing M2 verification suite
14. new M2B verification suite
15. critical statement inspection
16. dependency-cycle/circularity check
17. final source integrity
18. upload evidence
```

Every required step must exit 0.

---

# 33. CRITICAL CI STATEMENT INSPECTION

Evidence must print the exact types of:

```text
SymmetricTail
SymmetricGlueData
SymmetricThreeGeneratorGluingStatement
symmetric_three_generator_gluing
symmetric_tail_from_glue_data
symmetric_tail_type_le_four
```

Also inspect:

```text
#print axioms P21.Symmetric.symmetric_three_generator_gluing
#print axioms P21.Symmetric.symmetric_tail_type_le_four
```

or equivalent.

---

# 34. CIRCULARITY CHECK

Generate import/dependency evidence showing:

```text
M2B glue theorem
```

does not depend on `FullClosure`, and does not use the final full S3 theorem.

Required direction:

```text
FROZEN M1/M2A foundation
        ↓
M2B classification/glue proof
        ↓
symmetric_three_generator_gluing
        ↓
M2A symmetric_tail_from_glue_data
        ↓
FullClosure
```

No reverse edge.

---

# 35. CI ARTIFACT

Artifact name:

```text
P21_M2B_TRUE_AUDIT_EVIDENCE
```

Include at least:

```text
ENVIRONMENT.txt

FROZEN_SOURCE_INTEGRITY.txt
CANDIDATE_SOURCE_INTEGRITY.txt

ROOT_BUILD_LOG.txt
M2A_BUILD_LOG.txt
M2B_BUILD_LOG.txt

M2B_MODULE_LIST.txt

PROOF_DEBT_REPORT.txt
SCANNER_TEST_LOG.txt

AXIOM_REPORT.txt
AXIOM_SUMMARY.json

STATEMENT_INSPECTION.txt
DEPENDENCY_DAG_CHECK.txt
CIRCULARITY_CHECK.txt

M2_VERIFICATION_LOG.txt
M2B_VERIFICATION_LOG.txt

COMMIT_SHA.txt
RUN_CONTEXT.json
```

---

# 36. HANDOFF RECEIPT

Create:

```text
HANDOFF_RECEIPT_M2B.json
```

minimum fields:

```json
{
  "status": "M2B STD_SYM_GLUE + FULL S3 CI EVIDENCE READY FOR TRUE AUDIT",
  "repository": "https://github.com/stksk310/Problem21Lean",
  "branch": "m2b-std-sym-glue",
  "audit_target_commit": "...",
  "workflow_run": "...",
  "workflow_run_id": 0,
  "attempt": 1,
  "ci_conclusion": "success",
  "artifact_name": "P21_M2B_TRUE_AUDIT_EVIDENCE",
  "artifact_id": 0,
  "artifact_digest": "sha256:...",
  "candidate_zip_sha256": "...",
  "frozen_source_changed": false,
  "std_sym_glue_proved": true,
  "full_s3_proved": true,
  "proof_debt_tokens": 0,
  "project_specific_axioms": 0
}
```

Use actual values.

---

# 37. NETWORK FAILURE POLICY

If GitHub dependency download fails transiently:

* same commit may be rerun;
* report `RUN_ATTEMPT`.

Do not change mathematical source merely to avoid a network failure.

---

# 38. NO SELF-AUDIT CLAIM

Codex must not say:

```text
TRUE AUDIT PASS
FROZEN
AUDITED
```

even if everything succeeds.

Allowed success wording:

```text
M2B STD_SYM_GLUE + FULL S3
CANDIDATE FOR TRUE AUDIT

CI REPRODUCIBILITY EVIDENCE READY
```

Commander/TRUE AUDIT thread alone promotes FROZEN status.

---

# 39. FINAL USER REPORT — JAPANESE

Report:

```text
1. STD_SYM_GLUE proof status
2. chosen mathematical proof route
3. main new lemmas
4. exact glue-data construction
5. FULL S3 connection status

6. local build
7. proof debt
8. axiom report
9. frozen-source integrity

10. GitHub repository
11. branch
12. exact commit
13. workflow URL
14. workflow run ID / attempt
15. CI conclusion

16. artifact name / ID / digest
17. candidate ZIP SHA256
18. remaining OPEN obligations
```

最後にコピー用:

```text
REPOSITORY:
BRANCH:
AUDIT_TARGET_COMMIT:
WORKFLOW_RUN:
WORKFLOW_RUN_ID:
RUN_ATTEMPT:
CI_ARTIFACT:
CI_ARTIFACT_ID:
CI_ARTIFACT_DIGEST:
CANDIDATE_ZIP_SHA256:
STD_SYM_GLUE:
FULL_S3:
PROOF_DEBT:
PROJECT_SPECIFIC_AXIOMS:
FROZEN_SOURCE_CHANGED:
SOURCE_CHANGED:
```

---

# 40. FINAL SUCCESS CONDITION

Full success requires simultaneously:

```text
SymmetricThreeGeneratorGluingStatement proved in Lean
+
zero added assumptions
+
SymmetricGlueData explicitly constructed
+
actual nonnegative w∈⟨u,v⟩ witness
+
gcd(d,w)=1 proved
+
u,v,d≥2 proved
+
permutation exact
+
M2A theorem reused without modification
+
FULL S3 theorem proved
+
no proof debt
+
no project-specific axioms
+
all FROZEN source preserved
+
local fresh build PASS
+
GitHub clean CI PASS
+
evidence artifact externally inspectable
```

Only then return:

```text
M2B STD_SYM_GLUE + FULL S3
CANDIDATE FOR TRUE AUDIT
```
