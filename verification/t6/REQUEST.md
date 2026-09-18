# P21 LEAN — T6 / SECTION 6 TYPE II EXCLUSION

## TWO ACTUAL SINGLETON RETURNS / UNIFORM-I-CAP / LEVEL-ORDER EXHAUSTION

This is the next bounded formalization milestone in `Problem21Lean`.

The independently TRUE-AUDITED and FROZEN state is now:

```text
M1 — FOUNDATION + C2
FROZEN

M2A — INTERNAL SYMMETRIC CLOSURE
FROZEN

M2B — STD_SYM_GLUE
FROZEN

FULL S3 — SYMMETRIC TAIL
FROZEN

M3A — NONSYMMETRIC LOCAL GEOMETRY
FROZEN

M3B1 — MINBOX / WHITE
FROZEN

M3B2 — DPE
FROZEN

THREE-ARM
FROZEN

COLOR-CAP
FROZEN

M3 — NONSYMMETRIC G4 FULL CLASSIFICATION
FROZEN

P5 — PATH EXCLUSION
FROZEN
```

The current nonsymmetric terminal frontier is exactly

```text
TYPE II ∨ CHAIN
```

The only mathematical target of this milestone is:

```text
SECTION 6 — TYPE II EXCLUSION
```

Do not begin CHAIN.

---

# 0. REPOSITORY / IMMUTABLE BASE

Repository:

```text
https://github.com/stksk310/Problem21Lean
```

The new immutable mathematical base is:

```text
707d9386037e8bcdec9c9bfb02f95731c9ce2597
```

Current branch:

```text
p5-path-exclusion
```

Create a new branch from exactly that commit, preferably:

```text
t6-typeii-exclusion
```

Do not merge to `main`.

---

# 1. FROZEN FRONTIER

The active post-PATH wrapper is already:

```lean
P21.Nonsymmetric.SelectedTerminalAfterPath
```

with alternatives exactly:

```text
TYPE II ∨ CHAIN
```

and the frozen integration theorems:

```lean
nonsymmetric_selected_four_after_path
nonsymmetric_Q_ge_four_after_path
```

preserve the same selected four actual rows and values.

Do not reopen:

```text
G4 classification
COLOR-CAP
DPE
MINBOX
PATH
PAIR / PFREE
P5 ROOT normalization
```

Section 6 is mathematically independent of the PATH proof.

---

# 2. PRIMARY TARGET

The exact FROZEN input is:

```lean
P21.Nonsymmetric.TypeIIInput
```

Do not modify this structure.

The main theorem should conceptually have the form

```lean
theorem TypeIIInput.impossible
    {g : Generators}
    {s : g.Setting}
    {F : ℤ}
    {D : HerzogCriticalData g}
    (T : TypeIIInput s F D)
    (hF : s.semigroup.IsFrobenius F) :
    False := by
  ...
```

Exact argument order/name may differ.

Prefer the minimal theorem scope supported by the publication.

In particular, do not add:

```text
canonicality
nonsymmetry
PATH hypotheses
extra gcd assumptions
return uniqueness
minimal return levels
an actual return of Bj
```

unless logically required by the exact existing interface.

The publication proof of T6 does **not** require an actual return of `B_j`.

---

# 3. SOURCE OF TRUTH

Authority order:

```text
1. reference_inputs/
   P21_Journal_of_Algebra_Submission_Manuscript_FINAL_20260916.pdf

2. reference_inputs/
   P21_MANUSCRIPT_EN_FINAL_20260908_v1.zip
   Section 6

3. reference_inputs/
   P21_FINAL_FROZEN_VERIFICATION_EDITION_20260907.zip
   TYPE-II / T6 maintained proof material

4. existing FROZEN Lean input:
   P21/Nonsymmetric/Extraction.lean
   P21/Nonsymmetric/Path/Integration.lean
```

Publication Section 6 controls theorem scope.

The exact relevant publication chain is:

```text
§6.2 exact input
§6.3 two actual singleton returns
§6.4 endpoint caps
§6.5 uniform cap A,D ≤ b_i-1
§6.6 exhaustion of return levels
```

---

# 4. EXACT TYPE II DATA ALREADY AVAILABLE

For

```lean
T : TypeIIInput s F D
```

the existing FROZEN input supplies:

```text
lambda
mu
nu
qS
```

and the four actual rows

```text
qS
fA - lambda*n0
fB - mu*n1
fA - nu*n2
```

with distinctness.

It also supplies:

```text
qS singleton in direction 0

Ai missing direction 0
Bj missing direction 1
Ak missing direction 2
```

and exact ranges:

```text
1 ≤ lambda < a0
lambda ≤ b0

1 ≤ mu < b1

1 ≤ nu < a2
```

plus complements:

```text
cS  = (rho0-lambda)*n0

cAi = (b1-mu)*n1 + (rho2-nu)*n2

cBj = (a0-lambda)*n0 + (rho2-nu)*n2

cAk = (b0-lambda)*n0 + (rho1-mu)*n1
```

and

```text
W =
  (rho0-lambda-1)*n0
+ (rho1-mu-1)*n1
+ (rho2-nu-1)*n2
```

and the saturated singleton row

```text
qS =
  -n0
  + (rho1-mu-1)*n1
  + (rho2-nu-1)*n2
```

These are the entire Section 6 input.

Do not rederive G4 geometry.

---

# 5. T6.0 — PUBLICATION COORDINATES

Introduce proof-local notation:

```text
P0 := rho0 - lambda
R  := rho1 - mu
T0 := rho2 - nu
g1 := b1 - mu
```

Prove immediately:

```text
P0 = rho0-lambda
R  = rho1-mu = a1+g1
T0 = rho2-nu

g1 ≥ 1

P0-b0 = a0-lambda ≥ 1
T0-b2 = a2-nu ≥ 1
```

Do not confuse the scalar `T0` with the Lean `TypeIIInput` object.

Also expose the canonical singleton identity:

```text
qS = -n0 + (R-1)*n1 + (T0-1)*n2
```

directly from the existing field.

---

# 6. T6.1 — TWO ACTUAL SINGLETON RETURNS

Since `qS` is an actual pseudo-Frobenius row and singleton in direction `0`, directions `1` and `2` are missing tail directions.

Obtain genuine actual returns:

```text
SJ:
qS+n1 = ell*m + A*n0 + C*n2

SK:
qS+n2 = h*m + D0*n0 + B*n1
```

with

```text
ell ≥ 1
h   ≥ 1

A,B,C,D0 ≥ 0
```

The added generator coordinate itself must be zero.

This must follow by:

```text
actual successor factorization
→ if added-generator coefficient >0,
  remove one copy from that same actual factorization
→ qS ∈ Γ
→ contradiction
```

The positive `m` level must follow because if the `m` coefficient were zero then the successor would lie in `H`, contradicting the singleton/missing direction.

Do not assume either fact.

You may reuse a genuinely generic FROZEN helper such as the P5 `actual_return_exists` only if its theorem statement is completely independent of PATH.

Do not depend on `PathInput.impossible` or any PAIR/PFREE theorem.

Prefer a small TYPE-II-local wrapper making the actual provenance explicit.

---

# 7. T6.2 — JR / KR IDENTITIES

Compare SJ/SK with the canonical singleton identity and derive exactly:

```text
JR:
ell*m =
  -(A+1)*n0
  + R*n1
  + (T0-1-C)*n2
```

and

```text
KR:
h*m =
  -(D0+1)*n0
  + (R-1-B)*n1
  + T0*n2
```

These are signed identities.

Do not call JR/KR actual factorizations.

Their actual provenance remains SJ/SK.

---

# 8. T6.3 — ENDPOINT CAPS

## C-CAP

From

```text
qS + P0*n0 = W
```

and SJ derive:

```text
F =
  (ell-1)*m
  + (P0+A)*n0
  - n1
  + C*n2
```

Add the completed HCR zero identity:

```text
-a0*n0 + rho1*n1 - b2*n2 = 0
```

to obtain:

```text
F =
  (ell-1)*m
  + (b0-lambda+A)*n0
  + (rho1-1)*n1
  + (C-b2)*n2
```

Use:

```text
lambda ≤ b0
```

to prove that `C ≥ b2` would make **every coefficient nonnegative**.

Then obtain an actual factorization of `F`, contradicting Frobenius gapness.

Conclude:

```text
0 ≤ C ≤ b2-1
```

## B-CAP

Similarly derive from SK:

```text
F =
  (h-1)*m
  + (a0-lambda+D0)*n0
  + (B-a1)*n1
  + (rho2-1)*n2
```

using the completed HCR identity

```text
-b0*n0 - a1*n1 + rho2*n2 = 0
```

Since:

```text
a0-lambda ≥ 1
```

show that `B ≥ a1` would give an actual nonnegative factorization of `F`.

Conclude:

```text
0 ≤ B ≤ a1-1
```

No signed identity by itself implies membership.

---

# 9. T6.4 — UNIFORM-I-CAP

This is the main Section 6 gate.

Define:

```text
eta   := nu - b2
theta := mu - a1
```

Derive the exact value identities:

```text
ANCH-A:
fA - qS = mu*n1 + eta*n2
```

and

```text
ANCH-B:
fB - qS = theta*n1 + nu*n2
```

Important:

```text
ANCH-B is only an identity of values.
```

Do not assume or use any new gap status for `fB`.

The required conclusion is:

```text
0 ≤ A  ≤ b0-1
0 ≤ D0 ≤ b0-1
```

Prove it by the exact exhaustive sign partition below.

---

# 10. T6.4.1 — eta ≥ 1

Lift SJ and SK to the same actual `fA`.

Derive genuine actual factorizations:

```text
fA =
  ell*m
  + A*n0
  + (mu-1)*n1
  + (C+eta)*n2
```

and

```text
fA =
  h*m
  + D0*n0
  + (B+mu)*n1
  + (eta-1)*n2
```

Explicitly prove all coefficients nonnegative under `eta ≥ 1`.

Then:

```text
A ≥ lambda
```

would allow removal of `lambda*n0` from that same actual factorization and give

```text
fA-lambda*n0 ∈ Γ
```

contradicting the actual `A_i(lambda)` gap.

Likewise for `D0`.

Conclude:

```text
A,D0 ≤ lambda-1 ≤ b0-1
```

Same-factorization provenance is mandatory.

---

# 11. T6.4.2 — theta ≥ 1

Use the actual gap:

```text
qAk = fA - nu*n2
```

Do not require a return of `B_j`.

From SJ plus one completed `R_k` identity derive:

```text
AK-J:
qAk =
  ell*m
  + (A-b0)*n0
  + (mu-a1-1)*n1
  + (C+a2)*n2
```

Under:

```text
theta = mu-a1 ≥ 1
```

prove every coefficient other than possibly `A-b0` nonnegative.

Hence:

```text
A ≥ b0
```

would give an actual factorization of the gap.

Conclude:

```text
A ≤ b0-1
```

Similarly derive from SK:

```text
AK-K:
qAk =
  h*m
  + (D0-b0)*n0
  + (B+mu-a1)*n1
  + (a2-1)*n2
```

and conclude:

```text
D0 ≤ b0-1
```

Do not assume any sign of `eta` in this branch.

---

# 12. T6.4.3 — eta = theta = 0

Handle this boundary separately.

From SJ derive the genuine factorization:

```text
fA =
  ell*m
  + A*n0
  + (mu-1)*n1
  + C*n2
```

and obtain:

```text
A ≤ lambda-1 ≤ b0-1
```

by same-factorization removal.

Use AK-K with:

```text
B+mu-a1 = B ≥ 0
```

to conclude:

```text
D0 ≤ b0-1
```

Do not lose this zero/zero boundary case.

---

# 13. T6.4.4 — REMAINING SIGN REGIONS

Close exactly these three regions.

## eta = 0, theta ≤ -1

Derive:

```text
mu ≤ a1-1
```

and the actual tail representation:

```text
qS+n2 =
  (rho0-1)*n0
  + (a1-mu-1)*n1
```

with nonnegative coefficients.

Thus:

```text
qS+n2 ∈ H
```

contradicting singleton/missing direction `2`.

## theta = 0, eta ≤ -1

Derive:

```text
nu ≤ b2-1
```

and:

```text
qS+n1 =
  (rho0-1)*n0
  + (b2-nu-1)*n2
∈ H
```

contradicting missing direction `1`.

## eta ≤ -1, theta ≤ -1

Derive:

```text
qS =
  (rho0-1)*n0
  + (-theta-1)*n1
  + (-eta-1)*n2
```

with all coefficients nonnegative.

Hence:

```text
qS ∈ H ⊆ Γ
```

contradicting the actual pseudo-Frobenius gap.

Prove formally that these sign cases together with the previous cases exhaust all integer pairs `(eta,theta)`.

Then conclude:

```text
UNIFORM-I-CAP:
0 ≤ A,D0 ≤ b0-1
```

---

# 14. T6.5 — RETURN LEVEL EXHAUSTION

The final proof has only three cases:

```text
ell = h
ell > h
h > ell
```

These must be exhaustive.

No minimization of `ell` or `h` is allowed or needed.

---

# 15. T6.5.1 — ell = h

Subtract KR from JR so that the `m` coefficient is completely eliminated.

Obtain the pure-H relation:

```text
(D0-A)*n0 + (B+1)*n1 = (C+1)*n2
```

Split:

```text
D0 ≥ A
D0 < A
```

## D0 ≥ A

The left side is nonnegative and positive.

By C-CAP:

```text
1 ≤ C+1 ≤ b2 < rho2
```

so a positive subcritical multiple of `n2` is represented by `n0,n1`.

Contradict `n2` criticality.

## D0 < A

Rewrite:

```text
(B+1)*n1 =
  (A-D0)*n0
  + (C+1)*n2
```

By B-CAP:

```text
1 ≤ B+1 ≤ a1 < rho1
```

contradict `n1` criticality.

Mandatory firewall:

```text
Herzog criticality is invoked only after m has vanished completely.
```

---

# 16. T6.5.2 — ell > h

Start from the actual F-expression obtained from SJ and substitute KR **exactly once**.

Derive:

```text
ABS-L:

F =
  (ell-h-1)*m
  + (P0+A-D0-1)*n0
  + (R-2-B)*n1
  + (C+T0)*n2
```

Prove all coefficients nonnegative.

Specifically:

```text
ell-h-1 ≥ 0
```

and using UNIFORM-I-CAP:

```text
P0+A-D0-1
  ≥ P0-b0
  = a0-lambda
  ≥ 1
```

using B-CAP and

```text
R = a1+g1
```

prove:

```text
R-2-B ≥ g1-1 ≥ 0
```

and clearly:

```text
C+T0 ≥ 0
```

Thus ABS-L is a genuine actual factorization of `F`.

Contradict Frobenius gapness.

---

# 17. T6.5.3 — h > ell

Symmetrically, but prove directly rather than saying “same”.

Substitute JR exactly once into the F-expression from SK and derive:

```text
ABS-R:

F =
  (h-ell-1)*m
  + (P0+D0-A-1)*n0
  + (B+R)*n1
  + (T0-2-C)*n2
```

Prove:

```text
h-ell-1 ≥ 0
```

and:

```text
P0+D0-A-1
  ≥ P0-b0
  = a0-lambda
  ≥ 1
```

and:

```text
B+R ≥ 0
```

and by C-CAP:

```text
T0-2-C
  ≥ T0-b2-1
  = a2-nu-1
  ≥ 0
```

Hence ABS-R is a genuine factorization of `F`.

Contradiction.

---

# 18. T6 CLOSURE

The three level orderings are exhaustive.

Conclude the exact theorem:

```lean
theorem TypeIIInput.impossible ... : False
```

with:

```text
additional mathematical assumptions = 0
project-specific axioms = 0
```

Do not depend on a return of `B_j`.

Do not use PATH exclusion to prove the local Type II contradiction.

---

# 19. POST-TYPE-II INTEGRATION

After the local T6 theorem is complete, use the FROZEN post-PATH wrapper:

```lean
TerminalInputAfterPath
```

which contains exactly:

```text
TYPE II ∨ CHAIN
```

Eliminate only the TYPE II disjunct.

Introduce NEW wrapper definitions/theorems; do not edit FROZEN ones.

A natural structure is conceptually:

```lean
def SelectedTerminalAfterTypeII ... : Prop :=
  ∃ C : ChainInput s F D,
    C.values = selectedValues rows
```

and an orientation-preserving:

```lean
TerminalInputAfterTypeII
```

mirroring the existing post-PATH two-orientation wrapper.

Prove:

```text
TerminalInputAfterPath
→
TerminalInputAfterTypeII
```

using `TypeIIInput.impossible`.

Then add residual-free wrappers conceptually:

```lean
nonsymmetric_selected_four_after_typeII
nonsymmetric_Q_ge_four_after_typeII
```

The selected four actual row values must remain unchanged.

On success the exact terminal frontier becomes:

```text
CHAIN ONLY
```

Do not begin Section 7.

---

# 20. FROZEN SOURCE POLICY

Every mathematical Lean source existing at base commit

```text
707d9386037e8bcdec9c9bfb02f95731c9ce2597
```

is protected.

Expected mathematical source changes:

```text
NEW TypeII/T6 modules only
```

Do not modify:

```text
TypeIIInput
Extraction.lean
PathInput
P5 source
M3 source
ColorCap source
SelectedExtraction
Herzog source
C2 source
```

If a mathematical source change is genuinely necessary, stop and report:

```text
SOURCE CHANGE REQUIRED
FROZEN RE-AUDIT REQUIRED
```

Do not silently patch a FROZEN file.

Documentation/status files and new verification/CI files may be changed.

---

# 21. SUGGESTED MODULE LAYOUT

Prefer small NEW modules, for example:

```text
P21/Nonsymmetric/TypeII/
  Setup.lean
  Returns.lean
  EndpointCaps.lean
  UniformCap.lean
  LevelExhaustion.lean
  Exclusion.lean
  Integration.lean
```

Exact split may differ.

The proof is short enough that unnecessary abstraction should be avoided.

---

# 22. DANGEROUS INTERFACE REGRESSIONS

Add explicit theorem-level regression gates for at least:

```text
1. original TypeIIInput statement unchanged

2. lambda ≤ b0 remains present and is actually used
   in C-CAP / ABS-L / ABS-R

3. SJ/SK are genuine actual returns

4. the added generator has coefficient zero
   by same-factorization removal

5. SJ/SK m-levels are positive
   from missing directions

6. JR/KR remain signed identities only

7. no actual return of Bj is required by the main T6 theorem

8. fB in ANCH-B is used only as a value identity;
   no new gap hypothesis for fB

9. eta ≥ 1 branch uses same-fA actual factorizations

10. theta ≥ 1 branch does not assume sign(eta)

11. eta=theta=0 boundary is present

12. all three remaining nonpositive sign regions are present

13. UNIFORM-I-CAP is proved for both A and D0

14. ell=h invokes criticality only after m elimination

15. ABS-L final coefficients are all nonnegative

16. ABS-R final coefficients are all nonnegative

17. TypeIIInput.impossible has no added mathematical assumptions

18. post-Type-II wrapper contains CHAIN only

19. selected four values are preserved through integration
```

---

# 23. PROOF-DEBT / AXIOM POLICY

Forbidden:

```text
sorry
admit
axiom
sorryAx
unsafe proof escape
opaque project theorem
native_decide as theorem substitute
run_tac proof generation
external result asserted as proof
```

Required:

```text
project-specific axioms = 0
proof debt = 0
```

Expected allowed foundations only:

```text
propext
Classical.choice
Quot.sound
```

as actually required.

---

# 24. DEPENDENCY FIREWALL

Required direction:

```text
FROZEN C2 / Herzog / TypeIIInput
        ↓
new T6 setup
        ↓
actual singleton returns
        ↓
endpoint caps
        ↓
uniform-I-cap
        ↓
level-order exhaustion
        ↓
TypeIIInput.impossible
        ↓
post-Type-II CHAIN-only wrapper
```

Do not import mathematical results from:

```text
Section 7
Section 8
Section 9
Section 10
CHAIN closure
final Problem 21 theorem
```

No circular use of a theorem whose conclusion already assumes TYPE II impossible.

Reuse of a genuinely generic low-level helper from P5 is acceptable only if it has no dependency on PATH exclusion.

---

# 25. FRESH VERIFICATION

After implementation, run fresh verification.

At minimum:

```bash
lake build
```

Explicitly build every NEW T6 module.

Rerun all FROZEN milestone suites:

```text
M1
M2A
M2B
M3A
M3B1
M3B2
P5
```

Add:

```text
verification/t6/
```

with:

```text
declaration inventory
statement inspection
axiom inspection
proof-debt scan
dependency DAG
circularity scan
frozen-source integrity
new-module list
fresh root build log
frozen milestone regression logs
```

---

# 26. P5 AUDIT PACKAGING MINOR — FIX NOW

The independent P5 TRUE AUDIT found one non-mathematical packaging MINOR:

```text
P21_P5_TRUE_AUDIT_EVIDENCE
did not contain EVIDENCE_SHA256.json
```

Do not modify P5 mathematical source.

For T6, explicitly generate:

```text
EVIDENCE_SHA256.json
```

**before** artifact upload.

It must contain SHA-256 hashes for every evidence file in the artifact except itself, or use another clearly documented non-self-referential convention.

The T6 workflow must verify this manifest before upload.

This packaging repair is mandatory for the T6 candidate.

---

# 27. GITHUB CI

Create a T6-specific workflow, for example:

```text
.github/workflows/t6-audit.yml
```

CI must run on a clean GitHub runner against the exact candidate commit and record:

```text
branch
exact HEAD SHA
run ID
attempt

Lean version
Lake version
mathlib revision

candidate ZIP SHA-256
frozen-source integrity

fresh root build
explicit T6 module build

M1 regression
M2A regression
M2B regression
M3A regression
M3B1 regression
M3B2 regression
P5 regression
T6 verification

proof-debt scan
axiom scan
statement inspection
dependency/circularity check

EVIDENCE_SHA256 verification
```

Do not use project-owned compiled artifacts to bypass source compilation.

---

# 28. CANDIDATE PACKAGE

On success create exactly one principal candidate ZIP:

```text
P21_LEAN_T6_TYPEII_EXCLUSION_CANDIDATE_20260918.zip
```

Include:

```text
complete Lean project
all new TypeII modules

README_T6.md
SOURCE_OF_TRUTH_T6.md
T6_STATEMENT_MAP.md
T6_PROOF_ROUTE.md
T6_DEPENDENCY_DAG.md

NEXT_RESTART.md

verification/t6/
CI workflow
candidate SHA manifest
```

Compute and report SHA-256.

---

# 29. TRUE AUDIT ARTIFACT

Upload exactly one principal artifact:

```text
P21_T6_TRUE_AUDIT_EVIDENCE
```

It must include:

```text
RUN_CONTEXT
COMMIT_SHA
ENVIRONMENT

ROOT_BUILD_LOG
T6_MODULE_LIST
T6_BUILD_LOG
T6_VERIFICATION_LOG

M1_ORIGINAL_SUITE
M2A_ORIGINAL_SUITE
M2B_ORIGINAL_SUITE
M3A_ORIGINAL_SUITE
M3B1_ORIGINAL_SUITE
M3B2_ORIGINAL_SUITE
P5_ORIGINAL_SUITE

PROOF_DEBT_REPORT
AXIOM_REPORT
AXIOM_SUMMARY
STATEMENT_INSPECTION
DEPENDENCY_DAG_CHECK
CIRCULARITY_CHECK
FROZEN_SOURCE_INTEGRITY
VERIFIED_SOURCE_SHA256

candidate ZIP SHA
EVIDENCE_SHA256.json
```

Report:

```text
artifact ID
GitHub-provided artifact digest
```

---

# 30. SUCCESS GATE

You may return

```text
T6 TYPE II EXCLUSION CANDIDATE FOR TRUE AUDIT
```

only if all hold:

```text
[ ] exact TypeIIInput unchanged
[ ] no added mathematical hypotheses

[ ] two actual singleton returns proved
[ ] missing coordinates proved zero
[ ] positive m-levels proved

[ ] JR/KR proved

[ ] C-CAP proved
[ ] B-CAP proved

[ ] ANCH-A proved
[ ] ANCH-B used only as value identity

[ ] eta≥1 region closed
[ ] theta≥1 region closed
[ ] eta=theta=0 closed
[ ] eta=0,theta≤-1 closed
[ ] theta=0,eta≤-1 closed
[ ] eta≤-1,theta≤-1 closed
[ ] sign regions exhaustive

[ ] UNIFORM-I-CAP proved for A,D0

[ ] ell=h closed by pure-H criticality
[ ] ell>h closed by actual F absorption
[ ] h>ell closed by actual F absorption

[ ] TypeIIInput.impossible proved
[ ] no actual Bj return used as a hypothesis

[ ] post-Type-II CHAIN-only wrapper proved
[ ] selected four values preserved

[ ] project-specific axioms = 0
[ ] proof debt = 0
[ ] frozen mathematical source unchanged

[ ] fresh root build PASS
[ ] explicit T6 build PASS
[ ] M1–M3B2 regressions PASS
[ ] P5 regression PASS
[ ] T6 verification PASS

[ ] clean GitHub CI PASS
[ ] candidate digest recorded
[ ] artifact digest recorded
[ ] EVIDENCE_SHA256.json present and verified
```

---

# 31. PARTIAL / NO-GO POLICY

If exact TYPE II closure fails, do not fake completion.

Return:

```text
T6 PARTIAL — TYPE II OPEN
```

or:

```text
T6 NO-GO / INTERFACE OBSTRUCTION
```

Identify the **first exact unproved lemma** with:

```text
exact Lean statement
publication Section 6 anchor
proved dependencies
remaining mathematical gap
whether the obstruction is mathematical or FROZEN-API related
```

If a protected mathematical file must change:

```text
SOURCE CHANGE REQUIRED
FROZEN RE-AUDIT REQUIRED
```

Do not silently change it.

Still package the strongest exact partial state.

---

# 32. STATUS LANGUAGE

Codex must not self-award:

```text
TRUE AUDIT PASS
FROZEN
AUDITED
TYPE II CLOSED
```

The strongest permitted success status is:

```text
T6 TYPE II EXCLUSION CANDIDATE FOR TRUE AUDIT
```

Independent Commander review decides whether T6 becomes FROZEN.

---

# 33. FINAL REPORT

Report in Japanese.

Begin with exactly one of:

```text
T6 TYPE II EXCLUSION CANDIDATE FOR TRUE AUDIT
```

```text
T6 PARTIAL — TYPE II OPEN
```

```text
T6 NO-GO / INTERFACE OBSTRUCTION
```

Then report:

```text
Repository:
Branch:
Frozen base:
Candidate commit:

Primary theorem:
TypeIIInput unchanged:

§6.2 exact input:
§6.3 returns:
§6.4 endpoint caps:
§6.5 uniform-I-cap:
§6.6 equal levels:
§6.6 ell>h:
§6.6 h>ell:
T6 closure:

Post-Type-II wrapper:
Terminal frontier:
Next frontier:

New Lean modules:
New audited declarations:

Proof debt:
Project-specific axioms:
FROZEN mathematical source integrity:

Root build:
Explicit T6 build:

M1:
M2A:
M2B:
M3A:
M3B1:
M3B2:
P5:
T6 verification:

GitHub workflow:
Run ID:
Attempt:
Conclusion:

Candidate ZIP:
Candidate SHA-256:

Artifact:
Artifact ID:
Artifact digest:
EVIDENCE_SHA256:
EVIDENCE_SHA256 verification:

SOURCE_CHANGED:
```

On full success:

```text
SOURCE_CHANGED: NO
```

must mean no pre-existing mathematical Lean source changed.

The exact next frontier after successful T6 is:

```text
SECTIONS 7–10 — CHAIN
```

Do not begin CHAIN in this milestone.

Execute T6 completely now.
