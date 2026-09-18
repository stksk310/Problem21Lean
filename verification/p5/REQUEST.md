# P21 LEAN — P5 PATH EXCLUSION

## SECTION 5 / PAIR–PFREE / ROOT NORMALIZATION / DOUBLE-UNIT ENDGAME

This is the next bounded formalization milestone in `Problem21Lean`.

The preceding independent TRUE AUDIT has established:

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
```

Do not reopen or re-prove any of these.

The new mathematical frontier is exactly:

```text
SECTION 5 — PATH EXCLUSION
```

---

# 0. REPOSITORY / FROZEN BASE

Repository:

```text
https://github.com/stksk310/Problem21Lean
```

The new immutable mathematical base is the independently audited commit:

```text
fd4ea0c7cbc57df6e935790a1387242bcf9e0087
```

Current source branch:

```text
m3b2-dpe-box-positive-exit
```

Create a new branch from **exactly** that commit, preferably:

```text
p5-path-exclusion
```

Do not merge to `main`.

---

# 1. DOCUMENTATION STATUS CORRECTION

Before mathematical implementation, make a **documentation-only** correction to the current restart/status files.

The old sentence saying that “terminal branch exclusion is needed to turn selected-four terminal input into FULL G4” is obsolete.

The independently audited state is now:

```text
FULL G4 / nonsymmetric selected-four classification
CLOSED / FROZEN
```

The correct next frontier is:

```text
PATH exclusion
```

Update only status/documentation files as needed.

Do **not** modify any pre-existing mathematical Lean source for this correction.

---

# 2. PRIMARY TARGET

The exact frozen PATH input is:

```lean
P21.Nonsymmetric.PathInput
```

with fields already containing:

```text
lambda, nu, R
qL, qA, qB, qR

all four actual Q memberships
four-row distinctness

left singleton
right singleton

qA = fA - nu*n₂
qB = fB - lambda*n₀

missing directions
arm ranges

1 ≤ R < rho₁

all four exact complements
BOX-W
three exact ladder identities
```

The central milestone theorem should be an unconditional contradiction of the existing PATH input, conceptually:

```lean
theorem path_input_impossible
    {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g)
    (P : PathInput s F D) :
    False := by
  ...
```

Exact naming may differ.

Do not strengthen `PathInput`.

Do not add nonsymmetry, extra gcd assumptions, extra return minimality, or preselected factorizations unless they are derived from the existing hypotheses.

---

# 3. SOURCE OF TRUTH

Use this hierarchy:

```text
1. reference_inputs/
   P21_Journal_of_Algebra_Submission_Manuscript_FINAL_20260916.pdf

2. reference_inputs/
   P21_MANUSCRIPT_EN_FINAL_20260908_v1.zip
   sections/05.md
   sections/05.tex

3. reference_inputs/
   P21_FINAL_FROZEN_VERIFICATION_EDITION_20260907.zip
   05_PATH.md

4. adopted PATH audits:
   PATH_PFREE_SIGN_INTERFACE_INDEPENDENT_AUDIT.md
   PATH_ENDPOINT_LEVEL_INDEPENDENT_AUDIT.md
   PATH_DOUBLE_UNIT_INDEPENDENT_AUDIT.md
```

The publication Section 5 controls theorem scope and branch exhaustion.

The frozen verification edition and adopted audits control detailed provenance and known historical repair points.

---

# 4. ABSOLUTE FIREWALLS

Maintain all existing project firewalls.

## Actuality

Actual semigroup factorizations use nonnegative coefficients.

Signed identities for `m`, HCR zero-relations, ROOTs, M+/M−, etc. are **not** actual factorizations unless nonnegativity is separately proved.

## Same-element provenance

All packet replacements must occur inside an explicitly named factorization of the same element.

Do not choose a new unrelated factorization after using a coefficient from an old one.

## Criticality

Herzog criticality may only be applied to a **pure-H relation after the m-coordinate has been completely eliminated**.

Never apply criticality directly to a signed root involving `m`.

## Gap absorption

Whenever a branch is killed by showing

```text
q ∈ Γ
```

or

```text
F ∈ Γ
```

display an actual coefficientwise nonnegative factorization of that same element.

## Selected-row identity

Keep the original:

```text
Γ
F
m
W
qL
qA
qB
qR
```

fixed throughout Section 5 except under a formally proved full left-right relabeling.

---

# 5. P5.0 — RECONSTRUCT THE PUBLICATION COORDINATES

From an arbitrary `P : PathInput s F D`, define proof-local abbreviations corresponding to publication notation:

```text
lambda = P.lambda
nu     = P.nu

beta  = D.b 0 - lambda
alpha = D.a 2 - nu

P0 = D.rho 0 - lambda
R  = P.R
T  = D.rho 2 - nu
```

Avoid using bare `P` for both the Lean structure and the scalar publication `P`; choose an unambiguous Lean scalar name such as `P0`.

Derive:

```text
beta ≥ 1
alpha ≥ 1
P0 = D.a 0 + beta
T  = D.b 2 + alpha
1 ≤ R < D.rho 1
```

and the canonical row identities from the existing complement and ladder data.

Do not add these identities as new fields to `PathInput`.

Prove them in new PATH modules.

---

# 6. P5.1 — CENTRAL MATCH-OR-SEAM

This is the first major gate.

By C2 / existing row facts, derive actual tail factorizations of:

```text
qA + m ∈ H
qB + m ∈ H
```

Define a PAIR exactly in the publication sense:

```text
qA + m = X*n0 + H0*n1 + (Z+alpha)*n2
qB + m = (X+beta)*n0 + H0*n1 + Z*n2

X,H0,Z ≥ 0
```

PAIR must be represented as a proposition/structure carrying actual nonnegative coefficients.

Do not treat a signed equality as a PAIR.

---

# 7. NO-PAIR NORMALIZATION

If no PAIR exists, normalize genuine factorizations of `qA+m` and `qB+m` by HCR packet replacement within the same actual element.

Reach the exact ranges:

```text
qA+m = X*n0 + H0*n1 + K*n2

0 ≤ X  < rho0
0 ≤ H0 < rho1
0 ≤ K  < alpha
```

and

```text
qB+m = Y*n0 + J0*n1 + L*n2

0 ≤ Y  < beta
0 ≤ J0 < rho1
0 ≤ L  < rho2
```

The termination measure must be explicit.

Do not assume normal forms exist by informal reduction.

In particular:

* when removing a `j`-packet, prove the actual coefficient remains nonnegative;
* if an `i`-coefficient reaches `rho_i`, prove the HCR replacement produces the threshold needed to construct a PAIR;
* similarly for the `k`-coefficient on the other side.

---

# 8. CENTRAL COMPARISON / PFREE

Compare the two normalized actual factorizations.

Define:

```text
Ac = X + beta - Y
Bc = alpha + L - K
```

and obtain the pure-H relation

```text
Ac*n0 + (H0-J0)*n1 = Bc*n2
```

with

```text
Ac > 0
Bc > 0
```

Handle all three cases:

```text
H0 < J0
H0 = J0
H0 > J0
```

## H0 < J0

Follow the publication sign split exactly.

After one `R_i` comparison, inspect the four sign patterns.

Every criticality call must be on a pure-H relation.

Derive exactly:

```text
Ac = rho0
J0-H0 = b1
Bc = a2
```

and hence the PFREE_i kernel:

```text
qA+m =
  (Y + a0 + lambda)*n0
  + H0*n1
  + K0*n2

qB+m =
  Y*n0
  + (H0+b1)*n1
  + (K0+nu)*n2
```

with

```text
0 ≤ Y  < beta
0 ≤ K0 < alpha
0 ≤ H0 < a1
```

## H0 = J0

Exclude it via pure-H criticality exactly as Section 5 does.

## H0 > J0

Do not say “by symmetry” informally.

Formalize the **full left-right reversal**.

---

# 9. P5-DUAL — FULL LEFT-RIGHT REVERSAL

Implement or prove a reusable PATH reversal transport carrying:

```text
0 ↔ 2
1 fixed

n0 ↔ n2

(a0,b0) ↔ (b2,a2)
(a1,b1) ↔ (b1,a1)
(a2,b2) ↔ (b0,a0)

lambda ↔ nu
alpha ↔ beta

P0 ↔ T
R fixed

qL ↔ qR
qA ↔ qB
```

and preserving:

```text
Γ
F
m
W
HCR
arm ranges
singleton status
actual Q membership
complements
ladder
PathInput validity
```

Prefer a genuine structure-level relabel theorem if existing relabel APIs support it.

Do not implement a purely syntactic “dual theorem assumption”.

The reversal is needed in both P5.1 and later PAIR/PFREE branches.

---

# 10. P5.2 — PAIR ⇒ STRONG PORT / WEAK ROOT

From a genuine PAIR derive the exact signed identity:

```text
m =
  (X-a0+1)*n0
  + (H0+1)*n1
  + (Z-b2+1)*n2
```

Define:

```text
t0 = rho1-H0-1
```

and prove:

```text
1 ≤ t0 < rho1
```

Derive the two exact gap expressions for `qA` and `qB`.

Using actual gapness, prove the two disjunctions on `X,Z`.

Do not infer a coefficient sign merely because an expression “looks like a factorization”.

Then exclude the forbidden quadrant that would represent `m` nonnegatively in `H`.

Use formal left-right reversal to reduce to the strong-left case:

```text
X ≤ a0-2
Z ≥ T-1
```

Define:

```text
d = a0-1-X
S = H0+1
e = Z-b2+1
```

and obtain the WEAK-ROOT:

```text
m = -d*n0 + S*n1 + e*n2

1 ≤ d ≤ a0-1
S ≥ 1
e ≥ alpha
```

This ROOT is a signed identity only.

---

# 11. P5.3 — ACTUAL ENDPOINT RETURNS

For the same actual left singleton `qL`, use pseudo-Frobenius return properties to obtain genuine factorizations:

```text
qL+n1 = ell*m + A*n0 + C*n2
ell ≥ 1
A,C ≥ 0
```

and

```text
qL+n2 = Lk*m + Ak*n0 + Bk*n1
Lk ≥ 1
Ak,Bk ≥ 0
```

The missing coordinate must be proved zero by same-factorization removal.

The positive `m` level must be derived from singleton / missing-direction information.

Do not assume:

```text
return uniqueness
minimal return level
special support selection
```

The publication explicitly does not need them.

---

# 12. P5.3.3 — ROOT WALLS

Prove from **any WEAK-ROOT**:

```text
1 ≤ S < R
e ≥ T
```

in that order.

The order matters.

First use the actual `qL+n2` return to prove `S<R` by showing `S≥R` would give an actual factorization of `qA`.

Then return to the same `W` and prove `e≥T` by showing `e≤T-1` would give `F∈Γ`.

Define:

```text
K = e-alpha
```

and derive:

```text
K ≥ b2
```

This lemma must depend only on the WEAK-ROOT hypotheses and frozen PATH data, not on its original derivation from PAIR.

It must therefore be reusable after ROOT normalization.

---

# 13. P5.3.4 — FINITE ROOT NORMALIZATION

This is a critical audit point.

If

```text
K ≥ rho2
```

apply the pure HCR identity

```text
rho2*n2 = b0*n0 + a1*n1
```

to rewrite the **same signed equality** as:

```text
m = -d'*n0 + S'*n1 + e'*n2

d' = d-b0
S' = S+a1
e' = e-rho2
```

Show:

```text
e' ≥ alpha
S' ≥ 1
```

If:

```text
d' ≤ 0
```

derive a genuine nonnegative representation contradicting multiplicity.

Otherwise prove:

```text
1 ≤ d' ≤ a0-1
S' ≥ 1
e' ≥ alpha
```

so the full WEAK-ROOT hypotheses are preserved.

Then reapply the ROOT WALL lemma and define:

```text
K' = e'-alpha = K-rho2
```

with:

```text
0 < K' < K
```

Use an explicit well-founded positive-integer descent.

Do not assume the original K was already subcritical.

Do not assume:

```text
b0 > a0
```

At termination obtain:

```text
NORMALIZED-ROOT

m = -d*n0 + S*n1 + (K+alpha)*n2

1 ≤ d ≤ a0-1
1 ≤ S < R
b2 ≤ K < rho2
```

while preserving the same:

```text
Γ,F,m,W,qL,qA
```

and the same actual LJ/LK returns.

---

# 14. P5.3.5 — ENDPOINT LEVEL ≥ 2

Fix any genuine LJ:

```text
qL+n1 = ell*m + A*n0 + C*n2
```

First prove the C-cap:

```text
0 ≤ C ≤ b2-1
```

using the completed HCR repair of an exact F identity.

Then suppose:

```text
ell = 1
```

Use the NORMALIZED-ROOT to derive:

```text
0 ≤ A ≤ d-1
```

Finally eliminate `m` completely and obtain the pure-H relation:

```text
V*n2 =
  (d-A-1)*n0
  + (R-S)*n1
```

where

```text
V = C+K-b2+1
```

and prove:

```text
1 ≤ V ≤ K < rho2
```

The right side is nonnegative and positive.

Only now invoke `n2` criticality.

Conclude:

```text
ell ≥ 2
```

for every genuine LJ.

This theorem is one of the historically delicate PATH interfaces. Preserve the exact actuality/criticality order.

---

# 15. P5.3.6 — ONE-STEP FROBENIUS ABSORPTION

Insert the normalized ROOT once into LJ and prove the exact final identity:

```text
F =
  (ell-2)*m
  + (P0+A-d)*n0
  + (S-1)*n1
  + (C+K+alpha)*n2
```

Prove every coefficient nonnegative:

```text
ell-2 ≥ 0
P0+A-d ≥ beta+1 > 0
S-1 ≥ 0
C+K+alpha > 0
```

This must be a genuine factorization of **F itself**.

Conclude contradiction with Frobenius gapness.

Therefore the strong-left PAIR branch is impossible.

Use the proved full dual transport for the opposite PAIR orientation.

---

# 16. P5.4 — PFREE SIGN DETERMINATION

From the exact PFREE_i kernel define:

```text
eta = nu-b2

A0 = Y+lambda+1
B0 = H0+1
C0 = T-K0-1

D0 = P0-Y-1
E0 = H0+b1+1
F0 = K0+eta+1
```

derive the two exact signed identities:

```text
M+:
m = A0*n0 + B0*n1 - C0*n2

M-:
m = -D0*n0 + E0*n1 + F0*n2
```

and:

```text
A0+D0 = rho0
E0-B0 = b1
C0+F0 = a2
```

Do **not** assume the sign of `eta` or `F0`.

The entire purpose of P5.4 is to prove:

```text
F0 ≥ 1
```

---

# 17. P5.4.2–P5.4.5 — EXCLUDE F0 ≤ 0

Assume:

```text
F0 ≤ 0
```

and derive the publication consequences for `C0` and `T`.

For the same actual right singleton `qR`, obtain genuine returns:

```text
qR+n0 = s*m + U*n1 + V*n2
s ≥ 1
U,V ≥ 0
```

and

```text
qR+n1 = r*m + X*n0 + Z*n2
r ≥ 1
X,Z ≥ 0
```

Again derive the missing coordinate zero and positive m-level from actuality, not by assumption.

Construct the exact F absorption certificates:

```text
J-FABS
I-FABS
U-CERT
X-CERT
```

and prove:

```text
r = 1
s = 1

0 ≤ U ≤ b1-1
0 ≤ X ≤ a0-1
```

Then eliminate m completely between the two unit returns:

```text
(X+1)*n0 =
  (U+1)*n1 + (V-Z)*n2
```

Handle:

```text
V ≥ Z
V < Z
```

by pure-H criticality.

Conclude:

```text
PFREE_i ∩ {F0 ≤ 0} = ∅
```

therefore:

```text
F0 ≥ 1
```

Do not import this sign from an older historical proof.

---

# 18. P5.5 — PFREE TWO-RETURN ABSORPTION

Now work only after `F0 ≥ 1` has been proved.

Take a genuine left return LJ again.

Derive:

```text
C ≤ b2-1
A ≤ D0-1
```

and the exact F absorption:

```text
F =
  (ell-2)*m
  + (P0+A-D0)*n0
  + (E0-1)*n1
  + (C+F0)*n2
```

If:

```text
ell ≥ 2
```

this is a genuine F-factorization.

Hence any surviving case has:

```text
ell = 1
```

Then compare with M+ and perform the exact `Qc<0 / Qc≥0` split.

Do not use the historically unnecessary extra upper bound on `Kc-a2`.

For the `Qc≥0` branch, use the repaired argument:

```text
Pc = rho0
```

then

```text
(Qc-b1)*n1 + (Kc-a2)*n2 = 0
```

and prove directly:

```text
Qc = b1
Kc = a2
```

via subcritical j/k criticality.

Obtain exact `FIX-J`.

---

# 19. SECOND LEFT RETURN / DOUBLE-UNIT REDUCTION

Take the other genuine return:

```text
qL+n2 = L*m + D*n0 + B*n1
```

derive the corresponding F identity.

If:

```text
L ≥ 2
```

absorb F directly.

Thus only the double-unit case survives:

```text
qL+n1 = m + A*n0 + C*n2

qL+n2 = m + D*n0 + B*n1
```

with all coefficients nonnegative and FIX-J still active.

---

# 20. P5.6 — DOUBLE-UNIT ENDGAME

Follow the adopted audited repair.

First retain:

```text
0 ≤ C ≤ b2-1
A < P0 < rho0
```

Eliminate m between the two unit returns:

```text
(D-A)*n0 + (B+1)*n1 = (C+1)*n2
```

Handle:

```text
D ≥ A
D < A
```

with pure-H criticality.

In the surviving branch subtract `R_j` once and derive the unique PIN:

```text
D = A-a0
B = rho1-1
C = b2-1
```

Criticality must again only see pure-H relations.

---

# 21. P5.6.4 — NEW EXACT ROOTS

Compare FIX-J with PIN and derive exactly:

```text
F0 = alpha
T-nu = K0+1 ≥ 1
C0 = nu
```

Then obtain the signed roots:

```text
ROOT+:
m = A0*n0 + (H0+1)*n1 - nu*n2
```

with `A0>0`, and

```text
ROOT-T:
m = -(D+1)*n0 - mu*n1 + T*n2
```

where:

```text
mu = rho1-R ≥ 1
```

These are signed identities, not actual factorizations.

---

# 22. P5.6.5 — OPPOSITE SINGLETON RETURN

For the same actual right singleton `qR`, take a genuine missing-j return:

```text
qR+n1 = r*m + X*n0 + Z*n2

r ≥ 1
X,Z ≥ 0
```

If:

```text
r ≥ 2
```

use ROOT+ exactly once and obtain:

```text
F =
  (r-2)*m
  + (X+A0)*n0
  + H0*n1
  + (T+Z-nu)*n2
```

with all coefficients nonnegative.

If:

```text
r = 1
```

derive:

```text
0 ≤ Z ≤ nu-1
```

Then combine ROOT-T with the same actual return and the canonical `qR` identity to obtain:

```text
(P0+D+a0-X)*n0 =
  (alpha+Z+1)*n2
```

Prove:

```text
1 ≤ alpha+Z+1 ≤ alpha+nu = a2 < rho2
```

The left coefficient need not have a prior lower bound; positivity follows from equality with the positive right side.

Apply pure-H k-criticality.

Conclude the double-unit branch impossible.

Use full left-right reversal for the dual PFREE orientation.

---

# 23. P5.7 — PATH CLOSURE

Prove the exhaustive chain:

```text
central actual returns
→ PAIR ∨ PFREE_i ∨ dual(PFREE_i)

PAIR
→ impossible by P5.2–P5.3

PFREE_i
→ F0≥1 by P5.4
→ direct absorption or double-unit
→ impossible by P5.5–P5.6

dual PFREE
→ impossible by formal full reversal
```

Conclude:

```lean
theorem path_input_impossible
    ...
    (P : PathInput s F D) :
    False
```

with no additional mathematical assumptions.

---

# 24. DOWNSTREAM INTEGRATION

Once PATH is eliminated, add new wrapper theorems only.

Do not edit the FROZEN selected-four theorem.

From:

```lean
nonsymmetric_selected_four
```

and existing:

```text
TerminalInputExists =
  PATH ∨ TYPE II ∨ CHAIN
```

derive a residual-free post-PATH wrapper returning only:

```text
TYPE II ∨ CHAIN
```

while retaining exactly the same selected-four values and same semigroup.

A natural new Prop or theorem may be introduced, for example conceptually:

```text
SelectedTerminalAfterPath =
  TypeIIInput ∨ ChainInput
```

but do not alter the existing definition of `TerminalInputExists`.

Also add the corresponding `Q.ncard ≥ 4` wrapper if pure composition permits.

The next frontier after successful P5 is:

```text
SECTION 6 — TYPE II EXCLUSION
```

Do not begin Section 6 in this milestone.

---

# 25. SUGGESTED NEW MODULES

Prefer only NEW mathematical Lean source.

For example:

```text
P21/Nonsymmetric/Path/
  Setup.lean
  Returns.lean
  Pair.lean
  NoPairNormalization.lean
  Dual.lean
  WeakRoot.lean
  RootNormalization.lean
  EndpointLevel.lean
  PFreeSign.lean
  PFreeAbsorption.lean
  DoubleUnit.lean
  Closure.lean
  Integration.lean
```

Exact decomposition may differ.

Keep each module narrow enough to audit independently.

---

# 26. FROZEN SOURCE POLICY

Every mathematical Lean source existing at base commit

```text
fd4ea0c7cbc57df6e935790a1387242bcf9e0087
```

is protected.

Expected mathematical source changes:

```text
NEW PATH modules only
```

Do not edit:

```text
PathInput
M3 extraction
M3B1
M3B2
COLOR-CAP
SelectedExtraction
Herzog data
C2
```

If a mathematical source change is genuinely unavoidable, STOP and report:

```text
SOURCE CHANGE REQUIRED
FROZEN RE-AUDIT REQUIRED
```

Documentation / new verification / new CI files are allowed.

---

# 27. REGRESSION / DANGEROUS INTERFACE TESTS

Create explicit theorem-level regression gates for at least:

```text
- exact existing PathInput statement unchanged
- qA/qB labels are ladder labels, not Herzog color names
- PAIR coefficients are genuinely nonnegative
- no-PAIR normalization preserves the same actual element
- full left-right reversal preserves all PATH data
- ROOT is signed, never automatically actual
- ROOT normalization strictly decreases K
- ROOT normalization preserves every WEAK-ROOT hypothesis
- endpoint ell=1 contradiction applies criticality only after m elimination
- F0 sign is proved, not assumed
- eta may have either sign before P5.4 closes it
- r=s=1 unit comparison is pure-H
- FIX-J uses the repaired Qc argument without the obsolete bound
- double-unit PIN criticality is pure-H
- final F absorptions have all coefficients nonnegative
- opposite endpoint r=1 bound uses the same actual return
- dual PFREE branch uses formal transport
- final theorem has no added hypotheses
- post-PATH wrapper retains selected actual row values
```

---

# 28. PROOF-DEBT / AXIOM POLICY

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
external computation asserted as proof
```

Project-specific axioms must remain:

```text
0
```

Expected permitted roots only:

```text
propext
Classical.choice
Quot.sound
```

as actually required.

---

# 29. DEPENDENCY FIREWALL

Required direction:

```text
FROZEN C2 / Herzog / M3 / PathInput
        ↓
new P5 setup and actual returns
        ↓
PAIR / PFREE split
        ↓
PAIR root branch
        ↓
PFREE sign
        ↓
PFREE absorption
        ↓
double-unit
        ↓
path_input_impossible
        ↓
post-PATH TYPE II ∨ CHAIN wrapper
```

No import from:

```text
Section 6 TYPE II exclusion
Section 7–10 CHAIN
final theorem
```

into P5.

No circular use of a theorem whose proof already assumes PATH is impossible.

---

# 30. FRESH VERIFICATION

After implementation, run a fresh build.

At minimum:

```bash
lake build
```

Explicitly build every NEW P5 mathematical module.

Then rerun all frozen milestone suites:

```text
M1
M2A
M2B
M3A
M3B1
M3B2
```

Add:

```text
verification/p5/
```

with:

```text
declaration inventory
statement inspection
axiom inspection
proof-debt scan
dependency DAG
circularity scan
frozen-source SHA inventory
new-module list
fresh build log
old-suite regression logs
```

---

# 31. GITHUB CI

Create a clean GitHub Actions workflow, for example:

```text
.github/workflows/p5-audit.yml
```

CI must bind evidence to an exact candidate commit and record:

```text
branch
exact head SHA
run ID
attempt

Lean version
Lake version
mathlib revision

frozen-source integrity
candidate ZIP digest

fresh root build
explicit P5 module build

M1 regression
M2A regression
M2B regression
M3A regression
M3B1 regression
M3B2 regression
P5 verification

proof-debt scan
axiom scan
statement inspection
dependency/circularity scan
```

No project-owned compiled artifacts may bypass compilation.

---

# 32. CANDIDATE PACKAGE

On full success create one principal candidate ZIP:

```text
P21_LEAN_P5_PATH_EXCLUSION_CANDIDATE_20260918.zip
```

Include at least:

```text
complete Lean project
all new PATH modules

README_P5.md
SOURCE_OF_TRUTH_P5.md
P5_STATEMENT_MAP.md
P5_PROOF_ROUTE.md
P5_DEPENDENCY_DAG.md

NEXT_RESTART.md

verification/p5/
CI workflow
candidate SHA manifest
```

Compute and report SHA-256.

---

# 33. TRUE AUDIT ARTIFACT

Upload one artifact:

```text
P21_P5_TRUE_AUDIT_EVIDENCE
```

Include:

```text
RUN_CONTEXT
COMMIT_SHA
ENVIRONMENT

ROOT_BUILD_LOG
P5_MODULE_LIST
P5_BUILD_LOG
P5_VERIFICATION_LOG

M1_ORIGINAL_SUITE
M2A_ORIGINAL_SUITE
M2B_ORIGINAL_SUITE
M3A_ORIGINAL_SUITE
M3B1_ORIGINAL_SUITE
M3B2_ORIGINAL_SUITE

PROOF_DEBT_REPORT
AXIOM_REPORT
AXIOM_SUMMARY
STATEMENT_INSPECTION
DEPENDENCY_DAG_CHECK
CIRCULARITY_CHECK
FROZEN_SOURCE_INTEGRITY
VERIFIED_SOURCE_SHA256
candidate ZIP SHA
evidence SHA manifest
```

Report artifact ID and GitHub digest.

---

# 34. SUCCESS GATE

You may return:

```text
P5 PATH EXCLUSION CANDIDATE FOR TRUE AUDIT
```

only if all of the following are true:

```text
exact PathInput is unchanged
no new mathematical assumptions
PAIR/no-PAIR split complete
no-PAIR normalization proved
PFREE_i kernel proved
full left-right reversal proved
PAIR branch fully excluded
WEAK-ROOT walls proved
finite ROOT normalization proved
endpoint level≥2 proved
PAIR F-absorption proved
PFREE F0≥1 proved
PFREE direct absorption proved
FIX-J proved with repaired comparison
double-unit PIN proved
opposite-endpoint return endgame proved
dual PFREE excluded
P5.7 exhaustive PATH closure proved
post-PATH TYPE II∨CHAIN wrapper proved
project-specific axioms = 0
proof debt = 0
frozen mathematical sources unchanged
fresh root build PASS
all new P5 modules explicit build PASS
M1–M3B2 regression PASS
P5 verification PASS
GitHub clean CI PASS
candidate ZIP and artifact hashes recorded
```

---

# 35. PARTIAL / NO-GO POLICY

If full PATH does not close, do not fake completion.

Return one of:

```text
P5 PARTIAL — PATH OPEN
```

or:

```text
P5 NO-GO / INTERFACE OBSTRUCTION
```

Identify the **first exact unproved theorem**.

Give:

```text
its exact Lean statement
source anchor P5.x
proved dependencies
remaining mathematical gap
whether the issue is theorem difficulty or FROZEN API insufficiency
```

If a FROZEN mathematical file must change:

```text
SOURCE CHANGE REQUIRED
FROZEN RE-AUDIT REQUIRED
```

Do not silently patch it.

Package the strongest partial result and restart instructions.

---

# 36. STATUS LANGUAGE

Codex itself must never claim:

```text
TRUE AUDIT PASS
FROZEN
AUDITED
```

Even after all self-checks succeed.

The strongest permitted self-status is:

```text
P5 PATH EXCLUSION CANDIDATE FOR TRUE AUDIT
```

Independent Commander / TRUE AUDIT review decides FROZEN status.

---

# 37. FINAL REPORT

Report in Japanese.

Begin with exactly one of:

```text
P5 PATH EXCLUSION CANDIDATE FOR TRUE AUDIT
```

```text
P5 PARTIAL — PATH OPEN
```

```text
P5 NO-GO / INTERFACE OBSTRUCTION
```

Then report:

```text
Repository:
Branch:
Frozen base:
Candidate commit:

Primary theorem:
PathInput unchanged:

P5.0:
P5.1:
P5-dual:
P5.2:
P5.3:
P5.4:
P5.5:
P5.6:
P5.7:

Post-PATH selected-four wrapper:
Next frontier:

New Lean modules:
New audited declarations:

Proof debt:
Project-specific axioms:
FROZEN mathematical source integrity:

Root build:
Explicit P5 build:

M1:
M2A:
M2B:
M3A:
M3B1:
M3B2:
P5 verification:

GitHub workflow:
Run ID:
Attempt:
Conclusion:

Candidate ZIP:
Candidate SHA-256:

Artifact:
Artifact ID:
Artifact digest:

SOURCE_CHANGED:
```

On success:

```text
SOURCE_CHANGED: NO
```

must mean no pre-existing mathematical Lean source changed.

Do not begin Section 6.

Execute the P5 milestone completely now.
