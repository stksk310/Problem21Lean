# P21 LEAN — C7 / CHAIN CORE-ROOT

## SECTION 7 COMPLETE FORMALIZATION

## EXTREMAL SAME-ELEMENT FACTORIZATION / CORE-ROOT / RETURNS / SLOPES / INTRINSIC PACKET / SHIFT-NEW

This is the first formalization milestone for the final CHAIN branch of `Problem21Lean`.

The independently TRUE-AUDITED and FROZEN state is:

```text
M1    FOUNDATION + C2                  FROZEN
M2A   INTERNAL SYMMETRIC CLOSURE       FROZEN
M2B   STD_SYM_GLUE                     FROZEN
S3    SYMMETRIC TAIL                   FROZEN

M3A   NONSYMMETRIC LOCAL GEOMETRY      FROZEN
M3B1  MINBOX / WHITE                   FROZEN
M3B2  DPE                              FROZEN
       THREE-ARM                       FROZEN
       COLOR-CAP                       FROZEN
M3    FULL G4                          FROZEN

P5    PATH EXCLUSION                   FROZEN
T6    TYPE II EXCLUSION                FROZEN
```

The exact nonsymmetric terminal frontier is now:

```text
CHAIN ONLY
```

The final CHAIN program will be split into bounded milestones:

```text
C7  Section 7  — CORE-ROOT and complete late-stage input
C8  Section 8  — boundary elimination / packet window
C9  Section 9  — residual reduction / packet relations
C10 Section 10 — Euclidean descent / CHAIN closure
FINAL           — Section 11 main theorem assembly
```

This mission is **C7 only**.

Do not begin Section 8.

---

# 0. REPOSITORY / IMMUTABLE BASE

Repository:

```text
https://github.com/stksk310/Problem21Lean
```

The new immutable mathematical base is the independently audited T6 commit:

```text
6a1e395736e442bcda33c0da282220c98a444c76
```

Create a new branch from exactly this commit, preferably:

```text
c7-chain-core-root
```

Do not merge to `main`.

---

# 1. FROZEN ENTRYPOINT

The CHAIN-only post-T6 wrapper is already FROZEN:

```lean
P21.Nonsymmetric.SelectedTerminalAfterTypeII
P21.Nonsymmetric.TerminalInputAfterTypeII

nonsymmetric_selected_four_after_typeII
nonsymmetric_Q_ge_four_after_typeII
```

The local exact CHAIN input is:

```lean
P21.Nonsymmetric.ChainInput
```

Do not modify it.

The existing `ChainInput` already contains the same four actual rows:

```text
B_j(mu)
A_i(lambda)
B_i(lambda)
A_k(nu)
```

with actual Q-membership and distinctness, plus:

```text
Bj_missing
Ai_missing
Bi_missing
Ak_missing
```

and exact ranges:

```text
1 ≤ lambda < a_i
1 ≤ lambda < b_i

1 ≤ mu < b_j

1 ≤ nu < a_k
```

and exact complements:

```text
c_Bj = (a_i-lambda)n_i + (rho_k-nu)n_k
c_Ai = (b_j-mu)n_j     + (rho_k-nu)n_k

c_Bi = (rho_j-mu)n_j   + (a_k-nu)n_k
c_Ak = (b_i-lambda)n_i + (rho_j-mu)n_j
```

plus the common BOX-W:

```text
W =
  (rho_i-lambda-1)n_i
+ (rho_j-mu-1)n_j
+ (rho_k-nu-1)n_k
```

Existing helpers already define:

```lean
ChainInput.delta
ChainInput.beta
ChainInput.gapJ
ChainInput.alpha

ChainInput.all_slacks_positive
ChainInput.P_exact
```

Do not redo G4 extraction.

---

# 2. SOURCE OF TRUTH

Authority hierarchy:

```text
1. reference_inputs/
   P21_Journal_of_Algebra_Submission_Manuscript_FINAL_20260916.pdf

2. reference_inputs/
   P21_MANUSCRIPT_EN_FINAL_20260908_v1.zip
   Section 7

3. reference_inputs/
   P21_FINAL_FROZEN_VERIFICATION_EDITION_20260907.zip
   maintained CHAIN / CORE proof

4. existing FROZEN Lean source
```

The publication Section 7 controls the mathematical scope.

Formalize completely:

```text
§7.1  Existence of a unit root
§7.2  Exact hypotheses
§7.3  Extremal choice on same h_A
§7.4  Initial root and bounds
§7.5  Strictness
§7.6  Full color reversal
§7.7–7.8 CORE interface
§7.9  Actual returns and positive levels
§7.10 Additional caps and slopes
§7.11 Intrinsic candidates / orientation / COMPACT
§7.12 Return-level lower bounds
§7.13 SHIFT-NEW / packet cap
```

C7 succeeds only when the whole Section 7 package is complete.

---

# 3. ABSOLUTE FIREWALLS

Preserve all existing project firewalls.

## 3.1 Actual versus signed

Actual factorization coefficients are nonnegative.

ROOT/HCR/completed equations are signed equalities unless a separate actual witness exists.

Never obtain semigroup membership merely from a signed equality.

## 3.2 Same-element provenance

Any packet replacement must occur coefficientwise inside an explicitly named actual factorization of the same element.

Especially protect:

```text
h_A = q_A + m
EA
EB
Qj
Qk
Omega0
W
```

## 3.3 Criticality

Herzog criticality is permitted only after the m-coordinate has been completely eliminated.

Never call criticality on ROOT itself.

## 3.4 Extremal choices

Any maximal-factorization choice must come from an explicitly finite, nonempty set.

No informal “choose a maximal representation”.

## 3.5 No downstream imports

Do not use Section 8–10 results.

Do not use CHAIN impossibility or the final theorem.

---

# 4. C7.0 — CANONICAL CHAIN SCALARS

For

```lean
C : ChainInput s F D
```

use publication-local scalars conceptually:

```text
lambda := C.lambda
delta  := a_i - lambda
beta   := b_i - lambda

g      := b_j - mu
alpha  := a_k - nu

P := rho_i - lambda
R := rho_j - mu
T := rho_k - nu
```

Prove:

```text
delta,beta,g,alpha ≥ 1

a_i = lambda + delta
b_i = lambda + beta

P = lambda + delta + beta
P = a_i + beta
P = b_i + delta

R = a_j + g
T = b_k + alpha
```

Keep `C` for the Lean `ChainInput` object distinct from the later ROOT coefficient `Croot`.

Use an unambiguous Lean name for the root coefficient.

---

# 5. C7.1 — EXACT FOUR CHAIN ROWS

Expose the four actual rows in publication coordinates:

```text
qA := A_i(lambda)
qB := B_i(lambda)
qJ := B_j(mu)
qK := A_k(nu)
```

and prove their exact canonical value expressions from the FROZEN Herzog formulas and ChainInput data:

```text
qA =
  (P-1)n_i
+ (a_j-1)n_j
- n_k

qB =
  (P-1)n_i
- n_j
+ (b_k-1)n_k

qJ =
  (b_i-1)n_i
+ (R-1)n_j
- n_k

qK =
  (a_i-1)n_i
- n_j
+ (T-1)n_k
```

Retain actual pseudo-Frobenius membership of all four.

Also expose exactly:

```text
c_A = g*n_j + T*n_k
c_B = R*n_j + alpha*n_k
c_J = delta*n_i + T*n_k
c_K = beta*n_i + R*n_j
```

and:

```text
W = (P-1)n_i + (R-1)n_j + (T-1)n_k
```

All refer to the same actual Γ,F,m,W.

---

# 6. C7.2 — PFIBER

Recover the genuine FROZEN Section 4.6 factorization required by Section 7:

```text
PFIBER:

P*n_i =
  L*m
+ (t+1)*n_j
+ (u+1)*n_k

L ≥ 1
t,u ≥ 0
```

This must be a genuine actual Γ-factorization of the same named element `P*n_i`.

Locate and reuse the strongest existing FROZEN theorem if already available.

Do not reconstruct it from a signed relation.

If the existing FROZEN API truly does not expose the necessary theorem without modifying old mathematical source, STOP with:

```text
SOURCE CHANGE REQUIRED
FROZEN RE-AUDIT REQUIRED
```

Do not silently patch old files.

---

# 7. C7.3 — SAME-ELEMENT EXTREMAL FACTORIZATION OF hA

Define:

```text
hA := qA + m
```

Using the pseudo-Frobenius property:

```text
hA ∈ Γ
```

Prove that **every actual Γ-factorization of this same hA has m-coordinate zero**:

if its m-coordinate were positive, remove exactly one copy of m from that same actual factorization, obtaining:

```text
qA ∈ Γ
```

contradiction.

Hence:

```text
hA ∈ H
```

and the set of H-factorizations of hA is nonempty.

Prove this factorization set is finite.

Then choose one with maximal i-coordinate:

```text
MAX-I:

hA = X*n_i + Y*n_j + Z*n_k

X,Y,Z ≥ 0
```

with explicit extremality:

```text
∀ actual H-factorizations of hA,
  i-coordinate ≤ X
```

No uniqueness is assumed.

---

# 8. C7.3.1 — MAX-I BOX

Prove:

```text
X ≤ P-1
```

using PFIBER.

If `X ≥ P`, the **same named MAX-I factorization of hA** contains `P*n_i` coefficientwise.

Replace this contained block using:

```text
P*n_i - m =
  (L-1)m
  + (t+1)n_j
  + (u+1)n_k
```

and derive an actual factorization of:

```text
qA = hA-m
```

contradiction.

Then prove:

```text
Y ≤ rho_j-1
Z ≤ rho_k-1
```

using exact HCR replacements inside the same MAX-I factorization.

If:

```text
Y ≥ rho_j
```

replace the contained `rho_j*n_j` packet by:

```text
a_i*n_i + b_k*n_k
```

which strictly increases X.

Likewise, if:

```text
Z ≥ rho_k
```

replace with:

```text
b_i*n_i + a_j*n_j
```

which strictly increases X.

Conclude:

```text
0 ≤ X ≤ P-1
0 ≤ Y ≤ rho_j-1
0 ≤ Z ≤ rho_k-1
```

---

# 9. C7.4 — INITIAL ROOT

Define:

```text
d     := P-1-X
S     := Y-a_j+1
Croot := Z+1
```

and derive the exact signed identity:

```text
ROOT0:

m + d*n_i = S*n_j + Croot*n_k
```

equivalently:

```text
m = -d*n_i + S*n_j + Croot*n_k
```

Initial bounds:

```text
0 ≤ d ≤ P-1
1-a_j ≤ S ≤ b_j
1 ≤ Croot ≤ rho_k
```

Do not assume `S ≥ 0` at this stage.

---

# 10. C7.4.1 — FORCE S ≥ g

Using ROOT0 and the same W, perform the exact completed HCR rewrite from Section 7 and derive:

```text
F =
  (delta+d-1)n_i
+ (g-S-1)n_j
+ (rho_k+T-Croot-1)n_k
```

If:

```text
S ≤ g-1
```

prove every coefficient nonnegative:

```text
delta+d-1 ≥ 0
g-S-1 ≥ 0
rho_k+T-Croot-1 ≥ T-1 ≥ 0
```

and construct an actual factorization of F.

Contradiction.

Therefore:

```text
S ≥ g ≥ 1
```

---

# 11. C7.4.2 — FORCE Croot ≥ alpha

Similarly derive:

```text
F =
  (beta+d-1)n_i
+ (rho_j+R-S-1)n_j
+ (alpha-Croot-1)n_k
```

If:

```text
Croot ≤ alpha-1
```

prove:

```text
beta+d-1 ≥ 0
rho_j+R-S-1 ≥ a_j+R-1 ≥ 0
alpha-Croot-1 ≥ 0
```

and obtain `F ∈ Γ`.

Hence:

```text
Croot ≥ alpha ≥ 1
```

---

# 12. C7.4.3 — FORCE d ≥ 1

If:

```text
d = 0
```

ROOT0 becomes:

```text
m = S*n_j + Croot*n_k
```

with:

```text
S ≥ 1
Croot ≥ 1
```

contradicting multiplicity:

```text
m < n_j
m < n_k
```

Therefore:

```text
d ≥ 1
```

---

# 13. C7.4.4 — FORCE d ≤ lambda

From ROOT0 and W derive:

```text
F =
  (P+d-1)n_i
+ (R-S-1)n_j
+ (T-Croot-1)n_k
```

add exactly one completed `R_i` zero relation and obtain:

```text
F =
  (d-lambda-1)n_i
+ (R+b_j-S-1)n_j
+ (T+a_k-Croot-1)n_k
```

If:

```text
d ≥ lambda+1
```

show every coefficient nonnegative.

In particular use:

```text
S ≤ b_j
Croot ≤ rho_k
T = b_k+alpha
```

exactly as in the publication.

Conclude:

```text
1 ≤ d ≤ lambda
g ≤ S ≤ b_j
alpha ≤ Croot ≤ rho_k
```

Call this package conceptually:

```text
ROOT-BOX
```

---

# 14. C7.5 — STRICTNESS

If simultaneously:

```text
S = g
Croot = alpha
```

substitute ROOT0 into `F=W-m` and prove:

```text
F =
  (P+d-1)n_i
+ (a_j-1)n_j
+ (b_k-1)n_k
```

with all coefficients nonnegative.

Contradiction.

Therefore:

```text
S ≥ g+1
∨
Croot ≥ alpha+1
```

---

# 15. C7.6 — FULL CHAIN COLOR REVERSAL

Do not use informal symmetry.

Implement/prove the exact CHAIN color reversal from Section 7:

```text
i' = i
j' = k
k' = j
```

with Herzog data transformed by:

```text
(a_i,b_i) ↦ (b_i,a_i)

(a_j,b_j) ↦ (b_k,a_k)

(a_k,b_k) ↦ (b_j,a_j)
```

and parameters:

```text
lambda' = lambda

delta' = beta
beta'  = delta

g'     = alpha
alpha' = g

P' = P
R' = T
T' = R

d'     = d
S'     = Croot
Croot' = S
```

actual rows exchange exactly:

```text
qA ↔ qB
qJ ↔ qK
```

while preserving:

```text
Γ
F
m
W
actual Q-membership
distinctness
HCR
ChainInput validity
PFIBER actuality
```

PFIBER transforms only by exchanging its two positive tail coefficients:

```text
t ↔ u
```

Prefer using the existing `relabelSetting`, `reversePerm`, `reverseHerzog`, etc., if their exact semantics match.

Do not create a theorem that merely assumes a “dual copy”.

Prove reversal is strong enough to transport every hypothesis needed later.

---

# 16. C7.7 — ORIENT TO CORE-ROOT

Using STRICT:

```text
S ≥ g+1
∨
Croot ≥ alpha+1
```

orient the CHAIN configuration so that after zero or one formal color reversal:

```text
CORE-ROOT:

m + d*n_i = S*n_j + Croot*n_k

1 ≤ d ≤ lambda
S ≥ g+1
Croot ≥ alpha
```

with the same underlying:

```text
Γ,F,m,W
```

and four actual pseudo-Frobenius rows.

This is the canonical orientation passed downstream.

---

# 17. C7.8 — DEFINE THE MINIMAL CORE INTERFACE

Create a new Section-7-only structure/interface representing the exact minimal sufficient CORE input for Sections 8–10.

Conceptually:

```lean
structure ChainCore ... where
  chain : ChainInput ...
  d S Croot : ℤ
  root : g.m + d*g.n 0 = S*g.n 1 + Croot*g.n 2

  d_range : 1 ≤ d ∧ d ≤ chain.lambda
  S_strong : chain.gapJ + 1 ≤ S
  C_lower : chain.alpha ≤ Croot

  ...
```

Exact design may differ.

It must preserve/reference rather than duplicate:

```text
same Γ,F,m,W
same four actual rows
same ChainInput
same HCR data
same complements
```

Do not weaken actuality into bare integer equalities.

Provide a theorem conceptually like:

```lean
ChainInput.to_oriented_core
```

showing that every FROZEN actual CHAIN input produces an oriented `ChainCore` after at most the formally proved color reversal.

This is **not** yet CHAIN impossibility.

---

# 18. C7.9 — FOUR ACTUAL RETURNS

From the oriented CORE obtain genuine actual returns for the displayed missing directions.

Use the actual pseudo-Frobenius property and the same-factorization zero-coordinate rule.

Define/extract:

```text
EA = qA+n_i
   = Li*m + Uj*n_j + Uk*n_k

EB = qB+n_i
   = Lb*m + Vj*n_j + Vk*n_k

Qj = qJ+n_j
   = Lj*m + Aj*n_i + Cj*n_k

Qk = qK+n_k
   = Lk*m + Ak*n_i + Bk*n_j
```

with all tail coefficients nonnegative and:

```text
Li,Lb,Lj,Lk ≥ 1
```

Do not assume minimal return levels.

Do not assume uniqueness.

The missing coordinate must be exactly zero because removing one copy from that same actual factorization would give the original gap.

Positive m-level must follow from the missing-direction/H-support condition.

You may reuse the generic FROZEN actual-return helper if its scope is independent of PATH/TYPE II exclusion.

---

# 19. C7.9 — FI-CAPS

Using actual EA and its exact complement, construct:

```text
F+n_i =
  (Li-1)m
  + (Uj+g)n_j
  + (Uk+T)n_k
```

as an actual representation.

Similarly from EB:

```text
F+n_i =
  (Lb-1)m
  + (Vj+R)n_j
  + (Vk+alpha)n_k
```

Then prove:

```text
Uj+g < rho_j
Uk+T < rho_k

Vj+R < rho_j
Vk+alpha < rho_k
```

If a coefficient reaches the corresponding critical packet, replace it **inside this actual representation** using HCR to create a positive copy of `n_i`; remove that copy from `F+n_i` to obtain:

```text
F ∈ Γ
```

contradiction.

Conclude in particular:

```text
R < rho_j
T < rho_k

g < b_j
alpha < a_k
```

Do not use an abstract signed replacement.

---

# 20. C7.10 — FJ-KCAP

From actual Qj and its exact complement:

```text
F+n_j =
  (Lj-1)m
  + (Aj+delta)n_i
  + (Cj+T)n_k
```

If:

```text
Cj+T ≥ rho_k
```

replace one actual contained `rho_k*n_k` packet.

This creates at least one positive `n_j`.

Remove one copy and derive `F ∈ Γ`.

Conclude:

```text
Cj+T < rho_k
Cj < rho_k
```

This bound is later load-bearing in §7.12.2.

---

# 21. C7.10 — Aj / Ak CAPS

Make exactly one completed CORE-ROOT substitution into actual Qj.

Derive a representation of qJ whose potentially dangerous coefficient is:

```text
Aj-d
```

If:

```text
Aj ≥ d
```

all coefficients become nonnegative and the expression contains a positive j-coordinate.

Conclude:

```text
Aj ≤ d-1
```

Do the dual exact calculation for Qk:

```text
Ak ≤ d-1
```

No criticality is needed here unless the source explicitly requires it.

---

# 22. C7.10 — FOUR ROOT/PACKET CAPS

Using EA/EB and CORE-ROOT plus the appropriate single HCR packet, prove:

```text
Uj+S < rho_j
Uk+Croot < rho_k

Vj+S < rho_j
Vk+Croot < rho_k
```

The proof must identify the actual source representation used.

The final contradiction in each case must be an actual factorization of the original gap or F.

---

# 23. C7.10 — SLOPES

Compare CORE-ROOT with `R_j` and derive:

```text
rho_j*m =
  (S*a_i - d*rho_j)n_i
  + (S*b_k + Croot*rho_j)n_k
```

Prove:

```text
d*rho_j - S*a_i > 0
```

by contradiction using multiplicity.

Do not invoke criticality here.

Similarly derive:

```text
rho_k*m =
  (Croot*b_i - d*rho_k)n_i
  + (S*rho_k + Croot*a_j)n_j
```

and prove:

```text
d*rho_k - Croot*b_i > 0
```

Again use multiplicity, not criticality.

Conclude:

```text
S < rho_j
Croot < rho_k
```

These exact slope inequalities are part of the downstream C8/C9 input.

---

# 24. C7.11 — EUCLIDEAN PARAMETERS

Define the intrinsic integer-division data:

```text
h  := floor(lambda/d)
q0 := h+1

r  := lambda-h*d
e0 := q0*d-lambda
```

Formalize with a representation avoiding hidden Nat truncation.

Prove exact Euclidean facts:

```text
lambda = h*d+r
0 ≤ r < d

q0 ≥ 2
e0 = d-r
1 ≤ e0 ≤ d

h ≥ 1
```

as justified by:

```text
1 ≤ d ≤ lambda
```

---

# 25. C7.11 — COMPLETED F-ROW

Define for integers `x,y`:

```text
v(x,y) =
(
  x-1,
  P-1 + x*d - y*rho_i,
  R-1 - x*S + y*b_j,
  T-1 - x*Croot + y*a_k
)
```

representing the completed identity for F obtained from ROOT and `-R_i`.

Prove the exact algebraic equality for arbitrary integer `x,y`.

Do not call it actual unless all four coefficients have separately been shown nonnegative.

---

# 26. C7.11 — TWO-CANDIDATE INTEGER TEST

Prove:

1. Any successful nonnegative `v(x,y)` has:

```text
x ≥ 1
```

2. If `y ≤ 0` can succeed, then already:

```text
v(1,0)
```

is nonnegative and hence gives `F ∈ Γ`.

3. For `y ≥ 1`, prove the i-fit condition:

```text
x*d ≥ lambda+1+(y-1)rho_i
```

and the exact RHO-GAP identity:

```text
rho_i-q0*d-q0
 =
(q0-2)(d-1)
+2r
+delta
+beta
-2
```

with:

```text
rho_i-q0*d-q0 ≥ 0
```

Then derive:

```text
x ≥ y*q0
```

for all successful points with `y ≥ 1`.

---

# 27. C7.11 — SECOND CANDIDATE

Compute:

```text
v(q0,1) =
(
  q0-1,
  e0-1,
  J0,
  K0
)
```

where:

```text
J0 := rho_j+g-1-q0*S
K0 := rho_k+alpha-1-q0*Croot
```

Since `F` is a gap, the second candidate cannot be fully nonnegative.

Therefore:

```text
J0 < 0 ∨ K0 < 0
```

Prove they cannot both be deficient.

Derive exact QM:

```text
q0*m =
  (rho_i-q0*d)n_i
  + (q0*S-b_j)n_j
  + (q0*Croot-a_k)n_k
```

and use multiplicity, together with RHO-GAP, to prove the stronger implications:

```text
J0 < 0
→ q0*Croot ≤ a_k-1

K0 < 0
→ q0*S ≤ b_j-1
```

No criticality shortcut here unless the publication route explicitly reaches a pure-H relation.

---

# 28. C7.11 — SAFE CORE COLOR REVERSAL

If the only deficient coordinate is K0, apply the formal Section-7 color reversal.

Prove the entire CORE package survives:

```text
delta ↔ beta
g ↔ alpha
R ↔ T
S ↔ Croot

Γ,F,m,W unchanged
lambda,d unchanged

actual rows exchanged
actuality preserved
ROOT preserved
CORE inequalities preserved
```

Before reversal derive:

```text
1 ≤ -K0 ≤ Croot-alpha
```

so:

```text
Croot ≥ alpha+1
```

After reversal, the new strong coordinate satisfies the required CORE strong inequality.

Thus, without loss only via a proved transport theorem, orient to:

```text
J0 < 0
```

---

# 29. C7.11 — COMPACT PARAMETERS

In the oriented state define:

```text
Delta0 := q0*S-rho_j-g+1
A0     := e0-delta-1
C0     := a_k-q0*Croot-1

tau0   := rho_j-h*S
```

Prove:

```text
Delta0 ≥ 1
A0 ≥ 0
C0 ≥ 0

tau0 ≥ 1

Delta0+tau0 = S-g+1

1 ≤ Delta0 ≤ S-g
```

The proof of:

```text
A0 ≥ 0
```

must use the publication route:

```text
q0*S > rho_j
+
SLOPES
→ q0*d > a_i
```

Do not assume it.

---

# 30. C7.11 — COMPACT ACTUAL RELATION

Prove the actual relation:

```text
Omega0 := F + Delta0*n_j
```

has the genuine nonnegative factorization:

```text
Omega0 =
  (q0-1)m
  + (e0-1)n_i
  + (C0+T)n_k
```

Then prove the actual source:

```text
c_J = delta*n_i + T*n_k
```

is coefficientwise contained in this **same factorization**.

Remove that exact source and add one m.

Obtain the genuine actual relation:

```text
qJ + Delta0*n_j =
  q0*m
  + A0*n_i
  + C0*n_k
```

This provenance is load-bearing for Section 9.

---

# 31. C7.12.1 — I-LEVEL FOR qA/qB

For EA, compare its canonical and actual expressions and eliminate m completely.

Prove:

```text
Li*d ≥ lambda
```

using exact pure-H criticality arguments.

If:

```text
Li*d < lambda
```

split by sign of the j-coefficient exactly as in the publication:

* nonnegative → direct subcritical i-contradiction;
* negative → k-side becomes critical-large, subtract one R_k, then obtain another subcritical i-contradiction.

Repeat for EB:

```text
Lb*d ≥ lambda
```

Conclude:

```text
Li ≥ ceil(lambda/d)
Lb ≥ ceil(lambda/d)
```

and hence:

```text
Li ≥ h
Lb ≥ h
```

Use an exact integer ceil/floor bridge.

No floating arithmetic.

---

# 32. C7.12.2 — Bj LEVEL

Prove:

```text
Lj ≥ q0
```

by the exact source split under assumption `Lj ≤ h`.

All criticality calls must occur in pure-H relations.

Then prove the rigidity statement:

```text
Lj = q0
→
Delta0 = 1
∧ Aj = A0
∧ Cj = C0
```

by comparing the **same actual element**

```text
qJ + Delta0*n_j
```

in its two representations and eliminating m.

Use the already proved:

```text
Cj < rho_k
```

from FJ-KCAP.

Do not silently assume subcriticality of Cj.

---

# 33. C7.12.3 — Ak LEVEL IN STRICT REGION

This subsection applies only under:

```text
Croot > alpha
```

Do not use the conclusion on the boundary `Croot=alpha`.

Assuming:

```text
Lk ≤ h
```

eliminate m and follow the exact sign analysis.

After one j-criticality comparison derive the pure relation:

```text
(Lk*d-Ak-1)n_i
 =
(Bk+Lk*S+1-rho_j)n_j
+
(Lk*Croot-alpha)n_k
```

Use:

```text
Croot > alpha
```

to get positivity in the k-coordinate.

Conclude first:

```text
Lk ≥ q0
```

then strengthen to:

```text
Lk ≥ q0+1
```

using:

```text
q0*S > rho_j
```

and the i-critical threshold.

Then perform the completed F-row with `q0` ROOT copies and one `R_j` and prove:

```text
SUM-NOTCH:

Ak+beta+delta ≤ e0-1
e0 ≥ beta+delta+1
```

Again, this theorem must be scoped explicitly to `Croot>alpha`.

---

# 34. C7.13 — SHIFT-NEW

Compare `h` copies of CORE-ROOT with one `R_j` and prove the exact equality:

```text
SHIFT-NEW:

h*m + tau0*n_j
 =
(a_i-h*d)n_i
+
(b_k+h*Croot)n_k
```

Prove all coefficients nonnegative.

In particular:

```text
a_i-h*d = r+delta > 0
```

Thus SHIFT-NEW is a genuine replacement rule with nonnegative target.

---

# 35. C7.13 — APPLY SHIFT-NEW INSIDE EA / EB

From I-LEVEL:

```text
Li ≥ h
Lb ≥ h
```

the actual m-source of EA/EB contains the required `h` copies.

Apply SHIFT-NEW coefficientwise within those same named actual factorizations.

Derive:

```text
Uj ≤ tau0-1
Vj ≤ tau0-1
```

by contradiction: otherwise the replacement gives an actual representation of the corresponding gap/F forbidden by the publication argument.

Maintain same-element provenance explicitly.

---

# 36. C7.13 — FK-STRONG

Only in strict region:

```text
Croot > alpha
```

use:

```text
Lk ≥ q0+1 ≥ h+1
```

so the actual FK source has enough m copies for SHIFT-NEW.

If:

```text
Bk+R ≥ tau0
```

construct exactly:

```text
F =
  (Lk-h-1)m
  + (Ak+beta+a_i-h*d)n_i
  + (Bk+R-tau0)n_j
  + (b_k+h*Croot-1)n_k
```

and prove every coefficient nonnegative.

Conclude:

```text
0 ≤ Bk ≤ tau0-R-1
tau0 ≥ R+1
```

Call this:

```text
FK-STRONG
```

This is load-bearing for Section 9.6.

Do not assert it on `Croot=alpha`.

---

# 37. C7 FINAL INTERFACE

At successful completion, Section 7 must expose clean reusable declarations for C8/C9/C10.

At minimum the new API must make available:

```text
1. exact ChainInput coordinates

2. PFIBER

3. formal CHAIN color reversal

4. oriented CORE-ROOT existence

5. four actual positive-level returns

6. FI-CAPS

7. FJ-KCAP

8. Aj/Ak caps

9. four ROOT-return caps

10. SLOPES

11. Euclidean parameters
    h,q0,r,e0

12. RHO-GAP

13. second-candidate failure orientation

14. Delta0,A0,C0,tau0

15. COMPACT actual relation

16. I-LEVEL

17. Bj lower level + equality rigidity

18. Ak strict-region lower level

19. SUM-NOTCH in strict region

20. SHIFT-NEW

21. Uj/Vj tau0 caps

22. FK-STRONG in strict region
```

C7 must not prove `ChainInput.impossible`.

That remains downstream.

---

# 38. SUGGESTED MODULE LAYOUT

Use only NEW mathematical modules.

For example:

```text
P21/Nonsymmetric/Chain/
  Setup.lean
  PFiber.lean
  Extremal.lean
  Root.lean
  ColorReversal.lean
  Core.lean
  Returns.lean
  Caps.lean
  Slopes.lean
  Intrinsic.lean
  Compact.lean
  ReturnLevels.lean
  ShiftNew.lean
```

and optionally:

```text
P21/Nonsymmetric/Chain.lean
```

as a top-level import.

Exact split may differ.

Keep modules narrow enough for independent auditing.

---

# 39. FROZEN SOURCE POLICY

Every mathematical Lean file existing at base commit:

```text
6a1e395736e442bcda33c0da282220c98a444c76
```

is protected.

Expected mathematical source modifications:

```text
NEW Chain/C7 Lean modules only
```

Do not edit:

```text
ChainInput
Extraction.lean

TypeII source
Path source
ColorCap source
M3 source
C2 source
symmetric source
```

If an existing mathematical interface is insufficient and a protected source must change, STOP:

```text
SOURCE CHANGE REQUIRED
FROZEN RE-AUDIT REQUIRED
```

Do not silently repair FROZEN mathematics.

Documentation/new verification/new CI are allowed.

---

# 40. DANGEROUS REGRESSION GATES

Explicitly test at least:

```text
- ChainInput unchanged

- all four selected rows remain actual
- same Γ,F,m,W throughout

- PFIBER is actual, not signed

- MAX-I set is finite and nonempty

- X≤P-1 uses replacement inside same hA factorization

- Y/Z packet replacements preserve same hA

- ROOT is signed only

- S≥g and Croot≥alpha use actual F-factorizations

- d≥1 uses multiplicity

- d≤lambda uses completed R_i correctly

- STRICT is proved

- color reversal is formal and transports ChainInput

- color reversal preserves PFIBER and same W

- CORE-ROOT has no added minimality hypothesis

- returns EA/EB/Qj/Qk are actual

- all return m-levels are proved positive

- FI-CAPS use actual F+n_i representations

- FJ-KCAP source containment is explicit

- Aj/Ak caps use actual gap representations

- SLOPES use multiplicity, not criticality

- Euclidean division is exact integer arithmetic

- RHO-GAP is exact

- second candidate is not called actual unless coefficients are nonnegative

- J0/K0 deficiency cannot both occur

- safe reversal preserves CORE

- A0≥0 is proved from slope, not assumed

- COMPACT is an actual representation

- c_J source is coefficientwise contained in COMPACT

- I-LEVEL criticality is pure-H

- Bj equality rigidity uses FJ-KCAP

- Ak strict-region theorem is not exported to boundary

- SHIFT-NEW target coefficients are nonnegative

- SHIFT-NEW replacement is same-factorization

- FK-STRONG is strict-region only
```

---

# 41. DO NOT DO IN C7

Do not formalize:

```text
Section 8 boundary elimination
Section 8 packet window
U/D final split

Section 9 U elimination
Section 9 D reduction
715-term certificate

Section 10 Euclidean descent
3234-term certificate

ChainInput.impossible
main theorem
```

You may create future interface comments only.

---

# 42. PROOF-DEBT / AXIOM POLICY

Forbidden:

```text
sorry
admit
axiom
sorryAx
unsafe proof escape
opaque project theorem
native_decide theorem substitute
run_tac proof generation
external computation asserted as proof
```

Required:

```text
project-specific axioms = 0
proof debt = 0
```

Allowed foundations only as genuinely inherited:

```text
propext
Classical.choice
Quot.sound
```

---

# 43. DEPENDENCY FIREWALL

Required direction:

```text
FROZEN ChainInput / Herzog / C2
        ↓
C7 Setup / PFIBER
        ↓
Extremal same-hA
        ↓
ROOT / reversal / CORE
        ↓
returns
        ↓
caps + slopes
        ↓
intrinsic candidate
        ↓
COMPACT
        ↓
return-level bounds
        ↓
SHIFT-NEW / FK-STRONG
```

Forbidden transitive imports:

```text
Section 8+
CHAIN closure
final P21 theorem
```

---

# 44. VERIFICATION

Run a completely fresh build.

At minimum:

```bash
lake build
```

Explicitly build every new C7 module.

Rerun all FROZEN milestone suites:

```text
M1
M2A
M2B
M3A
M3B1
M3B2
P5
T6
```

Add:

```text
verification/c7/
```

including:

```text
declaration inventory
statement inspection
axiom inspection
proof-debt scan
dependency DAG
circularity check
frozen-source integrity
new-module list

fresh root build log
C7 build log
all old-suite regression logs
```

---

# 45. EVIDENCE MANIFEST

Retain the repaired T6 evidence convention.

Generate:

```text
EVIDENCE_SHA256.json
```

before artifact upload.

It must hash every evidence file except itself under a clearly documented non-self-referential convention.

Verify it in CI before upload.

---

# 46. GITHUB CI

Create:

```text
.github/workflows/c7-audit.yml
```

or equivalent.

CI must bind evidence to exact candidate HEAD and record:

```text
branch
exact commit
run ID
attempt

Lean
Lake
mathlib revision

candidate digest
frozen-source integrity

fresh root build
explicit C7 build

M1
M2A
M2B
M3A
M3B1
M3B2
P5
T6
C7 verification

proof debt
axioms
statement inspection
dependency/circularity
evidence manifest verification
```

No project-owned compiled artifacts may bypass source compilation.

---

# 47. CANDIDATE PACKAGE

On success create exactly one principal candidate:

```text
P21_LEAN_C7_CHAIN_CORE_ROOT_CANDIDATE_20260918.zip
```

Include:

```text
complete Lean project
all new C7 modules

README_C7.md
SOURCE_OF_TRUTH_C7.md
C7_STATEMENT_MAP.md
C7_PROOF_ROUTE.md
C7_DEPENDENCY_DAG.md

NEXT_RESTART.md

verification/c7/
CI workflow
candidate SHA manifest
```

Compute SHA-256.

---

# 48. TRUE AUDIT ARTIFACT

Upload:

```text
P21_C7_TRUE_AUDIT_EVIDENCE
```

containing at least:

```text
RUN_CONTEXT
COMMIT_SHA
ENVIRONMENT

ROOT_BUILD_LOG
C7_MODULE_LIST
C7_BUILD_LOG
C7_VERIFICATION_LOG

M1_ORIGINAL_SUITE
M2A_ORIGINAL_SUITE
M2B_ORIGINAL_SUITE
M3A_ORIGINAL_SUITE
M3B1_ORIGINAL_SUITE
M3B2_ORIGINAL_SUITE
P5_ORIGINAL_SUITE
T6_ORIGINAL_SUITE

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

Report artifact ID and GitHub artifact digest.

---

# 49. SUCCESS GATE

You may report only:

```text
C7 CHAIN CORE-ROOT CANDIDATE FOR TRUE AUDIT
```

if all of these are complete:

```text
[ ] exact ChainInput unchanged
[ ] no old mathematical source changed

[ ] exact CHAIN coordinates proved
[ ] PFIBER actual
[ ] hA actual H-factorization set proved nonempty/finite
[ ] MAX-I proved
[ ] X,Y,Z bounds proved

[ ] ROOT0 proved
[ ] S≥g
[ ] Croot≥alpha
[ ] d≥1
[ ] d≤lambda
[ ] STRICT proved

[ ] full color reversal proved
[ ] reversal preserves actual CHAIN data
[ ] oriented CORE-ROOT obtained

[ ] four actual positive-level returns
[ ] FI-CAPS
[ ] FJ-KCAP
[ ] Aj/Ak caps
[ ] four ROOT-return caps
[ ] SLOPES

[ ] h,q0,r,e0 exact
[ ] RHO-GAP
[ ] two-candidate reduction
[ ] J0/K0 deficiency control
[ ] safe orientation to J0<0

[ ] Delta0/A0/C0/tau0 bounds
[ ] COMPACT actual relation
[ ] source containment in COMPACT

[ ] I-LEVEL
[ ] Bj level bound
[ ] Bj equality rigidity

[ ] strict Ak level bound
[ ] SUM-NOTCH

[ ] SHIFT-NEW
[ ] Uj/Vj tau0 caps
[ ] FK-STRONG

[ ] proof debt = 0
[ ] project-specific axioms = 0
[ ] frozen source integrity PASS
[ ] forbidden reverse dependency = none

[ ] fresh root build PASS
[ ] C7 explicit build PASS
[ ] all M1–T6 regressions PASS
[ ] C7 verification PASS
[ ] clean GitHub CI PASS

[ ] candidate SHA recorded
[ ] artifact digest recorded
[ ] evidence manifest verified
```

---

# 50. PARTIAL / NO-GO

If Section 7 does not fully close, do not fake success.

Return:

```text
C7 PARTIAL — SECTION 7 OPEN
```

or:

```text
C7 NO-GO / INTERFACE OBSTRUCTION
```

Identify the **first exact missing theorem**:

```text
Lean statement
publication subsection
proved dependencies
remaining mathematical gap
whether mathematical or API/interface
```

If old mathematical source must change:

```text
SOURCE CHANGE REQUIRED
FROZEN RE-AUDIT REQUIRED
```

Still package the strongest valid checkpoint.

---

# 51. STATUS LANGUAGE

Codex must not self-award:

```text
TRUE AUDIT PASS
FROZEN
CHAIN CLOSED
```

The strongest success status is:

```text
C7 CHAIN CORE-ROOT CANDIDATE FOR TRUE AUDIT
```

CHAIN remains OPEN after C7.

The next frontier on successful audit will be:

```text
C8 — SECTION 8
BOUNDARY ELIMINATION / PACKET WINDOW
```

---

# 52. FINAL REPORT

Report in Japanese.

Begin with exactly one of:

```text
C7 CHAIN CORE-ROOT CANDIDATE FOR TRUE AUDIT
```

```text
C7 PARTIAL — SECTION 7 OPEN
```

```text
C7 NO-GO / INTERFACE OBSTRUCTION
```

Then report:

```text
Repository:
Branch:
Frozen base:
Candidate commit:

ChainInput unchanged:
Primary C7 interface:

§7.2 setup:
§7.3 MAX-I:
PFIBER:
ROOT0:
ROOT-BOX:
STRICT:
color reversal:
CORE-ROOT:

RET:
FI-CAPS:
FJ-KCAP:
Aj/Ak caps:
SLOPES:

h/q0/r/e0:
RHO-GAP:
J0/K0:
COMPACT:

I-LEVEL:
Bj level:
Bj rigidity:
Ak strict level:
SUM-NOTCH:

SHIFT-NEW:
EA/EB tau caps:
FK-STRONG:

Next frontier:
CHAIN overall status:

New Lean modules:
Audited declarations:

Proof debt:
Project-specific axioms:
FROZEN mathematical source integrity:
Forbidden reverse dependencies:

Root build:
Explicit C7 build:

M1:
M2A:
M2B:
M3A:
M3B1:
M3B2:
P5:
T6:
C7 verification:

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
EVIDENCE verification:

SOURCE_CHANGED:
```

On success:

```text
SOURCE_CHANGED: NO
CHAIN overall status: OPEN — C7 complete, C8 next
```

Execute C7 completely now.
