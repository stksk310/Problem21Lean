# P21 LEAN — C10 / EUCLIDEAN DESCENT / CHAIN FULL CLOSURE

## SECTION 10 COMPLETE FORMALIZATION

## ABSTRACT TWO-PACKET STATE / TERMINAL SOURCE CONTAINMENT / COLOR-EXCHANGE STEP / STRICT DESCENT / CHAIN IMPOSSIBILITY

This is the final mathematical milestone for the CHAIN branch of `Problem21Lean`.

The independently TRUE-AUDITED / FROZEN state is:

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

C7    CHAIN CORE / SECTION 7           FROZEN
C8    BOUNDARY / WINDOW / SECTION 8    FROZEN
C9    TWO PACKETS / SECTION 9          FROZEN
```

The exact current frontier is:

```text
EuclideanSeed only
```

This mission is:

```text
C10 — SECTION 10
EUCLIDEAN DESCENT
+
SAME-W TERMINAL SOURCE FIT
+
CHAIN FULL CLOSURE
```

On success, CHAIN itself is mathematically closed.

Do **not** begin Section 11 main-theorem assembly.

---

# 0. REPOSITORY / IMMUTABLE BASE

Repository:

```text
https://github.com/stksk310/Problem21Lean
```

Immutable independently audited C9 base:

```text
50d65c7982aebe67856cb85e81771d0452d62fec
```

Create a new branch from exactly this commit, preferably:

```text
c10-chain-euclidean-closure
```

Do not merge to `main`.

---

# 1. C9 AUDIT MINOR — FIX BY PROJECTION, NOT BY EDITING C9

The frozen `EuclideanSeed` contains:

```lean
canonical : s.semigroup.Canonical F g.m
```

Independent C9 audit classified this as API-scope baggage only.

Publication §10.1–§10.2 does **not** require canonicality as part of the abstract Euclidean descent state.

Therefore:

```text
DO NOT MODIFY EuclideanSeed.
DO NOT USE seed.canonical IN THE DESCENT.
```

Instead define a new C10-only abstract state:

```lean
EuclideanState
```

obtained by projection from `EuclideanSeed`.

It must omit:

```text
canonical
FirstFit
RegionD
q0
ROOT
PF rows
return levels
first-point minimality
```

The only use of `seed.frobenius` should be to obtain the original gap statement:

```text
F ∉ Γ
```

when converting the final `F ∈ Γ` into `False`.

The descent theorem itself should preferably prove:

```lean
F ∈ Γ
```

from the abstract state.

---

# 2. SOURCE OF TRUTH

Authority order:

```text
1. reference_inputs/
   P21_Journal_of_Algebra_Submission_Manuscript_FINAL_20260916.pdf
   Section 10

2. reference_inputs/
   P21_MANUSCRIPT_EN_FINAL_20260908_v1.zip
   Section 10

3. reference_inputs/
   P21_FINAL_FROZEN_VERIFICATION_EDITION_20260907.zip

4. reference_inputs/
   P21_supplement_v1.zip
   EUCLIDEAN static certificate

5. FROZEN C9 EuclideanSeed API
```

Formalize completely:

```text
§10.1–10.3  abstract theorem/state
§10.4       terminal packet
§10.4.1     SAME-W actual replacement
§10.5–10.9  terminal i-source fit / 3234-term certificate
§10.10      exact nonterminal Euclidean transformation
§10.11–14   preservation
§10.15      strict descent / strong induction
§10.16      preservation ledger

then:

EuclideanSeed impossible
→ ChainInput impossible
→ post-Type-II terminal CHAIN impossible
→ nonsymmetric |Q|≥4 impossible
```

Do not prove the final symmetric/nonsymmetric global theorem of §11.

---

# 3. ABSTRACT EUCLIDEAN STATE

Create a new structure, conceptually:

```lean
structure EuclideanState {g : Generators}
    (s : g.Setting) (F : ℤ) (D : HerzogCriticalData g) where
```

It must carry exactly the §10.2 data.

At minimum:

```text
F_gap:
  F ∉ g.Gamma

delta,beta,gap,alpha,P,R,T

delta,beta,gap,alpha > 0
P,R,T > 0

a_i = P-beta
b_i = P-delta

R = a_j+gap
T = b_k+alpha

W =
(P-1)n_i
+(R-1)n_j
+(T-1)n_k
=
F+m
```

Matrix:

```text
p,q,s,t ≥ 1

p*t-q*s = 1

L=p+q
M=s+t

L>M
```

Use a field name other than `s` for the matrix lower-left entry if necessary because `s` already denotes the Setting; e.g.

```text
v
```

as C9 currently does.

Source data:

```text
r ≥0

A =
p(r+delta)+q(r+beta)

B =
v(r+delta)+t(r+beta)
```

Packet parameters:

```text
u ≥1
E=R+u

w≥0
Hp=T+w

1≤theta≤u
chi≥1

Dp :=
theta*chi-E*Hp
>0
```

Genuine packet equalities:

```text
DP:
B*n_i+E*n_j
=
M*m+chi*n_k

PP:
A*n_i+Hp*n_k
=
L*m+theta*n_j
```

RHO:

```text
rho_j =
L*E+M*theta-a_j

rho_k =
L*chi+M*Hp-b_k
```

The type parameter:

```text
D : HerzogCriticalData g
```

supplies the genuine HCR.

Do not add ROOT.

Do not add first-point information.

---

# 4. EuclideanSeed → EuclideanState

Define:

```lean
EuclideanSeed.toState
```

or equivalent.

Use all exact C9 fields except:

```text
seed.canonical
```

The C10 mathematical proof must not inspect `seed.canonical`.

Add a regression that verifies the C10 abstract descent remains provable if that field is erased from the state.

---

# 5. ABSTRACT CROSS-PRODUCT SCALE — NO CANONICALITY

Publication §10.7 derives the common positive scale from HCR itself.

Do not reuse the C8 theorem whose proof went through canonical tail-cofiniteness.

Instead prove a new generic C10 lemma from:

```text
HCR
positive generators
```

only.

Define:

```text
Ical :=
rho_j*rho_k-a_j*b_k

Jcal :=
a_i*rho_k+b_i*b_k

Kcal :=
b_i*rho_j+a_i*a_j
```

Prove:

```text
Ical>0
Jcal>0
Kcal>0
```

directly from positivity and:

```text
rho_r=a_r+b_r
```

For example:

```text
Ical =
a_j*a_k+b_j*a_k+b_j*b_k
>0
```

and similarly for Jcal/Kcal.

From the pure-H relations prove:

```text
Jcal*n_i = Ical*n_j
Kcal*n_i = Ical*n_k
```

exactly.

A clean formal route is to define a positive rational scale:

```text
sigma : ℚ :=
(n_i : ℚ)/(Ical : ℚ)
```

and prove:

```text
sigma>0

(n_i:ℚ)=sigma*Ical
(n_j:ℚ)=sigma*Jcal
(n_k:ℚ)=sigma*Kcal
```

No gcd assumption.

No canonicality.

An equivalent positive cross-multiplication proof is acceptable.

---

# 6. MATRIX ORDER

From:

```text
p,q,v,t ≥1
p*t-q*v=1
L=p+q
M=v+t
L>M
```

prove exactly:

```text
p ≥ v+1
q ≥ t
```

Publication ORDER.

Do not assume these.

Proof route:

* if `p≤v`, determinant positivity forces `q<t`, contradicting `L>M`;
* once `p>v`, if `q<t`, write

```text
p=v+a
t=q+b
a,b≥1
```

and obtain:

```text
p*t-q*v
=
v*b+a*q+a*b
>1
```

contradiction.

---

# 7. PACKET ELIMINATION DATA

Define:

```text
I0 :=
E*A+theta*B

J0 :=
chi*A+Hp*B

M0 :=
L*E+M*theta

K0 :=
L*chi+M*Hp
```

Prove:

```text
M0 = rho_j+a_j

K0 = rho_k+b_k
```

from RHO.

Combine DP and PP to prove:

```text
I0*n_i =
M0*m
+
Dp*n_k
```

exactly.

Also prove:

```text
A*M-B*L = delta-beta
```

from the source formulas and determinant-one.

Then derive:

```text
I0*K0-M0*J0
=
-Dp*(delta-beta)
```

exactly.

---

# 8. ABSTRACT mhat FORMULA

Define:

```text
mhat :=
I0*rho_k
-
a_j*J0
-
Dp*(P-delta)
```

where:

```text
b_i=P-delta.
```

Prove from the previous algebra that the positive cross-product scale satisfies:

```text
(m:ℚ)=sigma*mhat
```

with the same `sigma>0` as for the three tail generators.

This theorem must use only:

```text
EuclideanState
HCR
matrix determinant
DP
PP
RHO
```

not canonicality.

This is the abstract §10.7 scale theorem.

---

# 9. Phi(P) AND MONOTONICITY

Define:

```text
Phi(Px) :=
mhat evaluated with P=Px
-
Kcal evaluated with P=Px
```

with:

```text
a_i = Px-beta
b_i = Px-delta.
```

Treat all remaining state variables as fixed.

Do not formalize calculus.

Prove exact finite difference:

```text
Phi(Px+1)-Phi(Px)
=
-(Dp+M0)
```

and therefore:

```text
Phi(Px+1)<Phi(Px)
```

because:

```text
Dp>0
M0>0.
```

Provide the monotonic consequence:

```text
P≤Pstar
→
Phi(P)≥Phi(Pstar)
```

for the terminal threshold used later.

---

# 10. DESCENT MEASURE

Define:

```text
measureZ :=
E+chi
```

and prove:

```text
measureZ ≥2
```

or at least:

```text
measureZ>0.
```

Define a natural-number recursion measure:

```lean
measureNat : ℕ := measureZ.toNat
```

with exact cast lemmas.

This is the **only** descent measure.

Do not carry any C7/C8/C9 depth into Section 10.

---

# 11. TERMINAL CANDIDATE

Define:

```text
nu :=
floor(u/theta)+1
```

using exact integer division.

Since:

```text
1≤theta≤u
```

prove:

```text
nu≥2.
```

Define:

```text
Z :=
B+nu*A

N :=
M+nu*L

jstar :=
E-nu*theta

kstar :=
nu*Hp-chi
```

From Euclidean division of u by theta prove:

```text
jstar≤R-1.
```

The terminal condition is exactly:

```text
kstar≤T-1.
```

Define:

```text
Terminal := kstar≤T-1
```

or equivalent.

---

# 12. TERMINAL PACKET IDENTITY

Combine:

```text
DP + nu * PP
```

to prove exactly:

```text
Z*n_i
+
jstar*n_j
+
kstar*n_k
=
N*m
```

as a signed identity.

Do not call it an actual packet when jstar/kstar may be negative.

---

# 13. POSITIVE-PART TERMINAL PACKET

Define exact integer positive/negative parts, for example:

```text
zplus  := max z 0
zminus := max (-z) 0
```

or Nat-valued equivalents.

Prove generic decomposition:

```text
z = zplus-zminus
```

and nonnegativity.

Rewrite TERMINAL-PACKET into a genuine nonnegative equality:

```text
Z*n_i
+
(jstar)+ * n_j
+
(kstar)+ * n_k

=

N*m
+
(-jstar)+ * n_j
+
(-kstar)+ * n_k.
```

This is the actual packet used inside W.

---

# 14. TERMINAL i-SOURCE THRESHOLD

The target theorem is:

```text
P ≥ Z+1
```

equivalently:

```text
P ≥ B+nu*A+1.
```

Do not assume it.

This is the load-bearing §10.5–10.9 certificate theorem.

---

# 15. TERMINAL SUBSTITUTION

At a terminal state define the Euclidean remainder:

```text
u =
(nu-1)*theta + z
```

with:

```text
0≤z<theta.
```

Define:

```text
hterm :=
theta-z
```

and prove:

```text
hterm≥1.
```

Terminal condition gives:

```text
x :=
chi-nu*Hp+T-1
≥0.
```

Derive exactly:

```text
theta =
hterm+z
```

```text
E =
nu*(hterm+z)
+
R
-
hterm
```

```text
Hp =
T+w
```

```text
chi =
nu*(T+w)
-
T
+
1
+
x
```

These are TERMINAL-SUB.

---

# 16. STATIC TERMINAL CERTIFICATE — FROZEN INPUT

Frozen supplement ZIP:

```text
reference_inputs/P21_supplement_v1.zip
```

Exact SHA-256:

```text
24a02d34651c35aa3d07f707fd38b7ca29d0f8bbfa86190d956657308b498c5e
```

Two byte-identical coefficient tables:

```text
supplement/verification_scripts/EUCLIDEAN/
  TERMINAL_POSITIVITY_COEFFICIENTS.json

supplement/coefficient_tables/
  TERMINAL_POSITIVITY_COEFFICIENTS.json
```

Exact table SHA-256:

```text
495504b4bcb8427db04b242cf09b83fbe7bde1188f9324b7e977036a5a4db9b3
```

Exact frozen verifier:

```text
supplement/verification_scripts/EUCLIDEAN/
  verify_euclidean_closure.py
```

SHA-256:

```text
23fcf03275bbe36ef7b9ca78a6cddb6b75dd1f04216d3675fbe0da759b9d048e
```

Expected result SHA:

```text
12a22a7ed7899ccb10cb8ff608ca4fc738da76ec0ed761c5fd72a4ab87967087
```

Expected stdout SHA:

```text
a298d66b61ca2b82ce9a429cbb795b7bd56c83f85795da7781e5c043ae12425f
```

Frozen verifier expected summary:

```text
status: PASS
identities: 35
positive_monomials: 3234
constant: 63
```

Table facts:

```text
3234 monomials including constant
total degree 7
constant term 63
```

Variable order:

```text
p0
q0
s0
t0
r0
delta0
beta0
aj0
g0
alpha0
bk0
nu0
h0
z0
x0
w0
```

---

# 17. TERMINAL CERTIFICATE SHIFT VARIABLES

Following ORDER define nonnegative variables exactly:

```text
s0 :=
v-1

t0 :=
t-1

p0 :=
p-v-1

q0 :=
q-t

r0 :=
r

delta0 :=
delta-1

beta0 :=
beta-1

aj0 :=
a_j-1

g0 :=
gap-1

alpha0 :=
alpha-1

bk0 :=
b_k-1

nu0 :=
nu-2

h0 :=
hterm-1

z0 :=
z

x0 :=
x

w0 :=
w
```

Prove all 16 are nonnegative.

Use only:

```text
ORDER
positivity
terminal remainder bounds
terminal condition
```

The determinant-one identity is **not** an extra domain constraint for the polynomial positivity.

---

# 18. TERMINAL CERTIFICATE GENERATION

Create:

```text
verification/c10/generate_euclidean_certificate.py
```

that deterministically:

1. reads the exact frozen supplement ZIP;
2. checks supplement ZIP SHA;
3. checks both EUCLIDEAN table SHA values;
4. checks both tables are byte-identical;
5. checks:

   * 3234 terms,
   * variable order,
   * degree 7 if encoded/derivable,
   * constant 63;
6. checks frozen verifier SHA;
7. emits committed transparent Lean proof data.

Because the table is large, split generated source into deterministic chunks, e.g.

```text
GeneratedTerminalCertificateTypes.lean
GeneratedTerminalCertificateData00.lean
...
GeneratedTerminalCertificateDataNN.lean
GeneratedTerminalCertificate.lean
```

The exact chunk count is implementation-dependent but must be deterministic.

CI must regenerate and byte-compare the output.

---

# 19. LEAN-KERNEL CERTIFICATE

As in C9, Python PASS is supporting evidence only.

The formal proof must be Lean-kernel checked.

Define a transparent term structure with:

```text
coefficient : ℕ
exponents : Fin 16 → ℕ
```

or equivalent.

Prove generic monomial nonnegativity for the shifted domain.

The generated polynomial must satisfy:

```text
certificatePolynomial ≥ 63 > 0.
```

Then prove the exact symbolic identity:

```text
TERMINAL-POS:

Phi(B+nu*A)
=
certificatePolynomial
```

using Lean.

Preferred:

```text
ring
```

on deterministically chunked generated expressions.

If one giant `ring` is too expensive, establish chunk identities and combine them.

Forbidden:

```text
native_decide
run_tac
Python PASS ⇒ theorem
axiom certificate identity
opaque imported certificate theorem
```

---

# 20. TERMINAL i-FIT

Let:

```text
Pstar :=
B+nu*A.
```

The certificate proves:

```text
Phi(Pstar)>0.
```

If:

```text
P≤Pstar
```

monotonicity gives:

```text
Phi(P)≥Phi(Pstar)>0.
```

Therefore:

```text
mhat>Kcal.
```

Use the positive cross-product scale to derive:

```text
m>n_k,
```

contradicting:

```text
m<n_k.
```

Hence by integrality:

```text
I-FIT:
P ≥ B+nu*A+1
```

or:

```text
P≥Z+1.
```

---

# 21. TERMINAL SOURCE CONTAINMENT IN SAME W

Construct the canonical actual W-factorization from:

```text
W_face:
W =
(P-1)n_i
+(R-1)n_j
+(T-1)n_k
```

with m-coordinate zero.

All source coefficients are nonnegative.

Using:

```text
P≥Z+1
jstar≤R-1
kstar≤T-1
```

prove coefficientwise containment of:

```text
source :=
0*m
+
Z*n_i
+
(jstar)+ n_j
+
(kstar)+ n_k
```

inside this **same W factorization**.

Do not use an external/shifted W.

---

# 22. TERMINAL SAME-W REPLACEMENT

Use the FROZEN helper:

```lean
P21.replaceWithinActualFactorization
```

with:

```text
source
target :=
N*m
+
0*n_i
+
(-jstar)+ n_j
+
(-kstar)+ n_k
```

and the genuine positive-part terminal packet equality.

Obtain a new actual factorization of the same W.

Prove its m-coordinate is exactly:

```text
N
```

and:

```text
N≥1.
```

Then use:

```lean
P21.removeOne
```

to remove one actually present copy of m.

Since:

```text
W-m=F
```

obtain:

```text
F ∈ g.Gamma.
```

This is the preferred formalization of publication §10.4.1.

No signed→membership shortcut.

---

# 23. FINAL-EXACT REGRESSION

Additionally prove the explicit terminal equality:

```text
F =
(M+nu*L-1)m
+
(P-1-B-nu*A)n_i
+
(hterm-1)n_j
+
x*n_k.
```

Prove all four coefficients nonnegative.

This is a regression theorem verifying the actual replacement result matches publication FINAL-EXACT.

---

# 24. NONTERMINAL FAILURE

Assume the terminal condition fails.

Since all quantities are integral:

```text
nu*Hp-chi ≥ T.
```

Call this:

```text
FAIL.
```

---

# 25. EUCLIDEAN QUOTIENTS

Define:

```text
e :=
floor(E/theta)

rhoRem :=
E-e*theta

kappa :=
chi-e*Hp
```

Use a name like `rhoRem` to avoid collision with Herzog `rho`.

Prove:

```text
e≥1
```

and:

```text
0≤rhoRem<theta.
```

Substitute into packet determinant:

```text
Dp
=
theta*kappa
-
rhoRem*Hp
>0.
```

Hence:

```text
kappa≥1.
```

---

# 26. PROVE nu=e+1

First prove:

```text
nu≤e+1.
```

If:

```text
nu≤e
```

then from:

```text
chi=e*Hp+kappa
```

derive:

```text
nu*Hp-chi≤-kappa<0,
```

contradicting FAIL.

Therefore:

```text
nu=e+1.
```

Since:

```text
nu=floor(u/theta)+1
```

obtain:

```text
floor(u/theta)=e.
```

Using:

```text
u=E-R
```

derive:

```text
rhoRem≥R.
```

Thus:

```text
R≤rhoRem<theta.
```

---

# 27. kappa≤w

From FAIL:

```text
nu*Hp-chi ≥ T
```

and:

```text
nu=e+1
chi=e*Hp+kappa
```

derive:

```text
Hp-kappa≥T.
```

Since:

```text
Hp=T+w
```

obtain:

```text
kappa≤w.
```

Thus:

```text
1≤kappa≤w.
```

In particular:

```text
w≥1.
```

This also proves:

```text
w=0 → terminal.
```

as a regression.

---

# 28. NEW GENUINE PACKET

Combine:

```text
DP + e*PP
```

to derive:

```text
(B+e*A)n_i
+
rhoRem*n_j

=

(M+e*L)m
+
kappa*n_k.
```

Call this:

```text
NEW-PACKET.
```

Explicitly prove every coefficient nonnegative:

```text
B+eA ≥0
rhoRem≥R≥1
M+eL≥1
kappa≥1.
```

This is a genuine packet.

---

# 29. ABSTRACT COLOR EXCHANGE

Do not refer back to `ChainInput.reverseChain`.

Section 10 is now abstract.

Define a C10-only transformation based on:

```text
relabelSetting s reversePerm
reverseHerzog D
```

with:

```text
n_i' = n_i
n_j' = n_k
n_k' = n_j

m'=m
F'=F
W'=W
```

Canonical scalar data transform:

```text
delta' = beta
beta'  = delta

gap'   = alpha
alpha' = gap

P'=P
R'=T
T'=R

r'=r
```

Herzog data are transported by:

```lean
reverseHerzog D
```

No pseudo-Frobenius rows are involved.

---

# 30. PACKET PARAMETER TRANSFORMATION

Define:

```text
E'     := Hp
theta' := kappa

chi'   := theta
Hp'    := rhoRem

u' := w

w' :=
rhoRem-R
```

Prove:

```text
u'≥1
```

from failure.

Prove:

```text
E'=R'+u'.
```

Because:

```text
R'=T
Hp=T+w.
```

Prove:

```text
Hp'=T'+w'
```

because:

```text
T'=R
rhoRem=R+(rhoRem-R).
```

Also prove:

```text
1≤theta'≤u'
w'≥0
chi'≥1.
```

---

# 31. MATRIX UPDATE

Original matrix:

```text
[p q]
[v t]
```

Define transformed matrix:

```text
p' := t+e*q
q' := v+e*p

v' := q
t' := p
```

This is publication:

```text
M' =
(t+e q    v+e p
 q        p)
```

Prove all entries positive.

Prove exact determinant:

```text
p'*t'-q'*v'
=
p*t-q*v
=
1.
```

---

# 32. NEW L / M

Define:

```text
L' := p'+q'
M' := v'+t'.
```

Prove:

```text
L' = M+e*L
```

and:

```text
M' = L.
```

Therefore:

```text
L'>M'
```

because:

```text
e≥1
M<L.
```

---

# 33. SOURCE TRANSFORMATION

Because color exchange swaps:

```text
r+delta
↔
r+beta
```

prove exact transformed source identities:

```text
A' = B+e*A
B' = A.
```

Also prove they equal the formulas generated by the new matrix:

```text
A' =
p'(r'+delta')
+
q'(r'+beta')
```

```text
B' =
v'(r'+delta')
+
t'(r'+beta').
```

---

# 34. TWO NEW GENUINE PACKETS

## New DP

After color exchange, the new DP is exactly old PP:

```text
B'*n_i'
+
E'*n_j'

=

M'*m'
+
chi'*n_k'.
```

Prove it by rewriting old PP.

## New PP

After color exchange, NEW-PACKET becomes:

```text
A'*n_i'
+
Hp'*n_k'

=

L'*m'
+
theta'*n_j'.
```

Both must be genuine nonnegative equalities.

No signed intermediate relation may be promoted to actuality.

---

# 35. PACKET DETERMINANT PRESERVED

Prove:

```text
Dp'
:=
theta'*chi'
-
E'*Hp'

=
kappa*theta
-
Hp*rhoRem
=
Dp
>0.
```

Exact invariant.

---

# 36. RHO IDENTITIES PRESERVED

Using the old RHO identities and the color exchange:

```text
rho_j' = old rho_k
rho_k' = old rho_j
```

prove:

```text
rho_j'
=
L'*E'
+
M'*theta'
-
a_j'
```

and:

```text
rho_k'
=
L'*chi'
+
M'*Hp'
-
b_k'.
```

Do not assume these.

---

# 37. ai / bi SOURCES PRESERVED

Under the full color reversal prove:

```text
a_i' = P'-beta'
b_i' = P'-delta'.
```

This should reduce to swapping the old:

```text
a_i=P-beta
b_i=P-delta.
```

---

# 38. SAME W FACE PRESERVED

Prove:

```text
W =
(P-1)n_i
+
(R-1)n_j
+
(T-1)n_k
```

becomes exactly:

```text
W =
(P'-1)n_i'
+
(R'-1)n_j'
+
(T'-1)n_k'.
```

Use actual relabel identities.

No new semigroup or new F.

---

# 39. F-GAP PRESERVED

The transformed state lives over:

```text
relabelSetting s reversePerm
```

and:

```text
relabel g reversePerm.
```

Use the FROZEN theorem:

```lean
relabel_Gamma
```

to prove:

```text
F ∉ (relabel g reversePerm).Gamma
```

from the old F-gap.

This is purely renaming.

---

# 40. DEFINE THE STEP

Construct:

```lean
EuclideanState.step
```

under:

```text
¬ Terminal
```

returning:

```text
EuclideanState
  (relabelSetting s reversePerm)
  F
  (reverseHerzog D)
```

with every field independently proved.

This must not carry:

```text
canonical
first-point
ROOT
PF rows
```

---

# 41. STRICT DESCENT

New measure:

```text
measureZ' =
E'+chi'
=
Hp+theta.
```

Using:

```text
E=e*theta+rhoRem

chi=e*Hp+kappa
```

prove exactly:

```text
measureZ-measureZ'
=
(e-1)(Hp+theta)
+
rhoRem
+
kappa.
```

Every term on the right is nonnegative and:

```text
kappa≥1.
```

Therefore:

```text
measureZ' < measureZ.
```

Prove the corresponding Nat result:

```text
step.measureNat < state.measureNat.
```

This is the sole well-foundedness argument.

---

# 42. STRONG INDUCTION ACROSS TYPE-CHANGING STATES

The transformation changes:

```text
g
s
D
```

through relabeling.

Therefore do not write an induction theorem with these parameters fixed outside the induction hypothesis.

Use a universally quantified strong-induction statement, conceptually:

```lean
theorem euclidean_closure_by_measure (n : ℕ) :
  ∀ {g : Generators}
    (s : g.Setting)
    (F : ℤ)
    (D : HerzogCriticalData g)
    (X : EuclideanState s F D),
      X.measureNat = n →
      F ∈ g.Gamma
```

and prove it by:

```text
Nat.strong_induction_on n.
```

At each state:

```text
if Terminal:
  use terminal SAME-W proof

else:
  construct X.step
  prove smaller measure
  apply induction hypothesis to transformed state
  transport membership back with relabel_Gamma
```

The recursion must be accepted by Lean without unsafe tricks.

---

# 43. ABSTRACT EUCLIDEAN CLOSURE THEOREM

Expose a theorem conceptually:

```lean
theorem EuclideanState.f_mem
    (X : EuclideanState s F D) :
    F ∈ g.Gamma
```

with no additional hypotheses.

This is formal Section 10.3.

Its assumptions are entirely structure fields.

---

# 44. EuclideanSeed IMPOSSIBLE

Project:

```text
seed : EuclideanSeed s F D
```

to:

```text
seed.toState.
```

Use:

```text
seed.toState.f_mem
```

to obtain:

```text
F ∈ g.Gamma.
```

Contradict:

```text
seed.frobenius.1.
```

Prove:

```lean
theorem EuclideanSeed.impossible
    (seed : EuclideanSeed s F D) :
    False
```

Crucial regression:

```text
seed.canonical IS NOT USED.
```

---

# 45. CORE → C9 SEED → CONTRADICTION HELPER

Create a helper for an already oriented CORE:

```lean
ChainCore.impossible
```

or equivalent.

Input:

```text
K : ChainCore s F D
hF : s.semigroup.IsFrobenius F
hc : s.semigroup.Canonical F g.m
```

The canonicality is allowed here only because C8/C9 upstream construction requires it.

It must not pass canonicality into the Euclidean descent itself.

Steps:

```text
A := K.firstFit
E := K.returns
```

Then use:

```lean
K.orientIntrinsic hF
```

## Direct intrinsic orientation

Given:

```text
hJ : K.J0<0
```

apply:

```lean
K.c9_handoff A E hJ hF hc
```

to obtain a EuclideanSeed and contradict:

```text
EuclideanSeed.impossible.
```

## Reversed intrinsic orientation

Given:

```text
h : K.chain.alpha+1≤K.Croot
hJ : (K.reverseCore h).J0<0
```

let:

```text
Kr := K.reverseCore h.
```

Transport:

```text
hF
hc
```

through the relabeling.

Define fresh:

```text
Ar := Kr.firstFit
Er := Kr.returns.
```

Apply:

```text
Kr.c9_handoff Ar Er hJ hF_relabel hc_relabel.
```

Then use seed impossibility.

Do not reuse A/E from the pre-reversal core.

---

# 46. ChainInput.impossible

For:

```lean
C : ChainInput s F D
```

prove:

```lean
theorem ChainInput.impossible
    (C : ChainInput s F D)
    (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) :
    False
```

No additional mathematical hypotheses.

Compose only FROZEN upstream APIs:

```text
PF := choice (C.pfiber_exists hF)

M :=
choice C.max_i_exists

RB :=
C.root_box hF PF M

C.to_oriented_core RB
```

Case split.

## Direct CORE

Apply the `ChainCore.impossible` helper.

## Reversed CORE

Transport:

```text
hF
hc
```

through `relabelSetting/reversePerm`.

Apply `ChainCore.impossible` to the reversed CORE.

This is the primary CHAIN exclusion theorem.

---

# 47. CHAIN CLOSURE MUST BE ORIENTATION-SAFE

The original post-Type-II terminal wrapper is:

```lean
TerminalInputAfterTypeII
```

and has two frozen global orientations.

Do not prove only the local canonical-orientation `ChainInput.impossible`.

Add integration that eliminates both wrapper orientations by relabeling `hF/hc`.

---

# 48. SelectedTerminalAfterTypeII IMPOSSIBLE

Recall:

```text
SelectedTerminalAfterTypeII
=
∃ C : ChainInput ..., C.values=selectedValues rows.
```

Prove:

```lean
selected_terminal_after_chain_impossible
```

or equivalent:

```text
SelectedTerminalAfterTypeII ...
→ False
```

using only `C.impossible hF hc`.

The values equality is preserved but mathematically not needed for the contradiction.

---

# 49. TerminalInputAfterTypeII IMPOSSIBLE

Prove:

```lean
terminal_input_after_chain_impossible
```

for:

```text
TerminalInputAfterTypeII s F D rows
```

handling both frozen orientations.

For each orientation transport:

```text
IsFrobenius
Canonical
```

through relabeling and apply local CHAIN impossibility.

No case may be dropped.

---

# 50. NONSYMMETRIC SELECTED-FOUR CLOSURE

Use FROZEN:

```lean
nonsymmetric_selected_four_after_typeII
```

to prove a theorem conceptually:

```lean
nonsymmetric_selected_four_impossible_after_chain
```

with inputs:

```text
hF
hc
hns
rows : FourDistinctActualQRows s F
```

and conclusion:

```text
False.
```

This closes every selected-four nonsymmetric configuration.

---

# 51. NONSYMMETRIC Q≥4 CLOSURE

Use FROZEN:

```lean
nonsymmetric_Q_ge_four_after_typeII
```

to prove:

```lean
nonsymmetric_Q_ge_four_impossible_after_chain
```

with:

```text
hF
hc
hns
hcard : 4 ≤ (s.semigroup.Q F).ncard
```

conclusion:

```text
False.
```

This is the exact nonsymmetric theorem Section 11 will consume.

Do not yet combine it with the symmetric theorem.

---

# 52. CHAIN STATUS

If all previous sections succeed, the mathematical statement:

```text
CHAIN CLOSED
```

is justified as a candidate for independent TRUE audit.

But Codex itself must report only:

```text
C10 CHAIN EUCLIDEAN CLOSURE CANDIDATE FOR TRUE AUDIT
```

Do not self-award FROZEN.

---

# 53. 3234-CERTIFICATE CI POLICY

Create:

```text
verification/c10/generate_euclidean_certificate.py
```

with exact frozen source checks.

CI must check:

```text
supplement ZIP SHA:
24a02d34651c35aa3d07f707fd38b7ca29d0f8bbfa86190d956657308b498c5e

table SHA:
495504b4bcb8427db04b242cf09b83fbe7bde1188f9324b7e977036a5a4db9b3

verifier SHA:
23fcf03275bbe36ef7b9ca78a6cddb6b75dd1f04216d3675fbe0da759b9d048e

expected result SHA:
12a22a7ed7899ccb10cb8ff608ca4fc738da76ec0ed761c5fd72a4ab87967087

expected stdout SHA:
a298d66b61ca2b82ce9a429cbb795b7bd56c83f85795da7781e5c043ae12425f
```

Run the frozen verifier with pinned:

```text
SymPy 1.14.0
```

Expected:

```text
PASS
35 identities
3234 positive monomials
constant 63
```

But Lean proof remains authoritative.

---

# 54. PROOF-DEBT / AXIOM POLICY

Forbidden:

```text
sorry
admit
axiom
sorryAx

unsafe proof escape
opaque project theorem

native_decide proof substitute
run_tac proof generation

Python verifier ⇒ theorem
external asserted certificate
```

Required:

```text
proof debt = 0
project-specific axioms = 0
```

Expected inherited roots only:

```text
propext
Classical.choice
Quot.sound
```

---

# 55. C10 SCOPE REGRESSIONS

Explicitly test:

```text
EuclideanState contains no:
  canonical
  FirstFit
  RegionD
  q0
  ROOT
  PF rows
```

and:

```text
EuclideanState closure never references seed.canonical
```

Also test:

```text
terminal source replacement uses SAME W

terminal signed packet is converted to positive-part genuine packet

replaceWithinActualFactorization used with explicit containment

removeOne removes an actually present m

terminal I-FIT is proved, not assumed

3234 certificate identity is Lean-kernel proved

nonterminal NEW-PACKET is genuine

step matrix determinant remains 1

L'>M'

DP' = old PP

PP' = NEW-PACKET

packet determinant preserved exactly

RHO identities preserved

same W face preserved

F-gap preserved under relabel

measure decreases strictly

recursion is well-founded

transformed state does not require original first point
```

---

# 56. DEPENDENCY FIREWALL

Required direction:

```text
FROZEN C9 EuclideanSeed
      ↓
C10 EuclideanState
      ↓
terminal analysis
      ↓
3234 certificate
      ↓
terminal SAME-W closure
      ↓
nonterminal transform
      ↓
strict descent
      ↓
strong induction
      ↓
EuclideanSeed.impossible
      ↓
ChainCore.impossible
      ↓
ChainInput.impossible
      ↓
nonsymmetric Q≥4 impossible
```

Forbidden reverse dependencies:

```text
Section 11 final theorem
P21MainStatement proof
future final assembly
```

---

# 57. SUGGESTED MODULE LAYOUT

Use only NEW C10 mathematical modules.

For example:

```text
P21/Nonsymmetric/Chain/C10/
  State.lean
  CrossProductScale.lean
  MatrixOrder.lean
  Elimination.lean

  TerminalSetup.lean
  TerminalPacket.lean

  GeneratedTerminalCertificateTypes.lean
  GeneratedTerminalCertificateData00.lean
  ...
  GeneratedTerminalCertificate.lean

  TerminalCertificate.lean
  TerminalIFit.lean
  TerminalClosure.lean

  NonterminalRemainders.lean
  NewPacket.lean
  Transform.lean
  Preservation.lean
  Descent.lean
  EuclideanClosure.lean

  ChainExclusion.lean
  Integration.lean
```

and:

```text
P21/Nonsymmetric/Chain/C10.lean
```

top-level import.

Exact split may differ.

Do not append C10 proofs to C9 files.

---

# 58. FROZEN SOURCE POLICY

Every mathematical Lean source existing at:

```text
50d65c7982aebe67856cb85e81771d0452d62fec
```

is protected.

Expected mathematical changes:

```text
NEW C10 modules only.
```

Allowed:

```text
C10 docs
verification/c10
new CI workflow
NEXT_RESTART documentation update
```

If an old mathematical file must change:

```text
SOURCE CHANGE REQUIRED
FROZEN RE-AUDIT REQUIRED
```

Stop.

---

# 59. VERIFICATION

Run fresh:

```bash
lake build
```

Explicitly build all C10 modules.

Rerun every frozen regression:

```text
M1
M2A
M2B
M3A
M3B1
M3B2
P5
T6
C7
C8
C9
```

Add:

```text
verification/c10/
```

including:

```text
statement inspection
axiom inspection
proof-debt scan

EuclideanState field audit

canonical-field nonuse audit

dependency DAG
circularity scan

frozen source integrity

terminal certificate source hashes
certificate generator reproducibility
original EUCLIDEAN verifier log
Lean certificate build

fresh root build
explicit C10 build
all frozen regressions
```

---

# 60. DOCUMENTATION

Create:

```text
README_C10.md
SOURCE_OF_TRUTH_C10.md
C10_STATEMENT_MAP.md
C10_PROOF_ROUTE.md
C10_DEPENDENCY_DAG.md
```

Update:

```text
NEXT_RESTART.md
```

On full success it should say:

```text
C10 candidate:
CHAIN locally closed.

Pending:
independent TRUE AUDIT.

After TRUE AUDIT:
Section 11 FINAL ASSEMBLY only.
```

Do not claim FROZEN within the repository docs before external audit.

---

# 61. GITHUB CI

Create:

```text
.github/workflows/c10-audit.yml
```

CI records:

```text
branch
exact SHA
run ID
attempt

Lean version
Lake version
mathlib revision

candidate digest

frozen source integrity
fresh root build
explicit C10 build

M1–C9 regressions

proof debt
axioms
statement gates
dependency/circularity

EuclideanState scope gate
canonical-nonuse gate

3234-table hashes
certificate regeneration
original verifier
Lean certificate compilation

evidence manifest verification
```

No precompiled project-owned artifact may bypass source compilation.

---

# 62. EVIDENCE MANIFEST

Generate:

```text
EVIDENCE_SHA256.json
```

before artifact upload.

Hash every evidence file except itself.

Verify it in CI.

---

# 63. CANDIDATE ZIP

On full success create exactly:

```text
P21_LEAN_C10_CHAIN_EUCLIDEAN_CLOSURE_CANDIDATE_20260919.zip
```

Include:

```text
complete Lean project

all new C10 modules
generated 3234-term certificate Lean sources

C10 documentation
NEXT_RESTART.md

verification/c10/
CI workflow

candidate SHA manifest
```

Compute SHA-256.

---

# 64. TRUE AUDIT ARTIFACT

Upload:

```text
P21_C10_TRUE_AUDIT_EVIDENCE
```

including at least:

```text
RUN_CONTEXT
COMMIT_SHA
ENVIRONMENT

ROOT_BUILD_LOG
C10_MODULE_LIST
C10_BUILD_LOG
C10_VERIFICATION_LOG

M1_ORIGINAL_SUITE
M2A_ORIGINAL_SUITE
M2B_ORIGINAL_SUITE
M3A_ORIGINAL_SUITE
M3B1_ORIGINAL_SUITE
M3B2_ORIGINAL_SUITE
P5_ORIGINAL_SUITE
T6_ORIGINAL_SUITE
C7_ORIGINAL_SUITE
C8_ORIGINAL_SUITE
C9_ORIGINAL_SUITE

PROOF_DEBT_REPORT
AXIOM_REPORT
AXIOM_SUMMARY

STATE_SCOPE_REPORT
CANONICAL_NONUSE_REPORT

STATEMENT_INSPECTION
DEPENDENCY_DAG_CHECK
CIRCULARITY_CHECK
FROZEN_SOURCE_INTEGRITY
VERIFIED_SOURCE_SHA256

EUCLIDEAN_SUPPLEMENT_HASHES
EUCLIDEAN_ORIGINAL_VERIFIER_LOG
EUCLIDEAN_CERTIFICATE_GENERATION_CHECK
EUCLIDEAN_CERTIFICATE_LEAN_BUILD

candidate ZIP SHA
EVIDENCE_SHA256.json
```

Report artifact ID and GitHub digest.

---

# 65. SUCCESS GATE

You may report:

```text
C10 CHAIN EUCLIDEAN CLOSURE CANDIDATE FOR TRUE AUDIT
```

only if all are proved:

```text
[ ] EuclideanState defined without canonicality
[ ] seed.canonical unused by descent

[ ] generic HCR-only positive cross-product scale
[ ] matrix ORDER

[ ] I0/J0/M0/K0 identities
[ ] mhat formula
[ ] Phi monotonicity

[ ] terminal nu
[ ] jstar cap
[ ] terminal signed packet
[ ] positive-parts genuine packet

[ ] 3234 table exact
[ ] 3234 term count
[ ] constant 63
[ ] degree 7
[ ] generated Lean reproducible
[ ] Lean terminal certificate identity
[ ] terminal positivity
[ ] terminal I-FIT

[ ] SAME-W source containment
[ ] replaceWithinActualFactorization
[ ] actual m created in W
[ ] removeOne gives F
[ ] FINAL-EXACT regression

[ ] failure remainders
[ ] nu=e+1
[ ] R≤rhoRem<theta
[ ] 1≤kappa≤w

[ ] NEW-PACKET genuine

[ ] full abstract color exchange
[ ] matrix update
[ ] determinant preserved
[ ] source formulas preserved
[ ] DP/PP preserved as genuine
[ ] Dp preserved
[ ] RHO preserved
[ ] W face preserved
[ ] F gap preserved

[ ] strict measure descent
[ ] type-changing strong induction
[ ] EuclideanState.f_mem

[ ] EuclideanSeed.impossible

[ ] ChainCore.impossible
[ ] ChainInput.impossible

[ ] both TerminalInputAfterTypeII orientations eliminated

[ ] nonsymmetric selected-four impossible
[ ] nonsymmetric Q≥4 impossible

[ ] no Section 11 theorem proved

[ ] no protected math source changed
[ ] proof debt 0
[ ] project axioms 0

[ ] fresh root build PASS
[ ] explicit C10 build PASS
[ ] M1–C9 regressions PASS
[ ] certificate verification PASS
[ ] C10 verification PASS
[ ] GitHub CI PASS

[ ] candidate SHA recorded
[ ] artifact digest recorded
[ ] evidence manifest verified
```

---

# 66. PARTIAL / NO-GO POLICY

If C10 does not reach `ChainInput.impossible`, do not fake success.

Return:

```text
C10 PARTIAL — SECTION 10 / CHAIN OPEN
```

or:

```text
C10 NO-GO / INTERFACE OBSTRUCTION
```

Identify the **first exact unproved theorem**:

```text
Lean statement
publication subsection

already-proved dependencies
remaining gap

math / Lean API / certificate integration / recursion
```

If certificate is the obstruction, separately report:

```text
3234 JSON parsed?
source hashes?
generated Lean?
kernel identity?
positivity?
terminal I-FIT?
```

If strong induction is the obstruction, report:

```text
state transformation complete?
measure decrease complete?
only type-changing recursion remains?
```

Do not weaken the theorem.

Do not add a descent axiom.

---

# 67. STATUS LANGUAGE

Codex must not self-award:

```text
TRUE AUDIT PASS
FROZEN
P21 CLOSED
```

Strongest permitted result:

```text
C10 CHAIN EUCLIDEAN CLOSURE CANDIDATE FOR TRUE AUDIT
```

On success report:

```text
CHAIN:
CANDIDATE CLOSED — pending independent TRUE AUDIT

Remaining mathematical work after independent PASS:
Section 11 final assembly only.
```

---

# 68. FINAL REPORT FORMAT

Report in Japanese.

Begin exactly with one of:

```text
C10 CHAIN EUCLIDEAN CLOSURE CANDIDATE FOR TRUE AUDIT
```

```text
C10 PARTIAL — SECTION 10 / CHAIN OPEN
```

```text
C10 NO-GO / INTERFACE OBSTRUCTION
```

Then report:

```text
Repository:
Branch:
Frozen base:
Candidate commit:

EuclideanState:
canonical removed:
seed.canonical used in descent:

Cross-product scale:
Matrix ORDER:
mhat:
Phi monotonicity:

Terminal nu:
jstar:
kstar:
Terminal condition:

3234 table:
Table SHA:
Terms:
Degree:
Constant:
Verifier:
Generator reproducibility:
Lean certificate:

Terminal I-FIT:
SAME-W containment:
Replacement:
FINAL-EXACT:

Nonterminal e/rho/kappa:
nu=e+1:
Remainders:
NEW-PACKET:

Color exchange:
Matrix update:
New DP:
New PP:
packet determinant:
RHO preservation:
W preservation:
F-gap preservation:

Measure:
Strict descent:
Strong induction:
EuclideanState.f_mem:

EuclideanSeed.impossible:

ChainCore.impossible:
ChainInput.impossible:

TerminalInputAfterTypeII closure:
Nonsymmetric selected-four closure:
Nonsymmetric Q>=4 closure:

CHAIN overall status:
Next frontier:

New Lean modules:
Audited declarations:

Proof debt:
Project-specific axioms:
Inherited axioms:

FROZEN mathematical source integrity:
Forbidden reverse dependencies:

Root build:
Explicit C10 build:

M1:
M2A:
M2B:
M3A:
M3B1:
M3B2:
P5:
T6:
C7:
C8:
C9:
C10 verification:

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
Evidence verification:

SOURCE_CHANGED:
```

On full success:

```text
SOURCE_CHANGED: NO

CHAIN overall status:
CANDIDATE CLOSED — independent TRUE AUDIT required

Next frontier:
SECTION 11 FINAL ASSEMBLY ONLY
```

Execute C10 completely now.
