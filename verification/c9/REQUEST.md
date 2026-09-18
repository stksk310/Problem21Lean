# P21 LEAN — C9 / CHAIN U-D RESIDUALS → TWO GENUINE PACKETS

## SECTION 9 COMPLETE FORMALIZATION

## REGION U ELIMINATION / REGION D REDUCTION / 715-TERM I-FIT CERTIFICATE / TWO-PACKET EUCLIDEAN SEED

This is the third formalization milestone for the final CHAIN branch of `Problem21Lean`.

The independently TRUE-AUDITED / FROZEN state is now:

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
```

CHAIN overall remains:

```text
OPEN
```

The exact current terminal frontier is:

```text
RegionU ∨ RegionD
```

The final program is:

```text
C9   Section 9
     U/D residuals → two genuine packets
     → determinant-one Euclidean seed

C10  Section 10
     Euclidean descent
     → CHAIN CLOSED

FINAL
     Section 11 assembly
     → P21MainStatement
```

This mission is **C9 only**.

Do not perform the Section 10 descent.

---

# 0. REPOSITORY / IMMUTABLE BASE

Repository:

```text
https://github.com/stksk310/Problem21Lean
```

Immutable independently audited C8 base:

```text
7769545a357c0c4d24520ec7a9fc8994f3f664e7
```

Create a new branch from exactly this commit, preferably:

```text
c9-chain-two-packets
```

Do not merge to `main`.

---

# 1. C8 DOCUMENTATION REPAIR — NON-MATHEMATICAL ONLY

Independent C8 audit found:

```text
MINOR:
README_C8.md
SOURCE_OF_TRUTH_C8.md
C8_STATEMENT_MAP.md
C8_PROOF_ROUTE.md
C8_DEPENDENCY_DAG.md
were omitted from the candidate package.

EDITORIAL:
NEXT_RESTART.md still begins from Post-C7.
```

Repair these documentation files on the C9 branch.

The new active restart state must say:

```text
C8 TRUE AUDIT PASS / FROZEN
frontier = C9
RegionU ∨ RegionD
```

Do not modify any C8 mathematical Lean source.

---

# 2. FROZEN C8 ENTRYPOINT

Use exactly the audited Section 8 handoff:

```lean
ChainCore.FirstFit.OneData.RegionU
ChainCore.FirstFit.RegionD

ChainCore.FirstFit.c8_handoff
ChainCore.FirstFit.handoff_disjoint
ChainCore.FirstFit.branch_table
```

The key scope firewall is FROZEN:

## Region U carries window-only data

Region U contains the exact unit-window consequences, including:

```text
UnitParam
UnitFirstPoint
Delta0 / tau0 specialization
Du > 0
Q > R
actual level-one EB
Caps
```

## Region D does NOT carry ONE/DET1/PARAM

Region D contains only:

```text
strict C > alpha
T < chi ≤ C-alpha
Xi ≥ 1
Xi ≤ C-b_k-2alpha
C ≥ b_k+2alpha+1

actual PACKET

general pure-H EA kernel
general pure-H Qj kernel

Caps
Slopes
```

Do not import into Region D any of:

```text
OneData
EA-ONE
QJ-ONE
DET1
PARAM
LEVEL-SPLIT
```

unless re-derived later under newly justified hypotheses.

This scope firewall is mandatory.

---

# 3. SOURCE OF TRUTH

Authority order:

```text
1. reference_inputs/
   P21_Journal_of_Algebra_Submission_Manuscript_FINAL_20260916.pdf
   Section 9

2. reference_inputs/
   P21_MANUSCRIPT_EN_FINAL_20260908_v1.zip
   Section 9

3. reference_inputs/
   P21_FINAL_FROZEN_VERIFICATION_EDITION_20260907.zip

4. reference_inputs/
   P21_supplement_v1.zip

5. FROZEN C7/C8 Lean API
```

Formalize all of:

```text
§9.1–9.5    Region U elimination

§9.6–9.10   Region D:
            high-q closure
            nonlinear-first closure

§9.11       linear-first exact parameterization
            two genuine packets
            packet determinant positivity

§9.12       715-term certificate
            i-source fitting

§9.13       j-shortage only
            zero-j upper representation

§9.14       complementary genuine packet

§9.15       determinant-one matrix embedding

§9.16–9.17 exact C10 abstract handoff
```

---

# 4. ABSOLUTE FIREWALLS

## 4.1 Actual versus signed

No signed relation implies Γ-membership.

Every U/D packet used for replacement must have nonnegative coefficients on both sides.

## 4.2 Same-element replacement

Every repeated packet replacement must occur coefficientwise inside an explicitly named actual upper element.

## 4.3 Criticality

Herzog criticality only after complete elimination of m.

## 4.4 Certificate policy

The 715-term JSON/table/verifier is proof data, not an oracle.

A Python PASS message is not a Lean proof.

The final positivity theorem must be checked by the Lean kernel.

## 4.5 No C10 reverse dependency

C9 may define the **abstract Euclidean seed structure** that C10 will consume.

C9 must not use:

```text
Euclidean descent
terminal source fit
C10 transformation
CHAIN impossibility
P21 main theorem
```

---

# 5. C9A — REGION U EXACT INPUT

Take:

```lean
O : A.OneData E
U : O.RegionU
```

Use only FROZEN Region U fields and their dependencies.

Use publication notation:

```text
a   := E.Aj + 1
z   := O.z
Q   := E.Uj + 1

eta := E.Cj + 1
```

and recover the exact U-PARAM equations:

```text
lambda = d = a + z*delta

S = g + z*Q

a_i = d + delta
b_i = d + beta

rho_j = g + (z+1)Q

rho_k =
  (z+1)C
+ eta
+ z*b_k
```

with:

```text
z ≥ 1
a ≥ 1
Q ≥ 1
```

and FROZEN U-signs:

```text
1 ≤ eta ≤ min(C-alpha,T)

Du :=
  Q*eta
- R*(C+b_k)
> 0
```

Do not treat `Du>0` as a new assumption: it is already a C8 RegionU conclusion.

---

# 6. C9A — REPETITION COUNT

Define:

```text
Hu := C-alpha-eta
```

and prove:

```text
Hu ≥ 0
```

Define exactly:

```text
t := floor(Hu / eta) + 1
```

with integer Euclidean division.

Prove:

```text
t ≥ 1
```

and define remainder:

```text
rU := Hu-(t-1)*eta
```

with:

```text
0 ≤ rU ≤ eta-1
```

Thus:

```text
Hu = (t-1)eta+rU
```

and:

```text
C = alpha+t*eta+rU
```

No bounded iteration or numerical scan.

---

# 7. C9A — J-FIT

Using:

```text
eta ≤ T = b_k+alpha
```

prove:

```text
C+b_k
=
T+t*eta+rU
≥ (t+1)eta
```

From:

```text
Du>0
```

obtain:

```text
Q*eta >
R*(C+b_k)
≥
R*(t+1)eta
```

Since:

```text
eta≥1
```

derive the exact integer fit:

```text
J-FIT:
Q ≥ (t+1)R + 1
```

This must be uniform in t.

---

# 8. C9A — U CROSS-PRODUCT MONOTONICITY

Reuse the scale-aware C8 cross products:

```text
Ical
Jcal
Kcal
sigma>0
```

Do not assume `sigma=1` unless re-proved from the existing global API.

Define:

```text
mhat :=
-d*Ical
+S*Jcal
+C*Kcal
```

and:

```text
PhiU(a) := mhat-Jcal
```

viewed as a linear expression in local parameter `a`, holding other U parameters fixed.

Rather than formal calculus, prove the exact integer finite-difference identity:

```text
PhiU(a+1)-PhiU(a)
=
-Du-rho_k-b_k
```

and hence:

```text
PhiU(a+1) < PhiU(a)
```

because:

```text
Du>0
rho_k>0
b_k>0
```

This is the Lean version of publication MONO-A.

---

# 9. C9A — U I-FIT THRESHOLD

Define:

```text
b0 := z*delta+beta
```

prove:

```text
b0>0
```

and threshold:

```text
astar :=
t*b0 + beta
```

The target is:

```text
I-FIT-U:
a ≥ t*b0 + beta + 1
```

---

# 10. C9A — U POS-DECOMP

Set:

```text
wU := T-eta ≥ 0

qprime :=
Q-(t+1)(a_j+g)-1
```

Use J-FIT to prove:

```text
qprime ≥ 0
```

Substitute:

```text
C = alpha+t*eta+rU

b_k =
eta-alpha+wU
```

into:

```text
PhiU(astar)
```

and prove the publication identity:

```text
PhiU(astar)
=
delta {
  Pdelta
  +(a_j-1)Xdelta
  +(g-1)Ydelta
  +qprime Zdelta
}
+
beta {
  Pbeta
  +(a_j-1)Xbeta
  +(g-1)Ybeta
  +qprime Zbeta
}
```

Use the exact six coefficient polynomials from Appendix C.

Do not alter their formulas.

---

# 11. C9A — POSITIVITY OF U POLYNOMIALS

Formalize the Appendix C expressions exactly.

Prove:

```text
Xdelta,Ydelta,Zdelta ≥0
Xbeta,Ybeta,Zbeta ≥0
```

over:

```text
t,z ≥1
alpha,eta ≥1
rU,wU ≥0
```

and prove:

```text
Pdelta>0
Pbeta>0
```

In particular explicitly discharge the apparently dangerous term:

```text
t^2*z+t^2+3*t*z+2*z-3 ≥ 4
```

for:

```text
t,z≥1
```

Hence:

```text
PhiU(astar)>0
```

because:

```text
delta,beta≥1
```

.

No external certificate is needed for Region U.

---

# 12. C9A — COMPLETE U I-FIT

If:

```text
a≤astar
```

use strict monotonicity to get:

```text
PhiU(a) ≥ PhiU(astar)>0
```

thus:

```text
mhat>Jcal
```

and with positive common scale:

```text
m>n_j
```

contradicting multiplicity.

Therefore:

```text
I-FIT-U:
a ≥ t*(z*delta+beta)+beta+1
```

---

# 13. C9A — GENUINE U-PACKET

Derive exactly:

```text
U-PACKET:

(z*delta+beta)n_i
+
R*n_j
=
(z+1)m
+
eta*n_k
```

Prove coefficients on both sides nonnegative.

This is a genuine packet equality.

---

# 14. C9A — ACTUAL UPPER ELEMENT

Let:

```text
qAk := K.chain.qK
```

or the exact frozen A_k row.

Prove:

```text
qAk + (Hu+1)n_k
```

is an actual Γ-element.

Do this from the actual PF successor:

```text
qAk+n_k ∈ Γ
```

plus:

```text
Hu≥0
```

copies of `n_k`.

Derive exact equality:

```text
U-UPPER:

qAk+(Hu+1)n_k
=
(z+2)m
+
(a-beta-1)n_i
+
(Q-R-1)n_j
```

Then use U I-FIT and J-FIT to prove the right side is genuinely nonnegative.

---

# 15. C9A — REPLACE t PACKETS IN THE SAME UPPER ELEMENT

From I-FIT-U:

```text
a-beta-1
≥
t*(z*delta+beta)
```

and J-FIT:

```text
Q-R-1
≥
t*R
```

there are coefficientwise at least t copies of the left side of U-PACKET inside the same U-UPPER factorization.

Replace all t copies by the right side of U-PACKET.

The new k-coordinate is:

```text
t*eta
```

and:

```text
t*eta-(Hu+1)
=
eta-rU-1
≥0
```

.

Remove exactly the previously added:

```text
(Hu+1)n_k
```

from this same factorization.

Obtain the genuine factorization:

```text
qAk
=
[z+2+t(z+1)]m
+
[a-beta-1-t(z*delta+beta)]n_i
+
[Q-(t+1)R-1]n_j
+
[eta-rU-1]n_k
```

with all coefficients nonnegative.

This contradicts the actual pseudo-Frobenius gap.

Conclude:

```text
RegionU.impossible
```

with no additional mathematical assumptions.

Formally:

```text
RegionU = ∅
```

---

# 16. C9B — ENTER REGION D

Now take:

```lean
RD : A.RegionD E hF
```

Do not construct `OneData`.

Do not use window DET1/PARAM.

Derive only Section-9-valid data from:

```text
RegionD
C7 intrinsic data
C7 SUM-NOTCH
C7 FK-STRONG
FirstFit
PACKET
Caps / Slopes
```

Because RegionD has:

```text
C>alpha
```

you may use C7 strict-region theorems:

```text
sum_notch
FK_strong
```

to derive:

```text
e0 ≥ beta+delta+1
```

and:

```text
tau0 ≥ R+1
```

These are C7 strict conclusions, not C8 window conclusions.

---

# 17. C9B — D NOTATION

Use:

```text
h   := floor(lambda/d)
q0  := h+1
r   := lambda-h*d

e0  := d-r

b   := r+delta
c   := r+beta

tau := rho_j-h*S
```

and derive:

```text
a_i = h*d+b
b_i = h*d+c
rho_j = h*S+tau
```

Region D gives:

```text
e0 ≥ beta+delta+1
```

```text
1 ≤ tau ≤ S-g
```

```text
tau ≥ R+1
```

and slope:

```text
V :=
d*rho_j-S*a_i
=
d*tau-b*S
>0
```

Also:

```text
C ≥ b_k+2alpha+1
```

and:

```text
1 ≤ b ≤ d-beta-1 < d
```

Prove these exactly.

---

# 18. C9B — D FIRST POINT / PACKET

Retain the FROZEN C8 first point:

```text
z := zhat
N
I
J
Xi
chi
```

with Region D:

```text
Xi≥1
T<chi≤C-alpha
```

The genuine packet simplifies to:

```text
D-PACKET:

DF*n_i + EF*n_j
=
(N-1)m + chi*n_k
```

where:

```text
DF = d+beta-1-I
EF = R+rho_j-S-1-J
```

because:

```text
chi>0
```

.

Also retain the genuine upper element:

```text
OmegaD :=
F+(C-alpha+1)n_k
```

with:

```text
OmegaD =
(d+beta-1)n_i
+
(R+rho_j-S-1)n_j
```

.

---

# 19. C9B — LEAST PACKET COUNT

Define:

```text
bD :=
floor((C-alpha)/chi)+1
```

and prove:

```text
bD≥2
```

using:

```text
1≤chi≤C-alpha
```

.

Record exact fitting conditions:

```text
bD*DF ≤ d+beta-1
bD*EF ≤ R+rho_j-S-1
```

but do not assume them.

They will be resolved symbolically.

---

# 20. C9B — LAST CROSSING IS AN h-STEP

Since:

```text
a_i=h*d+b
0<b<d
```

prove consecutive increments of `n_zeta` are exactly:

```text
h
or
h+1
```

At:

```text
zeta=1
```

use C7 compact data:

```text
n_1=q0
```

and:

```text
J_1=-Delta0<0
```

to prove:

```text
z≥2
```

.

If the final increment were:

```text
h+1
```

then:

```text
J_z-J_(z-1)
=
rho_j-(h+1)S
=
tau-S
≤-g<0
```

so it cannot cross from negative to nonnegative.

Therefore:

```text
n_z-n_(z-1)=h
```

.

---

# 21. C9B — SHARP FIRST-CAPS IN D

Using the last h-step prove:

```text
0≤J≤tau-1
```

and:

```text
0≤I≤d-b-1
```

equivalently:

```text
I≤e0-delta-1
```

because:

```text
d-b=e0-delta
```

.

These are D-specific sharper FIRST-CAPS.

---

# 22. C9B — NV / ZV IDENTITIES

Prove exact:

```text
N*V
=
rho_j*(I-delta+1)
+
a_i*(J-g+1)
```

and:

```text
z*V
=
S*(I-delta+1)
+
d*(J-g+1)
```

Then derive:

```text
N*V
≤
h*V
+
(d-delta)rho_j
-
a_i*g
```

and:

```text
(z-1)V
≤
S(d-delta)-d*g
```

Call these:

```text
FIRST-BOUNDS
```

No ONE/DET1/PARAM.

---

# 23. C9B — MULTIPLICITY MASTER

Reuse C8 scale-aware cross products:

```text
Ical,Jcal,Kcal
sigma>0
m=sigma*mhat
```

Define:

```text
Dj :=
d*a_j+S*b_i

Amul :=
Kcal-N*V

Bmul :=
Dj-(z-1)*V
```

From the first-point/Xi relation prove:

```text
rho_k =
N*C
+
(z-1)b_k
-
alpha
+1
-
Xi
```

and exact:

```text
mhat
=
C*Amul
+
b_k*Bmul
+
(alpha-1+Xi)*V
```

Then derive:

```text
M-MASTER:

mhat-Kcal
=
(C-b_k-2alpha-1)*Amul
+
(b_k-1)(Amul+Bmul)
+
(alpha-1)(2Amul+V)
+
(Xi-1)V
+
[4Amul+Bmul+V-Kcal]
```

Every coefficient outside the final bracket is nonnegative in Region D.

This theorem is used in the next two closures.

---

# 24. C9B — HIGH-q / h≥2 CLOSURE

Assume:

```text
h≥2
```

equivalently:

```text
q0≥3
```

.

Using FIRST-BOUNDS prove:

```text
Amul ≥ A0
Bmul ≥ B0
```

where:

```text
A0 :=
Kcal
-h*V
-(d-delta)rho_j
+a_i*g
```

and:

```text
B0 :=
d*R
+
S*(P-d)
```

.

Prove:

```text
B0>0
```

.

Expand:

```text
A0 =
S*AS
+
tau*Atau
+
a_i*R
```

where:

```text
AS =
h*((h-1)d+beta+2delta+2r)

Atau =
beta-d+delta+r
```

and:

```text
AS+Atau
=
[h(h-1)-1]d
+
(h+1)beta
+
(2h+1)(delta+r)
>0
```

Since:

```text
S>tau>0
```

derive:

```text
A0>0
```

without requiring `Atau≥0`.

---

# 25. C9B — HIGH-q FINAL BRACKET

Prove:

```text
4A0+B0+V-Kcal
=
S*HS
+
tau*Htau
+
Hc
```

where:

```text
HS =
(3h^2-3h-1)d
+
(3h+1)beta
+
8h delta
+
7h r
```

```text
Htau =
3beta
-(h+3)d
+4delta
+3r
```

```text
Hc =
a_j[(3h+1)d+3(delta+r)]
+
g[(4h+1)d+4(delta+r)]
```

Prove:

```text
HS>0
Hc>0
```

and:

```text
HS+Htau
=
(h-2)(3h+2)d
+
(3h+4)beta
+
(8h+4)delta
+
(7h+3)r
>0
```

Then:

```text
S*HS+tau*Htau
=
(S-tau)HS
+
tau(HS+Htau)
>0
```

.

Thus the final M-MASTER bracket is positive.

Conclude:

```text
mhat>Kcal
```

and therefore:

```text
m>n_k
```

contradicting multiplicity.

Hence:

```text
HIGH-Q-CLOSED:
RegionD ∩ {q0≥3} = ∅
```

and every Region D survivor satisfies:

```text
h=1
q0=2
d≤lambda<2d
```

.

---

# 26. C9B — q0=2 FIRST-POINT DECOMPOSITION

Now fix:

```text
h=1
q0=2
```

.

Write:

```text
lambda=d+r
a_i=d+b
b=r+delta
```

.

For first-point index `z` define:

```text
ell_z :=
ceil((z*b-delta+1)/d)
```

so:

```text
n_z = z+ell_z
```

and:

```text
ell_z≥1
```

.

The target is to eliminate:

```text
ell_z≥2
```

.

---

# 27. C9B — NONLINEAR-FIRST AUXILIARY kappa

Assume:

```text
ell_z≥2
```

and define:

```text
kappa :=
floor((d+delta-1)/b)
```

.

Prove:

```text
kappa≥1
```

.

For every:

```text
1≤v≤kappa
```

prove:

```text
ell_v=1
```

.

Since none of these earlier indices is the first successful point, derive:

```text
S≥kappa*tau+g
```

.

Define:

```text
rprime :=
d-kappa*b
```

.

Using:

```text
V=d*tau-b*S>0
```

show:

```text
rprime>0
```

and from floor bounds:

```text
1≤rprime≤b-delta
```

.

Call this:

```text
SMALL-R
```

.

---

# 28. C9B — NONLINEAR-FIRST I CAP

If:

```text
I≥rprime
```

construct the preceding integer candidate:

```text
(z-kappa, ell_z-1)
```

with i-coordinate:

```text
I-rprime≥0
```

and j-coordinate:

```text
J+S-kappa*tau≥g>0
```

.

Its z-index is positive and strictly smaller than z.

Replace n by its least allowed first-fit value; this only increases the j-coordinate.

Contradict minimality of the first point.

Therefore:

```text
0≤I≤rprime-1
```

.

---

# 29. C9B — NONLINEAR-FIRST MULTIPLICITY CLOSURE

Using:

```text
I≤rprime-1
J≤tau-1
```

and NV/ZV derive:

```text
Amul ≥ A1
Bmul ≥ B1
```

where:

```text
A1 :=
((kappa+1)b+beta)S
+
(beta-rprime)tau
+
a_i R
```

and:

```text
B1 :=
(kappa*b+beta)S
+
d R
```

.

Prove:

```text
A1>0
B1>0
```

using:

```text
S>tau
```

and:

```text
(kappa+1)b+2beta-rprime
≥
kappa*b+delta+2beta
>0
```

.

---

# 30. C9B — NONLINEAR-FIRST FINAL BRACKET

Prove:

```text
4A1+B1+V-Kcal
=
S*ES
+
tau*Etau
+
Ec
```

with:

```text
ES =
(4kappa+2)b
+
4beta
+
delta
-
rprime
```

```text
Etau =
-b
+
3beta
+
delta
-
4rprime
```

```text
Ec =
a_j[(4kappa+3)b+4rprime]
+
g[(5kappa+4)b+5rprime]
```

.

Prove:

```text
ES>0
Ec>0
```

and using:

```text
b≥rprime+delta
```

prove:

```text
kappa*ES+Etau
≥
(kappa-1)(4kappa+5)rprime
+
kappa(4kappa+3)delta
+
(4kappa+3)beta
>0
```

.

Since:

```text
S≥kappa*tau+g
```

derive:

```text
S*ES+tau*Etau
=
(S-kappa*tau)ES
+
tau(kappa*ES+Etau)
>0
```

.

M-MASTER then yields:

```text
m>n_k
```

contradiction.

Therefore:

```text
NONLINEAR-FIRST-CLOSED:

q0=2
∧ N≥z+2
→ False
```

.

Every surviving Region D case now satisfies exactly:

```text
q0=2
N=z+1
```

.

---

# 31. C9B — LINEAR-FIRST PARAMETERIZATION

Set:

```text
k := z-1
```

prove:

```text
k≥1
```

and define:

```text
Q := tau

upsilon :=
Q-1-J

G :=
g+upsilon

Epar :=
R+upsilon

b := r+delta
c := r+beta

Bpkt :=
k*b+c
```

and:

```text
a :=
d-k*b
```

.

Prove:

```text
upsilon≥0
a≥r+1≥1
```

and exact formulas:

```text
S = k*Q+G

rho_j =
(k+1)Q+G

rho_k =
(k+1)C
+
k*b_k
+
chi

a_i=d+b
b_i=d+c

d=a+k*b

I =
d+delta-1-(k+1)b

J =
Q-upsilon-1
```

and:

```text
Bpkt = DF
```

.

---

# 32. C9B — FIRST GENUINE LINEAR PACKET

Specialize the Region D genuine packet to obtain:

```text
D-LINEAR:

Bpkt*n_i
+
Epar*n_j
=
(k+1)m
+
chi*n_k
```

All coefficients must be explicitly nonnegative.

This is the future C10 DP packet.

---

# 33. C9B — SECOND INTRINSIC LINEAR PACKET

Since:

```text
q0=2
```

we have:

```text
h=1
```

.

Specialize the FROZEN C7 SHIFT-NEW relation:

```text
h*m+tau0*n_j
=
(a_i-h*d)n_i
+
(b_k+h*C)n_k
```

to obtain:

```text
INTRINSIC-LINEAR:

m+Q*n_j
=
b*n_i
+
(C+b_k)n_k
```

with all coefficients nonnegative.

This is a genuine packet equality.

Do not reconstruct it as a signed relation if the C7 actual packet theorem can be reused directly.

---

# 34. C9B — POSITIVE PACKET DETERMINANT

Define:

```text
Dp :=
Q*chi
-
Epar*(C+b_k)
```

.

The target is:

```text
Dp>0
```

.

Define the positive expressions:

```text
Mb :=
C[
  Q*k*(k+1)
  +a_j*(k+1)
  +G*(2k+1)
]
+
b_k[
  Q*k^2
  +a_j*k
  +2G*k
]
+
chi*G
```

and:

```text
Mc :=
C[
  Q*(k+1)+G
]
+
b_k[
  Q*k+G
]
```

.

Prove:

```text
Mb>0
Mc>0
```

.

Then prove the exact multiplicity identity:

```text
mhat-Ical
=
-(a+k+1)*Dp
+
(b-1)*Mb
+
(c-1)*Mc
```

.

If:

```text
Dp≤0
```

the right-hand side is nonnegative, because:

```text
a,k≥1
b,c≥1
```

.

Thus:

```text
mhat≥Ical
```

hence:

```text
m≥n_i
```

contradicting multiplicity.

Conclude:

```text
DSCR:
Dp>0
```

.

---

# 35. C9B — LEAST D-PACKET REPETITION

Define:

```text
f :=
floor((C-alpha)/chi)
```

.

Region D gives:

```text
1≤chi≤C-alpha
```

so prove:

```text
f≥1
```

.

Define:

```text
w :=
C-alpha-f*chi
```

and prove:

```text
0≤w<chi
```

thus:

```text
C =
alpha+f*chi+w
```

.

The least packet count is:

```text
bD=f+1
```

.

---

# 36. C9B — REMAINDER SLOPE

Use:

```text
Dp>0
```

and:

```text
Epar=R+upsilon
```

with:

```text
C+b_k
=
f*chi+T+w
```

to derive:

```text
Q*chi >
Epar*(f*chi+T+w)
```

.

Define:

```text
theta :=
Q-f*Epar
```

.

Prove:

```text
theta≥1
```

and the exact positive remainder slope:

```text
REMAINDER-SLOPE:

theta*chi >
Epar*(T+w)
```

.

---

# 37. C9B — 715-TERM CERTIFICATE: FROZEN INPUT

The exact frozen supplement is:

```text
reference_inputs/P21_supplement_v1.zip
```

Expected SHA-256 of that ZIP at the audited C8 base:

```text
24a02d34651c35aa3d07f707fd38b7ca29d0f8bbfa86190d956657308b498c5e
```

Inside it, the two copies of the linear coefficient table are byte-identical:

```text
supplement/verification_scripts/LINEAR/
  I_FIT_POSITIVE_COEFFICIENTS.json

supplement/coefficient_tables/
  I_FIT_POSITIVE_COEFFICIENTS.json
```

Expected SHA-256:

```text
9ba4fdcbdc1b5440785232e97e8cf8d729c3cf1254d87551d3a90d9abbff5916
```

Exact verifier:

```text
supplement/verification_scripts/LINEAR/verify_D_linear.py
```

Expected SHA-256:

```text
bcdedc3525a397601fd49704629e221f0e34e6d5ffcdc0c9c8e22d3f25775ae1
```

The table contains:

```text
715 terms total
constant term = 35
```

Variable order:

```text
f
r
delta
beta
g
u
alpha
w
theta
eps
k
a_j
b_k
```

with mathematical shifted variables:

```text
f      ↔ f-1
r      ↔ r
delta  ↔ delta-1
beta   ↔ beta-1
g      ↔ g-1
u      ↔ upsilon
alpha  ↔ alpha-1
w      ↔ w
theta  ↔ theta-1
eps    ↔ epsilon
k      ↔ k-1
a_j    ↔ a_j-1
b_k    ↔ b_k-1
```

---

# 38. CERTIFICATE FORMALIZATION POLICY

The Python verifier is only an auxiliary consistency check.

It must NOT be the proof of positivity.

Create a deterministic generator, for example:

```text
verification/c9/generate_linear_certificate.py
```

that:

1. reads the exact frozen nested ZIP;
2. verifies the supplement ZIP SHA;
3. verifies both JSON copies have the exact table SHA;
4. verifies both table copies are byte-identical;
5. verifies:

   * 715 terms,
   * variable order,
   * constant 35;
6. deterministically emits a committed Lean source, for example:

```text
P21/Nonsymmetric/Chain/C9/
  LinearCertificateData.lean
```

CI must regenerate it into a temporary path and require exact byte equality with the committed Lean file.

---

# 39. LEAN-KERNEL CERTIFICATE REQUIREMENT

The generated Lean source must contain transparent finite proof data.

Recommended design:

```text
structure CertTerm where
  coefficient : ℕ
  exponents : Fin 13 → ℕ
```

or equivalent.

Define exact monomial evaluation over ℤ.

Prove generically:

```text
all shifted variables ≥0
→
every certificate monomial ≥0
```

and therefore:

```text
certificateEval ≥ 35 > 0
```

.

The critical polynomial identity itself must be checked by Lean.

Preferred routes:

```text
A. generated explicit polynomial RHS + `ring`

or

B. a transparent MvPolynomial representation with
   kernel-checked coefficient equality / normalization
```

If `ring` on all 715 terms is expensive, reorganize the generated expression into deterministic chunks.

Forbidden:

```text
native_decide
run_tac
Python success ⇒ theorem
axiom certificate_identity
opaque imported theorem
```

The proof term must compile from source.

---

# 40. C9B — LINEAR I-FIT SETUP

Define:

```text
Phi(a) := mhat-Jcal
```

in the §9.11 linear parameterization.

Define threshold:

```text
astar :=
f*Bpkt+r
```

.

Target:

```text
a ≥ astar+1
```

equivalently:

```text
d ≥ (f+1)Bpkt-beta+1
```

.

---

# 41. C9B — EXACT MONOTONICITY

Do not formalize calculus.

Prove the integer difference identity:

```text
Phi(a+1)-Phi(a)
=
-Dp-rho_k-b_k
```

.

Since:

```text
Dp>0
rho_k,b_k>0
```

obtain:

```text
Phi(a+1)<Phi(a)
```

and hence:

```text
a≤astar
→
Phi(a)≥Phi(astar)
```

.

---

# 42. C9B — SHIFTED CERTIFICATE DOMAIN

Define:

```text
epsilon :=
chi-(b_k+alpha+1)
```

Region D has:

```text
chi>T=b_k+alpha
```

so prove:

```text
epsilon≥0
```

.

Substitute:

```text
Q =
f*(a_j+g+upsilon)+theta

C =
alpha+f*chi+w

chi =
b_k+alpha+1+epsilon

b =
r+delta

c =
r+beta

G =
g+upsilon
```

.

All 13 shifted certificate variables are now nonnegative.

---

# 43. C9B — 715-TERM IDENTITY

Use the generated Lean proof data to prove exact:

```text
I-POS-CERT:

Phi(astar)
=
35
+
Σ_{gamma≠0}
  c_gamma * y^gamma
```

with exactly the frozen 715-term table.

The table is authoritative proof data.

No coefficient may be omitted.

No regenerated/fitted alternative certificate is permitted without explicit source change.

Then prove:

```text
Phi(astar)≥35>0
```

.

---

# 44. C9B — LINEAR I-FIT

Assume:

```text
a≤astar
```

.

By monotonicity:

```text
Phi(a)≥Phi(astar)>0
```

hence:

```text
mhat>Jcal
```

and with positive common scale:

```text
m>n_j
```

contradicting multiplicity.

Therefore:

```text
a≥f*Bpkt+r+1
```

.

Prove the exactly equivalent source condition:

```text
I-FIT-D:

d ≥ (f+1)Bpkt-beta+1
```

.

This is the only place the 715-term certificate is load-bearing.

---

# 45. C9B — REPLACE f+1 D-PACKETS

Use the SAME actual upper element:

```text
OmegaD =
F+(C-alpha+1)n_k
```

with source factorization:

```text
(d+beta-1)n_i
+
(R+rho_j-S-1)n_j
```

.

By I-FIT-D the i-source contains:

```text
(f+1)*Bpkt
```

copies required by `f+1` D-LINEAR packets.

Perform the repeated replacement coefficientwise inside this exact actual upper element.

Derive the exact completed F-row:

```text
J-ONLY:

F =
(f+1)(k+1)m
+
[d+beta-1-(f+1)Bpkt]n_i
+
(theta-upsilon-1)n_j
+
(chi-w-1)n_k
```

.

Verify:

```text
m coefficient >0

i coefficient ≥0
k coefficient ≥0
```

.

The j-coordinate is the only possible shortage.

---

# 46. C9B — CLOSE theta ≥ upsilon+1

If:

```text
theta≥upsilon+1
```

then the j-coordinate in J-ONLY is also nonnegative.

Hence construct an actual factorization of `F`.

Contradiction.

Therefore every survivor satisfies:

```text
1≤theta≤upsilon
```

and in particular:

```text
upsilon≥1
```

.

Define:

```text
Delta1 :=
upsilon+1-theta
```

and prove:

```text
Delta1≥1
```

.

---

# 47. C9B — ACTUAL ZERO-j UPPER REPRESENTATION

The same repeated-packet representation yields:

```text
F+Delta1*n_j
=
(f+1)(k+1)m
+
[d+beta-1-(f+1)Bpkt]n_i
+
(chi-w-1)n_k
```

.

Prove this is a genuine actual factorization with zero j-coordinate.

Retain it explicitly in the C10 seed package if useful for provenance, even though Section 10 may not need it as a field.

---

# 48. C9B — COMPLEMENTARY PACKET

Take:

```text
f copies of D-LINEAR
+
1 copy of INTRINSIC-LINEAR
```

and prove exact:

```text
COMPLEMENTARY:

Ldiamond*m
+
theta*n_j
=
Bdiamond*n_i
+
(T+w)n_k
```

where:

```text
Ldiamond :=
1+f*(k+1)

Bdiamond :=
b+f*Bpkt
```

.

Every coefficient on both sides must be nonnegative.

This is a genuine packet equality.

---

# 49. C9B — INITIAL MATRIX

Define:

```text
p := f*k+1
q := f

s := k
t := 1
```

.

Prove:

```text
p,q,s,t ≥1
```

and exact:

```text
p*t-q*s = 1
```

.

Define:

```text
L := p+q
M := s+t
```

and prove:

```text
L =
1+f(k+1)

M =
k+1

L>M
```

because:

```text
f,k≥1
```

.

---

# 50. C9B — SOURCE COEFFICIENTS

Set:

```text
A :=
p*(r+delta)
+
q*(r+beta)

B :=
s*(r+delta)
+
t*(r+beta)
```

.

Prove exactly:

```text
A =
b+f*Bpkt

B =
Bpkt
```

.

Thus COMPLEMENTARY is future packet PP and D-LINEAR is future packet DP.

---

# 51. C9B — ABSTRACT PACKET PARAMETERS

Set:

```text
u  := upsilon

E  := R+u

Hp := T+w
```

retain:

```text
chi
theta
```

and prove:

```text
u≥1

E=R+u

Hp=T+w

1≤theta≤u

w≥0
chi≥1
```

.

Define:

```text
DpAbs :=
theta*chi-E*Hp
```

and prove:

```text
DpAbs>0
```

exactly from REMAINDER-SLOPE.

---

# 52. C9B — RHO IDENTITIES

Prove the exact identities:

```text
rho_j =
L*E
+
M*theta
-
a_j
```

and:

```text
rho_k =
L*chi
+
M*Hp
-
b_k
```

using the linear-first parameterization.

These are Section 10 load-bearing invariants.

---

# 53. C9 — DEFINE ABSTRACT EUCLIDEAN SEED

Create a genuinely Section-10-independent structure, preferably in C9, conceptually:

```lean
structure EuclideanSeed ... where
```

It must contain only the exact §10.2 abstract inputs.

It must NOT contain:

```text
FirstFit
RegionD
zhat
N,I,J
q0
ROOT
four PF rows
minimality of first point
```

Those conditions end here.

Required content:

```text
same setting / semigroup
same F,m,W
Frobenius gapness
multiplicity inequalities

positive canonical:
delta,beta,g,alpha,P,R,T
a_i=P-beta>0
b_i=P-delta>0

HCR
W-face

matrix p q s t ≥1
det=1

L=p+q
M=s+t
L>M

r≥0

A =
p(r+delta)+q(r+beta)

B =
s(r+delta)+t(r+beta)

u≥1
E=R+u

w≥0
Hp=T+w

1≤theta≤u
chi≥1

Dp=theta*chi-E*Hp>0

genuine DP:
B*n_i+E*n_j
=
M*m+chi*n_k

genuine PP:
A*n_i+Hp*n_k
=
L*m+theta*n_j

rho_j =
L*E+M*theta-a_j

rho_k =
L*chi+M*Hp-b_k
```

This structure should be sufficient for C10 without importing any C8/C9 first-point theory.

---

# 54. C9 — REGION D TO EUCLIDEAN SEED

Prove:

```lean
RegionD.toEuclideanSeed
```

or equivalent.

The theorem must internally compose:

```text
HIGH-Q closure
→ h=1

NONLINEAR-FIRST closure
→ N=z+1

linear parameterization

DSCR

715-term I-FIT

j-shortage reduction

COMPLEMENTARY packet

matrix embedding
```

No extra hypothesis.

---

# 55. C9 — FULL HANDOFF FROM C8

Use the FROZEN theorem:

```lean
c8_handoff
```

which gives:

```text
RegionU ∨ RegionD
```

.

Eliminate Region U using:

```text
RegionU.impossible
```

.

Map Region D to `EuclideanSeed`.

The main C9 theorem should conceptually be:

```lean
theorem ChainCore.c9_handoff
    (...) :
    Nonempty (EuclideanSeed ...)
```

or equivalent.

This theorem is the exact Section 9 output.

CHAIN is still OPEN.

---

# 56. C9 — SCOPE REGRESSION

Add explicit regression theorem/checks that prove:

```text
- RegionU is impossible

- RegionD high-q is impossible

- q0=2 nonlinear-first is impossible

- remaining D state is exactly linear-first

- 715-term certificate used only after linear-first

- first-point data do not appear in EuclideanSeed

- q0=2 does not appear in EuclideanSeed

- ROOT does not appear in EuclideanSeed

- PF rows do not appear in EuclideanSeed

- both DP and PP are genuine nonnegative packet equalities

- matrix determinant is exactly one

- matrix entries are positive

- L>M

- abstract packet determinant is positive

- RHO identities exact
```

---

# 57. CERTIFICATE CI VERIFICATION

C9 CI must additionally:

1. hash the frozen supplement ZIP;
2. hash both 715-term table copies;
3. verify they are byte-identical;
4. hash `verify_D_linear.py`;
5. run the original frozen verifier;
6. compare its result with expected output;
7. verify:

   * `status=PASS`
   * `identity_count=28`
   * monomial_count=715
   * constant=35
   * table SHA exact;
8. regenerate the committed Lean certificate data;
9. diff regenerated Lean against committed source;
10. compile the Lean certificate theorem fresh.

Again:

```text
original Python verifier PASS
```

is supporting evidence only.

The Lean theorem is authoritative for formalization.

---

# 58. NO C10 YET

Do not formalize:

```text
terminal source fit
Euclidean transformation
new packet after failure
color-exchange descent step
measure E+chi descent
strong induction
ChainInput.impossible
```

These belong to C10.

C9 stops when `EuclideanSeed` exists.

---

# 59. SUGGESTED MODULE LAYOUT

Use only NEW C9 mathematical modules.

For example:

```text
P21/Nonsymmetric/Chain/C9/
  RegionUSetup.lean
  RegionUCapacity.lean
  RegionUExclusion.lean

  DSetup.lean
  DFirstCaps.lean
  MultiplicityMaster.lean
  HighQ.lean
  NonlinearFirst.lean
  LinearFirst.lean
  PacketDeterminant.lean

  LinearCertificateData.lean
  LinearCertificate.lean
  LinearIFit.lean

  JShortage.lean
  ComplementaryPacket.lean
  EuclideanSeed.lean
  Handoff.lean
```

and:

```text
P21/Nonsymmetric/Chain/C9.lean
```

as top-level import.

Exact split may differ.

Do not append C9 mathematics to C8 files.

---

# 60. FROZEN SOURCE POLICY

Every mathematical Lean file existing at:

```text
7769545a357c0c4d24520ec7a9fc8994f3f664e7
```

is protected.

Expected mathematical modifications:

```text
NEW C9 modules only
```

Allowed non-math modifications:

```text
C8 documentation repair
NEXT_RESTART
new C9 verification/CI/docs
```

If any protected mathematical source must change:

```text
SOURCE CHANGE REQUIRED
FROZEN RE-AUDIT REQUIRED
```

Stop.

---

# 61. PROOF-DEBT / AXIOM POLICY

Forbidden:

```text
sorry
admit
axiom
sorryAx
unsafe escape
opaque project theorem
native_decide proof substitute
run_tac proof generation
external verifier result asserted as theorem
```

Required:

```text
proof debt = 0
project-specific axioms = 0
```

Expected inherited foundations only:

```text
propext
Classical.choice
Quot.sound
```

---

# 62. DEPENDENCY FIREWALL

Required direction:

```text
FROZEN C8
   ↓
Region U elimination
   ↓
Region D
   ↓
high-q closure
   ↓
q0=2
   ↓
nonlinear-first closure
   ↓
linear-first
   ↓
DSCR
   ↓
715-term I-FIT
   ↓
j-shortage
   ↓
two genuine packets
   ↓
det=1 matrix
   ↓
EuclideanSeed
```

Forbidden reverse dependencies:

```text
C10
CHAIN closure
main theorem
```

---

# 63. VERIFICATION

Run fresh:

```bash
lake build
```

Explicitly build all C9 modules.

Rerun:

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
```

Add:

```text
verification/c9/
```

containing:

```text
declaration inventory
statement inspection
axiom inspection
proof-debt scan
dependency DAG
circularity scan
frozen-source integrity
new-module list

certificate hash report
certificate generation reproducibility
original LINEAR verifier output

fresh root build
C9 build
all frozen regression logs
```

---

# 64. C9 DOCUMENTATION

Create:

```text
README_C9.md
SOURCE_OF_TRUTH_C9.md
C9_STATEMENT_MAP.md
C9_PROOF_ROUTE.md
C9_DEPENDENCY_DAG.md
```

Also create the previously missing C8 documentation:

```text
README_C8.md
SOURCE_OF_TRUTH_C8.md
C8_STATEMENT_MAP.md
C8_PROOF_ROUTE.md
C8_DEPENDENCY_DAG.md
```

as documentation-only reconstruction from already FROZEN C8 source.

Update:

```text
NEXT_RESTART.md
```

to Post-C9 on success.

---

# 65. GITHUB CI

Create:

```text
.github/workflows/c9-audit.yml
```

or equivalent.

CI must record:

```text
branch
exact HEAD SHA
run ID
attempt

Lean
Lake
mathlib revision

candidate ZIP SHA

frozen-source integrity
fresh root build
explicit C9 build

M1–C8 regressions

C9 statement gates
C9 axiom/debt gates
dependency/circularity

715 certificate exact hashes
715 generator reproducibility
original LINEAR verifier
Lean certificate compile

evidence manifest verification
```

---

# 66. EVIDENCE MANIFEST

Generate:

```text
EVIDENCE_SHA256.json
```

before upload.

Hash every evidence file except itself.

Verify it in CI.

---

# 67. CANDIDATE PACKAGE

On full success create exactly one principal candidate:

```text
P21_LEAN_C9_CHAIN_TWO_PACKET_CANDIDATE_20260919.zip
```

Include:

```text
complete Lean project
all new C9 modules
generated certificate Lean source

C8 repaired docs
C9 docs

NEXT_RESTART.md

verification/c9/
CI workflow

candidate SHA manifest
```

Compute SHA-256.

---

# 68. TRUE AUDIT ARTIFACT

Upload exactly:

```text
P21_C9_TRUE_AUDIT_EVIDENCE
```

including:

```text
RUN_CONTEXT
COMMIT_SHA
ENVIRONMENT

ROOT_BUILD_LOG
C9_MODULE_LIST
C9_BUILD_LOG
C9_VERIFICATION_LOG

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

PROOF_DEBT_REPORT
AXIOM_REPORT
AXIOM_SUMMARY
STATEMENT_INSPECTION
DEPENDENCY_DAG_CHECK
CIRCULARITY_CHECK
FROZEN_SOURCE_INTEGRITY
VERIFIED_SOURCE_SHA256

LINEAR_SUPPLEMENT_HASHES
LINEAR_ORIGINAL_VERIFIER_LOG
LINEAR_CERTIFICATE_GENERATION_CHECK
LINEAR_CERTIFICATE_LEAN_BUILD

candidate ZIP SHA
EVIDENCE_SHA256.json
```

Report artifact ID and GitHub digest.

---

# 69. SUCCESS GATE

You may report only:

```text
C9 CHAIN TWO-PACKET CANDIDATE FOR TRUE AUDIT
```

if all hold:

```text
[ ] RegionU eliminated completely

[ ] D first last-crossing h-step
[ ] D sharp FIRST-CAPS
[ ] NV/ZV
[ ] M-MASTER

[ ] high-q q0≥3 eliminated

[ ] q0=2 nonlinear-first eliminated
[ ] remaining q0=2,N=z+1 exactly

[ ] linear-first parameterization exact
[ ] D-LINEAR genuine
[ ] INTRINSIC-LINEAR genuine

[ ] DSCR > 0

[ ] f,w,theta exact
[ ] REMAINDER-SLOPE

[ ] frozen 715 table SHA exact
[ ] 715 terms exact
[ ] constant 35 exact
[ ] generated Lean data reproducible
[ ] Lean-kernel certificate identity proved
[ ] threshold positivity proved

[ ] I-FIT-D proved

[ ] repeated D-packet replacement actual
[ ] theta≥upsilon+1 eliminated

[ ] 1≤theta≤upsilon
[ ] Delta1≥1
[ ] zero-j actual upper representation

[ ] COMPLEMENTARY packet genuine

[ ] matrix entries positive
[ ] matrix determinant = 1
[ ] L>M

[ ] source A/B formulas exact
[ ] abstract Dp>0
[ ] RHO identities exact

[ ] EuclideanSeed contains no first-point baggage
[ ] c9_handoff proved

[ ] no C10 theorem imported

[ ] proof debt 0
[ ] project-specific axioms 0
[ ] frozen mathematical source unchanged

[ ] fresh build PASS
[ ] explicit C9 build PASS
[ ] M1–C8 regressions PASS
[ ] certificate checks PASS
[ ] C9 verification PASS
[ ] clean GitHub CI PASS

[ ] candidate SHA recorded
[ ] artifact digest recorded
[ ] evidence manifest verified
```

---

# 70. PARTIAL / NO-GO

If full C9 does not reach `EuclideanSeed`, do not fake success.

Return:

```text
C9 PARTIAL — SECTION 9 OPEN
```

or:

```text
C9 NO-GO / INTERFACE OBSTRUCTION
```

Identify the first exact unproved theorem:

```text
Lean statement
publication subsection
proved dependencies
remaining gap
math vs API vs certificate integration
```

If the static certificate integration is the obstruction, report separately:

```text
certificate table parsed?
715-term source generated?
kernel identity compile status?
positivity theorem status?
```

Do not replace it with Python PASS.

---

# 71. STATUS LANGUAGE

Codex must not self-award:

```text
TRUE AUDIT PASS
FROZEN
CHAIN CLOSED
```

Strongest permitted success:

```text
C9 CHAIN TWO-PACKET CANDIDATE FOR TRUE AUDIT
```

On C9 success:

```text
CHAIN overall status:
OPEN — EuclideanSeed ready
```

Exact next frontier:

```text
C10 — SECTION 10
EUCLIDEAN DESCENT / SOURCE CONTAINMENT / CHAIN CLOSURE
```

---

# 72. FINAL REPORT

Report in Japanese.

Begin with exactly one of:

```text
C9 CHAIN TWO-PACKET CANDIDATE FOR TRUE AUDIT
```

```text
C9 PARTIAL — SECTION 9 OPEN
```

```text
C9 NO-GO / INTERFACE OBSTRUCTION
```

Then report:

```text
Repository:
Branch:
Frozen base:
Candidate commit:

C8 source unchanged:

RegionU I/J fit:
RegionU packet:
RegionU exclusion:

D sharp FIRST-CAPS:
M-MASTER:
HIGH-Q:
NONLINEAR-FIRST:
linear-first:

D-LINEAR:
INTRINSIC-LINEAR:
DSCR:

715 table:
table SHA:
term count:
constant:
generator reproducibility:
Lean certificate:
I-FIT-D:

J-ONLY:
theta range:
Delta1:
zero-j upper:

COMPLEMENTARY:

matrix:
det:
L>M:
A/B sources:
packet determinant:
RHO identities:

EuclideanSeed:
first-point data absent:
c9_handoff:

CHAIN overall status:
Next frontier:

New Lean modules:
Audited declarations:

Proof debt:
Project-specific axioms:
FROZEN source integrity:
Forbidden reverse dependencies:

Root build:
Explicit C9 build:

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
C9 verification:

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

On success:

```text
SOURCE_CHANGED: NO

CHAIN overall status:
OPEN — C9 complete, C10 Euclidean descent only
```

Execute C9 completely now.
