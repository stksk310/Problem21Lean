# P21 LEAN — C8 / CHAIN BOUNDARY ELIMINATION & PACKET WINDOW

## SECTION 8 COMPLETE FORMALIZATION

## FIRST FIT / SAME-ELEMENT PACKET / DET1 TRIANGLE / BOUNDARY C=α / STRICT WINDOW / U∨D HANDOFF

This is the second formalization milestone for the final CHAIN branch of `Problem21Lean`.

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

C7    CHAIN CORE-ROOT / SECTION 7      FROZEN
```

CHAIN overall remains:

```text
OPEN
```

The remaining CHAIN program is:

```text
C8   Section 8  — boundary elimination / packet window
C9   Section 9  — residual reduction / packet relations
C10  Section 10 — Euclidean descent / CHAIN closure
FINAL             Section 11 main theorem assembly
```

This mission is **C8 only**.

Do not begin Section 9.

---

# 0. REPOSITORY / IMMUTABLE BASE

Repository:

```text
https://github.com/stksk310/Problem21Lean
```

The immutable independently audited C7 base is:

```text
80b36191937b2e2f0dc251ac6006d63f088e03b2
```

Create a new branch from exactly this commit, preferably:

```text
c8-chain-boundary-window
```

Do not merge to `main`.

---

# 1. DOCUMENTATION-ONLY C7 EDITORIAL REPAIR

Independent C7 audit found one documentation-only stale naming issue in:

```text
C7_STATEMENT_MAP.md
```

It references conceptual/old names such as:

```text
slope_j
slope_k
two_candidate
```

while the actual C7 API uses declarations including:

```text
ChainCore.slopes
ChainCore.successful_ge_q0
ChainCore.second_coordinates
ChainCore.second_deficient
```

Correct this documentation only.

Do not modify any C7 mathematical Lean source.

---

# 2. FROZEN C7 API — AUTHORITATIVE ENTRYPOINT

Do not reconstruct Section 7.

Use the FROZEN declarations already available.

Important existing interfaces include:

```lean
ChainCore
ChainInput.to_oriented_core

ChainCore.Returns
ChainCore.returns
Returns.levels_pos

ChainCore.Caps
ChainCore.caps

ChainCore.Slopes
ChainCore.slopes

ChainCore.euclidean

ChainCore.completed_F
ChainCore.Successful
ChainCore.successful_ge_q0
ChainCore.rho_gap_nonneg

ChainCore.second_coordinates
ChainCore.second_deficient

ChainCore.orientIntrinsic

ChainCore.compact_data
ChainCore.compact_actual
ChainCore.compact_contains_cJ
ChainCore.compact_return_actual

ChainCore.I_levels
ChainCore.Lj_level
ChainCore.Lj_rigidity
ChainCore.Lk_strict_level
ChainCore.sum_notch

ChainCore.shift_new
ChainCore.shift_new_coefficients
ChainCore.Uj_tau_cap
ChainCore.Vj_tau_cap
ChainCore.tau_caps
ChainCore.FK_strong
```

Also use the exact FROZEN scalar/row helpers from C7:

```text
qA,qB,qJ,qK
P,R,T
delta,beta,gapJ,alpha
```

and all exact row/complement/W equations.

Do not re-prove MAX-I, ROOT, color reversal, COMPACT, or SHIFT-NEW.

---

# 3. SOURCE OF TRUTH

Use this hierarchy:

```text
1. reference_inputs/
   P21_Journal_of_Algebra_Submission_Manuscript_FINAL_20260916.pdf
   Section 8

2. reference_inputs/
   P21_MANUSCRIPT_EN_FINAL_20260908_v1.zip
   Section 8

3. reference_inputs/
   P21_FINAL_FROZEN_VERIFICATION_EDITION_20260907.zip
   corresponding maintained CHAIN boundary proof

4. FROZEN C7 Lean source/API
```

Publication Section 8 controls theorem scope and branch exhaustion.

Formalize completely:

```text
§8.1  input
§8.2  first ROOT/R_j fitting point
§8.3  SAME-element PACKET / walls
§8.4  kernel coefficients = 1
§8.5  empty integer triangle / DET1 / level split
§8.6  k-ceiling
§8.7  boundary synchronization
§8.8  C=alpha multiplicity contradiction
§8.9  strict packet-window theorem
§8.10 deep strict region
§8.11 level-one unit boundary
§8.12 U∨D handoff
§8.13 complete branch table
```

---

# 4. ABSOLUTE FIREWALLS

Maintain all existing project rules.

## 4.1 Actual vs signed

`HRJ`, `C-FK`, kernel relations, cross-product identities, and completed zero rows are signed identities unless actual nonnegative coefficients are separately proved.

Do not convert them silently into Γ-membership.

## 4.2 Same-element packet provenance

The central PACKET must be derived by lifting two **actual upper elements to the same named element**, then removing the same common coefficient vector.

Do not compare unrelated representations.

## 4.3 Criticality

Herzog criticality only after the m-coordinate has been completely eliminated.

## 4.4 No finite numerical scan

The three exceptional strict-window cases are an exact symbolic finite classification derived from inequalities.

Do not introduce arbitrary cutoffs or brute-force scans.

## 4.5 Boundary/strict scope separation

Any theorem requiring:

```text
Croot > alpha
```

must not be applied at:

```text
Croot = alpha
```

In particular, do not import strict C7 `FK_strong` into the boundary.

---

# 5. C8.0 — WORKING DATA

Work with an oriented frozen CORE:

```lean
K : ChainCore s F D
```

together with one genuine return package:

```lean
E : K.Returns
```

and its frozen caps/slopes:

```lean
HC : K.Caps E
HS : K.Slopes
```

Use publication-local notation:

```text
L := E.Li
M := E.Lj

Q := E.Uj + 1
a := E.Aj + 1

C := K.Croot
g := K.chain.gapJ
alpha := K.chain.alpha

P := K.chain.P
R := K.chain.R
T := K.chain.T
```

Do not shadow the Lean `ChainInput` object ambiguously; use `Croot` in Lean if needed.

---

# 6. C8.2 — R_k FACE OF W

Prove the genuine alternative W-face:

```text
W =
  (delta-1)n_i
+ (g-1)n_j
+ (rho_k+T-1)n_k
```

using exactly one completed HCR transformation from the FROZEN `W_exact`.

All three coefficients must be nonnegative.

This is an actual W representation.

---

# 7. C8.2 — HRJ FAMILY

From CORE-ROOT and `R_j`, derive for arbitrary integers `zeta,n`:

```text
F =
  (n-1)m
+ (delta-1+n*d-zeta*a_i)n_i
+ (g-1+zeta*rho_j-n*S)n_j
+ (rho_k+T-1-n*C-zeta*b_k)n_k
```

Call this:

```text
HRJ
```

This is a completed signed family.

Do not claim every HRJ row is actual.

---

# 8. C8.2 — FIRST FITTING POINT

For every integer:

```text
zeta ≥ 1
```

define:

```text
n_zeta :=
  ceil((zeta*a_i-delta+1)/d)

I_zeta :=
  delta-1+n_zeta*d-zeta*a_i

J_zeta :=
  g-1+zeta*rho_j-n_zeta*S
```

Use exact integer ceiling arithmetic.

Prefer an explicit integer definition based on `Int.ediv` / proved ceil helper rather than floating arithmetic.

Prove:

```text
0 ≤ I_zeta ≤ d-1
```

and:

```text
n_zeta
```

is strictly increasing in `zeta`, using:

```text
a_i > d
```

from C7.

Also prove:

```text
n_1 = ceil((lambda+1)/d) ≥ 2
```

where the final lower bound follows from the appropriate C7 strict setup.

---

# 9. C8.2 — EXISTENCE OF FIRST zeta

Let:

```text
V := d*rho_j - S*a_i
```

so by frozen C7 slopes:

```text
V > 0
```

Prove the exact identity:

```text
J_d =
  V
+ S * floor((delta-1)/d)
+ g - 1
```

and hence:

```text
J_d > 0
```

Therefore the set:

```text
{zeta ∈ ℤ | 1 ≤ zeta ∧ J_zeta ≥ 0}
```

is nonempty.

Use a genuine minimum/well-ordering construction to define:

```text
zhat :=
  min { zeta ≥ 1 | J_zeta ≥ 0 }
```

and prove:

```text
1 ≤ zhat ≤ d
```

Define:

```text
N := n_zhat
I := I_zhat
J := J_zhat
```

---

# 10. C8.2 — FIRST-CAPS

Prove:

```text
N ≥ 2
0 ≤ I ≤ d-1
0 ≤ J
```

If:

```text
zhat > 1
```

use:

```text
J_(zhat-1) < 0
```

and strict increase of `n_zeta` to prove the sharper:

```text
J ≤ rho_j-S-1
```

For uniform use including `zhat=1`, prove:

```text
J ≤ rho_j-S+g-1
```

Thus expose:

```text
FIRST-CAPS
```

as a reusable structure/theorem.

---

# 11. C8.2 — Xi AND ZERO-k UPPER FACE

Define:

```text
Xi :=
  N*C
+ zhat*b_k
- (rho_k+T-1)
```

Substitute the first-fit point into HRJ.

If:

```text
Xi ≤ 0
```

then every HRJ coefficient is nonnegative.

Construct an actual factorization of `F`.

Contradiction.

Therefore every surviving CHAIN satisfies:

```text
Xi ≥ 1
```

and the exact actual upper-element identity:

```text
OmegaHat := F + Xi*n_k
```

with:

```text
OmegaHat =
  (N-1)m
+ I*n_i
+ J*n_j
```

This must be represented as a genuine actual factorization with zero k-coordinate.

---

# 12. C8.3.1 — CENTRAL FK SIGNED ROW

Re-derive exactly:

```text
F+n_k =
  (d+beta-1)n_i
+ (R+rho_j-S-1)n_j
+ (alpha-C)n_k
```

Call this:

```text
C-FK
```

When:

```text
C > alpha
```

the last coefficient is negative, so **C-FK itself is not actual**.

Do not call it an actual factorization.

Instead prove the genuine zero-k upper element:

```text
F + (C-alpha+1)n_k
 =
(d+beta-1)n_i
+
(R+rho_j-S-1)n_j
```

with nonnegative coefficients.

---

# 13. C8.3.1 — SAME-ELEMENT PACKET

Define:

```text
DF := d+beta-1-I
EF := R+rho_j-S-1-J

chi := C-alpha+1-Xi
```

Using FIRST-CAPS prove:

```text
DF ≥ beta > 0
EF ≥ a_j > 0
```

Now lift:

```text
OmegaHat
```

and the genuine CENTRAL FK upper element to the same named element by adding only copies of `n_k`.

Then remove the common contained coefficient vector:

```text
I*n_i + J*n_j
```

coefficientwise from those exact actual representations.

Derive the genuine PACKET identity:

```text
(N-1)m + max(chi,0)n_k
 =
DF*n_i
+
EF*n_j
+
max(-chi,0)n_k
```

with both sides coefficientwise nonnegative.

This must be formalized as a same-element replacement relation, not merely a ring identity.

---

# 14. C8.3.2 — BOUNDARY WALL C=alpha

Assume:

```text
C = alpha
```

Then:

```text
chi = 1-Xi ≤ 0
```

and PACKET becomes:

```text
(N-1)m
 =
DF*n_i
+
EF*n_j
+
(Xi-1)n_k
```

All target coefficients are nonnegative and:

```text
DF,EF > 0
```

Use this exact packet inside the SAME actual return representations.

If:

```text
N-1 ≤ E.Li
```

insert the packet in EA and derive an actual factorization of `qA`.

Contradiction.

Do the same for EB if:

```text
N-1 ≤ E.Lb
```

and for Qj if:

```text
N-1 ≤ E.Lj
```

producing an actual forbidden positive missing-direction representation.

Conclude:

```text
C=alpha
→
N ≥ max(Li,Lb,Lj)+2
```

Call this:

```text
BOUNDARY-WALL
```

---

# 15. C8.3.3 — GENERAL WINDOW WALL

Assume:

```text
chi ≤ T
```

If:

```text
N ≤ Li
```

apply PACKET inside the SAME frozen FI-A representation.

After removing one copy of `n_i`, derive:

```text
F =
  (Li-N)m
+ (DF-1)n_i
+ (Uj+g+EF)n_j
+ (Uk+T-chi)n_k
```

and prove all coefficients nonnegative.

Carefully handle:

```text
chi > 0
```

where `chi` copies of `n_k` are consumed from the canonical `T` supply, and:

```text
chi ≤ 0
```

where the packet produces k-copies.

Similarly, if:

```text
N ≤ Lj
```

inside the SAME FJ representation obtain:

```text
F =
  (Lj-N)m
+ (Aj+delta+DF)n_i
+ (EF-1)n_j
+ (Cj+T-chi)n_k
```

with all coefficients nonnegative.

Conclude:

```text
chi ≤ T
→
N ≥ max(Li,Lj)+1
```

Call this:

```text
WINDOW-WALL
```

Important:

Do **not** apply this T-window unconditionally to EB.

FI-B has canonical k-supply `alpha`, not `T`.

---

# 16. C8.4 — PURE-H KERNEL BASIS

Under WINDOW-WALL, compare actual EA with its canonical expression after eliminating m completely using ROOT.

Obtain integers `x,y` such that:

```text
(
  P+L*d,
  a_j-1-L*S-Uj,
  -L*C-Uk-1
)
=
x*r_j + y*r_k
```

where:

```text
L := Li
```

and:

```text
r_j=(a_i,-rho_j,b_k)
r_k=(b_i,a_j,-rho_k)
```

Use the existing FROZEN pure-H kernel basis theorem from §4.3.

Do not add a new kernel axiom.

By sign analysis prove:

```text
x ≥ 1
y ≥ 1
```

---

# 17. C8.4.2 — EA SECOND KERNEL COEFFICIENT = 1

From the kernel coordinates derive:

```text
L*d =
  x*a_i
+ (y-1)b_i
- delta
```

and:

```text
L*S =
  x*rho_j
- (y-1)a_j
- Q
```

where:

```text
Q := Uj+1 ≥ 1
```

Assume:

```text
y ≥ 2
```

At the HRJ point:

```text
(zeta,n)=(x,L)
```

derive:

```text
I = (y-1)b_i-1 ≥ 0
```

and:

```text
J =
  Q+g-1+(y-1)a_j
≥ 0
```

For fixed `zeta=x`, minimizing n only increases J, so:

```text
n_x ≤ L
```

and hence the first fit satisfies:

```text
N ≤ L
```

contradicting WINDOW-WALL.

Therefore:

```text
y = 1
```

and obtain exact:

```text
EA-ONE:

L*d = x*a_i-delta
L*S = x*rho_j-Q

epsilon :=
  rho_k-Uk-1
 =
L*C+x*b_k
```

---

# 18. C8.4.3 — SAME Qj SECOND KERNEL COEFFICIENT = 1

Similarly eliminate m completely in Qj:

```text
(
  M*d+b_i-1-Aj,
  R-M*S,
  -M*C-Cj-1
)
=
z*r_j + v*r_k
```

with:

```text
M := Lj
a := Aj+1
```

Prove:

```text
z ≥ 1
v ≥ 1
```

If:

```text
v ≥ 2
```

show at `(z,M)`:

```text
I = Aj+delta+(v-1)b_i ≥ 0
J = (v-1)a_j-1 ≥ 0
```

hence:

```text
N ≤ M
```

contradicting WINDOW-WALL.

Therefore:

```text
v=1
```

and obtain:

```text
QJ-ONE:

M*d = z*a_i + a
M*S = z*rho_j + g

rho_k =
  M*C
+ Cj
+ 1
+ z*b_k
```

---

# 19. C8.5 — EMPTY INTEGER TRIANGLE

Define the integer triangle with vertices:

```text
O  = (0,0)
U  = (x,L)
V0 = (z,M)
```

The affine functions `(I,J)` take:

```text
O:
I = delta-1
J = g-1

U:
I = -1
J = Q+g-1

V0:
I = Aj+delta
J = -1
```

At every nonvertex integer point of the triangle, prove:

```text
I,J > -1
```

hence, since integral:

```text
I,J ≥ 0
```

and:

```text
0 < n ≤ max(L,M)
```

Such a point would yield a first fit with:

```text
N ≤ max(L,M)
```

contradicting WINDOW-WALL.

---

# 20. C8.5 — DET1

Prove algebraically:

```text
(x*M-z*L)*d = x*a + z*delta > 0
```

hence:

```text
x*M-z*L ≥ 1
```

Now formalize the 2D lattice argument:

If:

```text
x*M-z*L ≥ 2
```

the fundamental parallelogram generated by `U,V0` contains a nonzero integer lattice point modulo the generated sublattice.

Show that either that point or its reflection across:

```text
U+V0
```

gives a nonvertex integer point of the closed triangle, contradicting the previous theorem.

Do not use this geometry as an external axiom.

Formalize the elementary determinant/index argument internally.

Conclude:

```text
DET1:
x*M-z*L = 1
```

This is a load-bearing C8 gate.

If this exact lattice lemma cannot be proved with the frozen API, report the first obstruction; do not assume DET1.

---

# 21. C8.5 — PARAM IDENTITIES

Using DET1 and EA/Qj equations prove:

```text
d   = x*a + z*delta
S   = x*g + z*Q

a_i   = L*a + M*delta
rho_j = L*g + M*Q

b_i =
  L*a
+ (M-1)delta
+ beta
```

Define:

```text
V := a*Q-delta*g
```

and prove:

```text
V > 0
```

This `V` equals the slope numerator after parameter substitution.

---

# 22. C8.5 — LEVEL-SPLIT

From:

```text
a_i > d
DET1
x,z,L,M ≥ 1
```

prove exactly:

```text
(
  L ≥ x+1
  ∧ x+1 ≥ 2
  ∧ M > z
  ∧ z ≥ 1
)
∨
(
  L=1
  ∧ x=1
  ∧ M=z+1
)
```

No third case.

The second alternative is the level-one exception later called:

```text
U
```

Do not eliminate it yet except on the boundary.

---

# 23. C8.6 — EXACT k-CEILING

From EA-ONE define:

```text
epsilon :=
  L*C + x*b_k
```

with exact actual packet relation:

```text
delta*n_i
+
epsilon*n_k
 =
L*m
+
Q*n_j
```

If:

```text
epsilon ≤ Cj+T
```

show this left packet is coefficientwise contained in the SAME FJ actual representation.

Perform the replacement and obtain a forbidden positive j-coefficient / actual F-factorization.

Therefore:

```text
epsilon ≥ Cj+T+1
```

Define:

```text
H0 :=
  L*C
+ (x-1)b_k
- alpha
- Cj
- 1
```

and prove:

```text
H0 ≥ 0
```

Using QJ-ONE derive the exact general formula:

```text
K-CEILING:

rho_k =
  (M+L)C
+ (z+x-1)b_k
- alpha
- H0
```

Important firewall:

Only when:

```text
C=alpha
```

may this become:

```text
rho_k =
  (M+L-1)alpha
+ (z+x-1)b_k
- H0
```

Do not replace `L*C-alpha` by `(L-1)C` in the strict case.

---

# 24. C8.7 — BOUNDARY EB SYNCHRONIZATION

Now assume:

```text
C=alpha
```

Use BOUNDARY-WALL.

Eliminate m in EB:

```text
(
  P+Lb*d,
  -1-Lb*S-Vj,
  b_k-1-Lb*C-Vk
)
=
xb*r_j + yb*r_k
```

Prove:

```text
xb,yb ≥ 1
```

If:

```text
yb ≥ 2
```

show the point `(xb,Lb)` has both first-fit coordinates nonnegative, hence:

```text
N ≤ Lb
```

contradicting BOUNDARY-WALL.

Thus:

```text
yb=1
```

and:

```text
Lb*d =
  xb*a_i-delta
```

```text
Lb*S =
  xb*rho_j-(Vj+a_j+1)
```

Apply the same DET1 triangle argument to EB and SAME Qj:

```text
xb*M-z*Lb = 1
```

Compare with EA DET1 and the i-equations.

Derive:

```text
a*(xb-x)=0
```

and since:

```text
a≥1
```

conclude:

```text
SYNC:

Lb = Li = L
xb = x

Uj = Vj+a_j
Vk = Uk+b_k
```

Therefore:

```text
Q=Uj+1 ≥ a_j+1 ≥ 2
```

---

# 25. C8.7 — BOUNDARY LEVEL-ONE EXCEPTION IMPOSSIBLE

Still under:

```text
C=alpha
```

assume the level-one alternative:

```text
L=x=1
M=z+1
```

Use the boundary formula for H0:

```text
H0 =
  (L-1)alpha
+ (x-1)b_k
- Cj
-1
```

to obtain:

```text
H0 = -Cj-1 < 0
```

contradicting:

```text
H0 ≥ 0
```

Therefore boundary necessarily lies in the regular level range:

```text
L ≥ x+1 ≥ 2
M > z ≥ 1
```

---

# 26. C8.8 — CROSS-PRODUCT SCALE

Define:

```text
Ical :=
  rho_j*rho_k-a_j*b_k

Jcal :=
  a_i*rho_k+b_i*b_k

Kcal :=
  b_i*rho_j+a_i*a_j
```

Use the existing FROZEN Herzog/primitive-generator package to prove existence of a positive common scale:

```text
sigma > 0
```

such that:

```text
n_i = sigma*Ical
n_j = sigma*Jcal
n_k = sigma*Kcal
```

Do not assume:

```text
sigma=1
```

Then from ROOT define:

```text
mhat :=
  -d*Ical
  + S*Jcal
  + C*Kcal
```

and prove:

```text
m = sigma*mhat
```

This is the exact scale-aware publication interface.

---

# 27. C8.8 — BOUNDARY MULTIPLICITY IDENTITY

Define:

```text
Dj :=
  d*a_j+S*b_i

P0 :=
  V+a_i
```

prove:

```text
P0>0
```

and define:

```text
CA :=
  Kcal-(M+L-1)*P0

CB :=
  Dj-b_i-(z+x-1)*P0
```

On boundary `C=alpha`, prove exactly:

```text
BOUND-MULT:

mhat-Jcal =
  H0*P0
+ alpha*CA
+ b_k*CB
```

---

# 28. C8.8 — POS-COEFF

Prove the exact coefficient decompositions:

```text
CA =
  a*Aa
+ delta*Adelta
+ beta*rho_j
```

```text
CB =
  a*Ba
+ delta*Bdelta
+ beta*(S-1)
```

where:

```text
Aa =
  (L-1)(M-1)(Q-2)
+ L^2(g-1)
+ L(a_j-1)
+ (L-2)M
+ 2
```

```text
Adelta =
  M(M-1)(Q-2)
+ (LM+M-1)(g-1)
+ M(a_j-1)
+ M^2+M-1
```

```text
Ba =
  [z(L-1)-x+1](Q-2)
+ Lx(g-1)
+ x(a_j-1)
+ z(L-x-1)
+ (z-1)(x-1)
+ 1
```

```text
Bdelta =
  (xM+z-1)(g-1)
+ z(M-1)(Q-2)
+ z(a_j-1)
+ zM
```

Under boundary facts:

```text
Q≥2
g≥1
a_j≥1
L≥x+1
M>z≥1
```

prove every displayed summand nonnegative and:

```text
Aa,Adelta,Ba,Bdelta > 0
```

In particular explicitly prove:

```text
z(L-1)-x+1
 =
x(z-1)+1+z(L-x-1)
≥1
```

Therefore:

```text
CA>0
CB>0
```

---

# 29. C8.8 — BOUNDARY CLOSED

From BOUND-MULT and:

```text
H0≥0
P0>0
alpha,b_k≥1
CA,CB>0
```

derive:

```text
mhat > Jcal
```

Since:

```text
sigma>0
m=sigma*mhat
n_j=sigma*Jcal
```

conclude:

```text
m>n_j
```

contradicting multiplicity.

Therefore prove the scoped theorem:

```text
Croot = alpha → False
```

or equivalent:

```text
Croot ≠ alpha
```

combined with `C_lower`, conclude for every surviving C8 input:

```text
Croot > alpha
```

This must cover all:

```text
Delta0=1
Delta0≥2
```

and all return-level possibilities.

Formal status after this theorem:

```text
BOUNDARY C=alpha CLOSED
```

but CHAIN remains OPEN.

---

# 30. C8.9 — STRICT WINDOW CLAIM

Now assume:

```text
C > alpha
chi ≤ T
Li ≥ 2
```

Prove contradiction.

By WINDOW-WALL and previous C8 results, EA/Qj kernel, DET1, PARAM and K-CEILING apply.

Since:

```text
L=Li≥2
```

the level-one exception is impossible.

Hence:

```text
L≥x+1
M>z
```

Do not use boundary SYNC.

Only:

```text
Q≥1
```

is available here.

Define:

```text
gamma := C-alpha ≥1
```

From general K-CEILING prove:

```text
STRICT-J:

mhat-Jcal =
  H0*P0
+ alpha*CA
+ gamma*(CA-P0)
+ b_k*CB
```

---

# 31. C8.9.2 — REGULAR Q≥2

For:

```text
Q≥2
```

reuse:

```text
CA>0
CB>0
```

from the regular positivity formulas.

Expand:

```text
CA-P0
```

with coefficient of `a`:

```text
Ea =
  [(L-1)(M-1)-1](Q-2)
+ L^2(g-1)
+ L(a_j-1)
+ (L-2)M
- L
```

coefficient of `delta`:

```text
Edelta =
  M(M-1)(Q-2)
+ (LM+M)(g-1)
+ M(a_j-1)
+ M^2
```

and beta coefficient:

```text
rho_j
```

Prove:

```text
Edelta>0
rho_j>0
```

Classify symbolically all cases where `Ea<0`.

The classification must be **exactly** the following three families:

```text
EX1:
L=2
x=1
M=2z+1
Q=2
g=1
a_j=1
z≥1

EX2:
L=2
x=1
z=1
M=3
Q=3
g=1
a_j=1

EX3:
L=3
x=2
z=1
M=2
Q=2
g=1
a_j=1
```

No arbitrary finite search.

Prove this by symbolic integer inequalities / exact case splitting.

Outside these cases:

```text
CA-P0>0
```

and STRICT-J yields:

```text
mhat>Jcal
```

hence:

```text
m>n_j
```

contradiction.

---

# 32. C8.9.3 — Q=1 AND THE THREE EXCEPTIONS

For the unresolved range define:

```text
Aprime :=
  Kcal-(M+L)*V
```

```text
Bprime :=
  Dj-(z+x-1)*V
```

Prove exact decompositions:

```text
Aprime =
a{
  L^2*g
  + [(L-1)M-L]Q
  + L*a_j
}
+
delta{
  (M-1)rho_j
  + M*a_j
  + (M+L)g
}
+
beta*rho_j
```

and:

```text
Bprime =
a{
  x*a_j
  + Lx*g
  + [z(L-1)-x+1]Q
}
+
delta{
  z*a_j
  + (M-1)S
  + (z+x-1)g
}
+
beta*S
```

Under:

```text
Q≥1
L≥x+1
M>z
```

prove:

```text
Aprime>0
Bprime>0
```

Define:

```text
Dbase :=
  2*Aprime+Bprime+V-Kcal
```

and prove:

```text
STRICT-K:

mhat-Kcal =
  H0*V
+ (alpha-1)(V+Aprime)
+ (gamma-1)Aprime
+ (b_k-1)Bprime
+ Dbase
```

Expand:

```text
Dbase =
a{
  (L+x)a_j
  + L(L+x)g
  + E*Q
}
+
delta{
  (M-1)rho_j
  + (M+z)a_j
  + (M-1)S
  + [2(M+L)+z+x-2]g
}
+
beta(rho_j+S)
```

where:

```text
E =
  (L-2)M
+ (L-1)z
- 2L
- x
+ 2
```

---

# 33. C8.9.3 — Q=1 POSITIVITY

For:

```text
Q=1
```

prove exactly:

```text
E-(L-x-3)
 =
(L-2)(M-2)
+
(L-1)(z-1)
≥0
```

Therefore the coefficient of `a` in Dbase is at least:

```text
(L+x)(L+1)-2
```

and is positive.

Prove all other coefficients positive.

Hence:

```text
Dbase>0
```

and STRICT-K gives:

```text
mhat>Kcal
```

thus:

```text
m>n_k
```

contradiction.

---

# 34. C8.9.3 — THE THREE EXCEPTIONAL CASES

In the three exact exceptions from §31, prove the coefficient of `a` in Dbase is respectively:

```text
EX1: 2z+3
EX2: 3
EX3: 16
```

all positive.

Prove all remaining coefficients nonnegative/positive as required.

Thus again:

```text
Dbase>0
mhat>Kcal
m>n_k
```

contradiction.

Conclude the exact scoped theorem:

```text
STRICT-WINDOW:

C>alpha
∧ chi≤T
∧ Li≥2
→ False
```

This is the main C8 strict theorem.

---

# 35. C8.10 — CLOSED STRICT INFINITE REGION

Every survivor has:

```text
Xi≥1
```

so:

```text
chi =
C-alpha+1-Xi
≤ C-alpha
```

If:

```text
C ≤ b_k+2alpha
```

then:

```text
chi ≤ b_k+alpha = T
```

If also:

```text
lambda>d
```

use frozen C7 I-level / Euclidean data to prove:

```text
Li≥2
```

Therefore close:

```text
lambda>d
∧ alpha<C
∧ C≤b_k+2alpha
→ False
```

---

# 36. C8.10 — DEEP SOURCE-SHORTAGE REGION

In any surviving strict case with:

```text
Li≥2
```

STRICT-WINDOW implies:

```text
chi≥T+1
```

Combine with:

```text
chi=C-alpha+1-Xi
```

to prove equivalently:

```text
1 ≤ Xi ≤ C-b_k-2alpha
```

and hence:

```text
C ≥ b_k+2alpha+1
```

Define the exact deep region:

```text
D-region:

T < chi ≤ C-alpha

1 ≤ Xi ≤ C-b_k-2alpha

C ≥ b_k+2alpha+1
```

This is the exact k-source shortage region passed to C9.

---

# 37. C8.11 — LEVEL-ONE SURVIVOR INSIDE WINDOW

Suppose a survivor has:

```text
chi≤T
```

STRICT-WINDOW forces:

```text
Li=1
```

Use frozen C7 I-level:

```text
lambda ≤ Li*d
```

and:

```text
d≤lambda
```

to prove:

```text
lambda=d
```

and therefore:

```text
q0=2
```

The LEVEL-SPLIT must then be the exceptional alternative:

```text
L=x=1
M=z+1
```

Define:

```text
eta := Cj+1
```

---

# 38. C8.11 — UNIT-PARAM

Derive exactly:

```text
d=lambda=a+z*delta
```

```text
S=g+z*Q
```

```text
a_i=d+delta
b_i=d+beta
```

```text
rho_j=g+(z+1)Q
```

```text
Lj=z+1
Aj=a-1
```

```text
rho_k =
  (z+1)C
+ eta
+ z*b_k
```

```text
Uj=Q-1
Uk=a_k-C-1
```

Call this exact package:

```text
UNIT-PARAM
```

From K-CEILING also prove:

```text
H0=C-alpha-eta≥0
```

---

# 39. C8.11.1 — EXACT FIRST POINT IN UNIT CASE

For:

```text
1≤zeta≤z+1
```

prove:

```text
n_zeta =
zeta
+
ceil(((zeta-1)delta+1)/d)
=
zeta+1
```

and:

```text
J_zeta =
(zeta-z)Q-1
```

Therefore the exact first point is:

```text
zhat=z+1
N=z+2
I=a-1
J=Q-1
```

and:

```text
Xi=C-alpha-eta+1
chi=eta
```

Thus:

```text
1≤eta≤min(C-alpha,T)
```

Call this:

```text
UNIT-ETA
```

---

# 40. C8.11.1 — COMPACT SPECIALIZATION

Using frozen C7 compact parameters prove in the unit region:

```text
Delta0=(z-1)Q+1
tau0=Q
```

Therefore:

```text
z=1 → Delta0=1
```

and:

```text
z≥2 → Delta0≥2
```

Do not eliminate either branch in C8.

They are both passed to C9 §9.1.

Also prove the important scope statement:

If a surviving unit configuration had **any other** actual EA return with level at least two, STRICT-WINDOW would close it.

Hence every missing-i EA factorization in a surviving unit configuration has level one.

This is a necessary condition, not a uniqueness assumption.

---

# 41. C8.11.2 — UNIT MULTIPLICITY TEST

Define:

```text
Du :=
  Q*eta
- R*(C+b_k)
```

and:

```text
Ma :=
  R*(C+b_k)-Q*eta
= -Du
```

Define:

```text
Mdelta :=
C[
  Q*z*(z+1)
  + a_j*(z+1)
  + g*(2z+1)
]
+
b_k[
  Q*z^2
  + a_j*z
  + 2g*z
]
+
eta*g
```

and:

```text
Mbeta :=
C[
  Q*(z+1)+g
]
+
b_k[
  Q*z+g
]
```

Prove:

```text
Mdelta>0
Mbeta>0
```

and exact:

```text
mhat =
  a*Ma
+ delta*Mdelta
+ beta*Mbeta
```

and:

```text
mhat-Ical =
  (a+z+1)*Ma
+ (delta-1)*Mdelta
+ (beta-1)*Mbeta
```

If:

```text
Du≤0
```

then:

```text
Ma≥0
```

and every term on the right is nonnegative.

Therefore:

```text
mhat≥Ical
```

so:

```text
m≥n_i
```

contradicting strict multiplicity.

Conclude:

```text
Du>0
```

Call this:

```text
UNIT-REMAIN
```

---

# 42. C8.11.2 — Q>R

From:

```text
Du>0
```

and:

```text
eta≤C-alpha<C+b_k
```

prove:

```text
Q>R
```

where:

```text
R=a_j+g
```

Thus all unit-window cases with:

```text
Q≤R
```

are eliminated.

In particular:

```text
Uj=Q-1≥a_j
```

---

# 43. C8.11.2 — LEVEL-ONE EB TRANSPORT

Use the same actual CHAIN configuration and the canonical difference between EA and EB.

From:

```text
Uj≥a_j
```

construct a genuine level-one EB representation:

```text
EB =
m
+
(Q-a_j-1)n_j
+
(Uk+b_k)n_k
```

with all coefficients nonnegative.

This is an actual representation of the same EB successor.

Do not claim uniqueness of arbitrary EB return levels.

---

# 44. C8.12 — DEFINE REGION U

Create an exact reusable structure for the surviving unit-window branch, conceptually:

```lean
structure RegionU ... where
  core : ChainCore ...
  returns : core.Returns
  ...
```

It must contain or make derivable at least:

```text
C>alpha

Li=1
lambda=d
q0=2

L=x=1
M=z+1

eta=Cj+1

UNIT-PARAM

1≤eta≤min(C-alpha,T)

Delta0=(z-1)Q+1
tau0=Q

Du>0
Q>R

actual level-one EB representation
```

and preserve:

```text
same Γ,F,m,W
same four actual CHAIN rows
same CORE
same COMPACT provenance
```

Do not add C9 conclusions.

---

# 45. C8.12 — DEFINE REGION D

Create an exact structure for the deep source-shortage branch containing at least:

```text
C>alpha

T<chi≤C-alpha

1≤Xi≤C-b_k-2alpha

C≥b_k+2alpha+1
```

plus the common frozen C7/C8 data:

```text
FIRST FIT
PACKET
EA/Qj ONE-relations
DET1
PARAM
K-CEILING
CORE / Returns / Caps / Slopes
```

and actual provenance needed by C9.

Call this conceptually:

```text
RegionD
```

Exact naming may differ.

---

# 46. C8.12 — EXHAUSTIVE HANDOFF

Prove that every oriented actual CHAIN CORE satisfying Frobenius gapness reaches exactly one of:

```text
RegionU
∨
RegionD
```

because:

```text
C=alpha
→ impossible

C>alpha, chi≤T
→ Li=1
→ RegionU

C>alpha, chi>T
→ RegionD
```

Do not silently require:

```text
Li≥2
```

in the U branch.

Do not apply strict-region `FK_strong` on the eliminated boundary.

The central final C8 theorem should conceptually be:

```lean
theorem ChainCore.c8_handoff
    (K : ChainCore s F D)
    (hF : s.semigroup.IsFrobenius F) :
    Nonempty (RegionU K) ∨ Nonempty (RegionD K)
```

or an equivalent exact structure preserving the chosen actual return data.

It is acceptable for the theorem to explicitly carry:

```text
E : K.Returns
HC : K.Caps E
```

if that gives cleaner provenance.

Do not strengthen the mathematical input.

---

# 47. C8.13 — COMPLETE BRANCH TABLE REGRESSION

Encode a regression theorem/check reflecting exactly:

```text
ENTRY:
C=alpha
→ excluded

ENTRY:
C>alpha
chi≤T
Li≥2
→ excluded

ENTRY:
C>alpha
chi≤T
Li=1
→ RegionU with Du>0

ENTRY:
C>alpha
chi>T
→ RegionD
```

This is the exact publication branch exhaustion.

No other surviving region is permitted.

---

# 48. POSITIVITY POLICY

The Section 8 polynomial decompositions are ordinary finite symbolic identities.

Formalize them directly in Lean using:

```text
ring
ring_nf
nlinarith
omega
```

and explicit auxiliary inequalities as appropriate.

Do not introduce an external certificate or oracle for C8.

The static 715-term certificate belongs to Section 9, not C8.

---

# 49. FROZEN SOURCE POLICY

Every mathematical Lean file existing at:

```text
80b36191937b2e2f0dc251ac6006d63f088e03b2
```

is protected.

Expected mathematical changes:

```text
NEW C8 Chain modules only
```

Do not modify:

```text
ChainInput
C7 Chain modules
T6
P5
M3
C2
symmetric modules
```

If old mathematical source modification is unavoidable:

```text
SOURCE CHANGE REQUIRED
FROZEN RE-AUDIT REQUIRED
```

Stop rather than patch silently.

Documentation-only C7 statement-map repair is allowed.

---

# 50. SUGGESTED MODULE LAYOUT

Prefer new narrow modules such as:

```text
P21/Nonsymmetric/Chain/C8/
  FirstFit.lean
  Packet.lean
  KernelOne.lean
  Triangle.lean
  KCeiling.lean
  BoundarySync.lean
  BoundaryMultiplicity.lean
  StrictWindow.lean
  UnitBoundary.lean
  Handoff.lean
```

and optionally a top-level:

```text
P21/Nonsymmetric/Chain/C8.lean
```

Exact organization may differ.

Do not edit C7 modules to append C8 proofs.

---

# 51. DANGEROUS REGRESSION GATES

Create explicit theorem-level checks for at least the following:

```text
- C7 ChainCore unchanged

- first-fit selection set nonempty
- zhat is a genuine minimum
- n_zeta uses exact integer ceiling
- FIRST-CAPS exact

- Xi≤0 really creates actual F-factorization

- OmegaHat actual ZERO-k face

- C-FK remains signed when C>alpha

- PACKET is derived through same upper element
- common I/J source is coefficientwise contained

- boundary wall uses EA, EB, Qj same-factorization insertion

- general T-window is NOT applied blindly to EB

- EA kernel comparison is pure-H
- Qj kernel comparison is pure-H

- y=1 and v=1 proved from first-fit wall

- DET1 is internally proved, not assumed

- LEVEL-SPLIT exhaustive

- K-CEILING general formula retains L*C-alpha
- boundary simplification only under C=alpha

- boundary EB synchronization proved from actual rows

- level-one boundary excluded via H0<0

- common cross-product scale sigma retained
- sigma=1 is never assumed

- boundary POS-COEFF exact
- C=alpha fully excluded

- strict window does not use boundary SYNC

- Q>=2 regular classification has exactly three exceptions

- Q=1 / exception alternate positivity closes all residuals

- STRICT-WINDOW theorem has exact hypotheses

- DEEP inequalities exact

- unit window forces Li=1, lambda=d, q0=2

- UNIT-PARAM exact

- unit first point exact

- no uniqueness of EA assumed

- UNIT-REMAIN Du>0 proved

- Q>R proved

- level-one EB is constructed as an actual factorization

- RegionU and RegionD preserve same original CHAIN data

- U∨D handoff exhaustive
```

---

# 52. PROOF-DEBT / AXIOM POLICY

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

# 53. DEPENDENCY FIREWALL

Required direction:

```text
FROZEN C7
   ↓
FirstFit
   ↓
PACKET / walls
   ↓
kernel ONE-relations
   ↓
DET1 / PARAM
   ↓
K-CEILING
   ↓
boundary closure
   ↓
strict-window closure
   ↓
unit-window normalization
   ↓
RegionU ∨ RegionD
```

Forbidden transitive imports:

```text
Section 9 mathematical closure
Section 10 Euclidean descent
CHAIN impossibility
main theorem
```

---

# 54. VERIFICATION

Run a fresh root build:

```bash
lake build
```

Explicitly build all new C8 modules.

Rerun every frozen suite:

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
```

Add:

```text
verification/c8/
```

with at least:

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
C8 build log
all previous regression logs
```

---

# 55. EVIDENCE MANIFEST

Retain the T6/C7 repaired convention.

Generate:

```text
EVIDENCE_SHA256.json
```

before artifact upload.

It must hash every evidence file except itself.

Verify it in CI.

---

# 56. GITHUB CI

Create:

```text
.github/workflows/c8-audit.yml
```

or equivalent.

CI must record:

```text
branch
exact candidate SHA
run ID
attempt

Lean
Lake
mathlib revision

candidate digest
frozen source integrity

fresh root build
explicit C8 build

M1
M2A
M2B
M3A
M3B1
M3B2
P5
T6
C7
C8 verification

proof debt
axioms
statement inspection
dependency/circularity
evidence manifest
```

No project-owned compiled artifacts may bypass source compilation.

---

# 57. CANDIDATE PACKAGE

On full success create:

```text
P21_LEAN_C8_CHAIN_BOUNDARY_WINDOW_CANDIDATE_20260918.zip
```

Include:

```text
complete Lean project
all new C8 modules

README_C8.md
SOURCE_OF_TRUTH_C8.md
C8_STATEMENT_MAP.md
C8_PROOF_ROUTE.md
C8_DEPENDENCY_DAG.md

NEXT_RESTART.md

verification/c8/
CI workflow
candidate SHA manifest
```

Compute SHA-256.

---

# 58. TRUE AUDIT ARTIFACT

Upload:

```text
P21_C8_TRUE_AUDIT_EVIDENCE
```

including:

```text
RUN_CONTEXT
COMMIT_SHA
ENVIRONMENT

ROOT_BUILD_LOG
C8_MODULE_LIST
C8_BUILD_LOG
C8_VERIFICATION_LOG

M1_ORIGINAL_SUITE
M2A_ORIGINAL_SUITE
M2B_ORIGINAL_SUITE
M3A_ORIGINAL_SUITE
M3B1_ORIGINAL_SUITE
M3B2_ORIGINAL_SUITE
P5_ORIGINAL_SUITE
T6_ORIGINAL_SUITE
C7_ORIGINAL_SUITE

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

Report artifact ID and GitHub digest.

---

# 59. SUCCESS GATE

You may return only:

```text
C8 CHAIN BOUNDARY/WINDOW CANDIDATE FOR TRUE AUDIT
```

if all of the following are proved:

```text
[ ] first-fit sequence and minimum
[ ] FIRST-CAPS
[ ] Xi≥1
[ ] actual OmegaHat

[ ] genuine CENTRAL FK upper face
[ ] SAME-element PACKET
[ ] BOUNDARY-WALL
[ ] WINDOW-WALL

[ ] EA kernel y=1
[ ] Qj kernel v=1

[ ] empty integer triangle
[ ] DET1
[ ] PARAM
[ ] LEVEL-SPLIT

[ ] H0≥0
[ ] general K-CEILING

[ ] boundary EB synchronization
[ ] boundary level-one exclusion
[ ] positive common cross-product scale
[ ] BOUND-MULT
[ ] POS-COEFF
[ ] C=alpha CLOSED

[ ] STRICT-J
[ ] exact three-exception classification
[ ] alternate STRICT-K
[ ] Q=1 closed
[ ] all three exceptions closed
[ ] STRICT-WINDOW

[ ] closed shallow strict region
[ ] DEEP source-shortage inequalities

[ ] Li=1 window reduction
[ ] lambda=d
[ ] q0=2
[ ] UNIT-PARAM
[ ] exact unit first point
[ ] UNIT-ETA
[ ] compact specialization

[ ] UNIT-MULT
[ ] Du>0
[ ] Q>R
[ ] actual level-one EB

[ ] RegionU defined
[ ] RegionD defined
[ ] exhaustive U∨D handoff

[ ] no Section 9 theorem imported
[ ] no old mathematical source changed
[ ] proof debt 0
[ ] project-specific axioms 0

[ ] fresh build PASS
[ ] C8 explicit build PASS
[ ] M1–C7 regressions PASS
[ ] C8 verification PASS
[ ] clean GitHub CI PASS

[ ] candidate hash recorded
[ ] artifact hash recorded
[ ] evidence manifest verified
```

---

# 60. PARTIAL / NO-GO POLICY

If C8 does not completely reach the U∨D handoff, do not fake success.

Return one of:

```text
C8 PARTIAL — SECTION 8 OPEN
```

or:

```text
C8 NO-GO / INTERFACE OBSTRUCTION
```

Identify the first exact missing theorem with:

```text
Lean statement
publication subsection
proved dependencies
remaining mathematical gap
whether mathematical or frozen-API obstruction
```

If protected mathematical source must change:

```text
SOURCE CHANGE REQUIRED
FROZEN RE-AUDIT REQUIRED
```

Package the strongest valid checkpoint.

---

# 61. STATUS LANGUAGE

Codex must not self-award:

```text
TRUE AUDIT PASS
FROZEN
CHAIN CLOSED
```

Strongest permitted success status:

```text
C8 CHAIN BOUNDARY/WINDOW CANDIDATE FOR TRUE AUDIT
```

CHAIN remains:

```text
OPEN
```

after C8.

The exact next frontier on successful independent audit will be:

```text
C9 — SECTION 9
FROM U/D RESIDUAL CASES TO TWO PACKET RELATIONS
```

Do not begin C9 in this mission.

---

# 62. FINAL REPORT

Report in Japanese.

Begin with exactly one of:

```text
C8 CHAIN BOUNDARY/WINDOW CANDIDATE FOR TRUE AUDIT
```

```text
C8 PARTIAL — SECTION 8 OPEN
```

```text
C8 NO-GO / INTERFACE OBSTRUCTION
```

Then report:

```text
Repository:
Branch:
Frozen base:
Candidate commit:

C7 source unchanged:

FirstFit:
FIRST-CAPS:
Xi/OmegaHat:

PACKET:
BOUNDARY-WALL:
WINDOW-WALL:

EA-ONE:
QJ-ONE:
DET1:
PARAM:
LEVEL-SPLIT:
K-CEILING:

Boundary SYNC:
BOUND-MULT:
POS-COEFF:
C=alpha closure:

STRICT-J:
three exceptions:
STRICT-K:
STRICT-WINDOW:

DEEP region:

UNIT-PARAM:
unit first point:
UNIT-ETA:
UNIT-MULT:
Du:
Q>R:
level-one EB:

RegionU:
RegionD:
U∨D handoff:

CHAIN overall status:
Next frontier:

New Lean modules:
Audited declarations:

Proof debt:
Project-specific axioms:
FROZEN source integrity:
Forbidden reverse dependencies:

Root build:
Explicit C8 build:

M1:
M2A:
M2B:
M3A:
M3B1:
M3B2:
P5:
T6:
C7:
C8 verification:

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
CHAIN overall status: OPEN — C8 complete, C9 next
```

Execute C8 completely now.
