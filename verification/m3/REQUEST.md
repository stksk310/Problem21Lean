# P21 LEAN — M3 NONSYMMETRIC G4 FULL CLASSIFICATION

Numerical Semigroup Problem 21 Lean formalization projectを継続する。

今回のprimary targetは

```text
M3 — NONSYMMETRIC G4 FULL CLASSIFICATION
```

すなわちpublication

```text
Section 4
Nonsymmetric factorization geometry and
classification into three terminal configurations
```

をLean formalizationし、

```text
four distinct actual Q-rows
+
nonsymmetric three-generated tail
+
canonical setting
```

からexhaustively

```text
PATH
∨ TYPE II
∨ CHAIN
```

を得て、それぞれについて§4.16の**exact terminal input data**まで抽出することである。

今回は最初から

```text
implementation
→ local verification
→ GitHub push
→ clean GitHub Actions CI
→ audit evidence
→ single candidate ZIP
```

まで一つのmissionとして実行する。

---

# 0. AUTHORITATIVE FROZEN STATE

Repository:

```text
https://github.com/stksk310/Problem21Lean
```

current authoritative FROZEN commit:

```text
9a9e01c401a934cfca2da15026986b0ecf83ff4f
```

Formal ledger:

```text
M1 — FOUNDATION + C2
TRUE AUDIT PASS / FROZEN

M2A — INTERNAL SYMMETRIC CLOSURE
TRUE AUDIT PASS / FROZEN

M2B — STD_SYM_GLUE
TRUE AUDIT PASS / FROZEN

FULL S3 — SYMMETRIC TAIL
TRUE AUDIT PASS / CLOSED / FROZEN
```

M3はこのcommitから新branchを作る。

推奨:

```text
m3-nonsym-g4
```

mainへmergeしない。

---

# 1. ATTACHED AUTHORITATIVE MATHEMATICS

添付:

```text
P21_Journal_of_Algebra_Submission_Manuscript_FINAL_20260916.pdf

P21_FINAL_FROZEN_VERIFICATION_EDITION_20260907.zip
```

source-of-truth order:

```text
1. 2026-09-16 Journal of Algebra submission PDF
2. frozen verification edition
3. existing TRUE-AUDITED Lean source
```

publication wordingとverification proofが食い違うように見える場合、
勝手に補正せずexact discrepancyを報告する。

---

# 2. IMMUTABILITY

commit

```text
9a9e01c401a934cfca2da15026986b0ecf83ff4f
```

に存在する**すべての既存project-owned mathematical `.lean` files**をFROZENとする。

原則:

```text
NO EDIT TO EXISTING LEAN MATHEMATICS
```

新規moduleのみを追加する。

不足APIはまずwrapper lemmaを新M3 moduleに置く。

FROZEN source変更が本当に必要なら、

```text
FROZEN API EXTENSION REQUIRED
```

として止め、変更対象・理由・minimal required interfaceを報告する。

---

# 3. EXACT ENDPOINT

最終的にconceptually:

```lean
theorem nonsymmetric_four_row_classification
    ...
    (hNonsym : NonsymmetricTail ...)
    (rows : FourDistinctActualQRows ...) :
    PathInput ... ∨ TypeIIInput ... ∨ ChainInput ...
```

を証明する。

続けて§4.16に対応するexact extraction theorem群:

```lean
path_exact_input
typeII_exact_input
chain_exact_input
```

を証明する。

最終M3は**terminal configurationsを排除しない**。

つまり今回OPENのまま残してよいもの:

```text
Section 5 PATH exclusion
Section 6 TYPE II exclusion
Sections 7–10 CHAIN exclusion
Euclidean descent
715-term certificate
3234-term certificate
```

M3の仕事は

```text
classification + exact input extraction
```

まで。

---

# 4. CRITICAL LOGICAL SCOPE

Contradiction hypothesisでは

```text
|Q(Γ)| ≥ 4
```

からfour distinct rowsを選ぶ。

絶対に

```text
|Q| = 4
```

と仮定してはいけない。

Section 4 classificationは
**selected four rows**について行う。

three-singleton resultだけは

```text
three singletons exist ⇒ full |Q| = 3
```

を別途証明する。

---

# 5. ACTUALITY FIREWALL

M1から継承した規律を厳守。

## Actual factorization

coefficientsはnonnegative。

## Signed relation

signed equality / kernel identity / completed zero identityは
actual factorizationではない。

## SAME element

coefficient replacementは必ずnamed actual factorizationの
同じelement内で行う。

## Criticality

Herzog criticalityは

```text
m coefficient = 0
```

まで完全に消去されたpure-H relationにしか適用しない。

## Extremal choice

least positive m-level / maximal coordinate等は
finite setまたはwell-orderingをLeanで明示する。

---

# 6. M3 INTERNAL PHASES

推奨DAG:

```text
FROZEN M1/C2
     │
     ├── M3-H: STD_HERZOG
     │
     ▼
G4.1 six-arm atlas
     ↓
G4.2 antichain / complement box
     ↓
G4.3 critical-box + integer kernel basis
     ↓
G4.4 corners vs singletons
     ↓
G4.5 matched-pair synchronization
     ↓
G4.6 root-free level rigidity
     ↓
G4.7 positive-m return minima
     ↓
G4.8 four caps
     ↓
G4.9 unequal-level exclusion
     ↓
G4.10 equal-level / coexistence
     ↓
G4.11–4.13 arm/singleton geometry
     │
     ├── M3-W: Appendix-B COLOR-CAP
     │         + exact White input
     ↓
G4.14 three-same-color exclusion
     ↓
G4.15 four-row exhaustive classification
     ↓
G4.16 PATH / TYPE II / CHAIN extraction
     ↓
M3 FULL CLASSIFICATION
```

---

# 7. M3-H — `STD_HERZOG`

Publication §2.2.2のstandard nonsymmetric three-generator formを
Leanで正式証明する。

No axiom.

No `sorry`.

No opaque assumption.

Desired data after cyclic permutation:

positive integers

```text
a_i,a_j,a_k
b_i,b_j,b_k
rho_r = a_r+b_r
```

with exact critical relations:

```math
ρ_i n_i = b_j n_j + a_k n_k
ρ_j n_j = a_i n_i + b_k n_k
ρ_k n_k = b_i n_i + a_j n_j
```

and every `ρ_r` is the **least positive critical multiplier** in that direction.

Also obtain exact two tail pseudo-Frobenius numbers:

```math
f_A=(ρ_i-1)n_i+(a_j-1)n_j-n_k
f_B=(ρ_i-1)n_i-n_j+(b_k-1)n_k
```

plus cyclic versions and

```math
PF(H)={f_A,f_B}.
```

Pairwise coprimality of `n_i,n_j,n_k` must NOT be assumed.

Under primitive tail/gcd-one conditions, formalize the primitive generator formulas if Appendix B requires them.

Suggested structure:

```lean
structure NonsymmetricHerzogData (g : Generators) where
  perm : Equiv.Perm (Fin 3)
  a b : Fin 3 → ℕ
  a_pos : ...
  b_pos : ...
  rho : Fin 3 → ℕ
  rho_eq : ...
  critical_relations : ...
  critical_minimal : ...
  fA fB : ℤ
  pf_exact : ...
```

Use a cleaner equivalent if preferable.

---

# 8. `STD_HERZOG` PROOF POLICY

Search pinned mathlib first.

If unavailable, formalize only the edim-3 nonsymmetric theorem needed here.

Do not build arbitrary affine-semigroup presentation theory.

Acceptable proof routes include:

```text
critical multiples
+
factorization support analysis
+
nonsymmetry excludes complete-intersection/gluing case
+
3-cycle critical relation matrix
+
PF formulas
```

M2B's symmetric classification infrastructure may be reused where mathematically valid.

Do not use `¬ SymmetricTail` to obtain a black-box Herzog structure without proof.

---

# 9. G4.1 — SIX-ARM ATLAS

For an actual row `q∈Q` define

```text
SH(q) = {r | q+n_r ∈ H}
```

using existing C2 data.

Classify:

```text
singleton: |SH|=1
doubleton: |SH|=2
corner:    |SH|=3
```

For a doubleton missing direction `r`, prove exactly:

```math
A_r(λ)=f_A-λn_r,\qquad 1≤λ≤a_r-1

B_r(μ)=f_B-μn_r,\qquad 1≤μ≤b_r-1.
```

The proof must use the largest gap-along-the-missing-direction argument.

Do not assume generic connectivity.

---

# 10. CORNERS

Formalize the actual corner rows corresponding to `f_A,f_B`.

Preserve cyclic representations.

Prove:

```text
two rows on same arm impossible
corner + same-color arm impossible
at most one lower triple-support corner
higher corner impossible
```

using actual PF antichain/Frobenius comparison exactly as source.

---

# 11. G4.2 — BASIC ANTICHAIN / SINGLETON CAPS

For distinct actual PF rows prove complement antichain.

For singleton `S_r`:

```math
c_S = κ_r n_r,
1≤κ_r≤ρ_r-1.
```

Then prove:

```text
no two singletons in one direction
```

and singleton cap:

every actual factorization of

```text
another complement
or W
```

has r-coordinate at most `κ_r-1`.

Also prove maximum `κ_r-1` is attained for W.

No global uniqueness assumption.

---

# 12. ARM COMPLEMENT BOX

For an arm missing direction `i`:

```math
c=yn_j+zn_k,
0≤y<ρ_j,
0≤z<ρ_k.
```

Prove existence and uniqueness.

The uniqueness must come from criticality of pure-H relations,
not generic factorization uniqueness.

---

# 13. G4.3 — CRITICAL BOX + INTEGER KERNEL

Prove critical-box uniqueness:

no two distinct actual nonnegative factorizations can both satisfy

```text
X_r < rho_r
```

for all three coordinates.

Then formalize exact integer kernel basis

```math
r_j=(a_i,-ρ_j,b_k),
r_k=(b_i,a_j,-ρ_k).
```

Prove they form a **ℤ-basis** of the integer kernel.

This is stronger than merely an ℝ-basis.

No hidden saturation assumption.

---

# 14. G4.4 — CORNER / SINGLETON EXCLUSION

Formalize §4.4:

```text
corner and singleton cannot coexist
```

for every direction/color via cyclic permutation and color reversal.

Preserve actual same-row provenance in the contradiction.

---

# 15. G4.5 — MATCHED PAIR SYNCHRONIZATION

For actual

```text
A_i(λ), B_i(μ)
```

prove

```math
λ=μ.
```

Then exact MATCH data:

```math
P=ρ_i-λ
R=a_j+g
T=b_k+α
```

with

```text
g≥0
α≥0
R<ρ_j
T<ρ_k
P>a_i,b_i
```

and

```math
c_A=g n_j+T n_k
c_B=R n_j+α n_k

W=(P-1)n_i+(R-1)n_j+(T-1)n_k.
```

**Do not silently assume `g>0` or `α>0`.**

Boundary cases `g=0`, `α=0` remain valid here.

---

# 16. MATCHED PAIR + SINGLETON PRELIMINARY EXCLUSION

Formalize §4.5.1.

At this stage only `S_i` may possibly coexist with matched pair in direction `i`.

`S_j`, `S_k` are excluded by genuine nonnegative H representations.

---

# 17. G4.6 — ROOT-FREE MATCHED LEVEL RIGIDITY

Prove directly from MATCH and actual PF rows:

there exist

```text
L≥1
t,u≥0
```

such that

```math
q_A+n_i=Lm+(a_j+t)n_j+u n_k
q_B+n_i=Lm+t n_j+(u+b_k)n_k
P n_i=Lm+(t+1)n_j+(u+1)n_k.
```

No unit-root hypothesis.

No Section 7 machinery.

This theorem must retain `g=0`, `α=0`.

---

# 18. G4.7 — INDEPENDENT POSITIVE-m RETURNS

For

```text
E_A=q_A+n_i
E_B=q_B+n_i
```

prove:

```text
E_A,E_B ∈ Γ
E_A,E_B ∉ H
```

using pure-H criticality exactly as publication.

Then choose **independently** the least positive m coefficient in each factorization fiber:

```math
E_A=L_A m+U_jn_j+U_kn_k

E_B=L_B m+V_jn_j+V_kn_k.
```

Formalize existence of minima from nonempty subsets of positive integers.

Do not synchronize levels yet.

---

# 19. G4.8 — FOUR CAPS

Construct the same actual `F+n_i` representations and prove:

```math
U_j+g ≤ ρ_j-1
U_k+T ≤ ρ_k-1
V_j+R ≤ ρ_j-1
V_k+α ≤ ρ_k-1.
```

Packet replacement must be coefficientwise in the **same actual factorization**.

---

# 20. G4.9 — UNEQUAL LEVELS

Define publication variables exactly:

```math
t=U_j-a_j
K=U_k+b_k
x=V_j-t
y=K-V_k
```

and

```math
(L_A-L_B)m=x n_j-y n_k.
```

Prove BOX bounds.

Then independently exclude:

```text
L_A > L_B
L_B > L_A.
```

Important:

intermediate `WJ` or `WK` may have a negative coefficient when

```text
α=0
or
g=0.
```

Those are **signed intermediate equalities only**.

Only the final `F` vector after adding the completed identity may be called an actual factorization, once every coefficient is proved nonnegative.

---

# 21. G4.10 — EQUAL LEVEL MATCHING

Conclude:

```math
L_A=L_B=L.
```

Then pure-H criticality after eliminating m gives

```math
x=y=0.
```

Hence obtain actual EA/EB and P-FIBER formulas.

Then prove matched-pair coexistence restrictions:

```text
additional A_j impossible
additional B_k impossible
```

so only

```text
B_j
A_k
```

can be extra arms.

Finally prove §4.10.2:

```text
matched pair cannot coexist with S_i either.
```

Therefore:

```text
matched pair + any singleton impossible.
```

---

# 22. G4.11 — TWO SAME-COLOR ARMS

For actual

```text
A_i(λ), A_k(ν)
```

derive exactly the two complement geometries:

```text
Case A (AA-A)
Case B (AA-B)
```

and nothing stronger.

All displayed complement coefficients must retain actual nonnegative provenance.

Then prove:

```text
S_j impossible
S_i and S_k simultaneously impossible
```

plus color-reversed B version.

---

# 23. G4.12 — MIXED COLORS / DIFFERENT DIRECTIONS

Formalize both orientations.

## Right orientation

```text
B_i(λ), A_k(ν)
```

obtain:

```math
β=b_i-λ>0
α=a_k-ν>0
R≥0

c_Bi=R n_j+αn_k
c_Ak=βn_i+R n_j.
```

When `R=0`, the naive W expression is signed.

The only W formula called actual must be the completed BA-W formula with nonnegative coefficients.

Prove singleton `S_j` impossible; only directions `i,k` remain possible.

## Opposite orientation

```text
A_i(λ), B_k(ν)
```

derive the exact reverse formulas and prove only `S_j` can coexist.

---

# 24. G4.13 — THREE SINGLETONS

Prove:

```text
S_i,S_j,S_k exist
⇒ |Q|=3.
```

Critical firewall:

do NOT assume global uniqueness of W.

First singleton caps confine **all W factorizations** to the critical box.

Then use critical-box uniqueness.

Only then obtain the unique W factorization.

For any other q, use coefficientwise containment to conclude q∈H.

---

# 25. M3-W — COLOR-CAP / APPENDIX B

Formalize the exact Appendix-B theorem required by §4.14.

Primary target:

```text
three actual arms of the same color
in all three directions
are impossible.
```

The source route uses:

```text
minimal positive m coefficient
→ empty relative-lattice tetrahedron
→ White width-one theorem
→ k=1
→ finite box path
→ positive exit
→ same actual f_A/f_B factorization contradiction.
```

Preserve this route unless a genuinely equivalent Lean proof is substantially cleaner.

Any alternate proof must be documented in

```text
M3_ALTERNATIVE_PROOF_NOTE.md
```

and must use no stronger hypothesis.

---

# 26. STD_WHITE

No axiom escape.

Need either:

### A. formalize the exact White input

An empty lattice tetrahedron has lattice width one,

in precisely the rank-3 lattice formulation needed by Appendix B,

or

### B. prove the exact consequence required by the P21 tetrahedron directly.

Do not formalize unnecessary arbitrary-dimensional geometry.

If using direct consequence B, clearly state the theorem replacing `STD_WHITE` and prove it entirely in Lean.

---

# 27. APPENDIX B FIREWALLS

The tetrahedron must be built in the **relative lattice** generated by the same actual data.

Intermediate-level lattice point:

```text
⇒ smaller positive m coefficient
```

must contradict the actual minimal choice.

Nonvertex top-face point:

```text
⇒ f_ε ∈ H
```

must use a genuine nonnegative factorization.

When applying White classes, preserve the source's pair partition and color-reversal/permutation bookkeeping.

No floating-point geometry.

No finite numerical scan.

---

# 28. BOX PATH

Formalize enough of Appendix B.9–B.19 to prove:

```text
a maximal path in the finite arm box
must have a positive exit.
```

Need termination from strict decrease of the tracked positive value / finiteness.

Cover all sink types:

```text
one-row
rows 1+2
rows 1+3
all three rows
```

Do not omit the first occurrence of the third color.

The weighted certificate must remain symbolic for arbitrary parameters.

---

# 29. G4.14

Use M3-W to conclude:

```text
three same-color arms impossible.
```

Then establish the publication color cap:

```text
for each color,
at most two corner/arm rows.
```

Include the corner cases needed for §4.15.

---

# 30. G4.15 — EXHAUSTIVE FOUR-ROW CLASSIFICATION

Take **four distinct selected actual Q rows**.

Classify by numbers:

```text
s = singletons
c = corners
a = arms
```

Exhaust all cases exactly as publication.

Corner-containing four-row configurations must be eliminated by COLOR-CAP.

Then derive exactly:

## PATH

```text
S_i,
B_i(λ),
A_k(ν),
S_k
```

## TYPE II

```text
S_i,
A_i(λ),
B_j(μ),
A_k(ν)
```

## CHAIN

```text
B_j(μ),
A_i(λ),
B_i(λ),
A_k(ν)
```

up to cyclic permutation and full color reversal.

Do not create a fourth fake terminal configuration for a matched pair + singleton:
it is already excluded by §4.10.2.

---

# 31. TERMINAL CONFIGURATION TYPES

Create explicit Lean structures, preferably:

```lean
structure PathInput ...
structure TypeIIInput ...
structure ChainInput ...
```

Each must carry:

```text
same Γ
same F
same m
same W
actual four PF rows
actual complement identities
positivity/range conditions
required missing directions
```

No re-instantiation of another semigroup.

---

# 32. G4.16.1 — SINGLETON SATURATION

Formalize general BOX-W theorem:

if

```math
W=(P-1)n_i+(R-1)n_j+(T-1)n_k
```

with

```text
1≤P≤ρ_i
1≤R≤ρ_j
1≤T≤ρ_k
```

and `S_i` has complement `κn_i`, prove:

```math
κ=P.
```

Do not assume whole factorization fiber uniqueness.

Use singleton cap + kernel basis exactly.

---

# 33. G4.16.2 — CHAIN EXACT INPUT

Extract:

```math
δ=a_i-λ ≥1
β=b_i-λ ≥1
g=b_j-μ ≥1
α=a_k-ν ≥1
```

and

```math
P=λ+δ+β
R=a_j+g
T=b_k+α
```

with complements:

```math
c_Bj=δn_i+Tn_k
c_Ai=g n_j+Tn_k
c_Bi=R n_j+αn_k
c_Ak=βn_i+R n_j.
```

This exact positivity is the downstream input to Sections 7–10.

---

# 34. G4.16.3 — TYPE II EXACT INPUT

Extract:

```text
1≤λ≤a_i-1
1≤μ≤b_j-1
1≤ν≤a_k-1
λ≤b_i
```

and

```math
P=ρ_i-λ
R=ρ_j-μ
T=ρ_k-ν
```

with the three arm complements and

```math
c_Si=P n_i.
```

Produce the exact singleton row formula.

---

# 35. G4.16.4 — PATH EXACT INPUT

Extract:

```text
β=b_i-λ>0
α=a_k-ν>0
1≤R<ρ_j
```

and

```math
P=a_i+β=ρ_i-λ
T=b_k+α=ρ_k-ν.
```

Singleton saturation gives:

```math
c_Si=P n_i
c_Sk=T n_k.
```

Then formalize the actual ladder:

```math
q_L+a_i n_i=q_A+R n_j
q_A+βn_i=q_B+αn_k
q_R+b_k n_k=q_B+R n_j.
```

Remember here `q_A/q_B` are ladder labels, not Herzog colors.

---

# 36. FINAL M3 THEOREM

Expose something semantically equivalent to:

```lean
theorem nonsymmetric_selected_four_terminal
    ...
    (hfour : FourDistinctActualQRows ...)
    (hnonsym : NonsymmetricTail ...)
    :
    Nonempty (PathInput ...)
      ∨ Nonempty (TypeIIInput ...)
      ∨ Nonempty (ChainInput ...)
```

Exact API may differ.

But the conclusion must retain full §4.16 data, either directly or through downstream extraction theorems.

---

# 37. EXTERNAL-INPUT SUCCESS POLICY

Ideal M3 success closes both:

```text
STD_HERZOG
STD_WHITE / exact White consequence
```

inside Lean.

If one remains genuinely too large, do NOT axiomatize it.

Return the strongest completed milestone with exact status, e.g.

```text
M3A NONSYMMETRIC LOCAL GEOMETRY CANDIDATE
STD_WHITE OPEN
FULL G4 OPEN
```

or

```text
M3H STD_HERZOG FROZEN-CANDIDATE
G4 LOCAL OPEN
```

But push as far as possible before stopping.

Remaining obligation must be an exact Lean proposition.

---

# 38. DEPENDENCY / CIRCULARITY

M3 must not import:

```text
PATH exclusion Section 5
TYPE II exclusion Section 6
CHAIN Sections 7–10
Euclidean closure
certificate results
main theorem
```

Required direction:

```text
M1/C2
+
new STD_HERZOG
+
new STD_WHITE consequence
      ↓
M3 G4
      ↓
PathInput / TypeIIInput / ChainInput
```

No later branch theorem may feed backward into classification.

---

# 39. SUGGESTED FILE TREE

Suggested only:

```text
P21/Nonsymmetric/
  HerzogData.lean
  HerzogClassification.lean
  Rows.lean
  Arms.lean
  ComplementGeometry.lean
  CriticalBox.lean
  Kernel.lean
  MatchedPair.lean
  ReturnLevels.lean
  SameColor.lean
  MixedColor.lean
  Singletons.lean

P21/Nonsymmetric/ColorCap/
  RelativeLattice.lean
  EmptyTetrahedron.lean
  WhiteInput.lean
  WhiteClasses.lean
  BoxPath.lean
  Closure.lean

P21/Nonsymmetric/
  TerminalTypes.lean
  Classification.lean
  Extraction.lean
```

Keep modules focused.

---

# 40. REGRESSION TESTS

Explicit theorem-level regression protection for:

```text
D(c) ⊆ SH(q), not equality
Q≥4 does not mean Q=4
g=0 and α=0 survive until legally excluded
signed WJ/WK are not actual when coefficient=-1
criticality only after m elimination
same-element replacement
three-singleton theorem concerns full Q
matched pair + singleton already excluded
PATH qA/qB labels ≠ Herzog colors
CHAIN coefficients δ,β,g,α all strictly positive only at extraction stage
```

---

# 41. PROOF DEBT / AXIOMS

No:

```text
sorry
admit
axiom
sorryAx
unsafe
project-specific opaque escape
```

Inspect all new declarations with `#print axioms`.

Allowed only:

```text
propext
Classical.choice
Quot.sound
```

---

# 42. FROZEN SOURCE INTEGRITY

Every pre-M3 mathematical `.lean` file must remain byte-identical to:

```text
9a9e01c401a934cfca2da15026986b0ecf83ff4f
```

CI must compute this automatically from Git.

New M3 files allowed.

Any changed frozen Lean file:

```text
FROZEN_SOURCE_CHANGED: YES
```

and no TRUE-AUDIT-ready claim.

---

# 43. LOCAL BUILD

Before push run:

```bash
lake build
```

plus explicit builds of:

```text
all frozen M2 modules
all new M3 modules
terminal classification/extraction root
```

Run old verification suites unchanged:

```text
M1
M2A
M2B
```

plus new M3 suite.

---

# 44. CANDIDATE ZIP

Full success filename:

```text
P21_LEAN_M3_NONSYMMETRIC_G4_FULL_CLASSIFICATION_CANDIDATE_20260917.zip
```

Include:

```text
complete reproducible source snapshot
README_M3.md
SOURCE_OF_TRUTH_M3.md
M3_DEPENDENCY_DAG.md
M3_STATEMENT_MAP.md
M3_PROOF_ROUTE.md
M3_EXTERNAL_INPUT_REPORT.md
FROZEN_SOURCE_INTEGRITY_REPORT.txt
BUILD_LOCAL_LOG.txt
AXIOM_REPORT_M3.txt
PROOF_DEBT_REPORT_M3.txt
CODEX_SELF_CHECK_M3.md
NEXT_RESTART.md
```

---

# 45. GITHUB INTEGRATION

Push exact source to:

```text
repository:
https://github.com/stksk310/Problem21Lean

branch:
m3-nonsym-g4
```

Do not merge main.

Record exact:

```text
AUDIT_TARGET_COMMIT=<40-char SHA>
```

Candidate ZIP and GitHub mathematical source must be hash-identical.

---

# 46. GITHUB ACTIONS

Create:

```text
.github/workflows/m3-audit.yml
```

Workflow name:

```text
P21 Lean M3 Audit
```

Clean Ubuntu runner.

Pinned existing:

```text
lean-toolchain
lake-manifest.json
```

No dependency upgrade.

No project-owned compiled cache.

---

# 47. CI REQUIRED CHECKS

Must run:

```text
1. exact commit checkout
2. frozen pre-M3 Lean integrity
3. candidate ZIP/source integrity
4. pinned Lean environment
5. pinned dependency verification
6. fresh root lake build
7. explicit frozen M2 module build
8. explicit ALL M3 module build
9. M1/M2 old verification suites
10. M3 verification suite
11. proof debt scanner
12. scanner regressions
13. all M3 axiom checks
14. critical statement inspection
15. import/circularity audit
16. final source integrity
17. evidence upload
```

---

# 48. CRITICAL STATEMENT INSPECTION

Print exact Lean types for at least:

```text
NonsymmetricHerzogData
six_arm_atlas
critical_box_unique
integer_kernel_basis
matched_pair_sync
root_free_level_rigidity
unequal_levels_impossible
three_singletons_force_Q_three
three_same_color_arms_impossible
nonsymmetric_selected_four_terminal
path_exact_input
typeII_exact_input
chain_exact_input
```

Use actual theorem names.

---

# 49. CI ARTIFACT

Name:

```text
P21_M3_TRUE_AUDIT_EVIDENCE
```

Include:

```text
ENVIRONMENT.txt
FROZEN_SOURCE_INTEGRITY.txt
CANDIDATE_SOURCE_INTEGRITY.txt

ROOT_BUILD_LOG.txt
M3_BUILD_LOG.txt
M3_MODULE_LIST.txt

OLD_SUITE_LOG.txt
M3_VERIFICATION_LOG.txt

PROOF_DEBT_REPORT.txt
AXIOM_REPORT.txt
AXIOM_SUMMARY.json

STATEMENT_INSPECTION.txt
DEPENDENCY_DAG_CHECK.txt
CIRCULARITY_CHECK.txt

COMMIT_SHA.txt
RUN_CONTEXT.json
```

---

# 50. HANDOFF RECEIPT

Create:

```text
HANDOFF_RECEIPT_M3.json
```

Include:

```text
repository
branch
audit_target_commit
workflow run URL
workflow run ID
attempt
CI conclusion
artifact name
artifact ID
artifact digest
candidate ZIP SHA256

STD_HERZOG status
STD_WHITE status
G4 status

M3 module count
proof debt
project-specific axioms
frozen source changed
source changed
remaining OPEN scope
```

---

# 51. SUCCESS LANGUAGE

Codex must NOT say:

```text
TRUE AUDIT PASS
FROZEN
AUDITED
```

Full success wording:

```text
M3 NONSYMMETRIC G4 FULL CLASSIFICATION
CANDIDATE FOR TRUE AUDIT

CI REPRODUCIBILITY EVIDENCE READY
```

Partial success must state exact reduced scope.

---

# 52. FINAL USER REPORT — JAPANESE

Report:

```text
1. STD_HERZOG status
2. STD_WHITE / replacement theorem status
3. six-arm atlas
4. critical box/kernel basis
5. matched-pair package
6. equal-level synchronization
7. same/mixed-color geometry
8. three-singleton result
9. COLOR-CAP
10. four-row classification
11. PATH extraction
12. TYPE II extraction
13. CHAIN extraction

14. local verification
15. proof debt
16. axioms
17. frozen integrity

18. GitHub repo/branch/commit
19. workflow URL/run ID/attempt
20. artifact ID/digest
21. candidate ZIP SHA256
22. remaining OPEN
```

Copy block:

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

STD_HERZOG:
STD_WHITE:
G4_FULL_CLASSIFICATION:

PATH_INPUT:
TYPEII_INPUT:
CHAIN_INPUT:

PROOF_DEBT:
PROJECT_SPECIFIC_AXIOMS:
FROZEN_SOURCE_CHANGED:
SOURCE_CHANGED:
```

---

# 53. FULL SUCCESS CONDITION

Full M3 requires:

```text
STD_HERZOG proved
+
required White theorem/consequence proved
+
six-arm atlas proved
+
actual complement geometry proved
+
critical box and ℤ-kernel basis proved
+
matched-pair synchronization proved
+
positive-m return level synchronization proved
+
all coexistence exclusions proved
+
three same-color arms excluded
+
selected four rows exhaustively reduce to
PATH / TYPE II / CHAIN
+
all §4.16 exact scalar inputs extracted
+
no proof debt
+
no project-specific axioms
+
all FROZEN source unchanged
+
local clean verification PASS
+
GitHub clean CI PASS
```

Only then return:

```text
M3 NONSYMMETRIC G4 FULL CLASSIFICATION
CANDIDATE FOR TRUE AUDIT
```
