# P21 LEAN — M2 SYMMETRIC TAIL / S3

Numerical Semigroup Problem 21 Lean formalization project を継続する。

現在の正式FROZEN state:

```text
M1 — FOUNDATION + C2
TRUE AUDIT PASS / FROZEN

FROZEN COMMIT:
9464b9cd3b6b070f9fa6d1c212f27065d1eb84b3

REPOSITORY:
https://github.com/stksk310/Problem21Lean
```

今回のprimary targetは

```text
M2 — SYMMETRIC TAIL / S3
```

すなわち publication Section 3 + Appendix A に対応する

```math
H = ⟨x,y,z⟩ symmetric
+
canonical condition
⟹
t(Γ) ≤ 4
```

のLean formalizationである。

ただし、標準外部入力 `STD_SYM_GLUE` のformalization statusに応じて、
milestoneを安全に分割してよい。

---

# 0. ABSOLUTE RULE — M1 IS IMMUTABLE

以下のFROZEN implementation filesは変更禁止。

```text
P21.lean
P21/Factorization.lean
P21/NumericalSemigroup.lean
P21/Basic.lean
P21/PseudoFrobenius.lean
P21/Apery.lean
P21/CanonicalReduction.lean
P21/Tail.lean
P21/Selection.lean
P21/Semantics.lean
lean-toolchain
lake-manifest.json
lakefile.toml
```

開始時にFROZEN commit

```text
9464b9cd3b6b070f9fa6d1c212f27065d1eb84b3
```

からbranchを切る。

推奨branch:

```text
m2-symmetric-tail
```

M1 filesのSHA-256 baselineを保存し、
終了時にbyte-identicalであることをmachine-checkする。

M2の都合でM1 APIが足りない場合でも、
まず新規M2 module側にwrapper lemmaを置く。

M1 sourceの変更が本当に不可避なら変更して続行せず、

```text
M1 FROZEN API EXTENSION REQUIRED
```

としてexact requirementを報告すること。

---

# 1. SOURCE-OF-TRUTH ORDER

authority hierarchy:

## Level 1 — publication theorem / wording

`P21_Journal_of_Algebra_Submission_Manuscript_FINAL_20260916.pdf`

特に:

```text
Section 2.2.1
Section 3
Appendix A
Section 11 integration references
```

## Level 2 — source navigation

`P21_MANUSCRIPT_EN_FINAL_20260908_v1.zip`

TeX navigation用。

2026-09-16版との差は既知のzero-math editorial changeのみ。

## Level 3 — proof provenance

`P21_FINAL_FROZEN_VERIFICATION_EDITION_20260907.zip`

特に:

```text
03_SYMMETRIC_CASE.md
10_DEPENDENCY_LEDGER.md
APPENDICES/INPUT_DEPENDENCY_LEDGER.json
```

authoritative dependency:

```text
S3 DEPENDS ON:
- C2
- STD_SYM_GLUE
```

## Level 4

`P21_supplement_v1.zip`

M2では原則不要。
715/3234 certificateには進まない。

---

# 2. EXACT M2 TARGET

publicationのS3 statementと数学的に一致するLean theoremを最終targetとする。

概念的には:

```lean
theorem symmetric_tail_type_le_four
    (g : Generators)
    (s : g.Setting)
    (F : ℤ)
    (hF : s.semigroup.IsFrobenius F)
    (hcan : s.semigroup.Canonical F g.m)
    (hsym : SymmetricTail g ...)
    : s.semigroup.type ≤ 4 := ...
```

実際のAPIは既存M1設計に合わせてよい。

ただしhypothesisのsilent strengtheningは禁止。

特にpublication theoremは

```text
Γ minimally four-generated
m multiplicity
H minimally three-generated numerical semigroup
H symmetric
canonical condition
```

から結論する。

余分なcoprimality、uniqueness、pairwise coprime、extra positivity等を
勝手に仮定してはならない。

---

# 3. GATE 0 — STD_SYM_GLUE

S3の唯一のstandard external inputは

```text
STD_SYM_GLUE
```

である。

使用形は正確に:

after permuting the three tail generators,

```math
H = ⟨du,dv,w⟩,
d,u,v ≥ 2,
gcd(u,v)=1,
gcd(d,w)=1,
w ∈ ⟨u,v⟩.
```

これは論文で証明されていないstandard external resultである。

## 最初に行うこと

現行pinned mathlib revisionを検索し、

* numerical semigroup
* symmetric numerical semigroup
* complete intersection
* embedding dimension three
* gluing
* Frobenius symmetry

に関する既存formal theoremがないか確認する。

結果を

```text
MATHLIB_SYM_GLUE_SEARCH.md
```

に記録する。

---

# 4. NO AXIOM ESCAPE

以下は禁止:

```lean
axiom STD_SYM_GLUE ...
theorem STD_SYM_GLUE := by sorry
opaque fakeSymmetricClassification ...
```

また、

```text
“standard theoremなのでassume”
```

として最終S3をCLOSED扱いすることも禁止。

---

# 5. ACCEPTABLE GATE-0 OUTCOMES

## Outcome A — mathlibに十分な theorem がある

exact statement bridgeを証明して使用する。

その場合full M2へ進む。

## Outcome B — mathlibにはないが、必要方向をlocal proofできる

必要方向だけをformalizeする。

不要な一般論までformalizeしない。

full M2へ進む。

## Outcome C — STD_SYM_GLUEが今回閉じない

ここでproject全体を失敗扱いしない。

代わりにnormal-form dataを明示hypothesisとした

```text
M2A — INTERNAL SYMMETRIC CLOSURE
```

を完全formalizeする。

例えばconceptually:

```lean
structure SymmetricGlueData where
  perm : Equiv.Perm (Fin 3)
  d u v w : ℕ
  ...
```

または既存APIに自然な別表現を用いる。

そして

```lean
theorem symmetric_tail_from_glue_data :
  ...
  → type ≤ 4
```

を証明する。

この場合のstatusは

```text
M2A INTERNAL SYMMETRIC CLOSURE
CANDIDATE FOR TRUE AUDIT

STD_SYM_GLUE: OPEN
FULL S3: NOT YET FROZEN
```

とする。

決してfull S3 PASSと呼ばない。

---

# 6. M2 INTERNAL DAG

内部formalizationは概ね以下の順序を推奨する。

```text
M1/C2 FROZEN
      │
      ├──────── STD_SYM_GLUE
      │
      ▼
TwoGeneratorFacts
      │
      ▼
StableCore / GAP-K
      │
      ▼
BRIDGE / TYPE-BRIDGE
      │
      ▼
RAW4 classification
      │
      ▼
Cross-layer rigidity
      │
      ▼
QM + SPLIT
      │
      ├──── Branch I
      │       ├ four-hit necessity
      │       └ X-only / Y-only / XY exclusion
      │
      └──── Branch II
              ├ k0 = 1 → Branch I
              ├ k0 = 0, e = 0
              └ k0 = 0, e > 0 cross-core
                      │
                      ▼
                contradiction
                      │
                      ▼
                   t ≤ 4
```

---

# 7. M2.1 — TWO-GENERATOR FOUNDATION

Formalize Appendix A.1.

Let

```math
T = ⟨u,v⟩,
gcd(u,v)=1,
u,v≥2.
```

必要なfacts:

## normal form

任意のintegerについてunique

```math
a u + b v,
a∈ℤ,
0≤b<u
```

normal form。

membership:

```math
a u + b v ∈ T ↔ a ≥ 0.
```

## representation difference

二つのinteger representationsの差:

```math
(kv,-ku).
```

## Frobenius symmetry

```math
F_T = uv-u-v
```

and

```math
t ∉ T ↔ F_T - t ∈ T.
```

可能なら既存mathlib `FrobeniusNumber` infrastructureをreuseする。

ただし整数上のpublication semanticsとのbridgeを明示する。

## subcritical coefficient facts

publication Appendix A.1の以下を正確にformalize:

```text
P < v, Q < u, Pu+Qv ∈ T ⇒ P,Q ≥ 0
P,Q > 0 ⇒ uv-Pu-Qv ∉ T
0≤P<v, 0≤Q<u ⇒ Pu+Qv-uv ∉ T
```

## two-generator intersection

```math
0<A<v,\quad 0<B<u
```

なら

```math
(Au+T) ∩ (Bv+T)
=
(Au+Bv+T) ∪ (uv+T).
```

tag:

```text
2GI
```

後続proofがこのlemmaに依存するため、
statementの強弱を変えない。

---

# 8. M2.2 — STABLE CORE / GAP-K

Publication §3.2 をformalize。

```math
K={a∈H : a+nm∈H for some/all required stable n},
h=min K.
```

sourceのquantifierを正確に確認すること。

証明する:

```math
t ∉ Γ ↔ f-t ∈ K
```

tag:

```text
GAP-K
```

then

```math
F = f-h
```

and

```math
r=h-m=f-F-m>0
```

and

```math
r+nm∈H  (n≥1).
```

tag:

```text
FS
```

KがΓ-idealであることもformalizeする。

---

# 9. M2.3 — EXACT BRIDGE

Define

```math
J = K-r
I_r = {c∈H : c+r∈H}.
```

prove

```math
J ⊆ Γ,
min J = m,
m ∈ J,
J ∩ H = I_r.
```

さらにpublicationのexact bridge:

```math
Min_Γ J
=
{m} ⊔ (Min_H I_r ∩ Ap(Γ,m)).
```

tag:

```text
BRIDGE
```

から

```math
t(Γ)
=
1 + |Min_H I_r ∩ Ap(Γ,m)|.
```

tag:

```text
TYPE-BRIDGE
```

を証明する。

actual factorizationから

```text
Apéry ⇒ m-coordinate zero ⇒ H-membership
```

を使う箇所はM1のFROZEN APIを利用する。

別factorizationへ勝手に乗り換えない。

---

# 10. M2.4 — RAW4 CLASSIFICATION

`STD_SYM_GLUE`から

```math
x=du,\quad y=dv,\quad z=w,
H=⟨du,dv,w⟩.
```

を得る。

prove:

```math
f=(d-1)w+dF_T.
```

write

```math
r=sw+dρ,\quad 0≤s<d.
```

## s=0

raw minima ≤2 をformalizeし、`t≥5` と矛盾。

## 1≤s≤d−1

raw minimaが存在し得るlayerがexactly

```text
j = 0
j = d-s
```

であることを証明。

associated two-generator ideals:

```math
J0={t∈T : t+ρ∈T}
J1={t∈T : t+ρ+w∈T}.
```

各々のminimal generatorsが≤2。

`t≥5` なら四つのraw minimaが全部存在しApéryに残ることを
TYPE-BRIDGEから導く。

RAW4:

```math
(c_x,a_x)   =(Ax, sw+Cy)
(c_y,a_y)   =(By, sw+Dx)

(c'_x,a'_x) =((d-s)w+A'x, C'y)
(c'_y,a'_y) =((d-s)w+B'y, D'x)
```

with

```math
a=c+r
A+D=A'+D'=v
B+C=B'+C'=u
ρ=uv-Au-Bv=-Au+Cv=-Bv+Du.
```

---

# 11. M2.5 — CROSS-LAYER / ACTUAL PF FIREWALL

prove

```math
α=A-A'>0
β=B-B'>0
```

and

```math
w=αu+βv
A'=A-α>0
B'=B-β>0
C'=C+β
D'=D+α.
```

tag:

```text
CROSS-LAYER
```

BRIDGEによってraw rowsがactual PF rowsへ対応することを、
単なるalgebraic rowではなくactual provenance付きでformalizeする。

特に

```math
c_x-m,
c_y-m,
c'_x-m,
c'_y-m ∉ Γ
```

tag:

```text
ALL-AP
```

を維持。

さらに

```math
q_x+m,
q_y+m ∈ H
```

tag:

```text
QM
```

を証明。

この部分では

```text
signed identity
≠
actual factorization
```

のM1 firewallを厳守する。

---

# 12. M2.6 — COMPLETE SPLIT

write

```math
m=ew+dμ,\quad 0≤e<d,
```

with `μ∉T`.

set

```math
ℓ=d-1-s
k0=floor((ℓ+e)/d) ∈ {0,1}
θ=μ+k0 w.
```

QMと2GIから

```math
θ-u-v ∈ T
```

or

```math
θ-ρ-u-v ∈ T.
```

tag:

```text
SPLIT
```

両branchがoverlapしてもよい。
排他的ORを勝手に要求しない。

---

# 13. M2.7 — BRANCH I

Formalize the same stable walk.

```math
θ=L=u+v+t0
```

derive

```math
k0=1,
κ=d-e,
m=dL-κw,
E=w-L>0.
```

Define exact integer sequences:

```math
c_n
j_n
τ_n
```

and establish

```math
FS ↔ τ_n∈T
```

for required range.

Formalize all four required hit sets:

```text
Ux
Uy
Zx
Zy
```

and prove **four-hit necessity** from the same actual PF data and same walk.

Do not introduce generic connectivity.

Then formalize:

```text
later-return LOWER
first-return exception
X-only
Y-only
XY
```

Important:

the predecessor constraint valid for `N>1`
must NOT be applied at `N=1`.

This is an explicit source firewall.

Conclude:

```text
Branch I impossible.
```

---

# 14. M2.8 — BRANCH II / k0=1

Formalize:

```math
θ=ρ+u+v+t0,
k0=1.
```

prove the auxiliary positivity

```math
g=w-u-v-t0>0.
```

This inequality must not be assumed.

Use actual D-row backward points.

If a backward point belongs to H,
use K + CAN + ALL-AP to contradict actuality.

Thus both points are H-gaps.

Apply two-generator symmetry and 2GI and derive

```math
θ-u-v∈T.
```

Hence reduce to Branch I.

No circular reference:
Branch I theorem must already be proved independently.

---

# 15. M2.9 — BRANCH II / k0=0, e=0

Formalize directly:

```math
θ=μ∉T
m=dθ
0<θ<min(u,v)
```

and

```math
τ1=2θ-u-v-t0<0.
```

Contradict FS.

---

# 16. M2.10 — BRANCH II / k0=0, e>0

Formalize the complete cross-core argument.

Define

```text
P,R,Q,S
k=d-s
c_n
τ_n
λ_n
ε_n
Y_n
```

prove:

```math
θ=-Pu+Qv=Su-Rv<0
```

and PHASE:

```math
(e-1)w < d h0 < d w/2
2e ≤ d+1.
```

prove COMP:

```math
Y_n+τ_n = D u - ε_n w.
```

Use ALL-AP to get

```math
Y_n∉T
```

for every required `n≥1`.

Then split

```text
ε_n=0
ε_n=1
```

exactly as source.

In `ε_n=1`, preserve the arithmetic proof that

```text
c_{n-1}=c_n
```

before using the previous stable point.

Conclude

```math
a_x-y+n m ∈ H
```

for all required n,

hence

```math
a_x-y∈K,
```

therefore by GAP-K

```math
q_x+y∉Γ,
```

contradicting actual PF property

```math
q_x+y∈Γ.
```

Thus Branch II is fully excluded.

---

# 17. FINAL INTERNAL CONCLUSION

From RAW4 contradiction:

```text
not all four raw minima can survive in Apéry.
```

Using TYPE-BRIDGE conclude

```math
t(Γ) ≤ 4.
```

If STD_SYM_GLUE was fully formalized/bridged, expose:

```lean
theorem symmetric_tail_type_le_four ...
```

with publication-equivalent hypotheses.

Status:

```text
M2 S3 CANDIDATE FOR TRUE AUDIT
```

If STD_SYM_GLUE remains open, expose only the conditional theorem and status:

```text
M2A INTERNAL SYMMETRIC CLOSURE CANDIDATE FOR TRUE AUDIT

STD_SYM_GLUE OPEN
FULL S3 OPEN
```

---

# 18. CRITICAL FORMALIZATION FIREWALLS

Throughout M2:

## Actuality

actual semigroup membership must arise from
nonnegative coefficient witnesses.

## Signed relations

signed algebraic equalities must never automatically imply membership.

## Same element

replacement must occur inside the explicitly named actual factorization.

## Symmetry

`H symmetric` must have an explicit Lean meaning.
Do not use the English word as an uninterpreted Prop unless Gate 0 is explicitly still open.

## Local notation

Section 3 symbols

```text
T,A,B,C,D,P,Q,R,S
```

are local to the symmetric branch.

Do not identify them with later nonsymmetric canonical coefficients.

## No hidden finite search

Branch closures must be symbolic over the full parameter range.

---

# 19. SUGGESTED MODULE LAYOUT

Do not modify M1 modules.

Suggested additions:

```text
P21/Symmetric/
  TwoGenerator.lean
  Symmetry.lean
  GlueNormalForm.lean
  StableCore.lean
  TypeBridge.lean
  Raw4.lean
  BranchI.lean
  BranchII.lean
  Closure.lean
```

Possible external-input separation:

```text
P21/External/
  SymmetricThreeGenerator.lean
```

Verification:

```text
verification/M2StatementCheck.lean
verification/M2AxiomCheck.lean
```

Adapt if a cleaner architecture emerges.

---

# 20. TEST-DRIVEN / REGRESSION REQUIREMENTS

For delicate interfaces, add compile-time regression examples or
small theorem tests where practical.

At minimum protect:

```text
2GI
exact TYPE-BRIDGE
SPLIT is non-exclusive
N=1 predecessor exception
signed ≠ actual
STD_SYM_GLUE is not an axiom
```

Do not create tests by weakening the theorem.

---

# 21. BUILD / DEBT / AXIOM CHECK

Before final output run fresh:

```bash
lake build
```

Then inspect project-owned source for:

```text
sorry
admit
axiom
sorryAx
unsafe
unjustified opaque declarations
```

Generate `#print axioms` report for all new M2 theorem declarations.

Allowed standard axioms remain only those already accepted at M1:

```text
propext
Classical.choice
Quot.sound
```

Any project-specific axiom means candidate FAIL.

---

# 22. FROZEN-M1 INTEGRITY CHECK

Machine-check at the end:

```text
all M1 protected files byte-identical
to commit
9464b9cd3b6b070f9fa6d1c212f27065d1eb84b3
```

Produce:

```text
M1_FROZEN_INTEGRITY_REPORT.txt
```

If any protected file changed:

```text
M2 NOT ELIGIBLE FOR TRUE AUDIT
```

unless the user explicitly starts an M1 repair/re-audit cycle.

---

# 23. REQUIRED ARTIFACT

Return one ZIP only.

If full S3 closes:

```text
P21_LEAN_M2_SYMMETRIC_TAIL_S3_CANDIDATE_YYYYMMDD.zip
```

If only internal closure closes:

```text
P21_LEAN_M2A_INTERNAL_SYMMETRIC_CLOSURE_CANDIDATE_YYYYMMDD.zip
```

Include:

```text
complete Lean project
all new M2 .lean files
README.md
SOURCE_OF_TRUTH.md
M2_DEPENDENCY_DAG.md
M2_STATEMENT_MAP.md
MATHLIB_SYM_GLUE_SEARCH.md
M1_FROZEN_INTEGRITY_REPORT.txt
BUILD_LOG.txt
AXIOM_REPORT.txt
PROOF_DEBT_REPORT.txt
CODEX_SELF_CHECK.md
NEXT_RESTART.md
```

If STD_SYM_GLUE is open, also include:

```text
STD_SYM_GLUE_OPEN.md
```

with:

```text
exact desired Lean statement
mathlib search result
what is proved conditionally
minimal remaining proof obligation
recommended next attack
```

---

# 24. STATUS LANGUAGE

Codex must not say:

```text
TRUE AUDIT PASS
FROZEN
AUDITED
```

Allowed final status only:

full:

```text
M2 S3 CANDIDATE FOR TRUE AUDIT
```

or partial:

```text
M2A INTERNAL SYMMETRIC CLOSURE CANDIDATE FOR TRUE AUDIT
STD_SYM_GLUE OPEN
```

---

# 25. FINAL REPORT — JAPANESE

User-visible reportは日本語。

最低限:

```text
1. Gate 0 / STD_SYM_GLUE status
2. TwoGenerator facts status
3. StableCore / GAP-K status
4. BRIDGE / TYPE-BRIDGE status
5. RAW4 status
6. Branch I status
7. Branch II各subcase status
8. final S3 or conditional closure status
9. lake build
10. proof debt
11. axiom report
12. M1 frozen integrity
13. remaining OPEN
14. TRUE AUDITへ渡す単一ZIP
```

を報告する。

---

# 26. PRIORITY POLICY

最優先は

```text
formal correctness
>
source-faithfulness
>
scope completeness
>
full S3 closure
>
code elegance
```

である。

STD_SYM_GLUEが大きすぎる場合に、
axiom化してfull S3を偽装するより、

```text
internal S3 closure complete
+
one exact external bridge OPEN
```

として返す方を正解とする。

M1/C2はFROZEN入力として再証明しない。
