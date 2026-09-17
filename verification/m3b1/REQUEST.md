# P21 LEAN FORMALIZATION — M3B1 MINBOX / WHITE CLOSURE

このスレッドでは、数値半群 Problem 21 の Lean 形式化を、最新の TRUE-AUDITED / FROZEN state から継続する。

今回の唯一の主目標は

$$
\boxed{\textbf{M3B1 — MINBOX / WHITE}}
$$

すなわち

```lean
P21.Nonsymmetric.ColorCap.MinimumOneStatement
```

を**無条件の Lean theorem として完全に証明すること**である。

`BoxPositiveExitStatement` / DPE は今回の対象外とする。

---

# 0. AUTHORITATIVE BASELINE

Repository:

```text
https://github.com/stksk310/Problem21Lean
```

今回の作業は必ず次の TRUE-AUDITED M3A commit から開始すること。

```text
M3A_FROZEN_COMMIT:
258d74ac941796c62bb45cc177f22a7396319413
```

推奨 branch:

```text
m3b1-minbox-white
```

main へ merge しないこと。

このcommitについて、以下は TRUE AUDIT PASS / FROZEN として扱い、再証明・再設計しない。

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
```

M3A内では特に以下がFROZENである。

```text
STD_HERZOG
primitive generator formulas
six-arm atlas
critical-box uniqueness
integer-kernel basis
matched-pair package
equal-level synchronization
same-color / mixed-color local geometry
three-singleton theorem
PATH exact input
TYPE II exact input
CHAIN exact input
conditional selected-four classification
```

現在残る数学的 obligations は正確に

```text
ColorCap.MinimumOneStatement
ColorCap.BoxPositiveExitStatement
```

の2本。

今回は前者だけを閉じる。

---

# 1. FROZEN SOURCE PROTECTION

M3B1では、原則として

```text
258d74ac941796c62bb45cc177f22a7396319413
```

に存在する既存 Lean source を**一切変更してはならない**。

特に以下を編集しないこと。

```text
P21/Nonsymmetric/ColorCap/ActualMinimum.lean
P21/Nonsymmetric/ColorCap/Residuals.lean
P21/Nonsymmetric/ColorCap/RelativeLattice.lean
P21/Nonsymmetric/ColorCap/WhiteCertificates.lean
P21/Nonsymmetric/PrimitiveGenerators.lean
P21/Nonsymmetric/HerzogData.lean
```

その他の M1 / M2 / M3A source もすべて immutable とする。

必要な証明は**新規moduleを追加することで行う**。

既存FROZEN sourceの変更が本当に不可避と判断した場合は、勝手に変更せず、

```text
M3A FROZEN API EXTENSION REQUIRED
```

として正確な理由を報告すること。

---

# 2. SOURCE OF TRUTH

以下をこの順に確認すること。

```text
reference_inputs/P21_Journal_of_Algebra_Submission_Manuscript_FINAL_20260916.pdf
reference_inputs/P21_FINAL_FROZEN_VERIFICATION_EDITION_20260907.zip

verification/m3/source/appendixB-readable.md
verification/m3/source/frozen-color-cap.md
verification/m3/REVIEW_CORRECTION_MINBOX.md

P21/Nonsymmetric/ColorCap/Residuals.lean
P21/Nonsymmetric/ColorCap/ActualMinimum.lean
P21/Nonsymmetric/ColorCap/RelativeLattice.lean
P21/Nonsymmetric/ColorCap/WhiteCertificates.lean
P21/Nonsymmetric/PrimitiveGenerators.lean
P21/Nonsymmetric/Kernel.lean
P21/Nonsymmetric/RowAtlas.lean
P21/Nonsymmetric/HerzogData.lean
```

publication / frozen verification の数学を authoritative とする。

ただしLean上の既存FROZEN theoremは再実装せず利用してよい。

---

# 3. EXACT TARGET

現在のFROZEN定義は次である。

```lean
def MinimumOneStatement : Prop :=
  ∀ (g : Generators) (_s : g.Setting)
    (_hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (D : HerzogCriticalData g) (colorA : Bool)
    (k : ℕ) (p : Point),
    0 < k →
    (∀ i, 1 ≤ p i ∧
      p i < (if colorA then (D.a i : ℤ) else (D.b i : ℤ))) →
    (if colorA then D.fA else D.fB) =
      (k : ℤ) * g.m + ∑ i, (p i - 1) * g.n i →
    (∀ k' : ℕ, ∀ x' : Fin 3 → ℕ,
      (if colorA then D.fA else D.fB) =
        (k' : ℤ) * g.m + value g.n x' →
      k ≤ k') →
    k = 1
```

最終的に、新規module内で少なくとも

```lean
namespace P21.Nonsymmetric.ColorCap

theorem minimum_one_proved :
    MinimumOneStatement := by
  ...

end P21.Nonsymmetric.ColorCap
```

に相当する theorem を得ること。

名前は多少変更してよいが、statementは**既存 `MinimumOneStatement` そのもの**でなければならない。

追加仮定は禁止。

特に次を追加してはならない。

```text
gcd n₁ n₂ n₃ = 1 を新規仮定
pairwise coprime
det C = ...
White-class data
width-one functional
existence of r,q
simplex emptiness
actual arm hypotheses
PF hypotheses
```

これらが必要なら、現在の `MinimumOneStatement` の既存仮定とFROZEN theoremから導出すること。

---

# 4. CRITICAL CORRECTION — PRIMITIVE TAIL

旧版 `MinimumOneStatement` にはtail primitivityが欠けており、counterexampleが存在した。

これはすでに修正済みで、現在のstatementには

```lean
_hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H
```

が含まれている。

この仮定を正しく使用すること。

特に、

```text
integer-kernel saturation
```

と

```text
gcd(n₁,n₂,n₃)=1 / primitive weight vector
```

を同一視してはならない。

必要なprimitivityは `hcof` から導出する。

既存FROZEN theorem

```lean
tail_bezout_vector
primitive_generator_minors
primitive_generator_formulas
```

を最大限利用すること。

`tail_bezout_vector hcof` は整数vector \(v\) で

$$
v\cdot n=1
$$

を与えるため、この部分を新たなaxiomにしてはならない。

---

# 5. MATHEMATICAL PROOF ROUTE

publication Appendix B の MINBOX proof を Lean 化する。

主ルートは以下。

## Phase A — common setup

`colorA` で場合分けする前に可能な限り共通部分を作る。

入力

$$
f=f_\varepsilon
=
km+\sum_i(p_i-1)n_i,
\qquad
1\le p_i<\alpha_i,
$$

および `k` のactual minimalityを受け取る。

`k=1` が目標。

反対に

$$
k\ge2
$$

と仮定して矛盾を導く。

`D.fA`, `D.fB` がtail gapであることなど、必要な性質はM3AのHerzog packageから導出すること。

---

## Phase B — socle simplex / relative lattice

publication Appendix B.1.3 に従う。

socle row matrix \(U_\varepsilon\) をFROZEN atlasから取得する。

$$
s=f_\varepsilon+n_1+n_2+n_3.
$$

rowsを \(R_1,R_2,R_3\) とし、

$$
C=U-\mathbf1p^T,
\qquad
c_i=R_i-p.
$$

を構成する。

次をLeanで証明する。

$$
Cn=km\mathbf1.
$$

primitive generator formulasを用いて必要なdeterminant identityを得る。

$$
\det C=km.
$$

relative lattice

$$
L_d=\{z\in\mathbf Z^3:z\cdot n\equiv0\pmod d\}
$$

について、tail primitivityから

$$
[\mathbf Z^3:L_d]=d
$$

に相当する正確なLean statementを証明する。

さらに必要な範囲で

$$
\operatorname{row}_{\mathbf Z}C=L_{km},
\qquad
L_m/L_{km}\cong\mathbf Z/k\mathbf Z
$$

を形式化する。

完全な抽象群論を導入する必要はない。

後段のWhite-class constructionに必要な**正確なspecialized consequenceだけ**でもよい。

---

## Phase C — empty tetrahedron

$$
\Delta=\operatorname{conv}(p,R_1,R_2,R_3)
$$

が affine lattice \(p+L_m\) に関してemptyであることを証明する。

sourceの論理をそのまま守る。

lattice point \(u\) のlevel

$$
\ell=\frac{s-u\cdot n}{m}
$$

について、

```text
0 < ell < k
```

なら coefficientwise positivity から、同じactual element \(f\) のより小さい正の m-level factorizationを作り、`hmin` に反する。

```text
ell = k
```

なら \(u=p\)。

```text
ell = 0
```

かつtop faceのnonvertexなら、socle rowsのzero-coordinate patternから \(u>0\) を導き、

$$
f\in H
$$

となることに反する。

ここでも、

```text
signed equality → actual membership
```

という飛躍は禁止。

actual membershipへ移る際には、全係数の非負性を明示すること。

既存

```lean
lower_companion_impossible
top_face_positive_impossible
positive_companion_failure
```

等を再利用してよい。

---

# 6. STD_WHITE GATE

publicationで唯一ここに新規に入るstandard external theoremはWhiteのempty lattice tetrahedron theoremである。

必要な内容は、

```text
empty lattice tetrahedron has lattice width one
```

から、4頂点がwidth-one planesによって2+2に分離されること。

## 禁止事項

次は禁止。

```lean
axiom STD_WHITE ...
```

```lean
theorem white ... := by sorry
```

```lean
opaque white ...
```

または、Whiteの結論をstructure fieldとして入力させること。

## 実行順

まず pinned mathlib `v4.34.0-rc1` を検索し、

```text
White
empty lattice simplex
lattice width
primitive affine functional
integer simplex
unimodular simplex
```

に相当する既存 theorem/API が利用できるか調査する。

結果を

```text
MATHLIB_WHITE_SEARCH.md
```

に保存すること。

### Route W1 — mathlib theorem exists

十分な theorem があるならbridgeを証明して使用する。

### Route W2 — direct internal proof

mathlibにない場合、Whiteの必要部分をLean内で証明する。

全文一般化が過剰なら、P21で実際に必要なspecialized theoremまで弱めてよい。

例えば、

```text
empty relative-lattice tetrahedron
+ relative volume k >= 2
+ cyclic quotient / primitive lattice input
```

から、

```text
適切なrow permutation後、
(p,R1) と (R2,R3) を分離するwidth-one functionalが存在
```

あるいは後段で完全に等価な

```text
White-class parameter r の存在
```

を直接導いてもよい。

ただしその theorem 自体を**Leanで証明すること**。

### Route W3 — alternative proof of MINBOX

White theoremを経由せず、既存のHerzog/kernel/relative-lattice arithmeticから直接 `MinimumOneStatement` を証明できるなら、それも許可する。

この場合、

```text
M3B1_ALTERNATIVE_PROOF_NOTE.md
```

に、

* publicationのWhite routeとの対応
* どの theorem を置換したか
* hidden stronger hypothesisがないこと

を記録する。

---

# 7. WHITE CLASS DATA

source routeを使う場合、`k ≥ 2` から以下を導く。

White width-one splitをrow permutationで

$$
(p,R_1)\mid(R_2,R_3)
$$

に正規化する。

class \(1\) representativeについて

$$
\theta_1
=
(1/k,\ r/k,\ (k-r)/k),
\qquad
1\le r<k.
$$

さらに

$$
\gcd(r,k)=1.
$$

\(q\) と \(\ell\) を

$$
1\le q<k,
\qquad
rq=1+\ell k
$$

で選ぶ。

次のvectorsのintegralityを得る。

$$
z=
\frac{R_1+r(R_2-R_3)-p}{k},
$$

$$
z_q=qz-\ell(R_2-R_3).
$$

必要なら既存relative-lattice APIを拡張する新規moduleを作ってよい。

---

# 8. SIX COMPANIONS

class \(j\) と \(k-j\) のlower companionsについて、既存FROZEN theorem

```lean
six_companion_failures
```

を利用する。

6 vectors のどれも coefficientwise strictly positive ではないことを、actual minimalityから得る。

この部分を新規axiomやabstract failure flagに置き換えないこと。

---

# 9. COLOR A CLOSURE

Appendix B.1.5–B.1.6 をLean化する。

White class dataから

$$
z=(-X,Y,Z)
$$

の正確な式を導く。

6 companion failuresをsource記載順に使用し、

$$
p_1\le X\le b_1,
\qquad
0\le Y\le b_2-p_2,
\qquad
a_3\le Z\le\rho_3-p_3
$$

を得る。

\(z_q\) にも対応するboundsを得る。

integralityを使って

$$
b_1=(k-q)p_1+ku,
$$

$$
b_2=p_2+(r-1)a_2+ky,
$$

$$
b_3=qp_3+(k-q-1)a_3+kv
$$

with

$$
u,y,v\ge0
$$

を導く。

その後は既存FROZEN theorem

```lean
colorA_parameter_contradiction
```

を使用し、`k ≥ 2` を矛盾させる。

既に証明済みのmultiplicity certificateを再証明しないこと。

---

# 10. COLOR B CLOSURE

Appendix B.1.7 の対応するcolor B argumentを完全Lean化する。

sourceのnatural row orderingを厳密に守ること。

White dataからcolor B用 \(z,z_q\) の式と6 companion inequalitiesを導出し、publicationのBP parametrizationを証明する。

その後は既存FROZEN theorem

```lean
colorB_parameter_contradiction
```

を用いて `k ≥ 2` を矛盾させる。

A/Bを「対称だから同様」で飛ばしてはならない。

既存にrigorous color-reversal theoremがあり、statement上完全に適用可能なら使用してよいが、そうでなければB branchを明示的に証明すること。

---

# 11. FINAL MINBOX THEOREM

両colorを統合して、

```lean
theorem minimum_one_proved :
    MinimumOneStatement
```

を得る。

そのうえで、新規module内に次のwrapperも作ることを推奨する。

```lean
theorem three_arms_impossible_of_dpe
    (hdpe : BoxPositiveExitStatement)
    ... :
    False :=
  three_arms_impossible_of_residuals
    minimum_one_proved hdpe ...
```

正確な引数列は既存 theorem に合わせること。

このwrapperによりM3B1終了時のresidual frontierを

```text
BoxPositiveExitStatement only
```

まで縮約する。

ただし、

```text
unconditional COLOR-CAP
FULL G4
```

をこの段階でCLOSEDと呼んではならない。

---

# 12. SUGGESTED NEW MODULES

既存FROZEN fileを編集せず、例えば以下のような構成を推奨する。

```text
P21/Nonsymmetric/White/
  RelativeIndex.lean
  EmptyTetrahedron.lean
  WidthOne.lean
  ClassData.lean

P21/Nonsymmetric/ColorCap/MinimumOne/
  Setup.lean
  SocleSimplex.lean
  WhiteClass.lean
  ColorA.lean
  ColorB.lean
  Closure.lean

P21/Nonsymmetric/ColorCap/MinimumOneProof.lean
```

これは推奨であり、数学的に自然なら分割は変更可。

ただし巨大な1ファイルにすべて詰め込まないこと。

---

# 13. FORMALIZATION FIREWALLS

以下を絶対に守る。

### Actuality firewall

actual factorization coefficientは \(\mathbb N\)。

signed relation / lattice vectorは \(\mathbb Z\)。

整数等式だけからmembershipへ飛ばない。

### SAME-ELEMENT firewall

factorizationの係数を削る場合、必ず**同じactual elementの同じfactorization**上であることを明示する。

### Criticality firewall

Herzog criticalityはpure-\(H\) relationにのみ使用する。

### Primitive-tail firewall

kernel saturationをtail primitivityと混同しない。

tail primitivityは `hcof` から導く。

### Minimality firewall

`hmin` はactual \(\mathbb N\)-factorizationに対する最小 \(m\)-level。

signed lattice representativesには直接適用しない。

### White firewall

White conclusionを仮定・structure field・axiomとして埋め込まない。

### No finite-search substitution

今回の theorem は symbolic all-parameter theorem。

bounded search / enumeration / native_decide による有限確認で置換しない。

有限計算を補助sanity checkに使用するのはよいが、proof termは一般証明でなければならない。

---

# 14. TEST / VERIFICATION REQUIREMENTS

新規証明完成後、fresh verificationを実施する。

最低限、

```text
lake build
```

に加えて、全新規M3B1 modulesを明示targetしたbuildを実施すること。

さらに、

```text
sorry
admit
sorryAx
axiom
unsafe
unjustified opaque
```

をproject sourceに対してscanする。

`axiom` はコメント・検査コード等のfalse positiveを区別し、Lean declarationとしてのproject-specific axiomが0であることを確認する。

全新規declarationについて `#print axioms` 相当を生成する。

許容するlogical dependenciesは従来通り標準的な

```text
propext
Classical.choice
Quot.sound
```

の範囲。

project-specific axiomが1つでも出ればFAIL。

---

# 15. FROZEN REGRESSION

base

```text
258d74ac941796c62bb45cc177f22a7396319413
```

に対して、既存FROZEN sourceがbyte-identicalであることを検査する。

特に

```text
M1 original suite
M2A original suite
M2B original suite
M3A original suite
```

を再実行すること。

M3B1のために既存FROZEN theorem statementが変わっていないことを確認する。

最終reportには

```text
FROZEN_SOURCE_CHANGED: NO
```

を要求する。

---

# 16. GITHUB CI REPRODUCIBILITY GATE

local build成功だけで終了しない。

branchをGitHubへpushし、fresh GitHub Actions runnerでCIを通すこと。

推奨workflow名:

```text
P21 Lean M3B1 Audit
```

CIは最低限以下を実施する。

```text
exact commit checkout
Lean/Lake environment report
root lake build
M3B1 explicit module build
M1 regression
M2A regression
M2B regression
M3A regression
proof-debt scan
new-declaration axiom scan
frozen-source integrity
candidate ZIP SHA-256 verification
```

Actions cacheを使用する場合も、project `.olean` を検証の代替にしてはならない。

最終artifact名:

```text
P21_M3B1_TRUE_AUDIT_EVIDENCE
```

artifact metadataとして

```text
workflow run ID
attempt
head SHA
artifact ID
artifact digest
candidate ZIP SHA-256
```

を報告すること。

---

# 17. DELIVERABLE

成功時は単一ZIP:

```text
P21_LEAN_M3B1_MINBOX_WHITE_CANDIDATE_20260917.zip
```

を返す。

ZIPには最低限以下を含める。

```text
complete Lean project
all new M3B1 Lean modules

README_M3B1.md
SOURCE_OF_TRUTH_M3B1.md
M3B1_DEPENDENCY_DAG.md
M3B1_STATEMENT_MAP.md
M3B1_PROOF_ROUTE.md
MATHLIB_WHITE_SEARCH.md

FROZEN_SOURCE_INTEGRITY_REPORT_M3B1.txt
BUILD_LOG_M3B1.txt
AXIOM_REPORT_M3B1.txt
PROOF_DEBT_REPORT_M3B1.txt
REGRESSION_REPORT_M3B1.txt
CODEX_SELF_CHECK_M3B1.md
NEXT_RESTART.md
```

CI evidenceはGitHub Actions artifactとして別に生成してよいが、最終チャットでは候補ZIPは1個だけ返すこと。

---

# 18. PARTIAL-SUCCESS POLICY

White theoremの完全形式化などで時間切れになっても、成果を捨てないこと。

その場合は、

```text
P21_LEAN_M3B1A_MINBOX_WHITE_PARTIAL_CANDIDATE_20260917.zip
```

として納品する。

必ず、

```text
THEOREM_OR_BEST_REDUCTION.md
EXACT_OPEN_OBLIGATION.md
NEXT_RESTART.md
```

を含める。

残余を「Whiteが必要」だけで曖昧にしない。

例えば、

```text
White width-one theoremそのもの
2+2 split
theta class normalization
r/q inverse construction
Color A inequalities
Color B inequalities
```

のどこまでLeanで閉じ、最初の未証明Lean statementが何かを正確に示す。

---

# 19. STATUS LANGUAGE

Codex自身は監査者ではない。

したがって最終報告で

```text
TRUE AUDIT PASS
FROZEN
AUDITED
```

とは言わないこと。

完全成功なら

```text
M3B1 MINBOX / WHITE CANDIDATE FOR TRUE AUDIT
```

とする。

部分成功なら

```text
M3B1A MINBOX / WHITE PARTIAL CANDIDATE FOR TRUE AUDIT
```

とする。

---

# 20. SUCCESS CRITERION

今回の最終成功条件はただ一つ。

$$
\boxed{
\texttt{MinimumOneStatement}
\text{ が追加数学仮定0・project axiom 0で証明される}
}
$$

さらに理想的には、

$$
\boxed{
\text{M3 residual frontier}
=
\texttt{BoxPositiveExitStatement only}
}
$$

まで縮約する。

DPEを今回ついでに攻撃してscopeを広げないこと。

MINBOX / WHITEを完全に閉じたところで止め、candidateをパッケージして返すこと。

優先順位は

```text
formal correctness
>
source-faithful statement
>
actuality / primitivity firewalls
>
reproducibility
>
proof elegance
>
speed
```

とする。
