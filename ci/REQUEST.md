# P21 LEAN — M1 GITHUB CI REPRODUCIBILITY GATE

これは Numerical Semigroup Problem 21 Lean formalization project の

```text
M1 = FOUNDATION + C2
```

candidate に対する **TRUE AUDIT build gate** を閉じるための実行ミッションである。

数学を追加・変更するmissionではない。

現在のstatusは

```text
M1 CANDIDATE FOR TRUE AUDIT

SOURCE / STATEMENT / SCOPE / AXIOM / DEBT
independent audit: no FATAL or MATERIAL defect found

ONLY REMAINING AUDIT BLOCKER:
auditor-side fresh `lake build` could not be executed
because the audit sandbox had no Lean/lake toolchain.
```

したがって今回の目的はただ一つ。

```text
EXACT M1 candidate
→ GitHub repository
→ clean GitHub Actions environment
→ fresh lake build
→ independent CI evidence
```

を作ること。

---

# 0. INPUT

入力artifactは

`P21_LEAN_M1_FOUNDATION_C2_CANDIDATE_20260916.zip`

のみをauthoritative implementation inputとする。

ZIP内のLean sourceを数学的にrepair・refactor・simplifyしてはならない。

今回の原則は

```text
NO MATH CHANGE
NO STATEMENT CHANGE
NO PROOF CHANGE
NO DEPENDENCY CHANGE
```

である。

CIを成立させるための

* `.github/workflows/...`
* repository metadata
* CI scripts
* README追記

のみ追加してよい。

もし既存Lean sourceへの変更が不可避なら、作業を止めず、
変更理由とexact diffを明示し、

```text
M1 CI CANDIDATE — SOURCE CHANGED, RE-AUDIT REQUIRED
```

として返すこと。

source変更を黙って行ってはならない。

---

# 1. REPOSITORY TARGET

GitHubのユーザーアカウント上に新規repositoryを作成する。

推奨名:

```text
Problem21Lean
```

または既に存在する場合:

```text
P21Lean
```

repository名を勝手に衝突させないこと。

## Visibility

可能なら

```text
public
```

を優先する。

理由は、このrepositoryをChatGPT TRUE AUDIT threadから
GitHub connector / GitHub API経由で直接検査するため。

ただしユーザーの既存設定や明示的privacy preferenceによりpublic作成が不適切なら
privateでもよい。

privateの場合は、ChatGPT側GitHub connectorが当該repoを読めるよう
GitHub App access対象に含まれる必要がある。

---

# 2. EXACT SOURCE PRESERVATION

まずZIPを展開し、project treeを確認する。

Git repositoryへ入れるLean implementation filesについて、
candidate ZIPとのSHA-256 manifestを作る。

最低限、

```text
SOURCE_SHA256_BEFORE_GITHUB.txt
```

を作成し、

```text
path
sha256
```

を記録する。

GitHubへ追加するCI filesを除き、
candidate ZIP内の既存implementation filesが変化していないことを確認する。

特に以下は内容を変更しない。

```text
*.lean
lean-toolchain
lakefile.toml / lakefile.lean
lake-manifest.json
```

candidateに存在するものはそのまま保持する。

---

# 3. GITHUB ACTIONS

workflowを作成する。

推奨path:

```text
.github/workflows/lean-audit.yml
```

workflow名:

```text
P21 Lean M1 Audit
```

trigger:

```yaml
on:
  push:
  pull_request:
  workflow_dispatch:
```

---

# 4. CLEAN TOOLCHAIN SETUP

`lean-toolchain` に記載されたexact Lean versionを使う。

最新Leanへ勝手にupgradeしない。

mathlibその他dependencyも既存

```text
lake-manifest.json
```

で固定されたrevisionを使用する。

GitHub Actions runner上でelan / Lean / lakeをclean installし、
cacheがなくてもbuild可能な構成にする。

cacheを使用してもよいが、
audit jobには少なくともclean reproducibilityを損なわない形にする。

可能なら

```text
ubuntu-latest
```

を使用する。

---

# 5. REQUIRED CI JOBS

最低限次を一つのaudit workflow内で行う。

## A. environment report

記録:

```bash
uname -a
lean --version
lake --version
cat lean-toolchain
```

dependency stateも可能な限り記録する。

---

## B. fresh build

必須:

```bash
lake build
```

exit code 0でなければCI FAIL。

既存compiled artifactをrepositoryへcommitしてbuildを偽装してはならない。

`.lake/build` 等の生成物はcommitしない。

---

## C. proof debt scan

project-owned Lean source全体に対して少なくとも

```text
sorry
admit
axiom
sorryAx
unsafe
```

を検索する。

ただし

* comment
* documentation
* intentional string literals

によるfalse positiveを区別すること。

単純grepだけを最終判定にしない。

既存candidateに含まれるproof-debt verifierがあるなら、それも実行する。

project-specific proof debtを発見したらCI FAIL。

---

## D. axiom report

candidateが使用している既存checkerを実行するか、
同等以上の方法でM1 theorem declarationsに対するaxiom reportを生成する。

許容されるstandard Lean axioms:

```text
propext
Classical.choice
Quot.sound
```

これ以外のproject-specific axiomがあればCI FAIL。

reportを

```text
AXIOM_REPORT_CI.txt
```

としてartifact化できるようにする。

---

## E. scope / source integrity

candidate ZIP由来のimplementation sourceについて
SHA-256を再計算し、

```text
SOURCE_SHA256_AFTER_GITHUB.txt
```

を生成する。

BEFORE manifestと比較し、

```text
ALL ORIGINAL IMPLEMENTATION FILES IDENTICAL
```

をmachine-checkする。

GitHub Actions filesなど今回追加したファイルは比較対象外。

このcheckが失敗したらCI FAIL。

---

## F. existing verification suite

candidate内にself-check script / verification suiteがある場合はすべて実行する。

例:

```text
statement map verification
dependency check
source-map consistency
proof-debt report
axiom checker
distribution-copy verification
```

実際に存在するscriptを確認し、
READMEの自己申告だけを根拠にしない。

---

# 6. CI ARTIFACT

workflow完了時に監査artifactをuploadする。

artifact名:

```text
P21_M1_TRUE_AUDIT_EVIDENCE
```

中身:

```text
BUILD_LOG.txt
ENVIRONMENT.txt
AXIOM_REPORT_CI.txt
PROOF_DEBT_REPORT_CI.txt
SOURCE_SHA256_BEFORE_GITHUB.txt
SOURCE_SHA256_AFTER_GITHUB.txt
SOURCE_INTEGRITY_REPORT.txt
VERIFICATION_SUITE_LOG.txt
COMMIT_SHA.txt
```

GitHub Actionsの通常job logだけでなく、
これらもartifactとして残す。

---

# 7. REPOSITORY DOCUMENTATION

repository root READMEに

```text
STATUS: M1 CANDIDATE FOR TRUE AUDIT
```

と書く。

まだ

```text
FROZEN
TRUE AUDIT PASS
AUDITED
```

とは書いてはならない。

明記する:

```text
M1 scope:
FOUNDATION + C2 only

OPEN:
symmetric tail
nonsymmetric classification
PATH
TYPE II
CHAIN
external structure theorems
Euclidean descent
715-term certificate
3234-term certificate
main theorem proof
```

---

# 8. GIT HISTORY

初回commitはできるだけ単純にする。

推奨:

```text
Import P21 Lean M1 FOUNDATION+C2 candidate
```

CI追加を別commitにするなら:

```text
Add reproducibility and audit CI
```

最終的にTRUE AUDITへ渡す対象commitを一つ明示する。

重要:

```text
AUDIT_TARGET_COMMIT=<40-char SHA>
```

を最終報告に記載する。

branch:

```text
main
```

でよい。

---

# 9. RUN THE CI

push後、

```text
P21 Lean M1 Audit
```

workflowが実際に走ることを確認する。

全jobがsuccessになるまで確認する。

ただしsource codeを修正してbuildを通してはいけない。

CI configだけの問題ならCI configを修正して再runしてよい。

Lean source変更が必要になった場合は、

```text
SOURCE CHANGE DETECTED
RE-AUDIT REQUIRED
```

として終了する。

---

# 10. NO SELF-AUDIT CLAIM

CodexはCI成功後も

```text
TRUE AUDIT PASS
FROZEN
```

を宣言してはならない。

許容statusは

```text
M1 CI REPRODUCIBILITY EVIDENCE READY FOR TRUE AUDIT
```

のみ。

---

# 11. REQUIRED FINAL REPORT

ユーザー可視報告は日本語。

必ず以下を返す。

```text
1. GitHub repository URL
2. visibility
3. default branch
4. exact AUDIT_TARGET_COMMIT SHA
5. workflow run URL
6. workflow run ID
7. lake build exit result
8. Lean version
9. proof debt result
10. axiom result
11. source-integrity result
12. source変更の有無
13. CI artifact名
14. TRUE AUDITへ渡す次の情報
```

特に最後はコピーしやすい形で

```text
REPOSITORY:
AUDIT_TARGET_COMMIT:
WORKFLOW_RUN:
WORKFLOW_RUN_ID:
CI_ARTIFACT:
SOURCE_CHANGED: NO
```

を出す。

---

# 12. SUCCESS CONDITION

今回のmissionの成功条件は数学的closureではない。

以下が全部成立すること:

```text
exact candidate source preserved
+
GitHub commit fixed
+
clean GitHub Actions environment
+
fresh lake build exit 0
+
proof debt check clean
+
axiom check clean
+
source-integrity check clean
+
workflow evidence externally inspectable
```

成立した場合のみ

```text
M1 CI REPRODUCIBILITY EVIDENCE READY FOR TRUE AUDIT
```

として終了する。

その成果をCommander / TRUE AUDIT control threadへ返すこと。
