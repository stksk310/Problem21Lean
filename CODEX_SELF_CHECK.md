# M2A self-check record

STATUS: M2A INTERNAL SYMMETRIC CLOSURE CANDIDATE FOR TRUE AUDIT
STD_SYM_GLUE OPEN
FULL S3 OPEN

## Mathematical result

The complete internal theorem `P21.Symmetric.symmetric_tail_from_glue_data`
compiles. Its hypotheses are the unchanged M1 Setting, a Frobenius element,
CAN, and explicit SymmetricGlueData. No branch, hit, raw-minimum cardinality,
auxiliary positivity, or actual PF property is assumed in that public theorem.

The standard classification producing gluing data from symmetric tail semantics
is the sole missing input for full S3. It is an explicitly documented target Prop,
not a project axiom or a supplied proof. No later certificate was used.

## Verification actually executed

- Fresh separate project copy, initially without any project .olean files.
- `lake build`: exit 0, all frozen M1 modules compiled.
- Explicit build of all 16 new M2 modules: exit 0; includes Closure.
- 190 theorems, 39 definitions and 6 structures inventoried.
- Every one of the 229 theorem/definition roots checked by `#print axioms`.
  Observed only propext, Classical.choice and Quot.sound; zero project-specific axioms.
- 36 project-owned Lean files scanned lexically: zero forbidden code tokens.
- Full statement inspection and all six compile-time regression/check files: exit 0.
- Thirteen adversarial lexical-scanner unit tests: passed.
- All 13 protected M1 files match both the initial SHA256 baseline and Git blobs
  at 9464b9cd3b6b070f9fa6d1c212f27065d1eb84b3.
- All nine dependency checkouts match the unchanged manifest and have no tracked changes.
- Every Lean file in the fresh verification copy was byte-compared to the delivery source.

Only pinned third-party package artifacts were reused. M1 and M2 project artifacts
were compiled anew. No independent Linux/GitHub M2 execution is claimed; this fresh
build was performed on Windows with the pinned Lean toolchain.

## Regression boundaries

2GI and TYPE-BRIDGE retain their exact set/cardinality statements. A concrete
example permits both SPLIT conditions simultaneously. The signed witness for 1
in the (2,3) group is paired with a proof that no actual nonnegative factorization
exists. Branch I has an explicit stable first-return example where the later-return
LOWER condition fails at N=1. Branch II protects its own predecessor exception.
The finite examples test interfaces; the general closures are symbolic proofs.

## Internal review

Separate agent reviews checked the stable/gluing/Branch II arithmetic modules,
the exact bridge and actuality interfaces, and the final integration. No material
correctness or source-faithfulness issues were found. Review identified the missing
explicit statement E=w-L>0; it was added and compiled as
`BranchIRealization.difference_pos`. These reviews are implementation checks, not
an independent TRUE AUDIT ruling.

## Evidence

BUILD_LOG.txt, AXIOM_REPORT.txt, PROOF_DEBT_REPORT.txt,
M1_FROZEN_INTEGRITY_REPORT.txt, verification/m2/AXIOM_SUMMARY.json,
verification/m2/DECLARATIONS.json, verification/m2/STATEMENTS.txt,
verification/m2/REGRESSION_LOG.txt, verification/m2/FRESH_CHECK_RUN.txt,
verification/m2/FRESH_VERIFICATION_REPORT.json, verification/m2/DEPENDENCY_STATE.json.

The packaging script requires a successful fresh-verification report and verifies
all protected/source hashes, ZIP CRC and every ZIP entry before reporting success.
The ZIP manifest covers every file except the manifest itself.
