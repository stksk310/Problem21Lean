# M2A GitHub reproducibility gate

This is a CI-only addition to the exact 2026-09-17 candidate. It does not close
STD_SYM_GLUE or full S3 and it does not issue a TRUE AUDIT ruling.

Authoritative ZIP: `ci/candidate/P21_LEAN_M2A_INTERNAL_SYMMETRIC_CLOSURE_CANDIDATE_20260917.zip`

SHA-256: `7bab9f713b64411e6d79b2dcd42ed15fc5d27b3a9a8307da0ce93bfa7e1bd665`

`m2a-audit.yml` checks the ZIP hash and every embedded manifest entry, compares
all candidate files with the checkout and committed Git blobs, and independently
compares the 13 M1 files against Git commit
`9464b9cd3b6b070f9fa6d1c212f27065d1eb84b3`. README permits an append only; all
other candidate bytes are immutable. CI additions are outside that comparison.
Tracked Lean inventory must equal the candidate inventory exactly.

The clean Ubuntu runner installs elan v4.2.4 from its pinned SHA-256 archive and
reads the exact Lean version from lean-toolchain. Only pinned third-party binary
cache is obtained. Project build artifacts must be absent before `lake build`.
Every non-M1 P21 module is enumerated recursively from the ZIP and explicitly
built, including modules outside the suggested Symmetric/External directories.

The unmodified candidate lexer and scanner tests, original M2 axiom checker and
original verifier are mandatory. The verifier runs in a separate exact ZIP copy
with only third-party packages shared. It regenerates its own reports/inspection
files there, compiles all original regressions, and leaves the checked-out
candidate untouched. Original-suite logs are included alongside separate CI logs.
Scope checks inspect actual Lean output and the unchanged implementation; they
do not replace the user-reported independent mathematical source audit.

The legacy M1 workflow still performs its original checks on M1/main refs.
Its job is skipped only on the two named M2 audit branches (including PR heads),
because an exact M1-only inventory cannot accept the deliberately added M2 files.
The M2 workflow independently checks the frozen M1 files and root build on the
same audited checkout. No main merge is performed by either workflow.

All evidence is uploaded as `P21_M2A_TRUE_AUDIT_EVIDENCE`, including failures.
Only a successful workflow with complete RESULTS.json and matching final hashes
qualifies as `M2A CI REPRODUCIBILITY EVIDENCE READY FOR TRUE AUDIT`.
The local handoff receipt binds the commit, workflow run and attempt, artifact ID
and GitHub SHA-256 digest. It is created after downloading and checking evidence;
it is not precommitted because the run/artifact IDs do not yet exist.
