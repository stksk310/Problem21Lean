# Next restart

STATUS: M2A INTERNAL SYMMETRIC CLOSURE CANDIDATE FOR TRUE AUDIT
STD_SYM_GLUE OPEN
FULL S3 OPEN

1. Independently inspect this exact ZIP, the final theorem hypotheses, source map,
   build/debt/axiom evidence, and all thirteen M1 protected hashes.
2. The internal theorem is `P21.Symmetric.symmetric_tail_from_glue_data`.
   Do not re-prove M1 and do not change its toolchain, lockfile, or sources.
3. To progress from M2A to full S3, prove the exact external direction documented
   in `STD_SYM_GLUE_OPEN.md`. Use the existing explicit data to invoke Closure.
4. Do not mark full S3 closed before that bridge and its independent audit.
   All nonsymmetric branches and both long certificates remain outside this scope.

Reproduction: `python3 verification/m2/verify.py` with the exact pinned Lean on PATH
(on Windows see the preserved path adapter and README). Default lake build is M1;
explicit M2 module builds in the verifier are mandatory.
