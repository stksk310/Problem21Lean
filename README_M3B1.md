# M3B1 MINBOX / White candidate

**M3B1 MINBOX / WHITE CANDIDATE FOR TRUE AUDIT**

The exact preexisting proposition is now proved:

```lean
P21.Nonsymmetric.ColorCap.minimum_one_proved :
  P21.Nonsymmetric.ColorCap.MinimumOneStatement
```

There is no additional mathematical assumption. In particular, primitivity,
cyclic class data, coprimality and positive modular inverse are derived; no
actual arm or PF premise has been added to MINBOX. The required specialized
White consequence is proved internally by `White.cyclic_white_proved`.

`three_arms_impossible_of_dpe` supplies this proof to the unchanged M3A
three-arm reduction. The remaining M3 frontier is exactly
`BoxPositiveExitStatement`. DPE, unconditional COLOR-CAP and FULL G4 remain
open and were not attacked in this milestone.

All 96 preexisting Lean files are byte-identical to base
`258d74ac941796c62bb45cc177f22a7396319413`. Protection additionally covers old
verification sources/evidence, dependency pins, historical candidate archives
and their checksums: 233 files in total. New mathematics is in 16 modules.
The work stays on `m3b1-minbox-white`, with no main merge.

Read `M3B1_STATEMENT_MAP.md`, `M3B1_PROOF_ROUTE.md`, and
`M3B1_ALTERNATIVE_PROOF_NOTE.md` for exact scope. This is the specialized
arithmetic White consequence needed by MINBOX; a general real-lattice
tetrahedron width API is not claimed.

## Reproduction and evidence

Use the unchanged Lean toolchain and Lake manifest. In a Git checkout with the
base commit available, and with an empty project `.lake/build`, run:

```text
python3 verification/m3b1/verify.py --fresh
python3 ci/m3b1_audit.py suite
```

The first builds the root, every old module and every new module, checks the
exact theorem type, scans proof debt, and reports all new kernel declarations'
axioms. The second runs unchanged M1/M2A/M2B/M3A suites on four isolated source
copies, sharing only pinned third-party dependencies. Windows uses the existing
`verification/lake.ps1` wrapper automatically.

GitHub workflow `P21 Lean M3B1 Audit` adds exact ZIP/Git byte comparison and
fresh Linux execution. Artifact: `P21_M3B1_TRUE_AUDIT_EVIDENCE`.
The separate post-run `HANDOFF_RECEIPT_M3B1.json` binds commit, run attempt,
artifact digest, its internal file manifest and candidate ZIP SHA256.
The ZIP carries local evidence and full sources, not project build caches.

These checks and internal reviews support a candidate for external review;
they do not constitute an independent audit ruling.
