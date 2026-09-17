# Internal review of M3B1 verification gates

Date: 2026-09-17. This is an internal source review, not an independent
external audit ruling or a report that CI has finished.

Reviewed `verification/m3b1/verify.py`, `test_verify.py`,
`ci/m3b1_audit.py`, and `.github/workflows/m3b1-audit.yml` after the
archive-freeze, nested-manifest, and required-kernel-inventory hardening.
Also read the reused frozen M2/M2B lexer, inventory, axiom parser, process
runner, historical archive readers, the milestone JSON, and the exact
statement regression. No tests or builds were repeated for this review.
Packaging, finalization, and artifact-fetch code are outside this review.

## Conclusion for the current candidate

No blocking false-success path was identified in the reviewed workflow for
the current proof sources. Completion still requires an actual successful
fresh CI run and its recorded evidence; this source review does not replace
those checks.

## Gates checked

1. **Exact target.** `generate()` does not trust the success Boolean alone.
   Full success must name an explicit new required theorem, and the generated
   checker contains `example : P21.Nonsymmetric.ColorCap.MinimumOneStatement :=
   <named theorem>`. The checker is compiled before the success exit flag is
   recorded. `StatementRegression.lean` also checks this exact frozen target,
   the proved cyclic White statement, and the DPE-only wrapper.

2. **Kernel declarations and axioms.** Every new project proof module is
   explicitly built and imported. Kernel environment enumeration includes
   generated helpers under `P21.Nonsymmetric.`, then subtracts the exact
   1,327-name frozen inventory read from the frozen Git blob. Explicit new
   names must be in this delta. Every delta name gets `#print axioms`, and the
   inherited parser rejects missing roots, duplicate roots, warnings/errors,
   `sorryAx`, and dependencies outside `propext`, `Classical.choice`, and
   `Quot.sound`. `complete()` requires `kernel_inventory = PASS`; preflight's
   pending state cannot satisfy it. Inspection of current new modules found
   only the expected public namespace declarations, with no private/global
   instance, macro, elaborator, initialization, or source-side `run_cmd`
   bypass. The inventory `run_cmd` only reads the environment.

3. **Frozen sources and old suite inputs.** Protected paths are reconstructed
   from commit `258d74ac941796c62bb45cc177f22a7396319413`, not accepted from an
   editable manifest. Coverage includes the exact 96 baseline Lean files,
   all old `verification/` files, old CI Python/PowerShell files, historical
   candidate ZIPs and their SHA-256 receipts, and Lean/Lake configuration.
   Manifest equality and current bytes are checked against Git. A read-only
   `git diff` inspection found no changes in the protected tracked source
   paths. The candidate ZIP inventory and executable/configuration bytes
   must also match both committed Git blobs and the workspace.

4. **Fresh builds and historical regressions.** The main verifier's `--fresh`
   gate rejects project `.olean` files before running root, frozen-module,
   and explicit new-module builds. Each M1/M2A/M2B/M3A suite is extracted from
   its verified historical archive into a separate temporary tree. Each tree
   has no project build cache and shares only `.lake/packages`; the original
   archived verifier is run unchanged. Failed subprocesses raise immediately.
   The wrapper checks mathematical sources after the run, records a zero
   suite result only after success, and retains output and nested evidence.

5. **CI and evidence.** Checkout HEAD is compared with the event SHA. The
   workflow installs the pinned toolchain and checks the downloaded elan
   archive hash. Cache requests are restricted to discovered `Mathlib.*`
   modules; no project cache restore step exists. Dependency revisions and
   tracked-source cleanliness are checked before and after verification.
   Initialization resets required reports and results. Completion requires
   all four old-suite results, the fresh-build flag, axiom/debt/integrity
   gates, and nonempty module/dependency/declaration counts. Nested evidence
   manifests are themselves hashed; only the root manifest is excluded from
   its own hash list. The artifact upload can run after failure, but an
   uploaded failure artifact does not imply successful completion.

## Scope limits and nonblocking hardening opportunities

- The declaration coverage contract is namespace-based, not a general
  module-origin inventory. The explicit parser recognizes theorem/lemma/
  def/abbrev/structure/inductive forms; the kernel pass supplies generated
  names inside the agreed namespace. A future global anonymous `instance`
  or metaprogram-generated declaration outside that prefix would require
  extending the gate or prohibiting that syntax. No such source is present
  in this candidate. Do not describe the scanner as a universal Lean parser.

- Dependency cleanliness uses `--untracked-files=no`, so its automatic
  guarantee is exact revisions and unchanged tracked package files. It does
  not independently reject an added untracked third-party `.lean` file.
  This does not identify a current mismatch on the fresh GitHub runner,
  but a stronger reusable verifier could reject untracked package sources
  while allowing dependency build/cache outputs.

- The seven M3B1 unit tests cover the targeted parser/schema protections;
  they do not simulate the whole CI state machine. The executable workflow,
  exact-source checks, and fresh Lean/process results remain essential
  evidence rather than consequences of unit-test success alone.

## Delivery-script review addendum

The additional read-only review covers `finalize_local.py`, `package.py`,
and `fetch_and_verify.py` as first presented. No scripts were changed and
no functional runs were performed by this reviewer. The findings below
are action items communicated to the coordinator; the earlier conclusion
was limited to the verifier and CI workflow, not these delivery scripts.

### Findings requiring resolution before relying on delivery success

1. **Bind source hashes when checks run, not only afterward.**
   `finalize_local.py` accepts the existing successful `RESULTS.json` and
   only then hashes the current executable files into
   `LOCAL_VERIFICATION.json`. If a proof source or verification script is
   changed after the recorded checks and before finalization, the new bytes
   are incorrectly labeled as the checked snapshot. `package.py` compares
   against that newly taken map, so it cannot detect this interval. Record
   and compare the executable input map across the verification run, account
   explicitly for generated checker files, and require the finalizer to
   match that check-bound map. The eventual exact-source CI run remains a
   separate protection, but does not make the local claim accurate.

2. **Do not permit optimized Python to erase delivery validation.**
   The receiving script uses `assert` for its run, attempt, artifact digest,
   entry manifest, log, and theorem-result gates. Python `-O` or
   `PYTHONOPTIMIZE` removes these statements and can emit a success receipt
   without those checks. Use explicit raising checks, or reject an optimized
   interpreter with an ordinary `if` before any delivery actions.

3. **Prevent stale extracted evidence from filling missing ZIP entries.**
   `ci-evidence-<run>` is opened with `exist_ok=True`, then the downloaded ZIP
   is extracted into it. Manifest coverage is compared with the resulting
   filesystem. A matching stale file can therefore supply an entry missing
   from the downloaded ZIP. Require an empty destination, use a fresh
   temporary directory, or compare the manifest and bytes directly with the
   exact downloaded archive entry set before extraction.

4. **Reject all nonzero recorded process statuses, including signals.**
   The log regex `^EXIT_CODE=(\d+)$` ignores negative statuses, although
   `subprocess` can write values such as `EXIT_CODE=-9`. With an earlier zero
   in a multi-command log, that negative status is invisible to the checker.
   Match signed integers and reject every code other than zero. The CI
   wrapper itself raises on negative statuses; this finding concerns the
   receiving script's independent log validation.

5. **Enforce the advertised candidate immutability.**
   `package.py` uses ZIP mode `w` and overwrites the SHA receipt. A second
   invocation after editing an unbound report/document silently replaces
   the candidate under the same name. Refuse an existing candidate, or
   require byte identity with the previously created artifact. The exact
   Git/ZIP/CI digest gate detects a mismatch afterward, but creation should
   enforce the stated immutable-artifact contract directly.

### Additional receiving-side coverage improvement

The axiom parser currently takes its expected roots from the downloaded
summary itself and compares only counts against local metadata. Also compare
the summary's root set with the downloaded kernel namespace inventory minus
the exact frozen inventory. This makes the receiving-side coverage check
independent of the summary it is validating. The CI producer already makes
this stronger comparison.

### Correctly connected parts observed

- Packaging excludes the candidate ZIP, its external digest receipt, and
  only the root `MANIFEST_SHA256.json` from self-hashing. Other nested
  manifests remain ordinary hashed entries. Each generated archive entry is
  read back and compared byte-for-byte, with ZIP CRC and entry-count checks.
- The receiver queries the specified run, requires the intended workflow
  and branch, obtains jobs for the actual run attempt, verifies successful
  steps, and checks the artifact's run/head association and downloaded SHA.
- Extracted run context is compared with the requested commit, repository,
  run ID, attempt, and Linux platform. The candidate digest is compared with
  both the integrity report and results; the copied deliverable is rehashed.
- Root and nested evidence manifests are covered by the producer's digest
  map. The receiver checks reported standard axioms using the frozen parser
  and retains the specialized White/MINBOX and DPE-only status distinctions.

## Delivery hardening re-review

The coordinator revised the executable scripts before beginning the fresh
source-bound verification. This second read-only review covered those
revisions and the new `merge_local_evidence.py`; no executable file was
modified and no tests/builds were repeated by this reviewer.

All five delivery findings above and the additional axiom-root coverage
improvement are resolved in the reviewed source:

- `verify()` resets its success/source-integrity flags at entry, captures
  the executable/input snapshot after deterministic statement generation,
  and compares it after all checks. It excludes only the axiom checker that
  is generated during the run from that initial comparison, then records
  the complete final snapshot, including the generated checker, as
  `VERIFIED_SOURCE_SHA256.json`. The source map also includes milestone and
  frozen-manifest inputs. Finalization requires the verified-source flag
  and exact equality with this recorded map; it no longer labels an
  after-the-fact hash as the tested snapshot.
- The receiver explicitly rejects optimized Python before reaching any
  assertion-based gate.
- The receiver requires an empty extraction directory and checks manifest
  coverage against the downloaded ZIP's own non-directory entries before
  extraction, then checks extracted coverage and every digest.
- Signed process statuses are parsed, and every matched status must be zero.
- Packaging refuses an existing candidate and opens the new ZIP in exclusive
  creation mode. Readback and external digest generation remain in place.
- The receiver derives its expected new axiom-root set from the downloaded
  kernel namespace inventory minus the frozen Git-derived inventory, checks
  frozen-prefix inclusion, and compares that set with parsed axiom results.

The separate local-fresh evidence root is wired consistently through both
the M3B1 module and the reused helper module whose `run`, `write`, and
`record` functions hold their own globals. The fresh subprocess receives
the matching directory switch. Thus the main-project proof run and the
historical suites do not concurrently update the same result map or logs.
Historical project builds remain in independent extracted trees; only
third-party packages are shared.

`merge_local_evidence.py` requires all four historical success flags,
successful fresh proof/source-integrity flags, a completed zero-exit fresh
wrapper log, and an unchanged verified source map before copying fresh
evidence and merging results. The finalizer then requires the complete
combined gate set. Invoke the merge after the historical-suite process has
exited, as planned: its combined `OLD_SUITE_LOG.txt` is written just after
the fourth individual suite flag. CI continues to run these stages
sequentially and does not use this local concurrency path.

No further required executable change was identified for that initialized
run sequence. This conclusion concerns source review only; the fresh local
run, exact-source CI run, artifact download, and final receipt still need
their own successful execution evidence.
