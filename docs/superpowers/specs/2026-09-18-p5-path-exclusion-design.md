# P5 PATH Exclusion Design

**Approved specification:** `verification/p5/REQUEST.md`

## Goal

Prove `P21.Nonsymmetric.path_input_impossible` from the unchanged frozen
`PathInput`, then eliminate the PATH disjunct from selected terminal data while
retaining the same semigroup and selected row values. Section 6 is outside the
milestone.

## Frozen boundary

Commit `fd4ea0c7cbc57df6e935790a1387242bcf9e0087` is the immutable mathematical
base. Every `.lean` file present at that commit is byte protected. Mathematical
changes consist only of new files below `P21/Nonsymmetric/Path/`. Documentation,
verification, CI, and packaging files may be added or corrected.

## Architecture

The proof follows publication Section 5 in dependency order. `Setup` derives
publication coordinates and identities without extending `PathInput`.
`Returns` exposes actual nonnegative return witnesses with the removed
coordinate and positive m-level proved from the same factorization. `Dual`
constructs a complete structure-level left-right reversal. `Pair` and
`NoPairNormalization` produce the exhaustive PAIR/PFREE/dual-PFREE split.
PAIR flows through signed weak roots, root walls, terminating normalization,
endpoint level, and Frobenius absorption. PFREE flows through its two signed
roots, the independently proved `F0` sign, two-return absorption, and the
pure-H double-unit endgame. `Closure` exhausts the split; `Integration` removes
PATH from the frozen selected-terminal disjunction.

## Proof interfaces

All actual witnesses store natural-number coefficient vectors or integer
coefficients together with explicit nonnegativity. Signed roots are separate
structures and provide no semigroup-membership projection. Packet replacement
accepts and returns a factorization of the same named integer. Every criticality
lemma consumes an equality containing only `g.n 0`, `g.n 1`, and `g.n 2`.

The central public interfaces are:

```lean
structure Path.PairData ...
structure Path.PFreeData ...
structure Path.WeakRoot ...
structure Path.NormalizedRoot ...

def PathInput.reverse (P : PathInput s F D) :
  PathInput (relabelSetting s reversePerm) F (reverseHerzog D)

theorem path_input_impossible
    {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (P : PathInput s F D) : False
```

Exact helper signatures may gain proof parameters derived from the frozen
input, but the primary theorem gains none.

## Verification

`verification/p5/StatementGate.lean` is written before each public interface and
must first fail because that declaration is absent. Each implementation then
makes the gate compile. Final verification inventories every new declaration,
prints statements and axioms, scans proof debt and imports, hashes all 101
frozen Lean files, performs a fresh root build and explicit P5 builds, and runs
M1 through M3B2 in isolated historical inputs. GitHub CI repeats the process and
uploads `P21_P5_TRUE_AUDIT_EVIDENCE` bound to the exact candidate commit.
