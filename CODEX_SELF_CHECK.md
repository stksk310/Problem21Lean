# Codex self-check

**Status: M1 CANDIDATE FOR TRUE AUDIT**

This file describes development self-checks. It does not claim an independent audit.

| Check | Result / evidence |
|---|---|
| Foundation and C2.1–C2.5 | All implemented as proved Lean declarations; root imports all modules |
| Main theorem | `P21MainStatement : Prop` only; intentionally unproved |
| Build | `BUILD_LOG.txt` records the final `lake build` and successful exit |
| Fresh project compilation | Copied distribution sources rebuilt with no project build cache; all modules succeeded, exit 0; `verification/FRESH_PROJECT_BUILD_LOG.txt` |
| Forbidden source tokens | 0 matches; `PROOF_DEBT_REPORT.txt` |
| Project-specific axioms | 0, both declaration scan and transitive axiom inspection |
| Axiom inspection | 107 theorem/definition/abbreviation declarations, including all 73 theorems; `AXIOM_REPORT.txt` and `verification/AXIOM_SUMMARY.json` |
| Allowed axioms observed | `propext`, `Classical.choice`, `Quot.sound` only |
| Actuality firewall | Natural coefficient witnesses; signed representations separate; no signed-to-semigroup shortcut |
| Source containment | `replaceWithinActualFactorization` requires coefficientwise containment in its explicit `a` argument |
| Same-element removal | `removeOne` consumes its named witness; KEY uses it for the same `q + n_i` |
| Criticality interface | Only a three-coordinate `SignedRelation3`; no criticality theorem or m-bearing criticality helper |
| Tail gcd | Actual inputs give a signed group expression; never an actual m-factorization |
| Four rows | Injective `Fin 4 → ℤ`; facts first proved for every member of the full Q |
| Source consistency | Main statement and C2 normalized PDF text agree; editorial differences explicitly recorded |
| Artifact integrity | Original input hashes; all ZIP entry hashes checked against `MANIFEST_SHA256.json` |

No unproved project fact was introduced as a theorem or an extra setup assumption.
Some foundational helpers have fewer hypotheses than the full publication setting;
the required statements retain the specified mathematical scope. Natural subtraction
occurs only in the final cardinality expression `type - 1`, not in factorization algebra.

Both the initial build and the fresh project compilation reused the locally installed, pinned mathlib compiled cache.
The supplied portable build commands enable a fresh dependency acquisition and
recheck. No claim is made that this run rebuilt every third-party dependency from
source or independently verified all of mathlib. Standard Lean kernel checking
of the project and transitive axiom reporting are the checks performed here.

Review priorities: publication-to-Setting equivalence, integer PF semantics, the
max/min Γ-order predicates, containment in the named actual witness, and preservation
of the full Q while selecting four rows. See `NEXT_RESTART.md`.
