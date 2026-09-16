# Statement map

This is a publication-to-Lean navigation ledger. Wording below uses normalized mathematical typography;
the complete source paragraphs are preserved verbatim in `source_excerpts/`. Each declaration also has
its source line, kind, proof/target status, and wording in `STATEMENT_MAP.json`. Supporting lemmas are
formal derivations for the indicated source claim, not additional publication assertions.

## Source claims

### FOUNDATION

Publication §1.1; 2.1; 2.4; 2.7; frozen node / anchor `T1 / C2 setup`.

A numerical semigroup is a cofinite subset of the nonnegative integers that contains 0 and is closed under addition.

### C2.1

Publication §2.8; frozen node / anchor `C2.1 / fr-C2.1`.

Let x be a nonnegative gap. Choose the largest integer φ in the finite set (x+Γ)\Γ.

### C2.2

Publication §2.9; frozen node / anchor `C2.2 / fr-C2.2`.

Thus exactly one of the following holds: W−w∈Ap or W+m−w∈Ap. Max A1=Q+m; Min A1={W−q:q∈Q}; |Min A1|=|Q|=t−1.

### C2.3

Publication §2.10; frozen node / anchor `C2.3 / fr-C2.3`.

c−n_i∈H implies q+n_i∈⟨n_j,n_k⟩. The set D(c) is nonempty and D(c)⊆SH(q). Equality is not asserted.

### C2.4

Publication §2.11; frozen node / anchor `C2.4 / fr-C2.4`.

m=(q+m)+(W−q)−W∈ℤH. Let d=gcd(n1,n2,n3). Then d also divides m; therefore d=1.

### C2.5

Publication §2.12; frozen node / anchor `C2.5 / fr-C2.5`.

We may choose four distinct elements q1,q2,q3,q4∈Q. The Apéry and KEY statements hold for all Q, hence simultaneously for these four selected rows. Thus the tail is minimally generated.

### T1 TARGET

Publication §1.1; frozen node / anchor `T1 / fr-T1`.

Γ=⟨m,n1,n2,n3⟩, edim Γ=4, m=min(Γ\{0}), all four generators minimal, F=F(Γ), ∀φ∈PF(Γ), F+m−φ∈Γ ⇒ t(Γ)≤4.

## Declaration inventory

| Lean declaration | File:line | Source node | Status |
|---|---|---|---|
| `P21.NumericalSemigroup.apery_le` | `P21/Apery.lean:6` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.apery_finite` | `P21/Apery.lean:9` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.zero_mem_apery` | `P21/Apery.lean:13` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.W_mem_apery` | `P21/Apery.lean:19` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.pf_add_m_mem_apery` | `P21/Apery.lean:23` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.apery_lower` | `P21/Apery.lean:27` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.pf_iff_maximal_apery` | `P21/Apery.lean:34` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.A0` | `P21/Apery.lean:54` | C2.2 / fr-C2.2 | definition / interface |
| `P21.NumericalSemigroup.A1` | `P21/Apery.lean:55` | C2.2 / fr-C2.2 | definition / interface |
| `P21.NumericalSemigroup.iota` | `P21/Apery.lean:56` | C2.2 / fr-C2.2 | definition / interface |
| `P21.NumericalSemigroup.complement_mem_apery` | `P21/Apery.lean:58` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.exact_two_layers` | `P21/Apery.lean:67` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.a0_lower` | `P21/Apery.lean:88` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.a1_upper` | `P21/Apery.lean:93` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.iota_involutive` | `P21/Apery.lean:97` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.iota_order_reverse` | `P21/Apery.lean:100` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.iota_mem_a1` | `P21/Apery.lean:106` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.pf_add_m_mem_a1` | `P21/Apery.lean:116` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.complement_of_q_mem_apery` | `P21/Apery.lean:126` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.maximal_a1_iff` | `P21/Apery.lean:136` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.minimal_iff_iota_maximal` | `P21/Apery.lean:161` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.minimal_a1_iff` | `P21/Apery.lean:185` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.maximal_a1_set` | `P21/Apery.lean:193` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.minimal_a1_set` | `P21/Apery.lean:202` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.minimal_a1_card` | `P21/Apery.lean:212` | C2.2 / fr-C2.2 | proved |
| `P21.Generators` | `P21/Basic.lean:5` | T1 / C2 setup | definition / interface |
| `P21.Generators.all` | `P21/Basic.lean:10` | T1 / C2 setup | definition / interface |
| `P21.Generators.Gamma` | `P21/Basic.lean:11` | T1 / C2 setup | definition / interface |
| `P21.Generators.H` | `P21/Basic.lean:12` | T1 / C2 setup | definition / interface |
| `P21.Generators.ActualFactorization4` | `P21/Basic.lean:13` | T1 / C2 setup | definition / interface |
| `P21.Generators.ActualFactorization3` | `P21/Basic.lean:14` | T1 / C2 setup | definition / interface |
| `P21.Generators.Minimal` | `P21/Basic.lean:15` | T1 / C2 setup | definition / interface |
| `P21.Generators.TailMinimal` | `P21/Basic.lean:17` | T1 / C2 setup | definition / interface |
| `P21.Generators.OffDirection` | `P21/Basic.lean:19` | T1 / C2 setup | definition / interface |
| `P21.Generators.D` | `P21/Basic.lean:21` | T1 / C2 setup | definition / interface |
| `P21.Generators.SH` | `P21/Basic.lean:22` | T1 / C2 setup | definition / interface |
| `P21.Generators.tailGcd` | `P21/Basic.lean:23` | T1 / C2 setup | definition / interface |
| `P21.Generators.value_cons` | `P21/Basic.lean:26` | T1 / C2 setup | proved |
| `P21.Generators.h_subset_gamma` | `P21/Basic.lean:30` | T1 / C2 setup | proved |
| `P21.Generators.m_mem` | `P21/Basic.lean:34` | T1 / C2 setup | proved |
| `P21.Generators.n_mem` | `P21/Basic.lean:35` | T1 / C2 setup | proved |
| `P21.Generators.tail_minimal` | `P21/Basic.lean:38` | C2.5 / fr-C2.5 | proved |
| `P21.Generators.Setting` | `P21/Basic.lean:46` | T1 / C2 setup | definition / interface |
| `P21.Generators.Setting.semigroup` | `P21/Basic.lean:53` | T1 / C2 setup | definition / interface |
| `P21.Generators.minimal_injective` | `P21/Basic.lean:61` | T1 / C2 setup | proved |
| `P21.Generators.minimal_four_distinct` | `P21/Basic.lean:67` | T1 / C2 setup | proved |
| `P21.P21MainStatement` | `P21/Basic.lean:75` | T1 / fr-T1 | unproved target definition |
| `P21.Generators.Setting.apery_m_coordinate_zero` | `P21/CanonicalReduction.lean:8` | T1 / C2 setup | proved |
| `P21.Generators.Setting.apery_in_tail` | `P21/CanonicalReduction.lean:14` | T1 / C2 setup | proved |
| `P21.Generators.Setting.a0_tail_iff` | `P21/CanonicalReduction.lean:21` | C2.2 / fr-C2.2 | proved |
| `P21.Generators.Setting.key_return_apery` | `P21/CanonicalReduction.lean:35` | C2.3 / fr-C2.3 | proved |
| `P21.Generators.Setting.return_coordinate_zero` | `P21/CanonicalReduction.lean:46` | C2.3 / fr-C2.3 | proved |
| `P21.Generators.Setting.key_support_zero` | `P21/CanonicalReduction.lean:55` | C2.3 / fr-C2.3 | proved |
| `P21.Generators.Setting.support_nonempty` | `P21/CanonicalReduction.lean:61` | C2.3 / fr-C2.3 | proved |
| `P21.Generators.Setting.key_support_inclusion` | `P21/CanonicalReduction.lean:72` | C2.3 / fr-C2.3 | proved |
| `P21.Generators.Setting.supported_rectangle` | `P21/CanonicalReduction.lean:82` | C2.3 / fr-C2.3 | proved |
| `P21.value` | `P21/Factorization.lean:12` | T1 / C2 setup | definition / interface |
| `P21.ActualFactorization` | `P21/Factorization.lean:15` | T1 / C2 setup | definition / interface |
| `P21.generated` | `P21/Factorization.lean:19` | T1 / C2 setup | definition / interface |
| `P21.actual_iff_mem` | `P21/Factorization.lean:26` | T1 / C2 setup | proved |
| `P21.generator_mem` | `P21/Factorization.lean:32` | T1 / C2 setup | proved |
| `P21.generated_nonneg` | `P21/Factorization.lean:36` | T1 / C2 setup | proved |
| `P21.replaceWithinActualFactorization` | `P21/Factorization.lean:43` | T1 / C2 setup | definition / interface |
| `P21.removeOne` | `P21/Factorization.lean:59` | T1 / C2 setup | definition / interface |
| `P21.SignedRepresentation` | `P21/Factorization.lean:72` | T1 / C2 setup | definition / interface |
| `P21.SignedRelation3` | `P21/Factorization.lean:77` | T1 / C2 setup | definition / interface |
| `P21.NumericalSemigroup` | `P21/NumericalSemigroup.lean:8` | T1 / C2 setup | definition / interface |
| `P21.NumericalSemigroup.Gap` | `P21/NumericalSemigroup.lean:16` | T1 / C2 setup | definition / interface |
| `P21.NumericalSemigroup.IsFrobenius` | `P21/NumericalSemigroup.lean:17` | T1 / C2 setup | definition / interface |
| `P21.NumericalSemigroup.PF` | `P21/NumericalSemigroup.lean:18` | T1 / C2 setup | definition / interface |
| `P21.NumericalSemigroup.type` | `P21/NumericalSemigroup.lean:20` | T1 / C2 setup | definition / interface |
| `P21.NumericalSemigroup.Apery` | `P21/NumericalSemigroup.lean:21` | T1 / C2 setup | definition / interface |
| `P21.NumericalSemigroup.Le` | `P21/NumericalSemigroup.lean:22` | T1 / C2 setup | definition / interface |
| `P21.NumericalSemigroup.Canonical` | `P21/NumericalSemigroup.lean:23` | T1 / C2 setup | definition / interface |
| `P21.NumericalSemigroup.Q` | `P21/NumericalSemigroup.lean:24` | T1 / C2 setup | definition / interface |
| `P21.NumericalSemigroup.Maximal` | `P21/NumericalSemigroup.lean:25` | T1 / C2 setup | definition / interface |
| `P21.NumericalSemigroup.Minimal` | `P21/NumericalSemigroup.lean:26` | T1 / C2 setup | definition / interface |
| `P21.NumericalSemigroup.le_refl` | `P21/NumericalSemigroup.lean:28` | T1 / C2 setup | proved |
| `P21.NumericalSemigroup.le_trans` | `P21/NumericalSemigroup.lean:29` | T1 / C2 setup | proved |
| `P21.NumericalSemigroup.le_antisymm` | `P21/NumericalSemigroup.lean:32` | T1 / C2 setup | proved |
| `P21.NumericalSemigroup.exists_frobenius` | `P21/NumericalSemigroup.lean:37` | T1 / C2 setup | proved |
| `P21.NumericalSemigroup.frobenius_mem_pf` | `P21/NumericalSemigroup.lean:43` | T1 / C2 setup | proved |
| `P21.NumericalSemigroup.mem_of_gt_frobenius` | `P21/NumericalSemigroup.lean:51` | T1 / C2 setup | proved |
| `P21.NumericalSemigroup.pf_finite` | `P21/NumericalSemigroup.lean:56` | T1 / C2 setup | proved |
| `P21.NumericalSemigroup.q_lt_frobenius` | `P21/NumericalSemigroup.lean:62` | T1 / C2 setup | proved |
| `P21.NumericalSemigroup.type_eq_q_card_add_one` | `P21/NumericalSemigroup.lean:67` | T1 / C2 setup | proved |
| `P21.NumericalSemigroup.translated_gaps_finite` | `P21/PseudoFrobenius.lean:7` | C2.1 / fr-C2.1 | proved |
| `P21.NumericalSemigroup.gap_below_pf` | `P21/PseudoFrobenius.lean:13` | C2.1 / fr-C2.1 | proved |
| `P21.NumericalSemigroup.canonical_all_nonnegative_gaps` | `P21/PseudoFrobenius.lean:29` | C2.1 / fr-C2.1 | proved |
| `P21.Generators.offDirection_iff_pair` | `P21/Selection.lean:7` | C2.3 / fr-C2.3 | proved |
| `P21.Generators.Setting.key_pair_return` | `P21/Selection.lean:23` | C2.3 / fr-C2.3 | proved |
| `P21.Generators.Setting.RowFacts` | `P21/Selection.lean:31` | C2.5 / fr-C2.5 | definition / interface |
| `P21.Generators.Setting.all_q_row_facts` | `P21/Selection.lean:40` | C2.5 / fr-C2.5 | proved |
| `P21.Generators.Setting.select_four_rows` | `P21/Selection.lean:50` | C2.5 / fr-C2.5 | proved |
| `P21.Generators.Setting.tail_minimal_and_cofinite` | `P21/Selection.lean:65` | C2.5 / fr-C2.5 | proved |
| `P21.W` | `P21/Semantics.lean:5` | T1 / C2 setup | definition / interface |
| `P21.complement` | `P21/Semantics.lean:6` | T1 / C2 setup | definition / interface |
| `P21.cofinite_iff_finite_nonnegative_gaps` | `P21/Semantics.lean:10` | T1 / C2 setup | proved |
| `P21.NumericalSemigroup.all_pf_finite` | `P21/Semantics.lean:28` | T1 / C2 setup | proved |
| `P21.NumericalSemigroup.q_finite` | `P21/Semantics.lean:34` | T1 / C2 setup | proved |
| `P21.NumericalSemigroup.a0_lower_in_semigroup` | `P21/Semantics.lean:36` | C2.2 / fr-C2.2 | proved |
| `P21.NumericalSemigroup.minimal_a1_card_eq_type_sub_one` | `P21/Semantics.lean:40` | C2.2 / fr-C2.2 | proved |
| `P21.divisor_of_generated` | `P21/Tail.lean:5` | C2.4 / fr-C2.4 | proved |
| `P21.generated_eq_closure` | `P21/Tail.lean:10` | C2.4 / fr-C2.4 | proved |
| `P21.signed_mem_group` | `P21/Tail.lean:20` | C2.4 / fr-C2.4 | proved |
| `P21.Generators.Setting.tail_signed_m` | `P21/Tail.lean:34` | C2.4 / fr-C2.4 | proved |
| `P21.Generators.Setting.m_mem_tail_group` | `P21/Tail.lean:48` | C2.4 / fr-C2.4 | proved |
| `P21.Generators.Setting.common_divisor_dvd_one` | `P21/Tail.lean:55` | C2.4 / fr-C2.4 | proved |
| `P21.Generators.Setting.tail_common_divisor_dvd_one` | `P21/Tail.lean:65` | C2.4 / fr-C2.4 | proved |
| `P21.Generators.Setting.tail_gcd_eq_one` | `P21/Tail.lean:74` | C2.4 / fr-C2.4 | proved |
| `P21.Generators.Setting.natural_closure_to_tail` | `P21/Tail.lean:87` | C2.4 / fr-C2.4 | proved |
| `P21.Generators.Setting.tail_cofinite` | `P21/Tail.lean:98` | C2.4 / fr-C2.4 | proved |
| `P21.Generators.Setting.tailSemigroup` | `P21/Tail.lean:118` | C2.4 / fr-C2.4 | definition / interface |
