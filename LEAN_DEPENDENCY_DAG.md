# Lean dependency DAG

Arrows below mean “imports / depends on”. The Lean root imports every project module.

```text
P21 → Semantics → Selection → Tail → CanonicalReduction → Apery
    → PseudoFrobenius → Basic → NumericalSemigroup → Factorization → mathlib
```

The line wraps one continuous module chain. `verification/AxiomCheck.lean` and
`verification/StatementCheck.lean` both import `P21`.

## Mathematical dependencies

```text
ActualFactorization + removeOne
  ├─ every Apéry factorization has m-coordinate zero → Apéry ⊆ H
  └─ positive return coordinate would put the same q in Γ → support zero

F greatest integer gap + finite translated gap set
  → maximal translated gap is PF → C2.1 canonical gap reflection
  → exact two layers → ideal/filter + reversing involution
  → Max Apéry = PF+m → Max A1 = Q+m → Min A1 = W−Q → cardinality bridge

PF + supported complement + F gap
  → (c−ni)+(q+ni−m)=F contradiction → KEY return in Apéry
  → support-zero actual witness → pair representation
  → D(c) nonempty and D(c) ⊆ SH(q) → supported rectangle

q+m, c, W ∈ Apéry ⊆ H
  → signed representation of m → m ∈ ZH
  → common tail divisor divides all Γ
  → two consecutive large elements of Γ → gcd(tail)=1
  → mathlib Nat.exists_mem_closure_of_ge + proved cast bridge → H cofinite

all-Q row facts + |Q|≥4 → four distinct selected actual rows
four-generator irredundance → tail irredundance
```

No PATH, TYPE II, CHAIN, classification, symmetric-tail theorem, external
structure theorem, or polynomial certificate is a dependency of this graph.
The Prop target `P21MainStatement` is never used as a premise of an M1 theorem.
