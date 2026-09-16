# M2 internal proof dependencies

Scope: M2A internal symmetric closure. The external classification is OPEN.

```mermaid
graph TD
  M1[Immutable M1 FOUNDATION and C2] --> TG[TwoGenerator]
  M1 --> SC[StableCore: GAP-K and FS]
  SC --> TB[TypeBridge]
  TG --> GN[GlueNormalForm]
  TG --> TI[TwoGeneratorIdeal]
  TI --> R4[Raw4: extraction from type at least five]
  GN --> R4
  TB --> R4
  TB --> RR[RawRows: actual PF and QM]
  R4 --> RC[Raw4Consequences: cross-layer and SPLIT]
  RR --> RC
  TG --> BI[BranchI: symbolic four-hit contradiction]
  BI --> BIA[BranchIActual: same actual rows and walk]
  RR --> BIA
  GN --> BIA
  BIA --> RC
  TG --> BII[BranchII: all arithmetic subcases]
  BII --> BIIA[BranchIIActual: actual-gap discharge]
  RC --> BIIA
  BIIA --> CL[Closure: type at most four from glue data]
  EXT[STD_SYM_GLUE: OPEN] -. produces data, not yet proved .-> GN
```

`Reduction.lean` transports QM through the exact quotient/remainder normal form.
`CrossLayer.lean` proves nonnegative-witness comparability and non-exclusive 2GI SPLIT.
The dependency from Branch II to Branch I is one-way; Branch I is proved first.
Arithmetic interfaces that mention FS or complementary gaps are discharged in
the corresponding Actual modules before Closure applies them.

The machine-readable declaration inventory is `verification/m2/DECLARATIONS.json`.
The complete declaration/source mapping is `M2_STATEMENT_MAP.md`.
