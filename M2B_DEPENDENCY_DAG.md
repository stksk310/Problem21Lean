# M2B dependency DAG

```mermaid
graph TD
  F[Frozen M1 and M2A foundation] --> T[TailNumericalSemigroup]
  F --> C[CriticalRelations: auxiliary foundation]
  T --> A[AperyCardinality]
  F --> G[GcdDecomposition]
  F --> R[SymmetricRigidity: elementary arithmetic]
  R --> P[TopFactorization: multiple expressions]
  G --> P
  R --> U[UniqueTop: rectangular case]
  G --> U
  A --> U
  P --> E[GlueExistence: exhaustive top dichotomy]
  U --> E
  E --> X[SymmetricThreeGeneratorProof]
  X --> S[FullClosure]
  M[Frozen M2A Closure] --> S
```

The gluing proof's transitive project imports exclude M2A Closure and FullClosure.
Only FullClosure imports both the new classification proof and the old internal
closure theorem. No reverse edge is permitted. The verifier writes the actual
import graph, critical declaration locations and circularity checks, separately
from this explanatory diagram.

CriticalRelations proves the requested least-positive actual relation foundation.
It is intentionally not required by the shorter Apéry classification spine.
