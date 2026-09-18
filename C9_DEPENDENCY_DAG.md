# C9 dependency DAG

```text
FROZEN C8 c8_handoff
  -> RegionUSetup -> RegionUCapacity -> RegionUExclusion
  -> DSetup -> DFirstCaps -> MultiplicityMaster
       -> HighQ -> NonlinearFirst -> LinearFirst -> PacketDeterminant
       -> LinearRemainder -> GeneratedLinearCertificate -> LinearCertificate
       -> IFit -> JShortage -> MatrixEmbedding -> EuclideanSeed
  -> Handoff -> C9
```

The graph is forward-only and acyclic. It imports no C10 module, CHAIN
impossibility, Euclidean descent, or final Problem 21 theorem.
