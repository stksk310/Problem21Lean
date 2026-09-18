# C8 dependency DAG

```text
FROZEN C7
  -> FirstFit / Packet / Triangle
  -> boundary synchronization -> boundary exclusion
  -> strict window
       -> OneData -> RegionU
       -> RegionD
  -> c8_handoff
```

C8 has no dependency on C9, C10, CHAIN closure, or the final theorem.
