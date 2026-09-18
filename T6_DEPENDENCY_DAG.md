# T6 dependency DAG

```text
frozen C2 / Herzog / TypeIIInput
  -> Setup
  -> Returns (generic actual-return helper only)
  -> EndpointCaps
  -> UniformCap
  -> LevelExhaustion
  -> Exclusion: TypeIIInput.impossible
  -> Integration: CHAIN-only wrappers
```

`Exclusion` does not import PATH exclusion, post-PATH integration, CHAIN
closure, later sections, or any final Problem 21 theorem. `Integration` alone
imports the frozen post-PATH wrapper to remove its TYPE II disjunct.
