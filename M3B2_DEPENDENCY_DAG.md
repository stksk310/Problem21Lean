# M3B2 dependency direction

```text
frozen BoxInput / BoxPath / arithmetic helpers
  -> Trace / Rotation / SuccessfulPrefix / ChronologicalPrefix / PathShape
  -> ReciprocalRank / TerminalCoordinates / Canonical
  -> TwoColor12 + TwoColor13
  -> FirstThirdColor
  -> Exhaustion.box_positive_exit_proved

frozen MinimumOneProof.minimum_one_proved
  + Exhaustion.box_positive_exit_proved
  + frozen residual reductions
  -> FullColorCap residual-free wrappers
  -> selected-four terminal extraction wrappers
```

`Exhaustion` has no import path to `FullColorCap`, `MinimumOneProof`,
`ActualClassification`, or `SelectedExtraction`. The generated full import DAG
is checked for cycles and the DPE ancestor closure is checked for those reverse
dependencies.
