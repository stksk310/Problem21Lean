# M3B1 dependency direction

```text
unchanged M1/M2/M3A (Herzog, primitive formulas, saturated kernel)
  -> Setup / RelativeIndex / SocleSimplex / EmptyTetrahedron
  -> CyclicClasses -> CyclicInput

integer division -> WidthOne -> WidthOneBeatty (cyclic_white_proved)
Bezout -> ClassData
CyclicClasses -> ClassReconstruction

unchanged actual minimum / six companions / multiplicity certificates
  -> ClassArithmetic -> ColorA + ColorB -> RotationClosure

CyclicInput + ClassReconstruction + ClassData + RotationClosure
  -> CyclicReduction
CyclicReduction + cyclic_white_proved
  -> MinimumOneProof.minimum_one_proved
  -> three_arms_impossible_of_dpe
```

The final wrapper uses the frozen DPE proposition only as an explicit argument.
No DPE proof, terminal exclusion, Euclidean closure or final Problem 21 theorem
is fed into MINBOX. The original M3A files cannot acquire reverse imports because
all 96 old Lean files are byte-protected. The generated full-project import DAG
and acyclicity report are in the verification evidence.
