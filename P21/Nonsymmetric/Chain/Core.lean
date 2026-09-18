import P21.Nonsymmetric.Chain.ColorReversal

namespace P21.Nonsymmetric

/-- Minimal Section 7 CORE interface. All actual rows, complements and W remain
referenced through the exact `chain` input. -/
structure ChainCore {g : Generators} (s : g.Setting) (F : ℤ)
    (D : HerzogCriticalData g) where
  chain : ChainInput s F D
  d : ℤ
  S : ℤ
  Croot : ℤ
  root : g.m + d * g.n 0 = S * g.n 1 + Croot * g.n 2
  d_range : 1 ≤ d ∧ d ≤ chain.lambda
  S_strong : chain.gapJ + 1 ≤ S
  C_lower : chain.alpha ≤ Croot

namespace ChainInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

inductive OrientedCore (C : ChainInput s F D) : Type
  | direct : ChainCore s F D → OrientedCore C
  | reversed : ChainCore (relabelSetting s reversePerm) F (reverseHerzog D) → OrientedCore C

def RootBox.directCore {C : ChainInput s F D} (N : C.RootBox)
    (h : C.gapJ + 1 ≤ N.S) : ChainCore s F D where
  chain := C
  d := N.d
  S := N.S
  Croot := N.Croot
  root := N.root
  d_range := N.d_range
  S_strong := h
  C_lower := N.C_range.1

def RootBox.reversedCore {C : ChainInput s F D} (N : C.RootBox)
    (h : C.alpha + 1 ≤ N.Croot) :
    ChainCore (relabelSetting s reversePerm) F (reverseHerzog D) where
  chain := C.reverseChain
  d := N.d
  S := N.Croot
  Croot := N.S
  root := by
    simpa [relabel, reversePerm, add_comm, add_left_comm, add_assoc] using N.root
  d_range := by simpa using N.d_range
  S_strong := by simpa using h
  C_lower := by simpa using N.S_range.1

/-- Every exact CHAIN input produces CORE after zero or one proved color
reversal. -/
def to_oriented_core (C : ChainInput s F D) (N : C.RootBox) : C.OrientedCore :=
  if h : C.gapJ + 1 ≤ N.S then
    .direct (N.directCore h)
  else
    .reversed (N.reversedCore (N.strict.resolve_left h))

end ChainInput
end P21.Nonsymmetric
