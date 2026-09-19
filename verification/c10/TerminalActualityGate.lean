import P21.Nonsymmetric.Chain.C10.TerminalFit

namespace P21.Nonsymmetric
namespace EuclideanState

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

example (z : ℤ) : (posPart z : ℤ) - negPart z = z := posPart_sub_negPart z

example (X : EuclideanState s F D) (hterminal : X.Terminal) : X.Z + 1 ≤ X.P :=
  X.terminal_i_fit hterminal

example (X : EuclideanState s F D) (hterminal : X.Terminal) :
    value g.all X.terminalSource = value g.all X.terminalTarget :=
  X.terminal_positive_parts_packet

example (X : EuclideanState s F D) (hterminal : X.Terminal) :
    ∀ i, X.terminalSource i ≤ (X.WFactorization).coeff i :=
  X.terminal_source_contained hterminal

example (X : EuclideanState s F D) (hterminal : X.Terminal) :
    (X.terminalReplacement hterminal).coeff 0 = X.N.toNat :=
  X.terminalReplacement_m_coeff hterminal

example (X : EuclideanState s F D) (hterminal : X.Terminal) : F ∈ g.Gamma :=
  X.terminal_f_mem hterminal

example (X : EuclideanState s F D) (hterminal : X.Terminal) :
    F = (X.N - 1) * g.m + (X.P - 1 - X.Z) * g.n 0 +
      (X.hterm - 1) * g.n 1 + X.xterm * g.n 2 :=
  X.final_exact hterminal

example (X : EuclideanState s F D) (hterminal : X.Terminal) :
    0 ≤ X.N - 1 ∧ 0 ≤ X.P - 1 - X.Z ∧ 0 ≤ X.hterm - 1 ∧ 0 ≤ X.xterm :=
  X.final_exact_coefficients hterminal

end EuclideanState
end P21.Nonsymmetric
