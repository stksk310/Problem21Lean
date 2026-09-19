import P21.Nonsymmetric.Chain.C10.TerminalCertificate

namespace P21.Nonsymmetric
namespace EuclideanState

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

example (X : EuclideanState s F D) (Px : ℤ) :
    X.Phi (Px + 1) - X.Phi Px = -(X.Dp + X.M0) := X.phi_step Px

example (X : EuclideanState s F D) {Pstar : ℤ} (h : X.P ≤ Pstar) :
    X.Phi Pstar ≤ X.Phi X.P := X.phi_antitone_of_le h

example (X : EuclideanState s F D) : 2 ≤ X.measureZ := X.measureZ_ge_two
example (X : EuclideanState s F D) : (X.measureNat : ℤ) = X.measureZ := X.measureNat_cast
example (X : EuclideanState s F D) : 2 ≤ X.nu := X.nu_ge_two
example (X : EuclideanState s F D) : X.jstar ≤ X.R - 1 := X.jstar_le

example (X : EuclideanState s F D) :
    X.Z * g.n 0 + X.jstar * g.n 1 + X.kstar * g.n 2 = X.N * g.m :=
  X.terminal_signed_packet

example (X : EuclideanState s F D) : 0 ≤ X.z ∧ X.z < X.theta := X.z_range
example (X : EuclideanState s F D) (hterm : X.Terminal) : 0 ≤ X.terminalShifts.p0 :=
  X.terminalShifts_nonnegative hterm |>.1

example (X : EuclideanState s F D) (hterm : X.Terminal) :
    X.Phi X.Z = Chain.C10.TerminalCertificateData.polynomial X.terminalShifts :=
  X.terminal_certificate_identity hterm

example (X : EuclideanState s F D) (hterm : X.Terminal) : 0 < X.Phi X.Z :=
  X.terminal_phi_pos hterm

end EuclideanState
end P21.Nonsymmetric
