import P21.Nonsymmetric.Chain.C10.TerminalSetup

namespace P21.Nonsymmetric
namespace EuclideanState

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

open Chain.C10.TerminalCertificateData

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem terminal_certificate_identity (X : EuclideanState s F D) (_hterminal : X.Terminal) :
    X.Phi X.Z = polynomial X.terminalShifts := by
  simp only [Phi, mhatAt, KcalAt, I0, J0, M0, K0, Dp, Z]
  rw [X.rhoj, X.rhok]
  rw [X.A_source, X.B_source, X.L_eq, X.M_eq]
  rw [X.E_terminal_sub, X.theta_terminal_sub, X.Hp_terminal_sub, X.chi_terminal_sub]
  rw [X.R_source, X.T_source]
  simp (config := { maxSteps := 1000000 }) only
    [polynomial, positiveRest, HExpr.eval, Variables.get, terminalShifts]
  ring

theorem terminal_phi_pos (X : EuclideanState s F D) (hterminal : X.Terminal) :
    0 < X.Phi X.Z := by
  rw [X.terminal_certificate_identity hterminal]
  rcases X.terminalShifts_nonnegative hterminal with
    ⟨hp, hq, hs, ht, hr, hd, hb, haj, hg, ha, hbk, hnu, hh, hz, hx, hw⟩
  exact polynomial_pos X.terminalShifts hp hq hs ht hr hd hb haj hg ha hbk hnu hh hz hx hw

end EuclideanState
end P21.Nonsymmetric
