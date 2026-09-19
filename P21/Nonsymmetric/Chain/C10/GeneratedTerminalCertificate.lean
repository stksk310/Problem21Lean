/- Generated frozen Section 10 certificate aggregation and positivity theorem. -/
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData00
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData01
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData02
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData03
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData04
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData05
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData06
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData07
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData08
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData09
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData10
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData11
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData12
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData13
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData14
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData15
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData16
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData17
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData18
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData19
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData20
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData21
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData22
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData23
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData24
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData25
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData26
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData27
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData28
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData29
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData30
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData31
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData32
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData33
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData34
import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData35

namespace P21.Nonsymmetric.Chain.C10.TerminalCertificateData

def terms : List Term := terms0 ++ terms1 ++ terms2 ++ terms3 ++ terms4 ++ terms5 ++ terms6 ++ terms7 ++ terms8 ++ terms9 ++ terms10 ++ terms11 ++ terms12 ++ terms13 ++ terms14 ++ terms15 ++ terms16 ++ terms17 ++ terms18 ++ terms19 ++ terms20 ++ terms21 ++ terms22 ++ terms23 ++ terms24 ++ terms25 ++ terms26 ++ terms27 ++ terms28 ++ terms29 ++ terms30 ++ terms31 ++ terms32 ++ terms33 ++ terms34 ++ terms35
def polynomial (y : Variables) : ℤ := 63 + (terms.map (evalTerm y)).sum

theorem polynomial_pos (y : Variables)
    (h_p0 : 0 ≤ y.p0)
    (h_q0 : 0 ≤ y.q0)
    (h_s0 : 0 ≤ y.s0)
    (h_t0 : 0 ≤ y.t0)
    (h_r0 : 0 ≤ y.r0)
    (h_delta0 : 0 ≤ y.delta0)
    (h_beta0 : 0 ≤ y.beta0)
    (h_aj0 : 0 ≤ y.aj0)
    (h_g0 : 0 ≤ y.g0)
    (h_alpha0 : 0 ≤ y.alpha0)
    (h_bk0 : 0 ≤ y.bk0)
    (h_nu0 : 0 ≤ y.nu0)
    (h_h0 : 0 ≤ y.h0)
    (h_z0 : 0 ≤ y.z0)
    (h_x0 : 0 ≤ y.x0)
    (h_w0 : 0 ≤ y.w0)
    : 0 < polynomial y := by
  have hsum : 0 ≤ (terms.map (evalTerm y)).sum := by
    apply List.sum_nonneg
    intro value hvalue
    simp only [List.mem_map] at hvalue
    rcases hvalue with ⟨term, _, rfl⟩
    exact evalTerm_nonneg y h_p0 h_q0 h_s0 h_t0 h_r0 h_delta0 h_beta0 h_aj0 h_g0 h_alpha0 h_bk0 h_nu0 h_h0 h_z0 h_x0 h_w0 term
  simp only [polynomial]
  omega

end P21.Nonsymmetric.Chain.C10.TerminalCertificateData
