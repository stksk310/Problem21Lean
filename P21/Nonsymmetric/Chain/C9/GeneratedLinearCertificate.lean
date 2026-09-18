/- Generated frozen certificate aggregation and positivity theorem. -/
import P21.Nonsymmetric.Chain.C9.GeneratedLinearCertificateData0
import P21.Nonsymmetric.Chain.C9.GeneratedLinearCertificateData1
import P21.Nonsymmetric.Chain.C9.GeneratedLinearCertificateData2
import P21.Nonsymmetric.Chain.C9.GeneratedLinearCertificateData3
import P21.Nonsymmetric.Chain.C9.GeneratedLinearCertificateData4
import P21.Nonsymmetric.Chain.C9.GeneratedLinearCertificateData5
import P21.Nonsymmetric.Chain.C9.GeneratedLinearCertificateData6
import P21.Nonsymmetric.Chain.C9.GeneratedLinearCertificateData7

namespace P21.Nonsymmetric.ChainCore.C9.LinearCertificateData

def terms : List Term := terms0 ++ terms1 ++ terms2 ++ terms3 ++ terms4 ++ terms5 ++ terms6 ++ terms7
def polynomial (y : Variables) : ℤ := 35 + (terms.map (evalTerm y)).sum

theorem polynomial_pos (y : Variables)
    (h_f : 0 ≤ y.f)
    (h_r : 0 ≤ y.r)
    (h_delta : 0 ≤ y.delta)
    (h_beta : 0 ≤ y.beta)
    (h_g : 0 ≤ y.g)
    (h_u : 0 ≤ y.u)
    (h_alpha : 0 ≤ y.alpha)
    (h_w : 0 ≤ y.w)
    (h_theta : 0 ≤ y.theta)
    (h_eps : 0 ≤ y.eps)
    (h_k : 0 ≤ y.k)
    (h_a_j : 0 ≤ y.a_j)
    (h_b_k : 0 ≤ y.b_k)
    : 0 < polynomial y := by
  have hs : 0 ≤ (terms.map (evalTerm y)).sum := by
    apply List.sum_nonneg
    intro z hz
    simp only [List.mem_map] at hz
    rcases hz with ⟨t, _, rfl⟩
    exact evalTerm_nonneg y h_f h_r h_delta h_beta h_g h_u h_alpha h_w h_theta h_eps h_k h_a_j h_b_k t
  simp only [polynomial]
  omega

end P21.Nonsymmetric.ChainCore.C9.LinearCertificateData
