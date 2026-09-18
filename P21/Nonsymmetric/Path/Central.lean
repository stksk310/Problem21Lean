import P21.Nonsymmetric.Path.Dual

namespace P21.Nonsymmetric
namespace PathInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

/-- The two actual central C2 returns, fixed before any packet replacement. -/
structure CentralReturns (P : PathInput s F D) where
  atA : g.ActualFactorization3 (P.qA + g.m)
  atB : g.ActualFactorization3 (P.qB + g.m)

/-- C2 supplies genuine H-factorizations of both central pseudo-Frobenius
elements after adding `m`. -/
theorem central_returns (P : PathInput s F D) : Nonempty (CentralReturns P) := by
  have hm : g.m ∈ g.Gamma := g.m_mem
  have hmn : g.m ≠ 0 := ne_of_gt s.m_pos
  have hAap := s.semigroup.pf_add_m_mem_apery hm hmn (P.actual 1).1
  have hBap := s.semigroup.pf_add_m_mem_apery hm hmn (P.actual 2).1
  obtain ⟨a⟩ := actual_iff_mem.mpr (s.apery_in_tail hAap)
  obtain ⟨b⟩ := actual_iff_mem.mpr (s.apery_in_tail hBap)
  exact ⟨⟨a, b⟩⟩

end PathInput
end P21.Nonsymmetric
