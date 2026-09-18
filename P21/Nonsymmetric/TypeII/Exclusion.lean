import P21.Nonsymmetric.TypeII.LevelExhaustion

namespace P21.Nonsymmetric
namespace TypeIIInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

/-- Section 6: the exact frozen TYPE II input is impossible. -/
theorem impossible (T : TypeIIInput s F D)
    (hF : s.semigroup.IsFrobenius F) : False := by
  obtain ⟨SJ⟩ := T.singleton_n1_return
  obtain ⟨SK⟩ := T.singleton_n2_return
  exact T.level_order_impossible hF SJ SK

end TypeIIInput
end P21.Nonsymmetric
