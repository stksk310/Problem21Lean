import P21.Symmetric.FullClosure
import P21.Nonsymmetric.Chain.C10.Integration

namespace P21

/-- Four distinct elements of `Q(F)` are impossible in every canonical
four-generator setting.  The split is exactly the frozen symmetric-tail /
nonsymmetric-tail dichotomy. -/
theorem q_ge_four_impossible
    {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m)
    (hcard : 4 ≤ (s.semigroup.Q F).ncard) : False := by
  by_cases hsym : P21.Symmetric.SymmetricTail g
  · have htype := P21.Symmetric.symmetric_tail_type_le_four g s F hF hc hsym
    have htypeQ := s.semigroup.type_eq_q_card_add_one hF g.m_mem (ne_of_gt s.m_pos)
    omega
  · exact P21.Nonsymmetric.nonsymmetric_Q_ge_four_impossible_after_chain
      s hF hc hsym hcard

/-- The canonical `Q(F)` set has at most three elements. -/
theorem q_card_le_three
    {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) :
    (s.semigroup.Q F).ncard ≤ 3 := by
  by_contra h
  have hcard : 4 ≤ (s.semigroup.Q F).ncard := by omega
  exact q_ge_four_impossible s hF hc hcard

/-- The numerical semigroup type bound obtained from the `Q(F)` bound. -/
theorem type_le_four
    {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) : s.semigroup.type ≤ 4 := by
  have hcard := q_card_le_three s hF hc
  have htypeQ := s.semigroup.type_eq_q_card_add_one hF g.m_mem (ne_of_gt s.m_pos)
  omega

/-- Section 11 assembly of the frozen symmetric and nonsymmetric closures. -/
theorem main_theorem : P21MainStatement := by
  intro g s F hF hc
  exact type_le_four s hF hc

end P21

