import P21.Nonsymmetric.Rows
import P21.Nonsymmetric.HerzogCoordinates
import P21.Nonsymmetric.CriticalBox

namespace P21.Nonsymmetric

theorem missing_complement_zero {g : Generators} (s : g.Setting) {F q : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hq : q ∈ s.semigroup.Q F) {i : Fin 3} (hmissing : i ∉ g.SH q)
    (a : g.ActualFactorization3 (complement F g.m q)) : a.coeff i = 0 := by
  by_contra hn
  have hd : i ∈ g.D (F+g.m-q) := actual_iff_mem.mp
    ⟨removeOne a i (Nat.pos_of_ne_zero hn)⟩
  exact hmissing ((s.key_support_inclusion hF hc hq).2 hd)

/-- Replacing a contained critical block is done inside the same named
complement factorization; the produced missing-direction copy is impossible. -/
theorem missing_complement_bound {g : Generators} (s : g.Setting) {F q : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (hq : q ∈ s.semigroup.Q F)
    {i : Fin 3} (hmissing : i ∉ g.SH q)
    (a : g.ActualFactorization3 (complement F g.m q)) (j : Fin 3) :
    a.coeff j < D.rho j := by
  classical
  by_cases hji : j = i
  · subst j
    rw [missing_complement_zero s hF hc hq hmissing a]
    exact D.rho_pos i
  by_contra hh
  have hle : D.rho j ≤ a.coeff j := by omega
  let source : Fin 3 → ℕ := fun t => if t = j then D.rho j else 0
  have hcontained : ∀ t, source t ≤ a.coeff t := by
    intro t; by_cases ht : t = j <;> simp_all [source]
  have hreplace : value g.n source = value g.n (D.relationCoeff j) := by
    rw [D.relationCoeff_value]
    simp [source,value]
  let b := replaceWithinActualFactorization a source (D.relationCoeff j) hcontained hreplace
  have hz := missing_complement_zero s hF hc hq hmissing b
  have hi := missing_complement_zero s hF hc hq hmissing a
  have hb : b.coeff i = D.relationCoeff j i := by
    simp [b, replaceWithinActualFactorization, source, Ne.symm hji, hi]
  rw [hb] at hz
  have hp := D.relationCoeff_pos j i (Ne.symm hji)
  omega

theorem arm_complement_box {g : Generators} (s : g.Setting) {F q : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (hq : q ∈ s.semigroup.Q F)
    {i : Fin 3} (hmissing : i ∉ g.SH q) :
    ∃ a : g.ActualFactorization3 (complement F g.m q),
      a.coeff i = 0 ∧ ∀ j, a.coeff j < D.rho j := by
  obtain ⟨a⟩ := actual_iff_mem.mpr
    (s.apery_in_tail (s.semigroup.complement_of_q_mem_apery hF hc hq))
  exact ⟨a, missing_complement_zero s hF hc hq hmissing a,
    missing_complement_bound s hF hc D hq hmissing a⟩

theorem arm_complement_unique {g : Generators} (s : g.Setting) {F q : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (hq : q ∈ s.semigroup.Q F)
    {i : Fin 3} (hmissing : i ∉ g.SH q)
    (a b : g.ActualFactorization3 (complement F g.m q)) : a.coeff = b.coeff := by
  apply critical_box_unique (fun j => lt_trans s.m_pos (s.n_gt j)) D.critical
  · intro j; rw [D.coeff_rho]; exact missing_complement_bound s hF hc D hq hmissing a j
  · intro j; rw [D.coeff_rho]; exact missing_complement_bound s hF hc D hq hmissing b j
  · exact a.equation.trans b.equation.symm

theorem arm_complement_pair {g : Generators} (s : g.Setting) {F q : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (hq : q ∈ s.semigroup.Q F)
    {i : Fin 3} (hmissing : i ∉ g.SH q) :
    ∃ y z : ℕ, y < D.rho (next i) ∧ z < D.rho (prev i) ∧
      complement F g.m q = (y : ℤ)*g.n (next i)+(z : ℤ)*g.n (prev i) := by
  obtain ⟨a,hzero,hb⟩ := arm_complement_box s hF hc D hq hmissing
  refine ⟨a.coeff (next i),a.coeff (prev i),hb _,hb _,?_⟩
  have hv := value_cyclic g a.coeff i
  rw [a.equation, hzero] at hv
  simpa using hv

end P21.Nonsymmetric
