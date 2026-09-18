import P21.Nonsymmetric.Path.Setup

namespace P21.Nonsymmetric
namespace PathInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

/-- An actual Gamma return in tail direction `i`.  The full factorization is
retained, so nonnegativity and same-element provenance cannot be lost. -/
structure ActualReturn (g : Generators) (q : ℤ) (i : Fin 3) where
  factorization : g.ActualFactorization4 (q + g.n i)
  direction_zero : factorization.coeff i.succ = 0
  level_pos : 0 < factorization.coeff 0

/-- A missing tail direction forces every actual return in that direction to
use a positive copy of `m`, while the returned direction itself has coefficient
zero. -/
theorem actual_return_exists {q : ℤ} (i : Fin 3)
    (hq : q ∈ s.semigroup.Q F) (hmissing : i ∉ g.SH q) :
    Nonempty (ActualReturn g q i) := by
  have hni : 0 < g.n i := lt_trans s.m_pos (s.n_gt i)
  have hret : q + g.n i ∈ g.Gamma := hq.1.2 (g.n i) (g.n_mem i) (ne_of_gt hni)
  obtain ⟨a⟩ := actual_iff_mem.mpr hret
  have hzero : a.coeff i.succ = 0 := by
    by_contra hn
    have hm := actual_iff_mem.mp
      ⟨removeOne a i.succ (Nat.pos_of_ne_zero hn)⟩
    apply hq.1.1
    change q ∈ g.Gamma
    simpa [Generators.all, Generators.Gamma] using hm
  have hlevel : 0 < a.coeff 0 := by
    by_contra hn
    have hz : a.coeff 0 = 0 := by omega
    apply hmissing
    change q + g.n i ∈ g.H
    refine ⟨fun j => a.coeff j.succ, ?_⟩
    have he := a.equation
    simpa [value, Generators.all, Fin.sum_univ_succ, hz] using he
  exact ⟨⟨a, hzero, hlevel⟩⟩

private theorem left_missing (P : PathInput s F D) (i : Fin 3) (hi : i ≠ 0) :
    i ∉ g.SH P.qL := by
  rw [P.left_singleton]
  simpa using hi

private theorem right_missing (P : PathInput s F D) (i : Fin 3) (hi : i ≠ 2) :
    i ∉ g.SH P.qR := by
  rw [P.right_singleton]
  simpa using hi

theorem qL_n1_return (P : PathInput s F D) :
    Nonempty (ActualReturn g P.qL 1) :=
  actual_return_exists 1 (P.actual 0) (left_missing P 1 (by decide))

theorem qL_n2_return (P : PathInput s F D) :
    Nonempty (ActualReturn g P.qL 2) :=
  actual_return_exists 2 (P.actual 0) (left_missing P 2 (by decide))

theorem qR_n0_return (P : PathInput s F D) :
    Nonempty (ActualReturn g P.qR 0) :=
  actual_return_exists 0 (P.actual 3) (right_missing P 0 (by decide))

theorem qR_n1_return (P : PathInput s F D) :
    Nonempty (ActualReturn g P.qR 1) :=
  actual_return_exists 1 (P.actual 3) (right_missing P 1 (by decide))

end PathInput
end P21.Nonsymmetric
