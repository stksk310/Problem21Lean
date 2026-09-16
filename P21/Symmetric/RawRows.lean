import P21.Symmetric.TypeBridge

namespace P21.Symmetric

/-- A raw minimum which actually survives in the frozen Apéry set. -/
def ActualRawRow {g : Generators} (s : g.Setting) (F f c : ℤ) : Prop :=
  idealMin g.H (tailIntersection g (f - F - g.m)) c ∧
    c ∈ s.semigroup.Apery g.m

namespace ActualRawRow
variable {g : Generators} {s : g.Setting} {F f c : ℤ}

theorem pf (hrow : ActualRawRow s F f c)
    (hF : s.semigroup.IsFrobenius F) (hcan : s.semigroup.Canonical F g.m)
    (hsym : SymmetricAt g.H f) : F + g.m - c ∈ s.semigroup.PF := by
  apply (min_shiftedCore_iff_pf s hsym).mp
  have he := exact_bridge s hF hcan hsym
  have hc : c ∈ insert g.m {c | idealMin g.H (tailIntersection g (f - F - g.m)) c ∧
      c ∈ s.semigroup.Apery g.m} := Or.inr hrow
  rw [← he] at hc
  exact hc

theorem core (hrow : ActualRawRow s F f c)
    (hF : s.semigroup.IsFrobenius F) (hsym : SymmetricAt g.H f) :
    c + (f - F - g.m) ∈ stableCore g :=
  ((tailIntersection_iff_shiftedCore s hF hsym).mp hrow.1.1).1

theorem all_ap (hrow : ActualRawRow s F f c) : c - g.m ∉ g.Gamma := hrow.2.2

theorem sub_multiple_gap (hrow : ActualRawRow s F f c) (n : ℕ) (hn : 1 ≤ n) :
    c - (n : ℤ) * g.m ∉ g.H := by
  intro hc
  apply hrow.all_ap
  have hm := g.Gamma.nsmul_mem g.m_mem (n - 1)
  have h := g.Gamma.add_mem (g.h_subset_gamma hc) hm
  have he : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  simp only [nsmul_eq_mul, he] at h
  convert h using 1; ring

theorem backward_gap (hrow : ActualRawRow s F f c)
    (hF : s.semigroup.IsFrobenius F) (hcan : s.semigroup.Canonical F g.m)
    (hsym : SymmetricAt g.H f) : c + (f - F - g.m) - g.m ∉ g.H := by
  intro ha
  have hk : c + (f - F - g.m) - g.m ∈ stableCore g := by
    intro n
    cases n with
    | zero => simpa using ha
    | succ n =>
      have h := hrow.core hF hsym n
      convert h using 1; push_cast; ring
  have hj : c - g.m ∈ shiftedCore g (f - F - g.m) := by
    change c - g.m + (f - F - g.m) ∈ stableCore g
    convert hk using 1; ring
  exact hrow.all_ap (shiftedCore_subset_gamma s hF hcan hsym hj)

/-- QM comes from the actual row, via CAN and its forbidden predecessor. -/
theorem pf_add_m_mem_tail (hrow : ActualRawRow s F f c)
    (hF : s.semigroup.IsFrobenius F) (hcan : s.semigroup.Canonical F g.m)
    (hsym : SymmetricAt g.H f) : (F + g.m - c) + g.m ∈ g.H := by
  have h := (hsym _).mp (hrow.backward_gap hF hcan hsym)
  convert h using 1; ring

theorem pf_add_tail_generator (hrow : ActualRawRow s F f c)
    (hF : s.semigroup.IsFrobenius F) (hcan : s.semigroup.Canonical F g.m)
    (hsym : SymmetricAt g.H f) (i : Fin 3) :
    (F + g.m - c) + g.n i ∈ g.Gamma :=
  (hrow.pf hF hcan hsym).2 _ (g.n_mem i)
    (by have := s.n_gt i; have := s.m_pos; omega)

/-- The same PF row forces failure of stability in each tail direction. -/
theorem predecessor_not_stable (hrow : ActualRawRow s F f c)
    (hF : s.semigroup.IsFrobenius F) (hcan : s.semigroup.Canonical F g.m)
    (hsym : SymmetricAt g.H f) (i : Fin 3) :
    c + (f - F - g.m) - g.n i ∉ stableCore g := by
  intro hk
  have hg : (F + g.m - c) + g.n i ∉ g.Gamma :=
    (gap_iff_stableCore hsym).mpr (by convert hk using 1; ring)
  exact hg (hrow.pf_add_tail_generator hF hcan hsym i)

theorem positive_hit_required (hrow : ActualRawRow s F f c)
    (hF : s.semigroup.IsFrobenius F) (hcan : s.semigroup.Canonical F g.m)
    (hsym : SymmetricAt g.H f) (i : Fin 3)
    (hbase : c + (f - F - g.m) - g.n i ∈ g.H) :
    ∃ n : ℕ, 1 ≤ n ∧ c + (f - F - g.m) - g.n i + (n : ℤ) * g.m ∉ g.H := by
  classical
  have h := hrow.predecessor_not_stable hF hcan hsym i
  change ¬ ∀ n : ℕ, c + (f - F - g.m) - g.n i + (n : ℤ) * g.m ∈ g.H at h
  push Not at h
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_, hn⟩
  by_contra hn0
  have he : n = 0 := by omega
  exact hn (by simpa [he] using hbase)

end ActualRawRow
end P21.Symmetric
