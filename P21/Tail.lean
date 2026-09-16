import P21.CanonicalReduction

namespace P21

theorem divisor_of_generated {k : ℕ} {n : Fin k → ℤ} {d x : ℤ}
    (hd : ∀ i, d ∣ n i) (hx : x ∈ generated n) : d ∣ x := by
  obtain ⟨a, rfl⟩ := hx
  exact Finset.dvd_sum fun i _ => dvd_mul_of_dvd_right (hd i) _

theorem generated_eq_closure {k : ℕ} (n : Fin k → ℤ) :
    generated n = AddSubmonoid.closure (Set.range n) := by
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    apply AddSubmonoid.sum_mem
    intro i _
    simpa [nsmul_eq_mul] using (AddSubmonoid.closure (Set.range n)).nsmul_mem
      (AddSubmonoid.subset_closure (Set.mem_range_self i)) (a i)
  · exact AddSubmonoid.closure_le.mpr (by rintro x ⟨i, rfl⟩; exact generator_mem n i)

theorem signed_mem_group {k : ℕ} {n : Fin k → ℤ} {x : ℤ} (a : SignedRepresentation n x) :
    x ∈ AddSubgroup.closure (Set.range n) := by
  rw [← a.equation]
  apply AddSubgroup.sum_mem
  intro i _
  simpa [zsmul_eq_mul] using (AddSubgroup.closure (Set.range n)).zsmul_mem
    (AddSubgroup.subset_closure (Set.mem_range_self i)) (a.coeff i)

namespace Generators
namespace Setting
variable {g : Generators} (s : g.Setting)
include s

/-- C2.4 signed group witness from the three actual Apéry elements. -/
theorem tail_signed_m {F : ℤ} (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) (hQ : (s.semigroup.Q F).Nonempty) :
    Nonempty (SignedRepresentation g.n g.m) := by
  obtain ⟨q, hq⟩ := hQ
  obtain ⟨a, ha⟩ := s.apery_in_tail
    (s.semigroup.pf_add_m_mem_apery g.m_mem (ne_of_gt s.m_pos) hq.1)
  obtain ⟨b, hb⟩ := s.apery_in_tail (s.semigroup.complement_of_q_mem_apery hF hc hq)
  obtain ⟨c, hc'⟩ := s.apery_in_tail (s.semigroup.W_mem_apery hF s.m_pos)
  refine ⟨⟨fun i => (a i : ℤ) + b i - c i, ?_⟩⟩
  simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  change value g.n a + value g.n b - value g.n c = g.m
  rw [ha, hb, hc']
  ring

theorem m_mem_tail_group {F : ℤ} (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) (hQ : (s.semigroup.Q F).Nonempty) :
    g.m ∈ AddSubgroup.closure (Set.range g.n) := by
  obtain ⟨a⟩ := s.tail_signed_m hF hc hQ
  exact signed_mem_group a

/-- Cofiniteness kills every common divisor: two consecutive large elements suffice. -/
theorem common_divisor_dvd_one {d : ℤ} (hm : d ∣ g.m) (hn : ∀ i, d ∣ g.n i) : d ∣ 1 := by
  have hall : ∀ i, d ∣ g.all i := by
    intro i
    exact Fin.cases hm hn i
  obtain ⟨B, hB⟩ := s.cofinite
  have h0 := divisor_of_generated hall (hB B le_rfl)
  have h1 := divisor_of_generated hall (hB (B + 1) (by omega))
  have := dvd_sub h1 h0
  simpa using this

theorem tail_common_divisor_dvd_one {F d : ℤ} (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) (hQ : (s.semigroup.Q F).Nonempty)
    (hn : ∀ i, d ∣ g.n i) : d ∣ 1 := by
  obtain ⟨a⟩ := s.tail_signed_m hF hc hQ
  have hm : d ∣ g.m := by
    rw [← a.equation]
    exact Finset.dvd_sum fun i _ => dvd_mul_of_dvd_right (hn i) _
  exact s.common_divisor_dvd_one hm hn

theorem tail_gcd_eq_one {F : ℤ} (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) (hQ : (s.semigroup.Q F).Nonempty) : g.tailGcd = 1 := by
  have hd : ∀ i, (g.tailGcd : ℤ) ∣ g.n i := by
    intro i
    rw [Int.natCast_dvd]
    fin_cases i
    · exact Nat.gcd_dvd_left _ _
    · exact dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
    · exact dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)
  have h := s.tail_common_divisor_dvd_one hF hc hQ hd
  have hnat : g.tailGcd ∣ 1 := by exact_mod_cast h
  exact Nat.eq_one_of_dvd_one hnat

theorem natural_closure_to_tail {x : ℕ}
    (hx : x ∈ AddSubmonoid.closure (Set.range (fun i => (g.n i).toNat))) : (x : ℤ) ∈ g.H := by
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    have hn : 0 ≤ g.n i := (lt_trans s.m_pos (s.n_gt i)).le
    simpa [H, Int.toNat_of_nonneg hn] using generator_mem g.n i
  | zero => simp
  | add x y _ _ hx hy => simpa using g.H.add_mem hx hy

/-- The tail is cofinite, not merely a gcd-one family. -/
theorem tail_cofinite {F : ℤ} (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) (hQ : (s.semigroup.Q F).Nonempty) :
    ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H := by
  let T : Set ℕ := Set.range (fun i => (g.n i).toNat)
  have hdiv : ∀ i, (Nat.setGcd T : ℤ) ∣ g.n i := by
    intro i
    have h := Nat.setGcd_dvd_of_mem (s := T) (Set.mem_range_self i)
    have hn : 0 ≤ g.n i := (lt_trans s.m_pos (s.n_gt i)).le
    have h' : (Nat.setGcd T : ℤ) ∣ ((g.n i).toNat : ℤ) := by exact_mod_cast h
    simpa [H, Int.toNat_of_nonneg hn] using h'
  have hd1 := s.tail_common_divisor_dvd_one hF hc hQ hdiv
  have hnat : Nat.setGcd T ∣ 1 := by exact_mod_cast hd1
  have hg : Nat.setGcd T = 1 := Nat.eq_one_of_dvd_one hnat
  obtain ⟨B, hB⟩ := Nat.exists_mem_closure_of_ge T
  refine ⟨B, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := le_trans (Int.natCast_nonneg B) hx
  have hb : B ≤ x.toNat := by omega
  have hc' := hB x.toNat hb (by simp [hg])
  simpa [Int.toNat_of_nonneg hx0] using s.natural_closure_to_tail hc'

def tailSemigroup {F : ℤ} (hF : s.semigroup.IsFrobenius F)
    (hc : s.semigroup.Canonical F g.m) (hQ : (s.semigroup.Q F).Nonempty) : NumericalSemigroup where
  carrier := g.H
  nonneg := fun _ hx => generated_nonneg (fun i => (lt_trans s.m_pos (s.n_gt i)).le) hx
  cofinite := s.tail_cofinite hF hc hQ

end Setting
end Generators
end P21
