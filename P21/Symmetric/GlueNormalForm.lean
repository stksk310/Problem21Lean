import P21.Symmetric.StableCore
import P21.Symmetric.TwoGenerator

/-! The exact normal-form input of STD_SYM_GLUE, and its internal consequences.
The classification that produces this data from symmetry is not assumed here. -/
namespace P21.Symmetric

structure SymmetricGlueData (g : Generators) where
  perm : Equiv.Perm (Fin 3)
  two : TwoGeneratorData
  d : ℤ
  w : ℤ
  d_ge_two : 2 ≤ d
  coprime : Int.gcd d w = 1
  w_mem : w ∈ two.T
  x_eq : g.n (perm 0) = d * two.u
  y_eq : g.n (perm 1) = d * two.v
  z_eq : g.n (perm 2) = w

namespace SymmetricGlueData
variable {g : Generators} (D : SymmetricGlueData g)

theorem d_pos : 0 < D.d := lt_of_lt_of_le (by norm_num) D.d_ge_two

theorem bezout : D.d * Int.gcdA D.d D.w + D.w * Int.gcdB D.d D.w = 1 := by
  simpa [D.coprime] using (Int.gcd_eq_gcd_ab D.d D.w).symm

/-- Integer normal form exists without any semigroup membership premise. -/
theorem normal_form_exists (a : ℤ) :
    ∃ j t : ℤ, 0 ≤ j ∧ j < D.d ∧ a = j * D.w + D.d * t := by
  let j₀ := a * Int.gcdB D.d D.w
  refine ⟨j₀ % D.d, a * Int.gcdA D.d D.w + (j₀ / D.d) * D.w,
    Int.emod_nonneg _ (ne_of_gt D.d_pos), Int.emod_lt_of_pos _ D.d_pos, ?_⟩
  have hdiv := Int.ediv_mul_add_emod j₀ D.d
  dsimp [j₀] at *
  linear_combination -a * D.bezout - D.w * hdiv

theorem normal_form_unique {j t j' t' : ℤ}
    (hj : 0 ≤ j) (hjd : j < D.d) (hj' : 0 ≤ j') (hj'd : j' < D.d)
    (he : j * D.w + D.d * t = j' * D.w + D.d * t') : j = j' ∧ t = t' := by
  let k := (j-j') * Int.gcdA D.d D.w - (t-t') * Int.gcdB D.d D.w
  have hk : j-j' = k * D.d := by
    dsimp [k]
    linear_combination -(j-j') * D.bezout + Int.gcdB D.d D.w * he
  have hk0 : k = 0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hn | hn
    · have : k ≤ -1 := by omega
      nlinarith [D.d_pos]
    · have : 1 ≤ k := by omega
      nlinarith [D.d_pos]
  have hjj : j = j' := by rw [hk0] at hk; omega
  refine ⟨hjj, ?_⟩
  rw [hjj] at he
  nlinarith [D.d_pos]

/-- This monoid retains natural w-coefficients and genuine T-membership. -/
def represented : AddSubmonoid ℤ where
  carrier := {a | ∃ n : ℕ, ∃ t ∈ D.two.T, a = (n : ℤ) * D.w + D.d * t}
  zero_mem' := ⟨0, 0, D.two.T.zero_mem, by ring⟩
  add_mem' := by
    rintro a b ⟨n,t,ht,rfl⟩ ⟨n',t',ht',rfl⟩
    refine ⟨n+n', t+t', D.two.T.add_mem ht ht', ?_⟩
    push_cast
    ring

theorem d_mul_mem_tail {t : ℤ} (ht : t ∈ D.two.T) : D.d * t ∈ g.H := by
  obtain ⟨a,b,ha,hb,rfl⟩ := ht
  have h₁ := g.H.nsmul_mem (generator_mem g.n (D.perm 0)) a.toNat
  have h₂ := g.H.nsmul_mem (generator_mem g.n (D.perm 1)) b.toNat
  simp only [nsmul_eq_mul, Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb,
    D.x_eq, D.y_eq] at h₁ h₂
  convert g.H.add_mem h₁ h₂ using 1; ring

theorem w_mem_tail : D.w ∈ g.H := by
  rw [← D.z_eq]
  exact generator_mem g.n (D.perm 2)

/-- Equality with the actual three-generated tail is proved in both directions. -/
theorem represented_eq_tail : D.represented = g.H := by
  apply le_antisymm
  · rintro a ⟨n,t,ht,rfl⟩
    have hn := g.H.nsmul_mem D.w_mem_tail n
    simpa [nsmul_eq_mul] using g.H.add_mem hn (D.d_mul_mem_tail ht)
  · change generated g.n ≤ D.represented
    rw [generated_eq_closure]
    apply AddSubmonoid.closure_le.mpr
    rintro a ⟨i,rfl⟩
    obtain ⟨j,rfl⟩ := D.perm.surjective i
    fin_cases j
    · change g.n (D.perm 0) ∈ D.represented
      rw [D.x_eq]
      exact ⟨0,D.two.u,⟨1,0,by norm_num,by norm_num,by ring⟩,by ring⟩
    · change g.n (D.perm 1) ∈ D.represented
      rw [D.y_eq]
      exact ⟨0,D.two.v,⟨0,1,by norm_num,by norm_num,by ring⟩,by ring⟩
    · change g.n (D.perm 2) ∈ D.represented
      rw [D.z_eq]
      exact ⟨1,0,D.two.T.zero_mem,by ring⟩

theorem mem_tail_iff {a : ℤ} : a ∈ g.H ↔
    ∃ n : ℕ, ∃ t ∈ D.two.T, a = (n : ℤ) * D.w + D.d * t := by
  rw [← D.represented_eq_tail]
  rfl

/-- Bounded-layer membership comes from reducing an actual nonnegative coefficient. -/
theorem normal_form_mem_iff {j t : ℤ} (hj : 0 ≤ j) (hjd : j < D.d) :
    j * D.w + D.d * t ∈ g.H ↔ t ∈ D.two.T := by
  constructor
  · intro ht
    obtain ⟨n,a,ha,he⟩ := D.mem_tail_iff.1 ht
    let k : ℤ := (n : ℤ) / D.d
    have hk : 0 ≤ k := Int.ediv_nonneg (Int.natCast_nonneg n) D.d_pos.le
    have hkr : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
    have hw : k * D.w ∈ D.two.T := by
      simpa only [nsmul_eq_mul, hkr] using D.two.T.nsmul_mem D.w_mem k.toNat
    have hnorm : (n : ℤ) * D.w + D.d * a =
        ((n : ℤ) % D.d) * D.w + D.d * (a + k * D.w) := by
      have hdiv := Int.ediv_mul_add_emod (n : ℤ) D.d
      dsimp [k]
      linear_combination -D.w * hdiv
    have he' := he.trans hnorm
    have hu := D.normal_form_unique hj hjd
      (Int.emod_nonneg _ (ne_of_gt D.d_pos)) (Int.emod_lt_of_pos _ D.d_pos) he'
    rw [hu.2]
    exact D.two.T.add_mem ha hw
  · intro ht
    exact D.mem_tail_iff.2 ⟨j.toNat,t,ht,by rw [Int.toNat_of_nonneg hj]⟩

def frobenius : ℤ := (D.d - 1) * D.w + D.d * D.two.frobenius

/-- The Frobenius symmetry follows from bounded-layer membership and symmetry of T. -/
theorem symmetry : SymmetricAt g.H D.frobenius := by
  intro a
  obtain ⟨j,t,hj,hjd,rfl⟩ := D.normal_form_exists a
  have he : D.frobenius - (j * D.w + D.d * t) =
      (D.d - 1 - j) * D.w + D.d * (D.two.frobenius - t) := by
    unfold frobenius
    ring
  rw [he, D.normal_form_mem_iff hj hjd,
    D.normal_form_mem_iff (by omega : 0 ≤ D.d - 1 - j) (by omega)]
  exact D.two.frobenius_symmetry t

/-- Nonnegativity of the original tail identifies the symmetry center with F(H). -/
theorem isGreatest_gap (s : g.Setting) :
    IsGreatest {a : ℤ | a ∉ g.H} D.frobenius :=
  ⟨symmetricAt_f_not_mem D.symmetry, fun _ ht => symmetricAt_gap_le s D.symmetry ht⟩

theorem w_pos (s : g.Setting) : 0 < D.w := by
  have hn := s.n_gt (D.perm 2)
  rw [D.z_eq] at hn
  exact lt_trans s.m_pos hn

theorem normal_form_existsUnique (a : ℤ) :
    ∃! jt : ℤ × ℤ, 0 ≤ jt.1 ∧ jt.1 < D.d ∧ a = jt.1 * D.w + D.d * jt.2 := by
  obtain ⟨j,t,hj,hjd,he⟩ := D.normal_form_exists a
  refine ⟨(j,t), ⟨hj,hjd,he⟩, ?_⟩
  rintro ⟨j',t'⟩ ⟨hj',hj'd,he'⟩
  obtain ⟨rfl,rfl⟩ := D.normal_form_unique hj' hj'd hj hjd (he'.symm.trans he)
  rfl

/-- The glued tail is cofinite by the proved integer Frobenius symmetry. -/
def tailSemigroup (s : g.Setting) : NumericalSemigroup where
  carrier := g.H
  nonneg := fun _ ht => s.semigroup.nonneg _ (g.h_subset_gamma ht)
  cofinite := ⟨D.frobenius + 1, fun a ha => by
    by_contra hgap
    have := symmetricAt_gap_le s D.symmetry hgap
    omega⟩

theorem isFrobenius (s : g.Setting) : (D.tailSemigroup s).IsFrobenius D.frobenius :=
  D.isGreatest_gap s

end SymmetricGlueData
end P21.Symmetric


