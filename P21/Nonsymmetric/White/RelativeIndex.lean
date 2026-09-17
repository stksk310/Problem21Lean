import P21.Nonsymmetric.ColorCap.RelativeLattice
import P21.Nonsymmetric.PrimitiveGenerators
import Mathlib.Data.Int.ModEq

namespace P21.Nonsymmetric.White
open ColorCap

/-- The original weight map is onto Z because the tail is primitive. -/
theorem weight_surjective {g : Generators}
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H) :
    Function.Surjective (weight g.n) := by
  obtain ⟨v,hv⟩ := tail_bezout_vector hcof
  intro r
  refine ⟨fun i => r*v i,?_⟩
  change ∑ i, (r*v i)*g.n i = r
  simp only [mul_assoc,← Finset.mul_sum]
  change r*integerValue g v = r
  rw [hv,mul_one]

/-- Equality of relative-lattice cosets is exactly equality of weight residues. -/
theorem relative_coset_iff (n : Point) (d : ℤ) (u v : Point) :
    u-v ∈ relativeLattice n d ↔ weight n u % d = weight n v % d := by
  change d ∣ weight n (u-v) ↔ _
  rw [weight_sub,Int.dvd_iff_emod_eq_zero]
  exact Int.emod_eq_emod_iff_emod_sub_eq_zero.symm

/-- A specialized index statement: every coset has exactly one residue in [0,d).
Together with residue_realized, this identifies the cosets with exactly d integers. -/
theorem relative_residue_unique (n : Point) (d : ℤ) (hd : 0 < d) (u : Point) :
    ∃! r : ℤ, 0 ≤ r ∧ r < d ∧ weight n u % d = r := by
  refine ⟨weight n u % d,⟨Int.emod_nonneg _ (ne_of_gt hd),Int.emod_lt_of_pos _ hd,rfl⟩,?_⟩
  intro r hr
  exact hr.2.2.symm

theorem residue_realized {g : Generators}
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (d r : ℤ) (hr : 0 ≤ r) (hrd : r < d) :
    ∃ u : Point, weight g.n u % d = r := by
  obtain ⟨u,hu⟩ := weight_surjective hcof r
  exact ⟨u,by rw [hu,Int.emod_eq_of_lt hr hrd]⟩

/-- The relative quotient L_m/L_(km) has exactly the k height residues. -/
theorem relative_level_residue_unique (n : Point) (m k : ℤ)
    (hm : 0 < m) (hk : 0 < k) (u : Point) (hu : u ∈ relativeLattice n m) :
    ∃! r : ℤ, 0 ≤ r ∧ r < k ∧ ∃ t : ℤ, weight n u = (r+k*t)*m := by
  obtain ⟨l,hl⟩ := hu
  refine ⟨l%k,⟨Int.emod_nonneg _ (ne_of_gt hk),Int.emod_lt_of_pos _ hk,l/k,?_⟩,?_⟩
  · linear_combination hl - m*(Int.emod_add_ediv_mul l k)
  · rintro r ⟨hr,hrk,t,ht⟩
    have he : l = r+k*t := by nlinarith [hl]
    rw [he,Int.add_mul_emod_self_left,Int.emod_eq_of_lt hr hrk]

theorem relative_level_residue_realized {g : Generators}
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H) (m r : ℤ) :
    ∃ u : Point, u ∈ relativeLattice g.n m ∧ weight g.n u = r*m := by
  obtain ⟨u,hu⟩ := weight_surjective hcof (r*m)
  exact ⟨u,show m ∣ weight g.n u by rw [hu]; exact dvd_mul_left m r,hu⟩


/-- Two points of L_m have the same L_(km) coset exactly when their integer
height levels have the same residue modulo k. -/
theorem relative_level_coset_iff (n : Point) (m k : ℤ) (hm : m ≠ 0)
    (u v : Point) (l r : ℤ) (hu : weight n u=l*m) (hv : weight n v=r*m) :
    u-v ∈ relativeLattice n (k*m) ↔ l%k=r%k := by
  change k*m ∣ weight n (u-v) ↔ _
  rw [weight_sub,hu,hv,← sub_mul,mul_dvd_mul_iff_right hm,Int.dvd_iff_emod_eq_zero]
  exact Int.emod_eq_emod_iff_emod_sub_eq_zero.symm

/-- Canonical representatives for every relative quotient class, with exactly
one representative per height residue. Their existence uses primitive tail. -/
theorem relative_cyclic_representatives {g : Generators}
    (hcof : ∃ B : ℤ,∀ x : ℤ,B ≤ x → x ∈ g.H)
    (m k : ℤ) (hm : 0 < m) (hk : 0 < k) :
    ∃ v : Point, weight g.n v=m ∧
      ∀ u : Point,u ∈ relativeLattice g.n m →
        ∃! r : ℤ, 0 ≤ r ∧ r < k ∧
          u-(fun i => r*v i) ∈ relativeLattice g.n (k*m) := by
  obtain ⟨v,hv⟩ := weight_surjective hcof m
  refine ⟨v,hv,?_⟩
  intro u hu
  obtain ⟨l,hl⟩ := hu
  have hl' : weight g.n u=l*m := by linarith [hl]
  have hmul (r : ℤ) : weight g.n (fun i => r*v i)=r*m := by
    simp only [weight,mul_assoc,← Finset.mul_sum]
    change r*weight g.n v=r*m
    rw [hv]
  refine ⟨l%k,⟨Int.emod_nonneg _ (ne_of_gt hk),Int.emod_lt_of_pos _ hk,?_⟩,?_⟩
  · rw [relative_level_coset_iff g.n m k (ne_of_gt hm) u _ l (l%k) hl' (hmul _)]
    rw [Int.emod_emod]
  · rintro r ⟨hr,hrk,hrcoset⟩
    have he := (relative_level_coset_iff g.n m k (ne_of_gt hm) u _ l r hl' (hmul r)).mp hrcoset
    rw [Int.emod_eq_of_lt hr hrk] at he
    exact he.symm

end P21.Nonsymmetric.White
