import P21.Symmetric.GlueNormalForm

namespace P21.Symmetric.Classification

/-- Irredundancy excludes every actual nonnegative representation off one index. -/
theorem tail_not_two (g : Generators) (s : g.Setting)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k)
    (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    g.n i ≠ a * g.n j + b * g.n k := by
  classical
  intro he
  apply g.tail_minimal s.minimal i
    (fun t => (if t = j then a.toNat else 0) + (if t = k then b.toNat else 0))
    (by simp [hij, hik])
  simp [value, Nat.cast_add, add_mul, Finset.sum_add_distrib,
    Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb, he]

/-- Once a primitive special pair is found, minimality supplies every lower bound. -/
theorem decomposition_glue_data (g : Generators) (s : g.Setting)
    (hcommon : ∀ d : ℤ, (∀ i, d ∣ g.n i) → d ∣ 1)
    (p : Equiv.Perm (Fin 3)) (d u v : ℤ) (hd : 0 < d)
    (hx : g.n (p 0) = d * u) (hy : g.n (p 1) = d * v)
    (huv : Int.gcd u v = 1)
    (hmem : ∃ a b : ℤ, 0 ≤ a ∧ 0 ≤ b ∧ g.n (p 2) = a * u + b * v) :
    Nonempty (SymmetricGlueData g) := by
  have hp01 : p 0 ≠ p 1 := fun h => by have hh := congrArg Fin.val (p.injective h); norm_num at hh
  have hp02 : p 0 ≠ p 2 := fun h => by have hh := congrArg Fin.val (p.injective h); norm_num at hh
  have hp12 : p 1 ≠ p 2 := fun h => by have hh := congrArg Fin.val (p.injective h); norm_num at hh
  have hxpos : 0 < g.n (p 0) := lt_trans s.m_pos (s.n_gt _)
  have hypos : 0 < g.n (p 1) := lt_trans s.m_pos (s.n_gt _)
  have hu : 0 < u := by nlinarith
  have hv : 0 < v := by nlinarith
  have hu2 : 2 ≤ u := by
    by_contra h
    have hu1 : u = 1 := by omega
    apply tail_not_two g s (p 1) (p 0) (p 0) hp01.symm hp01.symm v 0 hv.le (by omega)
    rw [hx, hy, hu1]
    ring
  have hv2 : 2 ≤ v := by
    by_contra h
    have hv1 : v = 1 := by omega
    apply tail_not_two g s (p 0) (p 1) (p 1) hp01 hp01 u 0 hu.le (by omega)
    rw [hx, hy, hv1]
    ring
  obtain ⟨a,b,ha,hb,he⟩ := hmem
  have hd2 : 2 ≤ d := by
    by_contra h
    have hd1 : d = 1 := by omega
    apply tail_not_two g s (p 2) (p 0) (p 1) hp02.symm hp12.symm a b ha hb
    simpa [hx, hy, hd1] using he
  have hcop : Int.gcd d (g.n (p 2)) = 1 := by
    have hall : ∀ i, (Int.gcd d (g.n (p 2)) : ℤ) ∣ g.n i := by
      intro i
      obtain ⟨j,rfl⟩ := p.surjective i
      fin_cases j
      · change (Int.gcd d (g.n (p 2)) : ℤ) ∣ g.n (p 0)
        rw [hx]
        exact dvd_mul_of_dvd_left (Int.gcd_dvd_left _ _) _
      · change (Int.gcd d (g.n (p 2)) : ℤ) ∣ g.n (p 1)
        rw [hy]
        exact dvd_mul_of_dvd_left (Int.gcd_dvd_left _ _) _
      · exact Int.gcd_dvd_right _ _
    have hc := hcommon _ hall
    have hn : Int.gcd d (g.n (p 2)) ∣ 1 := by exact_mod_cast hc
    exact Nat.dvd_one.mp hn
  exact ⟨{ perm := p
           two := ⟨u,v,hu2,hv2,huv⟩
           d := d
           w := g.n (p 2)
           d_ge_two := hd2
           coprime := hcop
           w_mem := ⟨a,b,ha,hb,he⟩
           x_eq := hx
           y_eq := hy
           z_eq := rfl }⟩

/-- Exact gcd quotients turn special-pair membership into the frozen gluing structure. -/
theorem special_pair_glue_data (g : Generators) (s : g.Setting)
    (hcommon : ∀ d : ℤ, (∀ i, d ∣ g.n i) → d ∣ 1)
    (p : Equiv.Perm (Fin 3))
    (hmem : ∃ a b : ℤ, 0 ≤ a ∧ 0 ≤ b ∧
      g.n (p 2) = a * (g.n (p 0) / (Int.gcd (g.n (p 0)) (g.n (p 1)) : ℤ)) +
        b * (g.n (p 1) / (Int.gcd (g.n (p 0)) (g.n (p 1)) : ℤ))) :
    Nonempty (SymmetricGlueData g) := by
  have hxpos : 0 < g.n (p 0) := lt_trans s.m_pos (s.n_gt _)
  have hgd : 0 < Int.gcd (g.n (p 0)) (g.n (p 1)) :=
    Int.gcd_pos_of_ne_zero_left _ (ne_of_gt hxpos)
  apply decomposition_glue_data g s hcommon p
    (Int.gcd (g.n (p 0)) (g.n (p 1))) _ _ (by exact_mod_cast hgd)
  · exact (Int.mul_ediv_cancel' (Int.gcd_dvd_left _ _)).symm
  · exact (Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)).symm
  · exact Int.gcd_ediv_gcd_ediv_gcd hgd
  · exact hmem

end P21.Symmetric.Classification

namespace P21.Symmetric.Classification

/-- The primitive quotient pair retains irredundant generators greater than one. -/
theorem primitive_pair_data (g : Generators) (s : g.Setting)
    (p : Equiv.Perm (Fin 3)) :
    ∃ D : TwoGeneratorData,
      D.u = g.n (p 0) / (Int.gcd (g.n (p 0)) (g.n (p 1)) : ℤ) ∧
      D.v = g.n (p 1) / (Int.gcd (g.n (p 0)) (g.n (p 1)) : ℤ) ∧
      g.n (p 0) = (Int.gcd (g.n (p 0)) (g.n (p 1)) : ℤ) * D.u ∧
      g.n (p 1) = (Int.gcd (g.n (p 0)) (g.n (p 1)) : ℤ) * D.v := by
  let d : ℤ := Int.gcd (g.n (p 0)) (g.n (p 1))
  let u := g.n (p 0) / d
  let v := g.n (p 1) / d
  have hxpos : 0 < g.n (p 0) := lt_trans s.m_pos (s.n_gt _)
  have hypos : 0 < g.n (p 1) := lt_trans s.m_pos (s.n_gt _)
  have hgd : 0 < Int.gcd (g.n (p 0)) (g.n (p 1)) :=
    Int.gcd_pos_of_ne_zero_left _ (ne_of_gt hxpos)
  have hd : 0 < d := by dsimp [d]; exact_mod_cast hgd
  have hx : g.n (p 0) = d * u := (Int.mul_ediv_cancel' (Int.gcd_dvd_left _ _)).symm
  have hy : g.n (p 1) = d * v := (Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)).symm
  have hu : 0 < u := by nlinarith
  have hv : 0 < v := by nlinarith
  have hp01 : p 0 ≠ p 1 := fun h => by have hh := congrArg Fin.val (p.injective h); norm_num at hh
  have hu2 : 2 ≤ u := by
    by_contra h
    have hu1 : u = 1 := by omega
    apply tail_not_two g s (p 1) (p 0) (p 0) hp01.symm hp01.symm v 0 hv.le (by omega)
    rw [hx, hy, hu1]
    ring
  have hv2 : 2 ≤ v := by
    by_contra h
    have hv1 : v = 1 := by omega
    apply tail_not_two g s (p 0) (p 1) (p 1) hp01 hp01 u 0 hu.le (by omega)
    rw [hx, hy, hv1]
    ring
  exact ⟨⟨u,v,hu2,hv2,Int.gcd_ediv_gcd_ediv_gcd hgd⟩,rfl,rfl,hx,hy⟩

end P21.Symmetric.Classification




namespace P21.Symmetric.Classification

/-- The rectangular Apéry relation supplies a primitive gluing after reordering. -/
theorem rectangle_glue_data (g : Generators) (s : g.Setting)
    (hcommon : ∀ d : ℤ, (∀ i, d ∣ g.n i) → d ∣ 1)
    (p : Equiv.Perm (Fin 3)) (L M r q b : ℤ) (hL : 0 < L)
    (hq : 0 ≤ q) (hb : 0 ≤ b)
    (hx : g.n (p 0) = L * M) (hz : g.n (p 2) = L * r)
    (hy : g.n (p 1) = q * M + b * r) : Nonempty (SymmetricGlueData g) := by
  have hcop : Int.gcd M r = 1 := by
    have hall : ∀ i, (Int.gcd M r : ℤ) ∣ g.n i := by
      intro i
      obtain ⟨j,rfl⟩ := p.surjective i
      fin_cases j
      · change (Int.gcd M r : ℤ) ∣ g.n (p 0)
        rw [hx]
        exact dvd_mul_of_dvd_right (Int.gcd_dvd_left _ _) _
      · change (Int.gcd M r : ℤ) ∣ g.n (p 1)
        rw [hy]
        exact dvd_add (dvd_mul_of_dvd_right (Int.gcd_dvd_left _ _) _)
          (dvd_mul_of_dvd_right (Int.gcd_dvd_right _ _) _)
      · change (Int.gcd M r : ℤ) ∣ g.n (p 2)
        rw [hz]
        exact dvd_mul_of_dvd_right (Int.gcd_dvd_right _ _) _
    have hc := hcommon _ hall
    have hn : Int.gcd M r ∣ 1 := by exact_mod_cast hc
    exact Nat.dvd_one.mp hn
  let p' : Equiv.Perm (Fin 3) := (Equiv.swap 1 2).trans p
  have hp0 : p' 0 = p 0 := by simp [p', Equiv.trans_apply, Equiv.swap_apply_def]
  have hp1 : p' 1 = p 2 := by simp [p', Equiv.trans_apply]
  have hp2 : p' 2 = p 1 := by simp [p', Equiv.trans_apply]
  apply decomposition_glue_data g s hcommon p' L M r hL
  · simpa [hp0] using hx
  · simpa [hp1] using hz
  · exact hcop
  · exact ⟨q,b,hq,hb,by simpa [hp2] using hy⟩

end P21.Symmetric.Classification

