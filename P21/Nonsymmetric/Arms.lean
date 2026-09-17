import P21.Nonsymmetric.HerzogCoordinates
import P21.Nonsymmetric.Rows

namespace P21.Nonsymmetric

theorem tail_pf_of_generator_returns {g : Generators} {q : ℤ}
    (hq : q ∉ g.H) (hret : ∀ i, q + g.n i ∈ g.H) : q ∈ TailPF g := by
  refine ⟨hq, ?_⟩
  intro t ht hne
  obtain ⟨a⟩ := actual_iff_mem.mpr ht
  have hp : ∃ i, 0 < a.coeff i := by
    by_contra hn
    have hz : ∀ i, a.coeff i = 0 := by intro i; by_contra hi; exact hn ⟨i, by omega⟩
    have he := a.equation
    simp [value, hz] at he
    exact hne he.symm
  obtain ⟨i, hi⟩ := hp
  have hm := g.H.add_mem (hret i) (actual_iff_mem.mp ⟨removeOne a i hi⟩)
  convert hm using 1; ring

/-- The maximal gap along the missing direction is chosen from a bounded
integer set, not from a presumed connectivity property. -/
theorem maximal_gap_along_direction {g : Generators} (hpos : ∀ i, 0 < g.n i)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    {q : ℤ} (i : Fin 3) (hgap : q + g.n i ∉ g.H)
    (hret : ∀ j, j ≠ i → q + g.n j ∈ g.H) :
    ∃ l : ℤ, 1 ≤ l ∧ q + l*g.n i ∈ TailPF g := by
  classical
  obtain ⟨B, hB⟩ := hcof
  let T : Set ℤ := {l | 0 ≤ l ∧ q + l*g.n i ∉ g.H}
  have hf : T.Finite := by
    apply (Set.finite_Icc 0 (B-q)).subset
    intro l hl
    have hb : q + l*g.n i < B := lt_of_not_ge (fun hx => hl.2 (hB _ hx))
    have hn := hpos i
    have hln : l ≤ l*g.n i := by nlinarith [hl.1]
    exact ⟨hl.1, by omega⟩
  have h1 : (1 : ℤ) ∈ T := ⟨by omega, by simpa using hgap⟩
  obtain ⟨l, hl, hm⟩ := Set.exists_max_image T id hf ⟨1,h1⟩
  have hl1 : 1 ≤ l := hm 1 h1
  refine ⟨l, hl1, tail_pf_of_generator_returns hl.2 ?_⟩
  intro j
  by_cases hj : j = i
  · subst j
    by_contra hh
    have hmem : l+1 ∈ T := ⟨by omega, by convert hh using 1; ring⟩
    have := hm (l+1) hmem
    simp only [id_eq] at this
    omega
  · have hn := g.H.nsmul_mem (generator_mem g.n i) l.toNat
    have hadd := g.H.add_mem (hret j hj) hn
    simp only [nsmul_eq_mul, Int.toNat_of_nonneg hl.1] at hadd
    convert hadd using 1; ring

theorem critical_pair_lower_bound {g : Generators} (D : HerzogCriticalData g)
    {i k : Fin 3} (hik : i ≠ k) {c d : ℤ} (hc : 0 < c) (hd : 0 ≤ d)
    (he : c*g.n k = d*g.n i) : (D.rho k : ℤ) ≤ c := by
  classical
  have hm := D.critical_minimal k c.toNat (by omega)
    (fun j => if j = i then d.toNat else 0)
    (by simp [Ne.symm hik])
    (by simpa [value, Int.toNat_of_nonneg hc.le, Int.toNat_of_nonneg hd] using he)
  exact_mod_cast (show (D.rho k : ℤ) ≤ (c.toNat : ℤ) from by exact_mod_cast hm) |>.trans_eq
    (Int.toNat_of_nonneg hc.le)

/-- The displayed signed expression is compared with an actual return first;
only the resulting positive pure-tail relation invokes criticality. -/
theorem arm_depth_bound {g : Generators} (hpos : ∀ i, 0 < g.n i)
    (D : HerzogCriticalData g) {q c l : ℤ} {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hq : q ∉ g.H) (hret : q + g.n j ∈ g.H)
    (he : q + g.n j = (c-l-1)*g.n i + (D.rho k-1 : ℤ)*g.n k) : l < c := by
  obtain ⟨a⟩ := actual_iff_mem.mpr hret
  have hz : a.coeff j = 0 := by
    by_contra hn
    have hm := actual_iff_mem.mp ⟨removeOne a j (Nat.pos_of_ne_zero hn)⟩
    exact hq (by simpa [Generators.H] using hm)
  obtain ⟨x,z,hxz⟩ := (Generators.offDirection_iff_pair (Ne.symm hij) hjk hik _).mp ⟨a,hz⟩
  by_contra hlt
  have hd : 0 < l-c+1+(x : ℤ) := by omega
  have heq : (D.rho k-1-(z : ℤ))*g.n k = (l-c+1+(x : ℤ))*g.n i := by
    linear_combination hxz - he
  have hleft : 0 < (D.rho k-1-(z : ℤ)) := by
    have hp := mul_pos hd (hpos i)
    rw [← heq] at hp
    exact (mul_pos_iff_of_pos_right (hpos k)).mp hp
  have hb := critical_pair_lower_bound D hik hleft hd.le heq
  omega

theorem fA_return_formula {g : Generators} (D : HerzogCriticalData g) (i : Fin 3) :
    D.fA + g.n (next i) = (D.a i-1 : ℤ)*g.n i + (D.rho (prev i)-1 : ℤ)*g.n (prev i) := by
  have h := D.fA_cyclic (prev i)
  have hn : next (prev i) = i := by fin_cases i <;> decide
  have hp : prev (prev i) = next i := by fin_cases i <;> decide
  rw [hn, hp] at h
  linear_combination h

theorem fB_return_formula {g : Generators} (D : HerzogCriticalData g) (i : Fin 3) :
    D.fB + g.n (prev i) = (D.b i-1 : ℤ)*g.n i + (D.rho (next i)-1 : ℤ)*g.n (next i) := by
  have h := D.fB_cyclic (next i)
  have hn : next (next i) = prev i := by fin_cases i <;> decide
  have hp : prev (next i) = i := by fin_cases i <;> decide
  rw [hn, hp] at h
  linear_combination h

theorem six_arm_atlas {g : Generators} (hpos : ∀ i, 0 < g.n i)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (D : NonsymmetricHerzogData g) {q : ℤ} (i : Fin 3)
    (hq : q ∉ g.H) (hgap : q + g.n i ∉ g.H)
    (hret : ∀ j, j ≠ i → q + g.n j ∈ g.H) :
    (∃ l : ℤ, 1 ≤ l ∧ l ≤ D.a i-1 ∧ q = D.fA-l*g.n i) ∨
    (∃ l : ℤ, 1 ≤ l ∧ l ≤ D.b i-1 ∧ q = D.fB-l*g.n i) := by
  obtain ⟨l, hl, hp⟩ := maximal_gap_along_direction hpos hcof i hgap hret
  rw [D.pf_exact] at hp
  rcases hp with he | he
  · have heq : q+l*g.n i = D.fA := he
    have form := fA_return_formula D.toHerzogCriticalData i
    have hb := arm_depth_bound hpos D.toHerzogCriticalData (cyclic_distinct i).1
      (cyclic_distinct i).2.1 (cyclic_distinct i).2.2 hq
      (hret _ (Ne.symm (cyclic_distinct i).1))
      (show q+g.n (next i) = (D.a i-l-1 : ℤ)*g.n i + (D.rho (prev i)-1 : ℤ)*g.n (prev i) by
        linear_combination form + heq)
    exact Or.inl ⟨l,hl,by omega,by linear_combination heq⟩
  · have heq : q+l*g.n i = D.fB := he
    have form := fB_return_formula D.toHerzogCriticalData i
    have hb := arm_depth_bound hpos D.toHerzogCriticalData (cyclic_distinct i).2.1
      (cyclic_distinct i).1 (Ne.symm (cyclic_distinct i).2.2) hq
      (hret _ (Ne.symm (cyclic_distinct i).2.1))
      (show q+g.n (prev i) = (D.b i-l-1 : ℤ)*g.n i + (D.rho (next i)-1 : ℤ)*g.n (next i) by
        linear_combination form + heq)
    exact Or.inr ⟨l,hl,by omega,by linear_combination heq⟩

theorem pair_nonnegative_mem {g : Generators} (i j : Fin 3) {a b : ℤ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) : a*g.n i+b*g.n j ∈ g.H := by
  have hm := g.H.add_mem (g.H.nsmul_mem (generator_mem g.n i) a.toNat)
    (g.H.nsmul_mem (generator_mem g.n j) b.toNat)
  simpa [nsmul_eq_mul, Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb] using hm

theorem gap_sub_multiple {g : Generators} {f l : ℤ} (hf : f ∉ g.H)
    (i : Fin 3) (hl : 0 ≤ l) : f-l*g.n i ∉ g.H := by
  intro hmem
  have hm := g.H.add_mem hmem (g.H.nsmul_mem (generator_mem g.n i) l.toNat)
  simp only [nsmul_eq_mul, Int.toNat_of_nonneg hl] at hm
  exact hf (by convert hm using 1; ring)

theorem armA_returns {g : Generators} (D : NonsymmetricHerzogData g) (i : Fin 3)
    {l : ℤ} (hl : 1 ≤ l) (hu : l ≤ D.a i-1) :
    D.fA-l*g.n i ∉ g.H ∧ (D.fA-l*g.n i)+g.n i ∉ g.H ∧
      ∀ j, j ≠ i → (D.fA-l*g.n i)+g.n j ∈ g.H := by
  have hf : D.fA ∉ g.H := by
    have hh : D.fA ∈ TailPF g := by rw [D.pf_exact]; simp
    exact hh.1
  refine ⟨gap_sub_multiple hf i (by omega), ?_, ?_⟩
  · have hh := gap_sub_multiple hf i (show 0 ≤ l-1 by omega)
    convert hh using 1; ring
  · intro j hji
    have hor : j = next i ∨ j = prev i := by
      fin_cases i <;> fin_cases j <;> simp_all [next,prev]
    rcases hor with rfl | rfl
    · have form := fA_return_formula D.toHerzogCriticalData i
      have hm := pair_nonnegative_mem (g:=g) i (prev i)
        (show 0 ≤ (D.a i : ℤ)-l-1 by omega)
        (show 0 ≤ (D.rho (prev i) : ℤ)-1 by have := D.rho_pos (prev i); omega)
      convert hm using 1
      linear_combination form
    · have form := D.fA_cyclic i
      have hr : (D.rho i : ℤ) = D.a i + D.b i := by exact_mod_cast D.rho_eq i
      have hm := pair_nonnegative_mem (g:=g) i (next i)
        (show 0 ≤ (D.rho i : ℤ)-l-1 by have := D.b_pos i; omega)
        (show 0 ≤ (D.a (next i) : ℤ)-1 by have := D.a_pos (next i); omega)
      convert hm using 1
      linear_combination form

theorem armB_returns {g : Generators} (D : NonsymmetricHerzogData g) (i : Fin 3)
    {l : ℤ} (hl : 1 ≤ l) (hu : l ≤ D.b i-1) :
    D.fB-l*g.n i ∉ g.H ∧ (D.fB-l*g.n i)+g.n i ∉ g.H ∧
      ∀ j, j ≠ i → (D.fB-l*g.n i)+g.n j ∈ g.H := by
  have hf : D.fB ∉ g.H := by
    have hh : D.fB ∈ TailPF g := by rw [D.pf_exact]; simp
    exact hh.1
  refine ⟨gap_sub_multiple hf i (by omega), ?_, ?_⟩
  · have hh := gap_sub_multiple hf i (show 0 ≤ l-1 by omega)
    convert hh using 1; ring
  · intro j hji
    have hor : j = next i ∨ j = prev i := by
      fin_cases i <;> fin_cases j <;> simp_all [next,prev]
    rcases hor with rfl | rfl
    · have form := D.fB_cyclic i
      have hr : (D.rho i : ℤ) = D.a i + D.b i := by exact_mod_cast D.rho_eq i
      have hm := pair_nonnegative_mem (g:=g) i (prev i)
        (show 0 ≤ (D.rho i : ℤ)-l-1 by have := D.a_pos i; omega)
        (show 0 ≤ (D.b (prev i) : ℤ)-1 by have := D.b_pos (prev i); omega)
      convert hm using 1
      linear_combination form
    · have form := fB_return_formula D.toHerzogCriticalData i
      have hm := pair_nonnegative_mem (g:=g) i (next i)
        (show 0 ≤ (D.b i : ℤ)-l-1 by omega)
        (show 0 ≤ (D.rho (next i) : ℤ)-1 by have := D.rho_pos (next i); omega)
      convert hm using 1
      linear_combination form

end P21.Nonsymmetric
