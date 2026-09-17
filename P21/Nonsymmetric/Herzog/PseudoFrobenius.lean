import P21.Nonsymmetric.HerzogClassification

namespace P21.Nonsymmetric
open P21.Symmetric.Classification

variable {g : Generators}

/-- Three integer coefficients are used as actual coefficients only after
all three nonnegativity inequalities have been proved. -/
theorem herzog_three_mem (x y z : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x * g.n 0 + y * g.n 1 + z * g.n 2 ∈ g.H := by
  refine ⟨![x.toNat,y.toNat,z.toNat], ?_⟩
  simp [value,Fin.sum_univ_succ,Int.toNat_of_nonneg hx,
    Int.toNat_of_nonneg hy,Int.toNat_of_nonneg hz,add_assoc]

theorem herzog_critical_le_int (D : HerzogCriticalData g)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (c x y : ℤ) (hc : 0 < c) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (he : c * g.n i = x * g.n j + y * g.n k) : (D.rho i : ℤ) ≤ c := by
  have h := critical_le_of_two hij hik (D.critical i) c.toNat x.toNat y.toNat
    (by omega) (by simpa [Int.toNat_of_nonneg hc.le,
      Int.toNat_of_nonneg hx,Int.toNat_of_nonneg hy] using he)
  rw [D.coeff_rho] at h
  have h' : (D.rho i : ℤ) ≤ (c.toNat : ℤ) := by exact_mod_cast h
  simpa [Int.toNat_of_nonneg hc.le] using h'

/-- The off-direction coefficients of any box relation cover the whole
positive mixed critical packet. -/
theorem herzog_packet_le (D : HerzogCriticalData g) (hp : ∀ i, 0 < g.n i)
    (x y z : ℤ) (hx : 0 < x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hyc : y < D.rho 1) (hzc : z < D.rho 2)
    (he : x * g.n 0 = y * g.n 1 + z * g.n 2) :
    (D.b 1 : ℤ) ≤ y ∧ (D.a 2 : ℤ) ≤ z := by
  have hmin := herzog_critical_le_int D (by decide : (0:Fin 3) ≠ 1)
    (by decide : (0:Fin 3) ≠ 2) x y z hx hy hz he
  have ht : 0 ≤ x - D.rho 0 := by omega
  constructor
  · by_contra hn
    have hb : 0 < (D.b 1 : ℤ) - y := by omega
    have he' : (z - D.a 2) * g.n 2 =
        (x - D.rho 0) * g.n 0 + (D.b 1 - y) * g.n 1 := by
      linear_combination D.relation_zero - he
    have hzp : 0 < z - D.a 2 := by
      have ht0 := mul_nonneg ht (hp 0).le
      have hb1 := mul_pos hb (hp 1)
      exact (mul_pos_iff_of_pos_right (hp 2)).mp (by omega)
    have h := herzog_critical_le_int D (by decide : (2:Fin 3) ≠ 0)
      (by decide : (2:Fin 3) ≠ 1) (z-D.a 2) (x-D.rho 0) (D.b 1-y)
      hzp ht hb.le he'
    have := D.a_pos 2
    omega
  · by_contra hn
    have ha : 0 < (D.a 2 : ℤ) - z := by omega
    have he' : (y - D.b 1) * g.n 1 =
        (x - D.rho 0) * g.n 0 + (D.a 2 - z) * g.n 2 := by
      linear_combination D.relation_zero - he
    have hyp : 0 < y - D.b 1 := by
      have ht0 := mul_nonneg ht (hp 0).le
      have ha2 := mul_pos ha (hp 2)
      exact (mul_pos_iff_of_pos_right (hp 1)).mp (by omega)
    have h := herzog_critical_le_int D (by decide : (1:Fin 3) ≠ 0)
      (by decide : (1:Fin 3) ≠ 2) (y-D.b 1) (x-D.rho 0) (D.a 2-z)
      hyp ht ha.le he'
    have := D.b_pos 1
    omega

/-- The L-shaped off-direction box is contained in the actual Apéry set. -/
theorem herzog_L_gap (D : HerzogCriticalData g) (hp : ∀ i, 0 < g.n i)
    (y z : ℤ) (_hy : 0 ≤ y) (_hz : 0 ≤ z)
    (hyc : y < D.rho 1) (hzc : z < D.rho 2)
    (hL : y < D.b 1 ∨ z < D.a 2) :
    y * g.n 1 + z * g.n 2 - g.n 0 ∉ g.H := by
  rintro ⟨v,hv⟩
  have he : ((v 0 : ℤ)+1)*g.n 0 =
      (y-v 1)*g.n 1 + (z-v 2)*g.n 2 := by
    simp [value,Fin.sum_univ_succ] at hv
    linarith
  have hx : (0:ℤ) < (v 0:ℤ)+1 := by omega
  have hn1 : (v 1:ℤ) < y := by
    by_contra hn
    have hd : 0 ≤ (v 1:ℤ)-y := by omega
    have he' : (z-v 2)*g.n 2 = ((v 0:ℤ)+1)*g.n 0 + (v 1-y)*g.n 1 := by
      linarith [he]
    have hzp : 0 < z-v 2 := by
      have h0 := mul_pos hx (hp 0)
      have h1 := mul_nonneg hd (hp 1).le
      exact (mul_pos_iff_of_pos_right (hp 2)).mp (by omega)
    have h := herzog_critical_le_int D (by decide : (2:Fin 3) ≠ 0)
      (by decide : (2:Fin 3) ≠ 1) (z-v 2) ((v 0:ℤ)+1) (v 1-y)
      hzp hx.le hd he'
    omega
  have hn2 : (v 2:ℤ) < z := by
    by_contra hn
    have hd : 0 ≤ (v 2:ℤ)-z := by omega
    have he' : (y-v 1)*g.n 1 = ((v 0:ℤ)+1)*g.n 0 + (v 2-z)*g.n 2 := by
      linarith [he]
    have hyp : 0 < y-v 1 := by
      have h0 := mul_pos hx (hp 0)
      have h2 := mul_nonneg hd (hp 2).le
      exact (mul_pos_iff_of_pos_right (hp 1)).mp (by omega)
    have h := herzog_critical_le_int D (by decide : (1:Fin 3) ≠ 0)
      (by decide : (1:Fin 3) ≠ 2) (y-v 1) ((v 0:ℤ)+1) (v 2-z)
      hyp hx.le hd he'
    omega
  have hh := herzog_packet_le D hp ((v 0:ℤ)+1) (y-v 1) (z-v 2)
    hx (by omega) (by omega) (by omega) (by omega) he
  rcases hL with hL | hL <;> omega

end P21.Nonsymmetric

namespace P21.Nonsymmetric
variable {g : Generators}

/-- Every actual Apéry element admits an L-shaped actual pair representation. -/
theorem herzog_apery_L (D : HerzogCriticalData g)
    {w : ℤ} (hw : w ∈ g.H) (hgap : w-g.n 0 ∉ g.H) :
    ∃ y z : ℤ, 0 ≤ y ∧ 0 ≤ z ∧ y < D.rho 1 ∧ z < D.rho 2 ∧
      (y < D.b 1 ∨ z < D.a 2) ∧ w = y*g.n 1+z*g.n 2 := by
  obtain ⟨v,hv⟩ := hw
  have he : w = (v 0:ℤ)*g.n 0+(v 1:ℤ)*g.n 1+(v 2:ℤ)*g.n 2 := by
    simpa [value,Fin.sum_univ_succ,add_assoc] using hv.symm
  have hzero : v 0 = 0 := by
    by_contra hn
    apply hgap
    have h := herzog_three_mem (g:=g) (v 0-1:ℤ) (v 1) (v 2)
      (by omega) (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    convert h using 1; linarith [he]
  have he' : w = (v 1:ℤ)*g.n 1+(v 2:ℤ)*g.n 2 := by simpa [hzero] using he
  have h1 : (v 1:ℤ) < D.rho 1 := by
    by_contra hn
    apply hgap
    have ha := D.a_pos 0
    have h := herzog_three_mem (g:=g) (D.a 0-1:ℤ) (v 1-D.rho 1:ℤ) (v 2+D.b 2:ℤ)
      (by omega) (by omega) (by positivity)
    convert h using 1
    linear_combination he' + D.relation_one
  have h2 : (v 2:ℤ) < D.rho 2 := by
    by_contra hn
    apply hgap
    have hb := D.b_pos 0
    have h := herzog_three_mem (g:=g) (D.b 0-1:ℤ) (v 1+D.a 1:ℤ) (v 2-D.rho 2:ℤ)
      (by omega) (by positivity) (by omega)
    convert h using 1
    linear_combination he' + D.relation_two
  have hL : (v 1:ℤ) < D.b 1 ∨ (v 2:ℤ) < D.a 2 := by
    by_contra hn
    push Not at hn
    apply hgap
    have hr := D.rho_pos 0
    have h := herzog_three_mem (g:=g) (D.rho 0-1:ℤ) (v 1-D.b 1:ℤ) (v 2-D.a 2:ℤ)
      (by omega) (by omega) (by omega)
    convert h using 1
    linear_combination he' - D.relation_zero
  exact ⟨v 1,v 2,Int.natCast_nonneg _,Int.natCast_nonneg _,h1,h2,hL,he'⟩

/-- Returns at the generators suffice for the full integer PF predicate. -/
theorem tailPF_of_returns (q : ℤ) (hq : q ∉ g.H)
    (hr : ∀ i, q+g.n i ∈ g.H) : q ∈ TailPF g := by
  refine ⟨hq, ?_⟩
  intro t ht hne
  obtain ⟨v,rfl⟩ := ht
  have hv : ∃ i, 0 < v i := by
    by_contra hn
    push Not at hn
    have hz : v = 0 := by funext i; have := hn i; simp; omega
    exact hne (by simp [hz,value])
  obtain ⟨i,hi⟩ := hv
  classical
  let u : Fin 3 → ℕ := fun j => if j=i then v j-1 else v j
  have he : value g.n v = g.n i + value g.n u := by
    have hv' : v = fun j => (if j=i then 1 else 0) + u j := by
      funext j; by_cases hj : j=i <;> simp [u,hj]; omega
    rw [hv']
    simp [value,Nat.cast_add,add_mul,Finset.sum_add_distrib]
  rw [he,← add_assoc]
  exact g.H.add_mem (hr i) ⟨u,rfl⟩

namespace HerzogCriticalData
variable (D : HerzogCriticalData g)

theorem fA_apery_formula : D.fA + g.n 0 =
    (D.rho 1-1:ℤ)*g.n 1+(D.a 2-1:ℤ)*g.n 2 := by
  have he : (D.rho 1:ℤ) = D.a 1+D.b 1 := by exact_mod_cast D.rho_eq 1
  dsimp [fA]
  linear_combination D.relation_zero - g.n 1 * he

theorem fB_apery_formula : D.fB + g.n 0 =
    (D.b 1-1:ℤ)*g.n 1+(D.rho 2-1:ℤ)*g.n 2 := by
  have he : (D.rho 2:ℤ) = D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
  dsimp [fB]
  linear_combination D.relation_zero - g.n 2 * he

theorem fA_gap (hp : ∀ i, 0 < g.n i) : D.fA ∉ g.H := by
  have ha := D.a_pos 2
  have hb := D.b_pos 2
  have hr := D.rho_pos 1
  have hs := D.rho_eq 2
  have hg := herzog_L_gap D hp (D.rho 1-1) (D.a 2-1)
    (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
  have he : D.fA = (D.rho 1-1:ℤ)*g.n 1+(D.a 2-1:ℤ)*g.n 2-g.n 0 := by
    linarith [D.fA_apery_formula]
  rwa [← he] at hg

theorem fB_gap (hp : ∀ i, 0 < g.n i) : D.fB ∉ g.H := by
  have ha := D.a_pos 1
  have hb := D.b_pos 1
  have hr := D.rho_pos 2
  have hs := D.rho_eq 1
  have hg := herzog_L_gap D hp (D.b 1-1) (D.rho 2-1)
    (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
  have he : D.fB = (D.b 1-1:ℤ)*g.n 1+(D.rho 2-1:ℤ)*g.n 2-g.n 0 := by
    linarith [D.fB_apery_formula]
  rwa [← he] at hg

end HerzogCriticalData
end P21.Nonsymmetric


namespace P21.Nonsymmetric
variable {g : Generators}
namespace HerzogCriticalData
variable (D : HerzogCriticalData g)

theorem fA_returns : ∀ i, D.fA + g.n i ∈ g.H := by
  have ha0 := D.a_pos 0
  have ha1 := D.a_pos 1
  have ha2 := D.a_pos 2
  have hr0 := D.rho_pos 0
  have hr1 := D.rho_pos 1
  have hr2 := D.rho_pos 2
  intro i
  fin_cases i
  · have h := herzog_three_mem (g:=g) 0 (D.rho 1-1) (D.a 2-1)
      (by omega) (by omega) (by omega)
    simpa [D.fA_apery_formula] using h
  · have h := herzog_three_mem (g:=g) (D.a 0-1) 0 (D.rho 2-1)
      (by omega) (by omega) (by omega)
    have he0 : (D.rho 0:ℤ) = D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
    convert h using 1
    dsimp [fA]
    linear_combination -D.relation_two + g.n 0*he0
  · have h := herzog_three_mem (g:=g) (D.rho 0-1) (D.a 1-1) 0
      (by omega) (by omega) (by omega)
    simpa [fA] using h

theorem fB_returns : ∀ i, D.fB + g.n i ∈ g.H := by
  have hb0 := D.b_pos 0
  have hb1 := D.b_pos 1
  have hb2 := D.b_pos 2
  have hr0 := D.rho_pos 0
  have hr1 := D.rho_pos 1
  have hr2 := D.rho_pos 2
  intro i
  fin_cases i
  · have h := herzog_three_mem (g:=g) 0 (D.b 1-1) (D.rho 2-1)
      (by omega) (by omega) (by omega)
    simpa [D.fB_apery_formula] using h
  · have h := herzog_three_mem (g:=g) (D.rho 0-1) 0 (D.b 2-1)
      (by omega) (by omega) (by omega)
    convert h using 1
    dsimp [fB]
    ring
  · have h := herzog_three_mem (g:=g) (D.b 0-1) (D.rho 1-1) 0
      (by omega) (by omega) (by omega)
    have he0 : (D.rho 0:ℤ) = D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
    convert h using 1
    dsimp [fB]
    linear_combination -D.relation_one + g.n 0*he0

theorem fA_mem_tailPF (hp : ∀ i, 0 < g.n i) : D.fA ∈ TailPF g :=
  tailPF_of_returns _ (D.fA_gap hp) D.fA_returns

theorem fB_mem_tailPF (hp : ∀ i, 0 < g.n i) : D.fB ∈ TailPF g :=
  tailPF_of_returns _ (D.fB_gap hp) D.fB_returns

/-- The two maximal points of the L-shaped Apéry set exhaust the actual PF set. -/
theorem tailPF_subset_pair (hp : ∀ i, 0 < g.n i) {q : ℤ} (hq : q ∈ TailPF g) :
    q = D.fA ∨ q = D.fB := by
  have hq0 := hq.2 (g.n 0) (generator_mem g.n 0) (ne_of_gt (hp 0))
  obtain ⟨y,z,hy,hz,hyc,hzc,hL,he⟩ := herzog_apery_L D hq0 (by simpa using hq.1)
  have hn1 : ¬ (y+1 < D.rho 1 ∧ (y+1 < D.b 1 ∨ z < D.a 2)) := by
    rintro ⟨hy',hL'⟩
    apply herzog_L_gap D hp (y+1) z (by omega) hz hy' hzc hL'
    have h := hq.2 (g.n 1) (generator_mem g.n 1) (ne_of_gt (hp 1))
    convert h using 1; linarith [he]
  have hn2 : ¬ (z+1 < D.rho 2 ∧ (y < D.b 1 ∨ z+1 < D.a 2)) := by
    rintro ⟨hz',hL'⟩
    apply herzog_L_gap D hp y (z+1) hy (by omega) hyc hz' hL'
    have h := hq.2 (g.n 2) (generator_mem g.n 2) (ne_of_gt (hp 2))
    convert h using 1; linarith [he]
  have hcorners : (y = D.rho 1-1 ∧ z = D.a 2-1) ∨
      (y = D.b 1-1 ∧ z = D.rho 2-1) := by
    have ha1 := D.a_pos 1
    have hb2 := D.b_pos 2
    have hr1 := D.rho_eq 1
    have hr2 := D.rho_eq 2
    omega
  rcases hcorners with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · left; linarith [D.fA_apery_formula]
  · right; linarith [D.fB_apery_formula]

/-- Exact PF equality, proved from actual critical minimality. -/
theorem tailPF_eq_pair (hp : ∀ i, 0 < g.n i) : TailPF g = {D.fA,D.fB} := by
  ext q
  constructor
  · intro hq
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using D.tailPF_subset_pair hp hq
  · intro hq
    rcases (show q = D.fA ∨ q = D.fB by simpa using hq) with rfl | rfl
    · exact D.fA_mem_tailPF hp
    · exact D.fB_mem_tailPF hp

end HerzogCriticalData
end P21.Nonsymmetric


namespace P21.Nonsymmetric
variable {g : Generators}
namespace HerzogCriticalData
variable (D : HerzogCriticalData g)

/-- The two PF expressions cannot coincide: equality would be a forbidden
subcritical pure two-generator relation. -/
theorem fA_ne_fB : D.fA ≠ D.fB := by
  intro h
  have ha := D.a_pos 1
  have hb := D.b_pos 1
  have hr := D.rho_eq 1
  have he1 : (D.rho 1:ℤ) = D.a 1+D.b 1 := by exact_mod_cast D.rho_eq 1
  have he2 : (D.rho 2:ℤ) = D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
  have he : (D.a 1:ℤ)*g.n 1 = (D.b 2:ℤ)*g.n 2 + 0*g.n 0 := by
    linear_combination D.fB_apery_formula - D.fA_apery_formula + h -
      g.n 1*he1 + g.n 2*he2
  have hc := herzog_critical_le_int D (by decide : (1:Fin 3) ≠ 2)
    (by decide : (1:Fin 3) ≠ 0) (D.a 1) (D.b 2) 0
    (by exact_mod_cast ha) (Int.natCast_nonneg _) (by omega) he
  omega

/-- Upgrade the proven critical cycle to the exact two-PF Herzog package. -/
def fullData (hp : ∀ i, 0 < g.n i) : NonsymmetricHerzogData g where
  toHerzogCriticalData := D
  distinct := D.fA_ne_fB
  pf_exact := D.tailPF_eq_pair hp

end HerzogCriticalData

/-- STD_HERZOG: the full positive critical cycle and exact two PF numbers,
derived from the actual nonsymmetric numerical tail. -/
theorem nonsymmetric_herzog_exists (g : Generators) (s : g.Setting)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (hns : ¬ P21.Symmetric.SymmetricTail g) : Nonempty (NonsymmetricHerzogData g) := by
  obtain ⟨D⟩ := herzog_critical_exists g s hcof hns
  exact ⟨D.fullData (fun i => lt_trans s.m_pos (s.n_gt i))⟩

theorem herzog_classification : HerzogClassificationStatement :=
  nonsymmetric_herzog_exists

end P21.Nonsymmetric

