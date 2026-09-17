import P21.Nonsymmetric.HerzogData
import P21.Symmetric.Classification.GcdDecomposition

namespace P21.Nonsymmetric
open P21.Symmetric P21.Symmetric.Classification

/-- Consecutive sufficiently large tail elements certify primitive gcd data. -/
theorem cofinite_common_divisor
    {g : Generators} (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (d : ℤ) (hd : ∀ i, d ∣ g.n i) : d ∣ 1 := by
  obtain ⟨B, hB⟩ := hcof
  have h0 := divisor_of_generated hd (hB B le_rfl)
  have h1 := divisor_of_generated hd (hB (B + 1) (by omega))
  simpa using dvd_sub h1 h0

/-- A pure two-generator critical relation forces the primitive-pair gluing
case. The proof constructs a forbidden smaller actual relation from the signed
normal form of the third generator if primitive membership fails. -/
theorem pure_critical_glue (g : Generators) (s : g.Setting)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (p : Equiv.Perm (Fin 3)) (r : CriticalRelation g (p 1))
    (c : ℕ) (he : (r.coeff : ℤ) * g.n (p 1) = (c : ℤ) * g.n (p 0)) :
    Nonempty (SymmetricGlueData g) := by
  classical
  obtain ⟨D, _, _, hx, hy⟩ := primitive_pair_data g s p
  let d : ℤ := Int.gcd (g.n (p 0)) (g.n (p 1))
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast Int.gcd_pos_of_ne_zero_left (g.n (p 1))
      (ne_of_gt (lt_trans s.m_pos (s.n_gt _)))
  have hre : (0 : ℤ) * D.u + r.coeff * D.v = c * D.u + 0 * D.v := by
    apply mul_left_cancel₀ (ne_of_gt hd)
    nlinarith [he, hx, hy]
  obtain ⟨k, _, hk⟩ := D.representation_difference hre
  have hkneg : k ≤ -1 := by
    have hcoeff : (0 : ℤ) < r.coeff := by exact_mod_cast r.coeff_pos
    nlinarith [D.u_pos]
  have hbound : D.u ≤ r.coeff := by nlinarith [D.u_pos]
  obtain ⟨a,b,hb,hbu,hn⟩ := D.normal_form_exists (g.n (p 2))
  have ha : 0 ≤ a := by
    by_contra han
    have ha' : 0 ≤ -a := by omega
    have hbpos : 0 < b := by
      have hnp : 0 < g.n (p 2) := lt_trans s.m_pos (s.n_gt _)
      nlinarith [D.u_pos, D.v_pos]
    have hp10 : p 1 ≠ p 0 := fun h => by
      have := p.injective h; exact (by decide : (1 : Fin 3) ≠ 0) this
    have hp12 : p 1 ≠ p 2 := fun h => by
      have := p.injective h; exact (by decide : (1 : Fin 3) ≠ 2) this
    let z : Fin 3 → ℕ := fun t =>
      (if t = p 0 then (-a).toNat else 0) + (if t = p 2 then d.toNat else 0)
    have hz : z (p 1) = 0 := by simp [z, hp10, hp12]
    have heq : (b.toNat : ℤ) * g.n (p 1) = value g.n z := by
      simp [z, value, Nat.cast_add, add_mul, Finset.sum_add_distrib,
        Int.toNat_of_nonneg ha', Int.toNat_of_nonneg hd.le,
        Int.toNat_of_nonneg hb]
      nlinarith [hn, hx, hy]
    have hmin := r.minimal b.toNat (by omega) z hz heq
    have : (r.coeff : ℤ) ≤ b := by
      have hcast : (r.coeff : ℤ) ≤ (b.toNat : ℤ) := by exact_mod_cast hmin
      simpa [Int.toNat_of_nonneg hb] using hcast
    omega
  exact decomposition_glue_data g s (cofinite_common_divisor hcof) p d D.u D.v hd
    hx hy D.coprime ⟨a,b,ha,hb,hn⟩

end P21.Nonsymmetric

namespace P21.Nonsymmetric
open P21.Symmetric P21.Symmetric.Classification

theorem perm_last_two (i j : Fin 3) (h : i ≠ j) :
    ∃ p : Equiv.Perm (Fin 3), p 1 = i ∧ p 2 = j := by
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first
    | exact ⟨Equiv.refl _, by decide, by decide⟩
    | exact ⟨Equiv.swap 0 1, by decide, by decide⟩
    | exact ⟨Equiv.swap 0 2, by decide, by decide⟩
    | exact ⟨Equiv.swap 1 2, by decide, by decide⟩
    | exact ⟨(Equiv.swap 0 1).trans (Equiv.swap 0 2), by decide, by decide⟩
    | exact ⟨(Equiv.swap 0 2).trans (Equiv.swap 0 1), by decide, by decide⟩

/-- Nonsymmetry excludes every zero off-diagonal critical coefficient. -/
theorem critical_other_pos (g : Generators) (s : g.Setting)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (hns : ¬ SymmetricTail g) {i : Fin 3} (r : CriticalRelation g i)
    (j : Fin 3) (hij : i ≠ j) : 0 < r.otherCoeff j := by
  classical
  by_contra hn
  have hj : r.otherCoeff j = 0 := by omega
  obtain ⟨p,hpi,hpj⟩ := perm_last_two i j hij
  have he : value g.n r.otherCoeff = (r.otherCoeff (p 0) : ℤ) * g.n (p 0) := by
    have hh := Equiv.sum_comp p (fun t => (r.otherCoeff t : ℤ) * g.n t)
    simpa [value, Fin.sum_univ_succ, hpi, hpj, r.zero_self, hj] using hh.symm
  let r' : CriticalRelation g (p 1) := hpi.symm ▸ r
  have hc : r'.coeff = r.coeff := by subst i; rfl
  obtain ⟨D⟩ := pure_critical_glue g s hcof p r' (r.otherCoeff (p 0))
    (by rw [hc, hpi]; exact r.equality.trans he)
  exact hns (glue_data_symmetric_tail D)

end P21.Nonsymmetric


namespace P21.Nonsymmetric
open P21.Symmetric P21.Symmetric.Classification

/-- Substituting a whole critical packet gives a strictly smaller actual
critical multiple, so positive critical coefficients are themselves subcritical. -/
theorem critical_pair_bound {g : Generators} (hpos : ∀ i, 0 < g.n i)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (r : CriticalRelation g i) (q : CriticalRelation g j)
    (x y z t : ℕ) (hy : 0 < y) (hz : 0 < z)
    (hr : (r.coeff : ℤ) * g.n i = (x : ℤ) * g.n j + (y : ℤ) * g.n k)
    (hq : (q.coeff : ℤ) * g.n j = (z : ℤ) * g.n i + (t : ℤ) * g.n k) :
    x < q.coeff := by
  classical
  by_contra hn
  have hqx : q.coeff ≤ x := by omega
  have he : ((r.coeff : ℤ) - z) * g.n i =
      ((x : ℤ) - q.coeff) * g.n j + ((y : ℤ) + t) * g.n k := by
    linear_combination hr + hq
  have hnonneg : 0 ≤ ((x : ℤ) - q.coeff) * g.n j :=
    mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hqx)) (hpos j).le
  have hyz : (0 : ℤ) < y + t := by exact_mod_cast Nat.add_pos_left hy t
  have hstrict := mul_pos hyz (hpos k)
  have hzr : z < r.coeff := by
    have : (0 : ℤ) < (r.coeff : ℤ) - z :=
      (mul_pos_iff_of_pos_right (hpos i)).mp (by omega)
    exact_mod_cast (by omega : (z : ℤ) < r.coeff)
  let u : Fin 3 → ℕ := fun l =>
    (if l = j then x - q.coeff else 0) + (if l = k then y + t else 0)
  have hu : u i = 0 := by simp [u,hij,hik]
  have hue : ((r.coeff - z : ℕ) : ℤ) * g.n i = value g.n u := by
    simp [u,value,Nat.cast_add,add_mul,Finset.sum_add_distrib,
      Nat.cast_sub hzr.le,Nat.cast_sub hqx]
    nlinarith [he]
  have hmin := r.minimal (r.coeff-z) (Nat.sub_pos_of_lt hzr) u hu hue
  omega

end P21.Nonsymmetric


namespace P21.Nonsymmetric
open P21.Symmetric P21.Symmetric.Classification

theorem critical_le_of_two {g : Generators} {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (r : CriticalRelation g i)
    (c x y : ℕ) (hc : 0 < c)
    (he : (c : ℤ) * g.n i = (x : ℤ) * g.n j + (y : ℤ) * g.n k) :
    r.coeff ≤ c := by
  classical
  apply r.minimal c hc (fun l => (if l = j then x else 0) + (if l = k then y else 0))
  · simp [hij,hik]
  · simpa [value,Nat.cast_add,add_mul,Finset.sum_add_distrib] using he

/-- Existence of the positive critical cycle is proved from nonsymmetry,
cofiniteness and the existing irredundant setting; no pairwise coprimality. -/
theorem herzog_critical_exists (g : Generators) (s : g.Setting)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (hns : ¬ SymmetricTail g) : Nonempty (HerzogCriticalData g) := by
  classical
  have hp : ∀ i, 0 < g.n i := fun i => lt_trans s.m_pos (s.n_gt i)
  let r : ∀ i, CriticalRelation g i := fun i => (criticalRelation_exists g hp i).some
  have hpos : ∀ i j, i ≠ j → 0 < (r i).otherCoeff j :=
    fun i j hij => critical_other_pos g s hcof hns (r i) j hij
  let a : Fin 3 → ℕ := ![(r 1).otherCoeff 0, (r 2).otherCoeff 1, (r 0).otherCoeff 2]
  let b : Fin 3 → ℕ := ![(r 2).otherCoeff 0, (r 0).otherCoeff 1, (r 1).otherCoeff 2]
  let c : Fin 3 → ℕ := fun i => (r i).coeff
  have ha : ∀ i, 0 < a i := by intro i; fin_cases i <;> apply hpos <;> decide
  have hb : ∀ i, 0 < b i := by intro i; fin_cases i <;> apply hpos <;> decide
  have e0 : (c 0 : ℤ) * g.n 0 = (b 1 : ℤ) * g.n 1 + (a 2 : ℤ) * g.n 2 := by
    simpa [a,b,c,value,Fin.sum_univ_succ,(r 0).zero_self] using (r 0).equality
  have e1 : (c 1 : ℤ) * g.n 1 = (a 0 : ℤ) * g.n 0 + (b 2 : ℤ) * g.n 2 := by
    simpa [a,b,c,value,Fin.sum_univ_succ,(r 1).zero_self] using (r 1).equality
  have e2 : (c 2 : ℤ) * g.n 2 = (b 0 : ℤ) * g.n 0 + (a 1 : ℤ) * g.n 1 := by
    simpa [a,b,c,value,Fin.sum_univ_succ,(r 2).zero_self] using (r 2).equality
  have b1 := critical_pair_bound hp (by decide : (0:Fin 3) ≠ 1) (by decide : (0:Fin 3) ≠ 2)
    (r 0) (r 1) (b 1) (a 2) (a 0) (b 2) (ha 2) (ha 0) e0 e1
  have a2 := critical_pair_bound hp (by decide : (0:Fin 3) ≠ 2) (by decide : (0:Fin 3) ≠ 1)
    (r 0) (r 2) (a 2) (b 1) (b 0) (a 1) (hb 1) (hb 0) (by linarith [e0]) e2
  have a0 := critical_pair_bound hp (by decide : (1:Fin 3) ≠ 0) (by decide : (1:Fin 3) ≠ 2)
    (r 1) (r 0) (a 0) (b 2) (b 1) (a 2) (hb 2) (hb 1) e1 e0
  have b2 := critical_pair_bound hp (by decide : (1:Fin 3) ≠ 2) (by decide : (1:Fin 3) ≠ 0)
    (r 1) (r 2) (b 2) (a 0) (a 1) (b 0) (ha 0) (ha 1) (by linarith [e1]) (by linarith [e2])
  have b0 := critical_pair_bound hp (by decide : (2:Fin 3) ≠ 0) (by decide : (2:Fin 3) ≠ 1)
    (r 2) (r 0) (b 0) (a 1) (a 2) (b 1) (ha 1) (ha 2) e2 (by linarith [e0])
  have a1 := critical_pair_bound hp (by decide : (2:Fin 3) ≠ 1) (by decide : (2:Fin 3) ≠ 0)
    (r 2) (r 1) (a 1) (b 0) (b 2) (a 0) (hb 0) (hb 2) (by linarith [e2]) (by linarith [e1])
  change b 1 < c 1 at b1
  change a 2 < c 2 at a2
  change a 0 < c 0 at a0
  change b 2 < c 2 at b2
  change b 0 < c 0 at b0
  change a 1 < c 1 at a1
  have le0 : c 0 ≤ a 0 + b 0 := by
    apply critical_le_of_two (by decide : (0:Fin 3) ≠ 1) (by decide : (0:Fin 3) ≠ 2)
      (r 0) (a 0+b 0) (c 1-a 1) (c 2-b 2) (by have := ha 0; omega)
    push_cast [Nat.cast_sub a1.le,Nat.cast_sub b2.le]
    linear_combination -e1 - e2
  have le1 : c 1 ≤ a 1 + b 1 := by
    apply critical_le_of_two (by decide : (1:Fin 3) ≠ 0) (by decide : (1:Fin 3) ≠ 2)
      (r 1) (a 1+b 1) (c 0-b 0) (c 2-a 2) (by have := ha 1; omega)
    push_cast [Nat.cast_sub b0.le,Nat.cast_sub a2.le]
    linear_combination -e0 - e2
  have le2 : c 2 ≤ a 2 + b 2 := by
    apply critical_le_of_two (by decide : (2:Fin 3) ≠ 0) (by decide : (2:Fin 3) ≠ 1)
      (r 2) (a 2+b 2) (c 0-a 0) (c 1-b 1) (by have := ha 2; omega)
    push_cast [Nat.cast_sub a0.le,Nat.cast_sub b1.le]
    linear_combination -e0 - e1
  have hz0 : (0:ℤ) ≤ (a 0+b 0-c 0 : ℤ) * g.n 0 :=
    mul_nonneg (sub_nonneg.mpr (by exact_mod_cast le0)) (hp 0).le
  have hz1 : (0:ℤ) ≤ (a 1+b 1-c 1 : ℤ) * g.n 1 :=
    mul_nonneg (sub_nonneg.mpr (by exact_mod_cast le1)) (hp 1).le
  have hz2 : (0:ℤ) ≤ (a 2+b 2-c 2 : ℤ) * g.n 2 :=
    mul_nonneg (sub_nonneg.mpr (by exact_mod_cast le2)) (hp 2).le
  have hez : (a 0+b 0-c 0 : ℤ)*g.n 0 + (a 1+b 1-c 1 : ℤ)*g.n 1 +
      (a 2+b 2-c 2 : ℤ)*g.n 2 = 0 := by linear_combination -(e0+e1+e2)
  have heq0 : (a 0+b 0-c 0 : ℤ) = 0 :=
    (mul_eq_zero.mp (show (a 0+b 0-c 0 : ℤ)*g.n 0 = 0 by omega)).resolve_right (ne_of_gt (hp 0))
  have heq1 : (a 1+b 1-c 1 : ℤ) = 0 :=
    (mul_eq_zero.mp (show (a 1+b 1-c 1 : ℤ)*g.n 1 = 0 by omega)).resolve_right (ne_of_gt (hp 1))
  have heq2 : (a 2+b 2-c 2 : ℤ) = 0 :=
    (mul_eq_zero.mp (show (a 2+b 2-c 2 : ℤ)*g.n 2 = 0 by omega)).resolve_right (ne_of_gt (hp 2))
  have eqc : ∀ i, c i = a i+b i := by
    intro i
    fin_cases i
    · exact_mod_cast (show (c 0:ℤ) = a 0+b 0 by omega)
    · exact_mod_cast (show (c 1:ℤ) = a 1+b 1 by omega)
    · exact_mod_cast (show (c 2:ℤ) = a 2+b 2 by omega)
  exact ⟨{
    a := a
    b := b
    rho := c
    a_pos := ha
    b_pos := hb
    rho_eq := eqc
    relation_zero := e0
    relation_one := e1
    relation_two := e2
    critical := r
    coeff_rho := fun _ => rfl }⟩

end P21.Nonsymmetric
