import P21.Nonsymmetric.Singletons
import P21.Nonsymmetric.MatchedPair
import P21.Nonsymmetric.Herzog.PseudoFrobenius

namespace P21.Nonsymmetric

/-- Integer coefficients are converted into an actual Gamma representation only
once every coordinate is nonnegative. -/
theorem four_mem {g : Generators} (l x y z : ℤ)
    (hl : 0 ≤ l) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    l * g.m + x * g.n 0 + y * g.n 1 + z * g.n 2 ∈ g.Gamma := by
  have hm := g.Gamma.nsmul_mem g.m_mem l.toNat
  have ht := g.h_subset_gamma (herzog_three_mem x y z hx hy hz)
  convert g.Gamma.add_mem hm ht using 1 <;>
    simp [nsmul_eq_mul, Int.toNat_of_nonneg hl, add_assoc]

/-- Independently minimized positive-m return for one actual element. -/
structure MinimalReturn (g : Generators) (E : ℤ) where
  L : ℤ
  U : ℤ
  V : ℤ
  L_pos : 0 < L
  U_nonneg : 0 ≤ U
  V_nonneg : 0 ≤ V
  equation : E = L * g.m + U * g.n 1 + V * g.n 2
  minimal : ∀ l u v : ℤ, 0 < l → 0 ≤ u → 0 ≤ v →
    E = l * g.m + u * g.n 1 + v * g.n 2 → L ≤ l

/-- No coordinate in the returned direction can occur in any Gamma return. -/
theorem full_return_coordinate_zero {g : Generators} {s : g.Setting} {F q : ℤ}
    (hq : q ∈ s.semigroup.Q F) (a : g.ActualFactorization4 (q + g.n 0)) :
    a.coeff 1 = 0 := by
  by_contra hn
  have hm := actual_iff_mem.mp ⟨removeOne a 1 (Nat.pos_of_ne_zero hn)⟩
  apply hq.1.1
  change q ∈ g.Gamma
  simpa [Generators.all, Generators.Gamma] using hm

/-- Well ordering is applied separately to each nonempty positive-level fiber. -/
theorem minimal_return_exists {g : Generators} (s : g.Setting) {F q : ℤ}
    (hq : q ∈ s.semigroup.Q F) (hnH : q + g.n 0 ∉ g.H) :
    Nonempty (MinimalReturn g (q + g.n 0)) := by
  classical
  have hret := hq.1.2 (g.n 0) (g.n_mem 0)
    (ne_of_gt (lt_trans s.m_pos (s.n_gt 0)))
  obtain ⟨a⟩ := actual_iff_mem.mpr hret
  have hz := full_return_coordinate_zero hq a
  have he : q + g.n 0 = (a.coeff 0 : ℤ) * g.m +
      (a.coeff 2 : ℤ) * g.n 1 + (a.coeff 3 : ℤ) * g.n 2 := by
    have hh := a.equation
    simpa [value, Generators.all, Fin.sum_univ_succ, hz, add_assoc] using hh.symm
  have hp : 0 < a.coeff 0 := by
    by_contra hh
    have hz0 : a.coeff 0 = 0 := by omega
    apply hnH
    rw [he, hz0]
    simpa using herzog_three_mem (g := g) 0 (a.coeff 2) (a.coeff 3)
      (by omega) (by omega) (by omega)
  let P : ℕ → Prop := fun l => 0 < l ∧ ∃ u v : ℕ,
    q + g.n 0 = (l : ℤ) * g.m + (u : ℤ) * g.n 1 + (v : ℤ) * g.n 2
  have hex : ∃ l, P l := ⟨a.coeff 0, hp, a.coeff 2, a.coeff 3, he⟩
  obtain ⟨hl, u, v, huv⟩ := Nat.find_spec hex
  refine ⟨{
    L := Nat.find hex, U := u, V := v,
    L_pos := by exact_mod_cast hl,
    U_nonneg := Int.natCast_nonneg _, V_nonneg := Int.natCast_nonneg _,
    equation := huv, minimal := ?_ }⟩
  intro l u' v' hl' hu' hv' he'
  have hh : P l.toNat := by
    refine ⟨by omega, u'.toNat, v'.toNat, ?_⟩
    simpa [Int.toNat_of_nonneg hl'.le, Int.toNat_of_nonneg hu', Int.toNat_of_nonneg hv'] using he'
  have hmin := Nat.find_min' hex hh
  have hmin' : (Nat.find hex : ℤ) ≤ (l.toNat : ℤ) := by exact_mod_cast hmin
  simpa [Int.toNat_of_nonneg hl'.le] using hmin'

namespace MatchedPairData
variable {g : Generators} {F qA qB : ℤ} {d : HerzogCriticalData g}
    (M : MatchedPairData g F d qA qB)
include M

/-- Pure-H gap argument: add the removed nonnegative copies to reach fA. -/
theorem returnA_not_tail (hp : ∀ i, 0 < g.n i) : qA + g.n 0 ∉ g.H := by
  intro he
  have hl : 0 ≤ M.depth - 1 := by have := M.depth_pos; omega
  have hm := g.H.nsmul_mem (generator_mem g.n 0) (M.depth - 1).toNat
  have hh := g.H.add_mem he hm
  apply d.fA_gap hp
  convert hh using 1
  simp only [nsmul_eq_mul, Int.toNat_of_nonneg hl]
  nlinarith [M.qA_eq]

theorem returnB_not_tail (hp : ∀ i, 0 < g.n i) : qB + g.n 0 ∉ g.H := by
  intro he
  have hl : 0 ≤ M.depth - 1 := by have := M.depth_pos; omega
  have hm := g.H.nsmul_mem (generator_mem g.n 0) (M.depth - 1).toNat
  have hh := g.H.add_mem he hm
  apply d.fB_gap hp
  convert hh using 1
  simp only [nsmul_eq_mul, Int.toNat_of_nonneg hl]
  nlinarith [M.qB_eq]

end MatchedPairData

/-- A critical packet in the same factorization of F+n0 would produce F.
This lemma is applied four times to obtain CAP. -/
theorem frobenius_return_caps {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (d : HerzogCriticalData g)
    (l u v : ℤ) (hl : 0 ≤ l) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (he : F + g.n 0 = l * g.m + u * g.n 1 + v * g.n 2) :
    u < d.rho 1 ∧ v < d.rho 2 := by
  constructor
  · by_contra hh
    have hcoef : 0 ≤ u - d.rho 1 := by omega
    have ha : 0 ≤ (d.a 0 : ℤ) - 1 := by have := d.a_pos 0; omega
    have hb : 0 ≤ v + d.b 2 := by omega
    have hmem := four_mem (g := g) l (d.a 0 - 1) (u - d.rho 1) (v + d.b 2) hl ha hcoef hb
    apply hF.1
    change F ∈ g.Gamma
    convert hmem using 1
    nlinarith [d.relation_one]
  · by_contra hh
    have hcoef : 0 ≤ v - d.rho 2 := by omega
    have hb : 0 ≤ (d.b 0 : ℤ) - 1 := by have := d.b_pos 0; omega
    have ha : 0 ≤ u + d.a 1 := by omega
    have hmem := four_mem (g := g) l (d.b 0 - 1) (u + d.a 1) (v - d.rho 2) hl hb ha hcoef
    apply hF.1
    change F ∈ g.Gamma
    convert hmem using 1
    nlinarith [d.relation_two]

/-- All four coordinate caps preserve the same actual F+n0 representations. -/
theorem four_return_caps {g : Generators} (s : g.Setting) {F qA qB : ℤ}
    (hF : s.semigroup.IsFrobenius F) {d : HerzogCriticalData g}
    (M : MatchedPairData g F d qA qB)
    (A : MinimalReturn g (qA + g.n 0)) (B : MinimalReturn g (qB + g.n 0)) :
    A.U + M.gapJ < d.rho 1 ∧ A.V + M.T < d.rho 2 ∧
    B.U + M.R < d.rho 1 ∧ B.V + M.gapK < d.rho 2 := by
  have ha := frobenius_return_caps s hF d (A.L - 1) (A.U + M.gapJ) (A.V + M.T)
    (by have := A.L_pos; omega) (add_nonneg A.U_nonneg M.gapJ_nonneg)
    (add_nonneg A.V_nonneg M.T_pos.le) (by
      have he := A.equation
      have hc := M.compA
      dsimp [complement, W] at hc
      nlinarith)
  have hb := frobenius_return_caps s hF d (B.L - 1) (B.U + M.R) (B.V + M.gapK)
    (by have := B.L_pos; omega) (add_nonneg B.U_nonneg M.R_pos.le)
    (add_nonneg B.V_nonneg M.gapK_nonneg) (by
      have he := B.equation
      have hc := M.compB
      dsimp [complement, W] at hc
      nlinarith)
  exact ⟨ha.1, ha.2, hb.1, hb.2⟩




/-- Unequal independent minimum levels lead to an actual representation of F.
The completed final coefficients, including the two zero-slack boundary cases,
are explicitly nonnegative before `four_mem` is applied. -/
theorem unequal_levels_impossible {g : Generators} (s : g.Setting) {F qA qB : ℤ}
    (hF : s.semigroup.IsFrobenius F) {d : HerzogCriticalData g}
    (M : MatchedPairData g F d qA qB)
    (A : MinimalReturn g (qA + g.n 0)) (B : MinimalReturn g (qB + g.n 0)) :
    A.L = B.L := by
  obtain ⟨hAU, hAV, hBU, hBV⟩ := four_return_caps s hF M A B
  have hqa := M.qA_eq
  have hqb := M.qB_eq
  dsimp [HerzogCriticalData.fA, HerzogCriticalData.fB] at hqa hqb
  have hdiff : qB = qA - (d.a 1 : ℤ) * g.n 1 + (d.b 2 : ℤ) * g.n 2 := by
    nlinarith
  let x : ℤ := B.U - A.U + d.a 1
  let y : ℤ := A.V + d.b 2 - B.V
  have hd : (A.L - B.L) * g.m = x * g.n 1 - y * g.n 2 := by
    dsimp [x, y]
    nlinarith [A.equation, B.equation]
  have hr := M.R_eq
  have ht := M.T_eq
  have hg := M.gapJ_nonneg
  have ha := M.gapK_nonneg
  have hxhi : x < d.rho 1 := by dsimp [x]; have := A.U_nonneg; omega
  have hyhi : y < d.rho 2 := by dsimp [y]; have := B.V_nonneg; omega
  have hp1 : 0 < g.n 1 := lt_trans s.m_pos (s.n_gt 1)
  have hp2 : 0 < g.n 2 := lt_trans s.m_pos (s.n_gt 2)
  rcases lt_trichotomy A.L B.L with hlt | heq | hgt
  · have hneg : A.U < d.a 1 := by
      by_contra hh
      have hmin := B.minimal A.L (A.U - d.a 1) (A.V + d.b 2)
        A.L_pos (by omega) (by have := A.V_nonneg; omega) (by
          nlinarith [A.equation])
      omega
    have hxp : 0 < x := by dsimp [x]; have := B.U_nonneg; omega
    have hsig : 0 < B.L - A.L := by omega
    have hyp : 0 < y := by
      have he : 0 < y * g.n 2 := by nlinarith [mul_pos hsig s.m_pos, mul_pos hxp hp1]
      exact (mul_pos_iff_of_pos_right hp2).mp he
    have hm := four_mem (g := g) (B.L - A.L - 1) (M.P - d.b 0 - 1)
      (M.gapJ + x - 1) (d.rho 2 + M.T - y - 1)
      (by omega) (by have := M.P_gt_b; omega) (by omega)
      (by have := M.T_pos; omega)
    apply False.elim
    apply hF.1
    change F ∈ g.Gamma
    convert hm using 1
    have hw := M.W_eq
    dsimp [W] at hw
    linear_combination hw + hd - d.relation_two + g.n 1 * hr
  · exact heq
  · have hneg : B.V < d.b 2 := by
      by_contra hh
      have hmin := A.minimal B.L (B.U + d.a 1) (B.V - d.b 2)
        B.L_pos (by have := B.U_nonneg; omega) (by omega) (by
          nlinarith [B.equation])
      omega
    have hyp : 0 < y := by dsimp [y]; have := A.V_nonneg; omega
    have hsig : 0 < A.L - B.L := by omega
    have hxp : 0 < x := by
      have he : 0 < x * g.n 1 := by nlinarith [mul_pos hsig s.m_pos, mul_pos hyp hp2]
      exact (mul_pos_iff_of_pos_right hp1).mp he
    have hm := four_mem (g := g) (A.L - B.L - 1) (M.P - d.a 0 - 1)
      (d.rho 1 + M.R - 1 - x) (M.gapK + y - 1)
      (by omega) (by have := M.P_gt_a; omega)
      (by have := M.R_pos; omega) (by omega)
    apply False.elim
    apply hF.1
    change F ∈ g.Gamma
    convert hm using 1
    have hw := M.W_eq
    dsimp [W] at hw
    linear_combination hw - hd - d.relation_one + g.n 2 * ht

/-- After m has been eliminated, critical-box uniqueness synchronizes the
remaining two coefficients. -/
theorem equal_level_matching {g : Generators} (s : g.Setting) {F qA qB : ℤ}
    (hF : s.semigroup.IsFrobenius F) {d : HerzogCriticalData g}
    (M : MatchedPairData g F d qA qB)
    (A : MinimalReturn g (qA + g.n 0)) (B : MinimalReturn g (qB + g.n 0)) :
    A.L = B.L ∧ A.U = (d.a 1 : ℤ) + B.U ∧ B.V = A.V + d.b 2 := by
  have hlevels := unequal_levels_impossible s hF M A B
  obtain ⟨hAU, hAV, hBU, hBV⟩ := four_return_caps s hF M A B
  let x : ℤ := B.U - A.U + d.a 1
  let y : ℤ := A.V + d.b 2 - B.V
  have hqA := M.qA_eq
  have hqB := M.qB_eq
  dsimp [HerzogCriticalData.fA, HerzogCriticalData.fB] at hqA hqB
  have hd : x * g.n 1 - y * g.n 2 = 0 := by
    dsimp [x, y]
    have hAe := A.equation
    rw [hlevels] at hAe
    nlinarith [B.equation]
  have hr := M.R_eq
  have ht := M.T_eq
  have hg := M.gapJ_nonneg
  have ha := M.gapK_nonneg
  have hAp := A.U_nonneg
  have hAv := A.V_nonneg
  have hBp := B.U_nonneg
  have hBv := B.V_nonneg
  have hboxx : -(d.rho 1 : ℤ) < x ∧ x < d.rho 1 := by
    have := d.a_pos 1
    dsimp [x]
    omega
  have hboxy : -(d.rho 2 : ℤ) < y ∧ y < d.rho 2 := by
    have := d.b_pos 2
    dsimp [y]
    omega
  have hzero := critical_kernel_box_zero
    (fun i => lt_trans s.m_pos (s.n_gt i)) d.critical (![0, x, -y])
    (by simpa [integerValue, Fin.sum_univ_succ, sub_eq_add_neg] using hd)
    (by intro i; fin_cases i <;> simp [d.coeff_rho] <;>
      first | omega | exact_mod_cast d.rho_pos 0)
    (by intro i; fin_cases i <;> simp [d.coeff_rho] <;>
      first | omega | exact_mod_cast d.rho_pos 0)
  have hx := congrFun hzero 1
  have hy := congrFun hzero 2
  simp [x, y] at hx hy
  exact ⟨hlevels, by omega, by omega⟩

/-- Publication §4.6, with no unit-root hypothesis and no strict slack bounds. -/
theorem root_free_level_rigidity {g : Generators} (s : g.Setting) {F qA qB : ℤ}
    (hF : s.semigroup.IsFrobenius F) {d : HerzogCriticalData g}
    (M : MatchedPairData g F d qA qB)
    (hqA : qA ∈ s.semigroup.Q F) (hqB : qB ∈ s.semigroup.Q F) :
    ∃ L t u : ℤ, 0 < L ∧ 0 ≤ t ∧ 0 ≤ u ∧
      qA + g.n 0 = L * g.m + ((d.a 1 : ℤ) + t) * g.n 1 + u * g.n 2 ∧
      qB + g.n 0 = L * g.m + t * g.n 1 + (u + d.b 2) * g.n 2 ∧
      M.P * g.n 0 = L * g.m + (t + 1) * g.n 1 + (u + 1) * g.n 2 := by
  have hp := fun i => lt_trans s.m_pos (s.n_gt i)
  obtain ⟨A⟩ := minimal_return_exists s hqA (M.returnA_not_tail hp)
  obtain ⟨B⟩ := minimal_return_exists s hqB (M.returnB_not_tail hp)
  obtain ⟨hL, hU, hV⟩ := equal_level_matching s hF M A B
  refine ⟨A.L, B.U, A.V, A.L_pos, B.U_nonneg, A.V_nonneg, ?_, ?_, ?_⟩
  · simpa [hU] using A.equation
  · simpa [← hL, hV] using B.equation
  · rw [M.P_eq]
    have ha := A.equation
    rw [hU] at ha
    have hq := M.qA_eq
    dsimp [HerzogCriticalData.fA] at hq
    nlinarith





/-- A matched pair excludes the extra A arm in the next cyclic direction. -/
theorem matched_pair_excludes_A_one {g : Generators} (s : g.Setting) {F qA qB q : ℤ}
    (hF : s.semigroup.IsFrobenius F) {d : HerzogCriticalData g}
    (M : MatchedPairData g F d qA qB)
    (hqA : qA ∈ s.semigroup.Q F) (hqB : qB ∈ s.semigroup.Q F)
    (hq : q ∈ s.semigroup.Q F) (mu : ℤ) (hmu : mu < d.a 1)
    (he : q = d.fA - mu * g.n 1) : False := by
  obtain ⟨L, t, u, hL, ht, hu, hA, _, _⟩ := root_free_level_rigidity s hF M hqA hqB
  have hm := four_mem (g := g) L (M.depth - 1) ((d.a 1 : ℤ) + t - mu) u
    hL.le (by have := M.depth_pos; omega) (by omega) hu
  apply hq.1.1
  change q ∈ g.Gamma
  convert hm using 1
  nlinarith [M.qA_eq]

/-- The color-reversed extra B arm in direction k is also excluded. -/
theorem matched_pair_excludes_B_two {g : Generators} (s : g.Setting) {F qA qB q : ℤ}
    (hF : s.semigroup.IsFrobenius F) {d : HerzogCriticalData g}
    (M : MatchedPairData g F d qA qB)
    (hqA : qA ∈ s.semigroup.Q F) (hqB : qB ∈ s.semigroup.Q F)
    (hq : q ∈ s.semigroup.Q F) (mu : ℤ) (hmu : mu < d.b 2)
    (he : q = d.fB - mu * g.n 2) : False := by
  obtain ⟨L, t, u, hL, ht, hu, _, hB, _⟩ := root_free_level_rigidity s hF M hqA hqB
  have hm := four_mem (g := g) L (M.depth - 1) t (u + d.b 2 - mu)
    hL.le (by have := M.depth_pos; omega) ht (by omega)
  apply hq.1.1
  change q ∈ g.Gamma
  convert hm using 1
  nlinarith [M.qB_eq]

/-- A matched pair excludes every singleton direction, including its own. -/
theorem matched_pair_no_singleton {g : Generators} (s : g.Setting) {F qA qB q : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    {d : HerzogCriticalData g} (M : MatchedPairData g F d qA qB)
    (hqA : qA ∈ s.semigroup.Q F) (hqB : qB ∈ s.semigroup.Q F)
    (hq : q ∈ s.semigroup.Q F) (i : Fin 3) (hs : IsSingleton g q i) : False := by
  obtain ⟨k, hk, he⟩ := singleton_pure_complement s hF hc hq hs
  have hkbound := singleton_critical_bound s hF hc hq hs (d.critical i) he
  rw [d.coeff_rho] at hkbound
  have hrp := M.R_pos
  have htp := M.T_pos
  have hw := M.W_eq
  fin_cases i
  · change complement F g.m q = (k : ℤ) * g.n 0 at he
    have hkp : M.P ≤ (k : ℤ) := by
      by_contra hh
      have hm := herzog_three_mem (g := g) (M.P - 1 - k) (M.R - 1) (M.T - 1)
        (by omega) (by omega) (by omega)
      apply hq.1.1
      apply g.h_subset_gamma
      convert hm using 1
      dsimp [complement] at he
      nlinarith
    obtain ⟨L, t, u, hL, ht, hu, _, _, hpf⟩ := root_free_level_rigidity s hF M hqA hqB
    have hm := four_mem (g := g) (L - 1) ((k : ℤ) - M.P) (t + 1) (u + 1)
      (by omega) (by omega) (by omega) (by omega)
    have hap := s.semigroup.complement_of_q_mem_apery hF hc hq
    apply hap.2
    change complement F g.m q - g.m ∈ g.Gamma
    convert hm using 1
    rw [he]
    nlinarith
  · change k < d.rho 1 at hkbound
    change IsSingleton g q 1 at hs
    change complement F g.m q = (k : ℤ) * g.n 1 at he
    have hm := herzog_three_mem (g := g) (M.P - d.a 0 - 1)
      (M.R - k - 1 + d.rho 1) M.gapK
      (by have := M.P_gt_a; omega) (by omega) M.gapK_nonneg
    have hret : q + g.n 2 ∈ g.H := by
      convert hm using 1
      have ht := M.T_eq
      dsimp [complement] at he
      linear_combination hw - he - d.relation_one + g.n 2 * ht
    have hdir : (2 : Fin 3) ∈ g.SH q := hret
    rw [hs] at hdir
    exact (by decide : (2 : Fin 3) ≠ 1) hdir
  · change k < d.rho 2 at hkbound
    change IsSingleton g q 2 at hs
    change complement F g.m q = (k : ℤ) * g.n 2 at he
    have hm := herzog_three_mem (g := g) (M.P - d.b 0 - 1)
      M.gapJ (M.T - k - 1 + d.rho 2)
      (by have := M.P_gt_b; omega) M.gapJ_nonneg (by omega)
    have hret : q + g.n 1 ∈ g.H := by
      convert hm using 1
      have hr := M.R_eq
      dsimp [complement] at he
      linear_combination hw - he - d.relation_two + g.n 1 * hr
    have hdir : (1 : Fin 3) ∈ g.SH q := hret
    rw [hs] at hdir
    exact (by decide : (1 : Fin 3) ≠ 2) hdir

end P21.Nonsymmetric

