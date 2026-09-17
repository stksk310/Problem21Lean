import P21.Nonsymmetric.Kernel
import P21.Nonsymmetric.Rows

namespace P21.Nonsymmetric

/-- The asymmetric comparison box used for a matched pair contains only the
zero integer kernel vector. This is a consequence of the proved integer basis. -/
theorem matched_kernel_box_zero {g : Generators} (hpos : ∀ i, 0 < g.n i)
    (d : HerzogCriticalData g) (v : Fin 3 → ℤ) (hv : integerValue g v = 0)
    (h0lo : 2 - (d.a 0 : ℤ) ≤ v 0) (h0hi : v 0 ≤ (d.b 0 : ℤ) - 2)
    (h1lo : 1 - (d.b 1 : ℤ) ≤ v 1)
    (h1hi : v 1 ≤ (d.rho 1 : ℤ) + d.a 1 - 1)
    (h2hi : v 2 ≤ (d.a 2 : ℤ) - 1) : v = 0 := by
  obtain ⟨u, t, he⟩ := integer_kernel_span hpos d v hv
  have he0 := he 0
  have he1 := he 1
  have he2 := he 2
  simp [kernelRowJ, kernelRowK] at he0 he1 he2
  have ha0 : (0 : ℤ) < d.a 0 := by exact_mod_cast d.a_pos 0
  have hb0 : (0 : ℤ) < d.b 0 := by exact_mod_cast d.b_pos 0
  have ha1 : (0 : ℤ) < d.a 1 := by exact_mod_cast d.a_pos 1
  have hb1 : (0 : ℤ) < d.b 1 := by exact_mod_cast d.b_pos 1
  have ha2 : (0 : ℤ) < d.a 2 := by exact_mod_cast d.a_pos 2
  have hb2 : (0 : ℤ) < d.b 2 := by exact_mod_cast d.b_pos 2
  have hr1 : (d.rho 1 : ℤ) = (d.a 1 : ℤ) + d.b 1 := by exact_mod_cast d.rho_eq 1
  have hr2 : (d.rho 2 : ℤ) = (d.a 2 : ℤ) + d.b 2 := by exact_mod_cast d.rho_eq 2
  have hr1p : (0 : ℤ) < d.rho 1 := by omega
  have hr2p : (0 : ℤ) < d.rho 2 := by omega
  have hut : u = 0 ∧ t = 0 := by
    by_cases hu : 1 ≤ u
    · by_cases ht : 1 ≤ t
      · nlinarith [mul_nonneg (show 0 ≤ u - 1 by omega) ha0.le,
          mul_nonneg (show 0 ≤ t - 1 by omega) hb0.le]
      · have ht0 : t ≤ 0 := by omega
        nlinarith [mul_nonneg (show 0 ≤ u - 1 by omega) hr1p.le,
          mul_nonpos_of_nonpos_of_nonneg ht0 ha1.le]
    · have hu0 : u ≤ 0 := by omega
      by_cases hun : u ≤ -1
      · by_cases ht : 1 ≤ t
        · nlinarith [mul_nonneg (show 0 ≤ -u - 1 by omega) hr1p.le,
            mul_nonneg (show 0 ≤ t - 1 by omega) ha1.le]
        · have ht0 : t ≤ 0 := by omega
          nlinarith [mul_nonneg (show 0 ≤ -u - 1 by omega) ha0.le,
            mul_nonpos_of_nonpos_of_nonneg ht0 hb0.le]
      · have huz : u = 0 := by omega
        subst u
        by_cases ht : 1 ≤ t
        · nlinarith [mul_nonneg (show 0 ≤ t - 1 by omega) hb0.le]
        · by_cases htn : t ≤ -1
          · nlinarith [mul_nonneg (show 0 ≤ -t - 1 by omega) hr2p.le]
          · omega
  funext i
  simpa [hut.1, hut.2] using he i

/-- Depths and both off-direction complement coordinates synchronize. All
coefficient hypotheses are genuine nonnegative critical-box coefficients. -/
theorem matched_pair_sync {g : Generators} (hpos : ∀ i, 0 < g.n i)
    (d : HerzogCriticalData g) {F qA qB : ℤ} {lam mu y z y' z' : ℕ}
    (hl : 0 < lam) (hlA : lam < d.a 0) (hm : 0 < mu) (hmB : mu < d.b 0)
    (hqA : qA = d.fA - (lam : ℤ) * g.n 0)
    (hqB : qB = d.fB - (mu : ℤ) * g.n 0)
    (hcA : complement F g.m qA = (y : ℤ) * g.n 1 + (z : ℤ) * g.n 2)
    (hcB : complement F g.m qB = (y' : ℤ) * g.n 1 + (z' : ℤ) * g.n 2)
    (hy : y < d.rho 1) (hz : z < d.rho 2)
    (hy' : y' < d.rho 1) (hz' : z' < d.rho 2) :
    lam = mu ∧ y' = y + d.a 1 ∧ z = z' + d.b 2 := by
  let v : Fin 3 → ℤ := ![(mu : ℤ) - lam, (d.a 1 : ℤ) + y - y', -(d.b 2 : ℤ) + z - z']
  have hv : integerValue g v = 0 := by
    simp only [complement, W] at hcA hcB
    dsimp [HerzogCriticalData.fA, HerzogCriticalData.fB] at hqA hqB
    simp [integerValue, v, Fin.sum_univ_succ]
    nlinarith
  have hr1 : (d.rho 1 : ℤ) = (d.a 1 : ℤ) + d.b 1 := by exact_mod_cast d.rho_eq 1
  have hr2 : (d.rho 2 : ℤ) = (d.a 2 : ℤ) + d.b 2 := by exact_mod_cast d.rho_eq 2
  have he := matched_kernel_box_zero hpos d v hv
    (by simp [v]; omega) (by simp [v]; omega)
    (by simp [v]; omega) (by simp [v]; omega) (by simp [v]; omega)
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  simp [v] at h0 h1 h2
  omega



/-- Exact MATCH scalars. The two slack coefficients are allowed to vanish. -/
structure MatchedPairData (g : Generators) (F : ℤ) (d : HerzogCriticalData g)
    (qA qB : ℤ) where
  depth : ℤ
  gapJ : ℤ
  gapK : ℤ
  P : ℤ
  R : ℤ
  T : ℤ
  depth_pos : 0 < depth
  depth_a : depth < d.a 0
  depth_b : depth < d.b 0
  gapJ_nonneg : 0 ≤ gapJ
  gapK_nonneg : 0 ≤ gapK
  P_eq : P = (d.rho 0 : ℤ) - depth
  R_eq : R = (d.a 1 : ℤ) + gapJ
  T_eq : T = (d.b 2 : ℤ) + gapK
  R_lt : R < d.rho 1
  T_lt : T < d.rho 2
  qA_eq : qA = d.fA - depth * g.n 0
  qB_eq : qB = d.fB - depth * g.n 0
  compA : complement F g.m qA = gapJ * g.n 1 + T * g.n 2
  compB : complement F g.m qB = R * g.n 1 + gapK * g.n 2
  W_eq : W F g.m = (P - 1) * g.n 0 + (R - 1) * g.n 1 + (T - 1) * g.n 2

namespace MatchedPairData
variable {g : Generators} {F qA qB : ℤ} {d : HerzogCriticalData g}
    (M : MatchedPairData g F d qA qB)

theorem P_gt_a : (d.a 0 : ℤ) < M.P := by
  have he : (d.rho 0 : ℤ) = (d.a 0 : ℤ) + d.b 0 := by exact_mod_cast d.rho_eq 0
  have := M.P_eq
  have := M.depth_b
  omega

theorem P_gt_b : (d.b 0 : ℤ) < M.P := by
  have he : (d.rho 0 : ℤ) = (d.a 0 : ℤ) + d.b 0 := by exact_mod_cast d.rho_eq 0
  have := M.P_eq
  have := M.depth_a
  omega

theorem P_pos : 0 < M.P := by have := M.P_gt_a; have := d.a_pos 0; omega

theorem R_pos : 0 < M.R := by have := M.R_eq; have := M.gapJ_nonneg; have := d.a_pos 1; omega

theorem T_pos : 0 < M.T := by have := M.T_eq; have := M.gapK_nonneg; have := d.b_pos 2; omega

end MatchedPairData

/-- Construct the full MATCH packet from the actual critical-box complements. -/
theorem matched_pair_data {g : Generators} (hpos : ∀ i, 0 < g.n i)
    (d : HerzogCriticalData g) {F qA qB : ℤ} {lam mu y z y' z' : ℕ}
    (hl : 0 < lam) (hlA : lam < d.a 0) (hm : 0 < mu) (hmB : mu < d.b 0)
    (hqA : qA = d.fA - (lam : ℤ) * g.n 0)
    (hqB : qB = d.fB - (mu : ℤ) * g.n 0)
    (hcA : complement F g.m qA = (y : ℤ) * g.n 1 + (z : ℤ) * g.n 2)
    (hcB : complement F g.m qB = (y' : ℤ) * g.n 1 + (z' : ℤ) * g.n 2)
    (hy : y < d.rho 1) (hz : z < d.rho 2)
    (hy' : y' < d.rho 1) (hz' : z' < d.rho 2) :
    Nonempty (MatchedPairData g F d qA qB) := by
  obtain ⟨hlm, hyy, hzz⟩ := matched_pair_sync hpos d hl hlA hm hmB hqA hqB hcA hcB hy hz hy' hz'
  have hyy' : (y' : ℤ) = (y : ℤ) + d.a 1 := by exact_mod_cast hyy
  have hzz' : (z : ℤ) = (z' : ℤ) + d.b 2 := by exact_mod_cast hzz
  refine ⟨{
    depth := lam, gapJ := y, gapK := z', P := (d.rho 0 : ℤ) - lam,
    R := y', T := z,
    depth_pos := by exact_mod_cast hl,
    depth_a := by exact_mod_cast hlA,
    depth_b := by rw [hlm]; exact_mod_cast hmB,
    gapJ_nonneg := Int.natCast_nonneg _, gapK_nonneg := Int.natCast_nonneg _,
    P_eq := rfl, R_eq := by omega, T_eq := by omega,
    R_lt := by exact_mod_cast hy', T_lt := by exact_mod_cast hz,
    qA_eq := hqA, qB_eq := by simpa [hlm] using hqB,
    compA := hcA, compB := hcB, W_eq := ?_ }⟩
  dsimp [complement, W] at hcA ⊢
  dsimp [HerzogCriticalData.fA] at hqA
  linear_combination hqA + hcA - g.n 1 * hyy'

end P21.Nonsymmetric



