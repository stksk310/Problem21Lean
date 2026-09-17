import P21.Nonsymmetric.Singletons
import P21.Nonsymmetric.Kernel

namespace P21.Nonsymmetric

set_option maxHeartbeats 800000

/-- BOX-W saturation uses the cap on every factorization and the exact integer
kernel. No uniqueness of the entire W factorization fiber is assumed. -/
theorem singleton_saturation {g : Generators} (s : g.Setting) {F q P R T : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (hq : q ∈ s.semigroup.Q F)
    (hs : IsSingleton g q 0) {k : ℕ} (hk : 0 < k)
    (he : complement F g.m q = (k : ℤ)*g.n 0)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hT : 1 ≤ T)
    (_hPr : P ≤ D.rho 0) (hRr : R ≤ D.rho 1) (hTr : T ≤ D.rho 2)
    (hW : W F g.m = (P-1)*g.n 0+(R-1)*g.n 1+(T-1)*g.n 2) : (k : ℤ) = P := by
  classical
  have hPc : ((P-1).toNat : ℤ) = P-1 := Int.toNat_of_nonneg (by omega)
  have hRc : ((R-1).toNat : ℤ) = R-1 := Int.toNat_of_nonneg (by omega)
  have hTc : ((T-1).toNat : ℤ) = T-1 := Int.toNat_of_nonneg (by omega)
  let b : Fin 3 → ℕ := ![(P-1).toNat,(R-1).toNat,(T-1).toNat]
  have hb : value g.n b = W F g.m := by
    simp only [value, Fin.sum_univ_three]
    change ((P-1).toNat : ℤ)*g.n 0+((R-1).toNat : ℤ)*g.n 1+
      ((T-1).toNat : ℤ)*g.n 2 = W F g.m
    rw [hPc,hRc,hTc,hW]
  let base : g.ActualFactorization3 (W F g.m) := ⟨b,hb⟩
  have hcap := singleton_W_cap hq he base
  have hbase0 : (base.coeff 0 : ℤ) = P-1 := hPc
  have hPk : P ≤ k := by omega
  obtain ⟨a,ha⟩ := singleton_W_cap_attained s hq hk hs he
  have hka := singleton_critical_bound s hF hc hq hs (D.critical 0) he
  rw [D.coeff_rho] at hka
  let v : Fin 3 → ℤ := fun i => (a.coeff i : ℤ)-b i
  have hv : integerValue g v = 0 := by
    simp only [integerValue,v,sub_mul,Finset.sum_sub_distrib]
    change value g.n a.coeff - value g.n b = 0
    rw [a.equation,hb]; ring
  obtain ⟨u,w,huw⟩ := integer_kernel_span (fun i => lt_trans s.m_pos (s.n_gt i)) D v hv
  have h0 := huw 0
  have h1 := huw 1
  have h2 := huw 2
  change (a.coeff 0 : ℤ)-((P-1).toNat : ℤ) = u*(D.a 0 : ℤ)+w*(D.b 0 : ℤ) at h0
  change (a.coeff 1 : ℤ)-((R-1).toNat : ℤ) = u*(-(D.rho 1 : ℤ))+w*(D.a 1 : ℤ) at h1
  change (a.coeff 2 : ℤ)-((T-1).toNat : ℤ) = u*(D.b 2 : ℤ)+w*(-(D.rho 2 : ℤ)) at h2
  rw [hPc] at h0
  rw [hRc] at h1
  rw [hTc] at h2
  have hp0 : (0 : ℤ) < D.a 0 := by exact_mod_cast D.a_pos 0
  have hp1 : (0 : ℤ) < D.a 1 := by exact_mod_cast D.a_pos 1
  have hp2 : (0 : ℤ) < D.b 2 := by exact_mod_cast D.b_pos 2
  have hb0 : (0 : ℤ) < D.b 0 := by exact_mod_cast D.b_pos 0
  have hr1 : (0 : ℤ) < D.rho 1 := by exact_mod_cast D.rho_pos 1
  have hr2 : (0 : ℤ) < D.rho 2 := by exact_mod_cast D.rho_pos 2
  have he0 : (D.rho 0 : ℤ) = D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
  have hbnd : (a.coeff 0 : ℤ) ≤ P-1 := by
    by_cases hu : 1 ≤ u
    · by_cases hw : 1 ≤ w
      · have hbig : (D.rho 0 : ℤ) ≤ a.coeff 0 := by
          nlinarith [mul_nonneg (show 0 ≤ u-1 by omega) hp0.le,
            mul_nonneg (show 0 ≤ w-1 by omega) hb0.le]
        omega
      · have hw0 : w ≤ 0 := by omega
        nlinarith [mul_nonneg (show 0 ≤ u-1 by omega) hr1.le,
          mul_nonpos_of_nonpos_of_nonneg hw0 hp1.le]
    · have hu0 : u ≤ 0 := by omega
      by_cases hw : 1 ≤ w
      · nlinarith [mul_nonneg (show 0 ≤ w-1 by omega) hr2.le,
          mul_nonpos_of_nonpos_of_nonneg hu0 hp2.le]
      · have hw0 : w ≤ 0 := by omega
        nlinarith [mul_nonpos_of_nonpos_of_nonneg hu0 hp0.le,
          mul_nonpos_of_nonpos_of_nonneg hw0 hb0.le]
  omega

end P21.Nonsymmetric
