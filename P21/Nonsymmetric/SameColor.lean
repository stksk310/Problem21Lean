import P21.Nonsymmetric.Kernel
import P21.Nonsymmetric.ComplementGeometry
import P21.Nonsymmetric.Singletons
import P21.Nonsymmetric.Herzog.PseudoFrobenius

namespace P21.Nonsymmetric
variable {g : Generators}

/-- The coefficient inequalities of two A-arms permit exactly the two
publication kernel combinations, including zero boundary coefficients. -/
theorem same_color_kernel_coefficients (D : HerzogCriticalData g)
    (u v I J K : ℤ)
    (hI : 0 < I) (hI' : I < D.rho 0+D.a 0)
    (_hJ : -(D.rho 1:ℤ) < J) (hJ' : J < D.rho 1)
    (hK : 0 < K) (hK' : K < D.rho 2+D.a 2)
    (eI : I = u*D.a 0+v*D.b 0)
    (eJ : J = -u*D.rho 1+v*D.a 1)
    (eK : K = -u*D.b 2+v*D.rho 2) :
    (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 1) := by
  have ha0 : (0:ℤ) < D.a 0 := by exact_mod_cast D.a_pos 0
  have hb0 : (0:ℤ) < D.b 0 := by exact_mod_cast D.b_pos 0
  have ha1 : (0:ℤ) < D.a 1 := by exact_mod_cast D.a_pos 1
  have hb2 : (0:ℤ) < D.b 2 := by exact_mod_cast D.b_pos 2
  have hr1 : (0:ℤ) < D.rho 1 := by exact_mod_cast D.rho_pos 1
  have hr2 : (0:ℤ) < D.rho 2 := by exact_mod_cast D.rho_pos 2
  have er0 : (D.rho 0:ℤ) = D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
  have er2 : (D.rho 2:ℤ) = D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
  have hu : 0 ≤ u := by
    by_contra hn
    have hu : u ≤ -1 := by omega
    by_cases hv : 0 < v
    · have hv' : 1 ≤ v := by omega
      nlinarith [mul_nonneg (by omega : 0 ≤ -u-1) hr1.le,
        mul_nonneg (by omega : 0 ≤ v-1) ha1.le]
    · have hv' : v ≤ 0 := by omega
      nlinarith [mul_nonpos_of_nonpos_of_nonneg (by omega : u ≤ 0) ha0.le,
        mul_nonpos_of_nonpos_of_nonneg hv' hb0.le]
  have hv : 1 ≤ v := by
    by_contra hn
    have hv : v ≤ 0 := by omega
    nlinarith [mul_nonneg hu hb2.le, mul_nonpos_of_nonpos_of_nonneg hv hr2.le]
  have hu' : u ≤ 1 := by
    by_contra hn
    have hu2 : 2 ≤ u := by omega
    nlinarith [mul_nonneg (by omega : 0 ≤ u-2) ha0.le,
      mul_nonneg (by omega : 0 ≤ v-1) hb0.le]
  have hv' : v ≤ 1 := by
    by_contra hn
    have hv2 : 2 ≤ v := by omega
    nlinarith [mul_nonneg (by omega : 0 ≤ 1-u) hb2.le,
      mul_nonneg (by omega : 0 ≤ v-2) hr2.le]
  omega

/-- Exact two-case geometry, starting with the actual pair coefficients of
the two named complements. No coefficient is strengthened to positivity. -/
theorem same_color_complement_cases (D : HerzogCriticalData g)
    (hp : ∀ i, 0 < g.n i) (F l n : ℤ)
    (hl : 1 ≤ l) (hla : l < D.a 0) (hn : 1 ≤ n) (hna : n < D.a 2)
    (x y z y' : ℕ) (hx : x < D.rho 0) (hy : y < D.rho 1)
    (hz : z < D.rho 2) (hy' : y' < D.rho 1)
    (hci : complement F g.m (D.fA-l*g.n 0) = (y:ℤ)*g.n 1+(z:ℤ)*g.n 2)
    (hck : complement F g.m (D.fA-n*g.n 2) = (x:ℤ)*g.n 0+(y':ℤ)*g.n 1) :
    ((z:ℤ) = D.rho 2-n ∧ (x:ℤ) = D.b 0-l ∧ (y':ℤ) = y+D.a 1) ∨
    ((z:ℤ) = D.a 2-n ∧ (x:ℤ) = D.rho 0-l ∧ (y:ℤ) = y'+D.b 1) := by
  let w : Fin 3 → ℤ := ![l+x,(y':ℤ)-y,-n-z]
  have hw : integerValue g w = 0 := by
    simp [integerValue,w,Fin.sum_univ_succ]
    simp only [complement,W] at hci hck
    linear_combination hci-hck
  obtain ⟨u,v,hev⟩ := integer_kernel_span hp D w hw
  have eI := hev 0
  have eJ := hev 1
  have eK := hev 2
  simp [w,kernelRowJ,kernelRowK] at eI eJ eK
  have hc := same_color_kernel_coefficients D u v (l+x) ((y':ℤ)-y) (n+z)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    eI (by linarith [eJ]) (by linarith [eK])
  rcases hc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · left; simp at eI eJ eK; exact ⟨by linarith,by linarith,by linarith⟩
  · right
    have er0 : (D.rho 0:ℤ) = D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
    have er1 : (D.rho 1:ℤ) = D.a 1+D.b 1 := by exact_mod_cast D.rho_eq 1
    have er2 : (D.rho 2:ℤ) = D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
    simp at eI eJ eK
    exact ⟨by linarith,by linarith,by linarith⟩

end P21.Nonsymmetric



namespace P21.Nonsymmetric
variable {g : Generators}

/-- The remaining-direction singleton is excluded in both same-color cases
by actual nonnegative tail representations. -/
theorem same_color_no_middle_singleton (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (l n : ℤ)
    (hl : 1 ≤ l) (hla : l < D.a 0) (hn : 1 ≤ n) (hna : n < D.a 2)
    (x y z y' : ℕ) (hx : x < D.rho 0) (hy : y < D.rho 1)
    (hz : z < D.rho 2) (hy' : y' < D.rho 1)
    (hci : complement F g.m (D.fA-l*g.n 0) = (y:ℤ)*g.n 1+(z:ℤ)*g.n 2)
    (hck : complement F g.m (D.fA-n*g.n 2) = (x:ℤ)*g.n 0+(y':ℤ)*g.n 1)
    {q : ℤ} (hq : q ∈ s.semigroup.Q F) (hs : IsSingleton g q 1) : False := by
  have hp : ∀ i, 0 < g.n i := fun i => lt_trans s.m_pos (s.n_gt i)
  obtain ⟨k,hkp,hsk⟩ := singleton_pure_complement s hF hc hq hs
  have hk := singleton_critical_bound s hF hc hq hs (D.critical 1) hsk
  rw [D.coeff_rho] at hk
  have er0 : (D.rho 0:ℤ) = D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
  have er1 : (D.rho 1:ℤ) = D.a 1+D.b 1 := by exact_mod_cast D.rho_eq 1
  have er2 : (D.rho 2:ℤ) = D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
  have ha1 := D.a_pos 1
  have hb0 := D.b_pos 0
  rcases same_color_complement_cases D hp F l n hl hla hn hna x y z y' hx hy hz hy'
    hci hck with ⟨ez,ex,ey⟩ | ⟨ez,ex,ey⟩
  · have hm := herzog_three_mem (g:=g) (D.b 0-l) (D.a 1+y-k-1+D.rho 1) (D.a 2-n-1)
      (by omega) (by omega) (by omega)
    have hret : q+g.n 0 ∈ g.H := by
      convert hm using 1
      rw [ez] at hci
      simp only [complement,W,HerzogCriticalData.fA] at hci hsk
      linear_combination hci-hsk-D.relation_one+g.n 0*er0+g.n 2*er2
    have hi : (0:Fin 3) ∈ g.SH q := hret
    rw [hs] at hi
    simp at hi
  · have hm := herzog_three_mem (g:=g) (D.rho 0-l-1) (D.rho 1+y'-k-1) (D.a 2-n-1)
      (by omega) (by omega) (by omega)
    have hqH : q ∈ g.H := by
      convert hm using 1
      rw [ez,ey] at hci
      simp only [complement,W,HerzogCriticalData.fA] at hci hsk
      linear_combination hci-hsk-g.n 1*er1
    exact hq.1.1 (g.h_subset_gamma hqH)

end P21.Nonsymmetric

namespace P21.Nonsymmetric
variable {g : Generators}

/-- Distinct actual PF complements cannot lie on one nonnegative generator ray. -/
theorem distinct_complements_not_one_ray {s : g.Setting} {F q r : ℤ}
    (hq : q ∈ s.semigroup.Q F) (hr : r ∈ s.semigroup.Q F) (hne : q ≠ r)
    (i : Fin 3) (a b : ℕ)
    (ha : complement F g.m q = (a:ℤ)*g.n i)
    (hb : complement F g.m r = (b:ℤ)*g.n i) : False := by
  rcases le_total a b with hab | hba
  · apply complement_antichain hq hr hne
    apply g.h_subset_gamma
    have hm := g.H.nsmul_mem (generator_mem g.n i) (b-a)
    have he : complement F g.m r-complement F g.m q = ((b-a:ℕ):ℤ)*g.n i := by
      rw [ha,hb,Nat.cast_sub hab]; ring
    simpa [he,nsmul_eq_mul] using hm
  · apply complement_antichain hr hq (Ne.symm hne)
    apply g.h_subset_gamma
    have hm := g.H.nsmul_mem (generator_mem g.n i) (a-b)
    have he : complement F g.m q-complement F g.m r = ((a-b:ℕ):ℤ)*g.n i := by
      rw [ha,hb,Nat.cast_sub hba]; ring
    simpa [he,nsmul_eq_mul] using hm

/-- Two same-color arms exclude simultaneous endpoint singletons. The
positive auxiliary coefficients are derived by actual complement antichain. -/
theorem same_color_no_two_endpoint_singletons (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (l n : ℤ)
    (hl : 1 ≤ l) (hla : l < D.a 0) (hn : 1 ≤ n) (hna : n < D.a 2)
    (x y z y' : ℕ) (hx : x < D.rho 0) (hy : y < D.rho 1)
    (hz : z < D.rho 2) (hy' : y' < D.rho 1)
    (hci : complement F g.m (D.fA-l*g.n 0) = (y:ℤ)*g.n 1+(z:ℤ)*g.n 2)
    (hck : complement F g.m (D.fA-n*g.n 2) = (x:ℤ)*g.n 0+(y':ℤ)*g.n 1)
    (hqi : D.fA-l*g.n 0 ∈ s.semigroup.Q F) (hqk : D.fA-n*g.n 2 ∈ s.semigroup.Q F)
    {qI qK : ℤ} (hqI : qI ∈ s.semigroup.Q F) (hqK : qK ∈ s.semigroup.Q F)
    (hsI : IsSingleton g qI 0) (hsK : IsSingleton g qK 2)
    (hneI : D.fA-n*g.n 2 ≠ qI) (hneK : D.fA-l*g.n 0 ≠ qK) : False := by
  have hp : ∀ i, 0 < g.n i := fun i => lt_trans s.m_pos (s.n_gt i)
  obtain ⟨ki,hkip,hsi⟩ := singleton_pure_complement s hF hc hqI hsI
  obtain ⟨kk,hkkp,hsk⟩ := singleton_pure_complement s hF hc hqK hsK
  have hki := singleton_critical_bound s hF hc hqI hsI (D.critical 0) hsi
  have hkk := singleton_critical_bound s hF hc hqK hsK (D.critical 2) hsk
  rw [D.coeff_rho] at hki hkk
  have er0 : (D.rho 0:ℤ) = D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
  have er1 : (D.rho 1:ℤ) = D.a 1+D.b 1 := by exact_mod_cast D.rho_eq 1
  have er2 : (D.rho 2:ℤ) = D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
  have hb0 := D.b_pos 0
  have hb2 := D.b_pos 2
  rcases same_color_complement_cases D hp F l n hl hla hn hna x y z y' hx hy hz hy'
    hci hck with ⟨ez,ex,ey⟩ | ⟨ez,ex,ey⟩
  · have hyp : 0 < y := by
      by_contra hh
      have hy0 : y = 0 := by omega
      exact distinct_complements_not_one_ray hqi hqK hneK 2 z kk
        (by simpa [hy0] using hci) hsk
    have hm := herzog_three_mem (g:=g) (D.a 0-l) (y-1:ℤ) (2*D.rho 2-n-kk-1)
      (by omega) (by omega) (by omega)
    have hret : qK+g.n 0 ∈ g.H := by
      convert hm using 1
      rw [ez] at hci
      simp only [complement,W,HerzogCriticalData.fA] at hci hsk
      linear_combination hci-hsk-D.relation_two+g.n 0*er0
    have hi : (0:Fin 3) ∈ g.SH qK := hret
    rw [hsK] at hi
    simp at hi
  · have hyp : 0 < y' := by
      by_contra hh
      have hy0 : y' = 0 := by omega
      exact distinct_complements_not_one_ray hqk hqI hneI 0 x ki
        (by simpa [hy0] using hck) hsi
    have hm := herzog_three_mem (g:=g) (D.rho 0-l+D.a 0-ki-1) (y'-1:ℤ) (D.rho 2-n)
      (by omega) (by omega) (by omega)
    have hret : qI+g.n 2 ∈ g.H := by
      convert hm using 1
      rw [ez,ey] at hci
      simp only [complement,W,HerzogCriticalData.fA] at hci hsi
      linear_combination hci-hsi+D.relation_one-g.n 1*er1-g.n 2*er2
    have hi : (2:Fin 3) ∈ g.SH qI := hret
    rw [hsI] at hi
    simp at hi

end P21.Nonsymmetric

