import P21.Nonsymmetric.SameColor
import P21.Nonsymmetric.Herzog.PseudoFrobenius

namespace P21.Nonsymmetric
variable {g : Generators}

/-- Right mixed orientation: the only possible integral kernel coefficients. -/
theorem mixed_right_kernel_coefficients (D : HerzogCriticalData g)
    (u v I J K : ℤ)
    (hI : 0 < I) (hI' : I < D.rho 0+D.b 0)
    (hJ : -(D.b 1:ℤ) < J) (hJ' : J < D.rho 1+D.a 1)
    (hK : 0 < K) (hK' : K < 2*D.rho 2)
    (eI : I = u*D.a 0+v*D.b 0)
    (eJ : J = -u*D.rho 1+v*D.a 1)
    (eK : K = -u*D.b 2+v*D.rho 2) : u = 0 ∧ v = 1 := by
  have ha0 : (0:ℤ) < D.a 0 := by exact_mod_cast D.a_pos 0
  have hb0 : (0:ℤ) < D.b 0 := by exact_mod_cast D.b_pos 0
  have ha1 : (0:ℤ) < D.a 1 := by exact_mod_cast D.a_pos 1
  have hb2 : (0:ℤ) < D.b 2 := by exact_mod_cast D.b_pos 2
  have hr1 : (0:ℤ) < D.rho 1 := by exact_mod_cast D.rho_pos 1
  have hr2 : (0:ℤ) < D.rho 2 := by exact_mod_cast D.rho_pos 2
  have er0 : (D.rho 0:ℤ) = D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
  have er1 : (D.rho 1:ℤ) = D.a 1+D.b 1 := by exact_mod_cast D.rho_eq 1
  have hu : 0 ≤ u := by
    by_contra hn
    have hu : u ≤ -1 := by omega
    by_cases hv : 0 < v
    · nlinarith [mul_nonneg (by omega : 0 ≤ -u-1) hr1.le,
        mul_nonneg (by omega : 0 ≤ v-1) ha1.le]
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg (by omega : u ≤ 0) ha0.le,
        mul_nonpos_of_nonpos_of_nonneg (by omega : v ≤ 0) hb0.le]
  have hv : 1 ≤ v := by
    by_contra hn
    nlinarith [mul_nonneg hu hb2.le,
      mul_nonpos_of_nonpos_of_nonneg (by omega : v ≤ 0) hr2.le]
  have hu0 : u = 0 := by
    by_contra hn
    have hu1 : 1 ≤ u := by omega
    by_cases hv1 : v = 1
    · subst v
      nlinarith [mul_nonneg (by omega : 0 ≤ u-1) hr1.le]
    · nlinarith [mul_nonneg (by omega : 0 ≤ u-1) ha0.le,
        mul_nonneg (by omega : 0 ≤ v-2) hb0.le]
  subst u
  constructor
  · rfl
  · nlinarith [mul_nonneg (by omega : 0 ≤ v-1) hr2.le]

/-- Opposite mixed orientation: the only possible integral kernel coefficients. -/
theorem mixed_left_kernel_coefficients (D : HerzogCriticalData g)
    (u v I J K : ℤ)
    (hI : 0 < I) (hI' : I < D.rho 0+D.a 0)
    (_hJ : -(D.rho 1:ℤ)-D.a 1 < J) (_hJ' : J < D.b 1)
    (hK : -(D.rho 2:ℤ) < K) (hK' : K < D.b 2)
    (eI : I = u*D.a 0+v*D.b 0)
    (eJ : J = -u*D.rho 1+v*D.a 1)
    (eK : K = u*D.b 2-v*D.rho 2) : u = 1 ∧ v = 1 := by
  have ha0 : (0:ℤ) < D.a 0 := by exact_mod_cast D.a_pos 0
  have hb0 : (0:ℤ) < D.b 0 := by exact_mod_cast D.b_pos 0
  have hb2 : (0:ℤ) < D.b 2 := by exact_mod_cast D.b_pos 2
  have hr2 : (0:ℤ) < D.rho 2 := by exact_mod_cast D.rho_pos 2
  have ha2 : (0:ℤ) < D.a 2 := by exact_mod_cast D.a_pos 2
  have er0 : (D.rho 0:ℤ) = D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
  have er2 : (D.rho 2:ℤ) = D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
  have hu : 1 ≤ u := by
    by_contra hn
    have hu : u ≤ 0 := by omega
    by_cases hv : 0 < v
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hu hb2.le,
        mul_nonneg (by omega : 0 ≤ v-1) hr2.le]
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hu ha0.le,
        mul_nonpos_of_nonpos_of_nonneg (by omega : v ≤ 0) hb0.le]
  have hv : 1 ≤ v := by
    by_contra hn
    nlinarith [mul_nonneg (by omega : 0 ≤ u-1) hb2.le,
      mul_nonpos_of_nonpos_of_nonneg (by omega : v ≤ 0) hr2.le]
  have hu1 : u = 1 := by
    by_contra hn
    nlinarith [mul_nonneg (by omega : 0 ≤ u-2) ha0.le,
      mul_nonneg (by omega : 0 ≤ v-1) hb0.le]
  subst u
  constructor
  · rfl
  · by_contra hn
    nlinarith [mul_nonneg (by omega : 0 ≤ v-2) hr2.le]

/-- The right-orientation complements share the same actual j-coefficient;
this coefficient is allowed to be zero. -/
theorem mixed_right_complement_geometry (D : HerzogCriticalData g)
    (hp : ∀ i, 0 < g.n i) (F l n : ℤ)
    (hl : 1 ≤ l) (hlb : l < D.b 0) (hn : 1 ≤ n) (hna : n < D.a 2)
    (x y z y' : ℕ) (hx : x < D.rho 0) (hy : y < D.rho 1)
    (hz : z < D.rho 2) (hy' : y' < D.rho 1)
    (hci : complement F g.m (D.fB-l*g.n 0) = (y:ℤ)*g.n 1+(z:ℤ)*g.n 2)
    (hck : complement F g.m (D.fA-n*g.n 2) = (x:ℤ)*g.n 0+(y':ℤ)*g.n 1) :
    (z:ℤ) = D.a 2-n ∧ (x:ℤ) = D.b 0-l ∧ y' = y := by
  let w : Fin 3 → ℤ := ![l+x,(D.a 1:ℤ)-y+y',-(D.b 2:ℤ)-n-z]
  have hw : integerValue g w = 0 := by
    simp [integerValue,w,Fin.sum_univ_succ]
    simp only [complement,W,HerzogCriticalData.fA,HerzogCriticalData.fB] at hci hck
    linear_combination hci-hck
  obtain ⟨u,v,hev⟩ := integer_kernel_span hp D w hw
  have eI := hev 0
  have eJ := hev 1
  have eK := hev 2
  simp [w,kernelRowJ,kernelRowK] at eI eJ eK
  have er1 : (D.rho 1:ℤ) = D.a 1+D.b 1 := by exact_mod_cast D.rho_eq 1
  have er2 : (D.rho 2:ℤ) = D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
  have hc := mixed_right_kernel_coefficients D u v (l+x) ((D.a 1:ℤ)-y+y') (D.b 2+n+z)
    (by omega) (by omega) (by omega) (by omega) (by have := D.b_pos 2; omega) (by omega)
    eI (by linarith [eJ]) (by linarith [eK])
  rcases hc with ⟨rfl,rfl⟩
  simp at eI eJ eK
  exact ⟨by linarith,by linarith,by omega⟩

/-- The reverse orientation retains both independently nonnegative pair
coefficients; their difference is exactly a_j-b_j. -/
theorem mixed_left_complement_geometry (D : HerzogCriticalData g)
    (hp : ∀ i, 0 < g.n i) (F l n : ℤ)
    (hl : 1 ≤ l) (hla : l < D.a 0) (hn : 1 ≤ n) (hnb : n < D.b 2)
    (x y z y' : ℕ) (hx : x < D.rho 0) (hy : y < D.rho 1)
    (hz : z < D.rho 2) (hy' : y' < D.rho 1)
    (hci : complement F g.m (D.fA-l*g.n 0) = (y:ℤ)*g.n 1+(z:ℤ)*g.n 2)
    (hck : complement F g.m (D.fB-n*g.n 2) = (x:ℤ)*g.n 0+(y':ℤ)*g.n 1) :
    (z:ℤ) = D.rho 2-n ∧ (x:ℤ) = D.rho 0-l ∧ (y':ℤ) = y+D.a 1-D.b 1 := by
  let w : Fin 3 → ℤ := ![l+x,-(D.a 1:ℤ)-y+y',(D.b 2:ℤ)-n-z]
  have hw : integerValue g w = 0 := by
    simp [integerValue,w,Fin.sum_univ_succ]
    simp only [complement,W,HerzogCriticalData.fA,HerzogCriticalData.fB] at hci hck
    linear_combination hci-hck
  obtain ⟨u,v,hev⟩ := integer_kernel_span hp D w hw
  have eI := hev 0
  have eJ := hev 1
  have eK := hev 2
  simp [w,kernelRowJ,kernelRowK] at eI eJ eK
  have er0 : (D.rho 0:ℤ) = D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
  have er1 : (D.rho 1:ℤ) = D.a 1+D.b 1 := by exact_mod_cast D.rho_eq 1
  have er2 : (D.rho 2:ℤ) = D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
  have hc := mixed_left_kernel_coefficients D u v (l+x) (-(D.a 1:ℤ)-y+y') (D.b 2-n-z)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    eI (by linarith [eJ]) (by linarith [eK])
  rcases hc with ⟨rfl,rfl⟩
  simp at eI eJ eK
  exact ⟨by linarith,by linarith,by linarith⟩

end P21.Nonsymmetric

namespace P21.Nonsymmetric
variable {g : Generators}

/-- Completed BA-W has nonnegative coefficients even when the shared
j-coordinate vanishes. -/
theorem mixed_right_completed_W (D : HerzogCriticalData g) (F l n : ℤ) (R : ℕ)
    (hlb : l < D.b 0) (hna : n < D.a 2)
    (hci : complement F g.m (D.fB-l*g.n 0) =
      (R:ℤ)*g.n 1+(D.a 2-n)*g.n 2) :
    W F g.m = (D.b 0-l-1)*g.n 0+(R+D.rho 1-1:ℤ)*g.n 1+(D.a 2-n-1)*g.n 2 ∧
    0 ≤ D.b 0-l-1 ∧ 0 ≤ (R+D.rho 1-1:ℤ) ∧ 0 ≤ D.a 2-n-1 := by
  have hr := D.rho_pos 1
  refine ⟨?_,by omega,by omega,by omega⟩
  have er0 : (D.rho 0:ℤ) = D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
  simp only [complement,HerzogCriticalData.fB] at hci
  linear_combination hci-D.relation_one+g.n 0*er0

/-- The completed actual BA-W excludes the middle singleton without assuming
that its common complement coefficient is positive. -/
theorem mixed_right_no_middle_singleton (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (l n : ℤ) (R : ℕ)
    (hlb : l < D.b 0) (hna : n < D.a 2)
    (hci : complement F g.m (D.fB-l*g.n 0) =
      (R:ℤ)*g.n 1+(D.a 2-n)*g.n 2)
    {q : ℤ} (hq : q ∈ s.semigroup.Q F) (hs : IsSingleton g q 1) : False := by
  obtain ⟨k,hkp,hsk⟩ := singleton_pure_complement s hF hc hq hs
  have hk := singleton_critical_bound s hF hc hq hs (D.critical 1) hsk
  rw [D.coeff_rho] at hk
  have hw := (mixed_right_completed_W D F l n R hlb hna hci).1
  have hm := herzog_three_mem (g:=g) (D.b 0-l-1) (R+D.rho 1-k-1:ℤ) (D.a 2-n-1)
    (by omega) (by omega) (by omega)
  have hqH : q ∈ g.H := by
    convert hm using 1
    simp only [complement] at hsk
    linear_combination hw-hsk
  exact hq.1.1 (g.h_subset_gamma hqH)

end P21.Nonsymmetric

namespace P21.Nonsymmetric
variable {g : Generators}

/-- Reverse orientation excludes the i-singleton. The needed positive
j-coefficient is obtained from the actual PF complement antichain. -/
theorem mixed_left_no_first_singleton (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (l n : ℤ)
    (hl : 1 ≤ l) (hla : l < D.a 0) (hn : 1 ≤ n) (hnb : n < D.b 2)
    (x y z y' : ℕ) (hx : x < D.rho 0) (hy : y < D.rho 1)
    (hz : z < D.rho 2) (hy' : y' < D.rho 1)
    (hci : complement F g.m (D.fA-l*g.n 0) = (y:ℤ)*g.n 1+(z:ℤ)*g.n 2)
    (hck : complement F g.m (D.fB-n*g.n 2) = (x:ℤ)*g.n 0+(y':ℤ)*g.n 1)
    (hqk : D.fB-n*g.n 2 ∈ s.semigroup.Q F)
    {q : ℤ} (hq : q ∈ s.semigroup.Q F) (hs : IsSingleton g q 0)
    (hne : D.fB-n*g.n 2 ≠ q) : False := by
  obtain ⟨k,hkp,hsk⟩ := singleton_pure_complement s hF hc hq hs
  have hk := singleton_critical_bound s hF hc hq hs (D.critical 0) hsk
  rw [D.coeff_rho] at hk
  have ⟨ez,ex,ey⟩ := mixed_left_complement_geometry D
    (fun i => lt_trans s.m_pos (s.n_gt i)) F l n hl hla hn hnb x y z y' hx hy hz hy' hci hck
  have hyp : 0 < y' := by
    by_contra hh
    have hy0 : y' = 0 := by omega
    exact distinct_complements_not_one_ray hqk hq hne 0 x k
      (by simpa [hy0] using hck) hsk
  have hb0 := D.b_pos 0
  have er0 : (D.rho 0:ℤ) = D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
  have er2 : (D.rho 2:ℤ) = D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
  have hm := herzog_three_mem (g:=g) (2*D.rho 0-l-k-1) (y'-1:ℤ) (D.b 2-n-1)
    (by omega) (by omega) (by omega)
  have hqH : q ∈ g.H := by
    convert hm using 1
    rw [ez] at hci
    rw [ey]
    simp only [complement,W,HerzogCriticalData.fA] at hci hsk
    linear_combination hci-hsk-D.relation_zero+g.n 2*er2
  exact hq.1.1 (g.h_subset_gamma hqH)

/-- Reverse orientation also excludes the k-singleton. -/
theorem mixed_left_no_last_singleton (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (l n : ℤ)
    (hl : 1 ≤ l) (hla : l < D.a 0) (hn : 1 ≤ n) (hnb : n < D.b 2)
    (x y z y' : ℕ) (hx : x < D.rho 0) (hy : y < D.rho 1)
    (hz : z < D.rho 2) (hy' : y' < D.rho 1)
    (hci : complement F g.m (D.fA-l*g.n 0) = (y:ℤ)*g.n 1+(z:ℤ)*g.n 2)
    (hck : complement F g.m (D.fB-n*g.n 2) = (x:ℤ)*g.n 0+(y':ℤ)*g.n 1)
    (hqi : D.fA-l*g.n 0 ∈ s.semigroup.Q F)
    {q : ℤ} (hq : q ∈ s.semigroup.Q F) (hs : IsSingleton g q 2)
    (hne : D.fA-l*g.n 0 ≠ q) : False := by
  obtain ⟨k,hkp,hsk⟩ := singleton_pure_complement s hF hc hq hs
  have hk := singleton_critical_bound s hF hc hq hs (D.critical 2) hsk
  rw [D.coeff_rho] at hk
  have ⟨ez,ex,ey⟩ := mixed_left_complement_geometry D
    (fun i => lt_trans s.m_pos (s.n_gt i)) F l n hl hla hn hnb x y z y' hx hy hz hy' hci hck
  have hyp : 0 < y := by
    by_contra hh
    have hy0 : y = 0 := by omega
    exact distinct_complements_not_one_ray hqi hq hne 2 z k
      (by simpa [hy0] using hci) hsk
  have ha2 := D.a_pos 2
  have er0 : (D.rho 0:ℤ) = D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
  have er2 : (D.rho 2:ℤ) = D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
  have hm := herzog_three_mem (g:=g) (D.a 0-l-1) (y-1:ℤ) (2*D.rho 2-n-k-1)
    (by omega) (by omega) (by omega)
  have hqH : q ∈ g.H := by
    convert hm using 1
    rw [ez] at hci
    simp only [complement,W,HerzogCriticalData.fA] at hci hsk
    linear_combination hci-hsk-D.relation_two+g.n 0*er0
  exact hq.1.1 (g.h_subset_gamma hqH)

end P21.Nonsymmetric


namespace P21.Nonsymmetric
variable {g : Generators}

theorem mixed_right_next_kernel_coefficients (D : HerzogCriticalData g)
    (u v I J K : ℤ)
    (hI : 0 < I) (hI' : I < D.rho 1+D.b 1)
    (hJ : -(D.b 2:ℤ) < J) (hJ' : J < D.rho 2+D.a 2)
    (hK : 0 < K) (hK' : K < 2*D.rho 0)
    (eI : I = u*D.a 1+v*D.b 1)
    (eJ : J = -u*D.rho 2+v*D.a 2)
    (eK : K = -u*D.b 0+v*D.rho 0) : u = 0 ∧ v = 1 := by
  have ha0 : (0:ℤ) < D.a 1 := by exact_mod_cast D.a_pos 1
  have hb0 : (0:ℤ) < D.b 1 := by exact_mod_cast D.b_pos 1
  have ha1 : (0:ℤ) < D.a 2 := by exact_mod_cast D.a_pos 2
  have hb2 : (0:ℤ) < D.b 0 := by exact_mod_cast D.b_pos 0
  have hr1 : (0:ℤ) < D.rho 2 := by exact_mod_cast D.rho_pos 2
  have hr2 : (0:ℤ) < D.rho 0 := by exact_mod_cast D.rho_pos 0
  have er0 : (D.rho 1:ℤ) = D.a 1+D.b 1 := by exact_mod_cast D.rho_eq 1
  have er1 : (D.rho 2:ℤ) = D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
  have hu : 0 ≤ u := by
    by_contra hn
    have hu : u ≤ -1 := by omega
    by_cases hv : 0 < v
    · nlinarith [mul_nonneg (by omega : 0 ≤ -u-1) hr1.le,
        mul_nonneg (by omega : 0 ≤ v-1) ha1.le]
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg (by omega : u ≤ 0) ha0.le,
        mul_nonpos_of_nonpos_of_nonneg (by omega : v ≤ 0) hb0.le]
  have hv : 1 ≤ v := by
    by_contra hn
    nlinarith [mul_nonneg hu hb2.le,
      mul_nonpos_of_nonpos_of_nonneg (by omega : v ≤ 0) hr2.le]
  have hu0 : u = 0 := by
    by_contra hn
    have hu1 : 1 ≤ u := by omega
    by_cases hv1 : v = 1
    · subst v
      nlinarith [mul_nonneg (by omega : 0 ≤ u-1) hr1.le]
    · nlinarith [mul_nonneg (by omega : 0 ≤ u-1) ha0.le,
        mul_nonneg (by omega : 0 ≤ v-2) hb0.le]
  subst u
  constructor
  · rfl
  · nlinarith [mul_nonneg (by omega : 0 ≤ v-1) hr2.le]


end P21.Nonsymmetric

namespace P21.Nonsymmetric
variable {g : Generators}

/-- Cyclic right pair B_j,A_i, needed for both TYPE II and CHAIN extraction. -/
theorem mixed_right_next_complement_geometry (D : HerzogCriticalData g)
    (hp : ∀ i, 0 < g.n i) (F l m : ℤ)
    (hl : 1 ≤ l) (hla : l < D.a 0) (hm : 1 ≤ m) (hmb : m < D.b 1)
    (x y z z' : ℕ) (hx : x < D.rho 0) (hy : y < D.rho 1)
    (hz : z < D.rho 2) (hz' : z' < D.rho 2)
    (hci : complement F g.m (D.fA-l*g.n 0) = (y:ℤ)*g.n 1+(z:ℤ)*g.n 2)
    (hcj : complement F g.m (D.fB-m*g.n 1) = (x:ℤ)*g.n 0+(z':ℤ)*g.n 2) :
    (x:ℤ) = D.a 0-l ∧ (y:ℤ) = D.b 1-m ∧ z' = z := by
  let w : Fin 3 → ℤ := ![-(D.b 0:ℤ)-l-x,m+y,(D.a 2:ℤ)-z'+z]
  have er0 : (D.rho 0:ℤ) = D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
  have er1 : (D.rho 1:ℤ) = D.a 1+D.b 1 := by exact_mod_cast D.rho_eq 1
  have er2 : (D.rho 2:ℤ) = D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
  have hw : integerValue g w = 0 := by
    simp [integerValue,w,Fin.sum_univ_succ]
    simp only [complement,W,HerzogCriticalData.fA,HerzogCriticalData.fB] at hci hcj
    linear_combination hcj-hci+D.relation_two-g.n 2*er2
  obtain ⟨u,v,hev⟩ := integer_kernel_span hp D w hw
  have e0 := hev 0
  have e1 := hev 1
  have e2 := hev 2
  simp [w,kernelRowJ,kernelRowK] at e0 e1 e2
  have heI : m+y = (v-u)*(D.a 1:ℤ)+(-u)*D.b 1 := by
    linear_combination e1-u*er1
  have heJ : (D.a 2:ℤ)-z'+z = -(v-u)*D.rho 2+(-u)*D.a 2 := by
    linear_combination e2-u*er2
  have heK : (D.b 0:ℤ)+l+x = -(v-u)*D.b 0+(-u)*D.rho 0 := by
    linear_combination -e0+u*er0
  have hc := mixed_right_next_kernel_coefficients D (v-u) (-u)
    (m+y) ((D.a 2:ℤ)-z'+z) (D.b 0+l+x)
    (by omega) (by omega) (by omega) (by omega) (by have := D.b_pos 0; omega) (by omega)
    heI heJ heK
  have hu : u = -1 := by omega
  have hv : v = -1 := by omega
  subst u v
  simp at e0 e1 e2
  exact ⟨by linarith,by linarith,by omega⟩

end P21.Nonsymmetric

