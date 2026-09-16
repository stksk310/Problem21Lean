import P21.Symmetric.GlueNormalForm

/-! Appendix A, S3.8--S3.10: the arithmetic closures for Branch II.
Geometric gap premises are supplied by actual rows through GAP-K and CAN. -/
namespace P21.Symmetric.BranchII

/-- K1-g is derived from the positive stable shift and the strict multiplicity bound. -/
theorem k1_aux_pos {d w s kappa rho theta : ℤ}
    (hd : 0 < d) (hw : 0 < w) (hks : kappa + s + 1 ≤ d)
    (hr : 0 < s * w + d * rho) (hmw : d * theta - kappa * w < w) :
    0 < w - theta + rho := by
  have hprod := mul_nonneg (show 0 ≤ d - (kappa + s + 1) by omega) hw.le
  nlinarith

/-- The two actual backward gaps force the already independent Branch I condition. -/
theorem k1_reduces_to_branchI (T : TwoGeneratorData) {a b w rho theta t₀ : ℤ}
    (ha : 0 < a) (hav : a < T.v) (hb : 0 < b) (hbu : b < T.u)
    (hrho : rho = T.u * T.v - w - a * T.u - b * T.v)
    (htheta : theta = rho + T.u + T.v + t₀)
    (hg : 0 < w - T.u - T.v - t₀)
    (hgapx : a * T.u + (w - T.u - T.v - t₀) ∉ T.T)
    (hgapy : b * T.v + (w - T.u - T.v - t₀) ∉ T.T) :
    theta - T.u - T.v ∈ T.T := by
  let X := T.frobenius - (w - T.u - T.v - t₀)
  have hx : X - a * T.u ∈ T.T := by
    convert (T.frobenius_symmetry _).1 hgapx using 1; dsimp [X]; ring
  have hy : X - b * T.v ∈ T.T := by
    convert (T.frobenius_symmetry _).1 hgapy using 1; dsimp [X]; ring
  rcases (T.two_generator_intersection_iff ha hav hb hbu).1 ⟨hx,hy⟩ with h | h
  · have he : theta - T.u - T.v = X - (a * T.u + b * T.v) := by
      dsimp [X, TwoGeneratorData.frobenius]
      linear_combination htheta + hrho
    rw [he]
    exact h
  · have hn := T.nonneg h
    dsimp [X, TwoGeneratorData.frobenius] at hn
    have hu := T.u_pos
    have hv := T.v_pos
    omega

/-- The e=0 case fails already at the first stable coordinate. -/
theorem k0_e0_impossible (T : TwoGeneratorData) {rho theta t₀ : ℤ}
    (htheta : theta = rho + T.u + T.v + t₀)
    (ht₀ : t₀ ∈ T.T) (hu : theta < T.u) (hv : theta < T.v)
    (hfs : rho + theta ∈ T.T) : False := by
  have ht := T.nonneg ht₀
  have hf := T.nonneg hfs
  omega

/-- The negative parameter in K0 has both mixed-sign coordinate representations. -/
theorem k0_theta_coefficients (T : TwoGeneratorData) {A B p q rho theta : ℤ}
    (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hrho : rho = T.u*T.v - A*T.u - B*T.v)
    (htheta : theta = rho + T.u + T.v + (p*T.u+q*T.v))
    (hgap : theta ∉ T.T) (hAv : A < T.v) (hBu : B < T.u) :
    p ≤ A - 2 ∧ q ≤ B - 2 ∧
    theta = -(A-1-p)*T.u + (T.u-(B-1-q))*T.v ∧
    theta = (T.v-(A-1-p))*T.u - (B-1-q)*T.v := by
  have he₁ : theta = (p+1-A)*T.u + (T.u+q+1-B)*T.v := by
    linear_combination htheta + hrho
  have he₂ : theta = (T.v+p+1-A)*T.u + (q+1-B)*T.v := by
    linear_combination htheta + hrho
  have hpA : p ≤ A-2 := by
    by_contra hn
    exact hgap ⟨p+1-A,T.u+q+1-B,by omega,by omega,he₁⟩
  have hqB : q ≤ B-2 := by
    by_contra hn
    exact hgap ⟨T.v+p+1-A,q+1-B,by omega,by omega,he₂⟩
  exact ⟨hpA,hqB,by linear_combination he₁,by linear_combination he₂⟩

/-- Euclidean division identified by its exact half-open interval. -/
theorem div_eq_of_bounds {a d q : ℤ} (hd : 0 < d)
    (hl : q*d ≤ a) (hu : a < (q+1)*d) : a/d = q := by
  have he := Int.ediv_mul_add_emod a d
  have hr₀ := Int.emod_nonneg a (ne_of_gt hd)
  have hrd := Int.emod_lt_of_pos a hd
  by_contra hn
  rcases lt_or_gt_of_ne hn with hn | hn
  · have : a/d ≤ q-1 := by omega
    nlinarith
  · have : q+1 ≤ a/d := by omega
    nlinarith

/-- The publication's floor, ceiling, and carry difference, on integer indices. -/
def carry (d s e n : ℤ) : ℤ := (s+n*e)/d
def ceiling (d e n : ℤ) : ℤ := (n*e+d-1)/d
def epsilon (d s e n : ℤ) : ℤ := ceiling d e n - carry d s e n
def tau (d s e w rho theta n : ℤ) : ℤ := rho+n*theta+carry d s e n*w
def complement (d e w B v theta n : ℤ) : ℤ := B*v-n*theta-ceiling d e n*w

/-- COMP is a same-index identity, with no membership inferred from signed arithmetic. -/
theorem complement_add_tau {d s e w rho theta A B D u v n : ℤ}
    (hrho : rho = u*v-A*u-B*v) (hAD : A+D=v) :
    complement d e w B v theta n + tau d s e w rho theta n =
      D*u-epsilon d s e n*w := by
  dsimp [complement,tau,epsilon]
  linear_combination hrho - u*hAD

theorem carry_of_residue {d s e n q r : ℤ} (hd : 0 < d)
    (hs : 0 ≤ s) (hsd : s < d) (hr : 0 ≤ r) (hrd : r < d)
    (he : n*e = q*d+r) :
    carry d s e n = q + if s+r < d then 0 else 1 := by
  dsimp [carry]
  split_ifs with h
  · apply div_eq_of_bounds hd <;> nlinarith
  · apply div_eq_of_bounds hd <;> nlinarith

theorem ceiling_of_residue {d e n q r : ℤ} (hd : 0 < d)
    (hr : 0 ≤ r) (hrd : r < d) (he : n*e = q*d+r) :
    ceiling d e n = q + if r = 0 then 0 else 1 := by
  dsimp [ceiling]
  split_ifs with h
  · apply div_eq_of_bounds hd <;> nlinarith
  · have hr1 : 1 ≤ r := by omega
    apply div_eq_of_bounds hd <;> nlinarith

theorem epsilon_zero_or_one {d s e n : ℤ} (hd : 0 < d)
    (hs : 0 ≤ s) (hsd : s < d) :
    epsilon d s e n = 0 ∨ epsilon d s e n = 1 := by
  have hr := Int.emod_nonneg (n*e) (ne_of_gt hd)
  have hrd := Int.emod_lt_of_pos (n*e) hd
  have he := (Int.ediv_mul_add_emod (n*e) d).symm
  dsimp [epsilon]
  rw [carry_of_residue hd hs hsd hr hrd he, ceiling_of_residue hd hr hrd he]
  split_ifs <;> omega

theorem epsilon_one_residue {d s e n : ℤ} (hd : 0 < d)
    (hs : 0 ≤ s) (hsd : s < d) (heps : epsilon d s e n = 1) :
    0 < (n*e)%d ∧ s+(n*e)%d < d := by
  have hr := Int.emod_nonneg (n*e) (ne_of_gt hd)
  have hrd := Int.emod_lt_of_pos (n*e) hd
  have he := (Int.ediv_mul_add_emod (n*e) d).symm
  dsimp [epsilon] at heps
  rw [carry_of_residue hd hs hsd hr hrd he, ceiling_of_residue hd hr hrd he] at heps
  split_ifs at heps <;> omega

/-- The predecessor equality is proved before the previous stable point is used.
The index is proved to be at least two; no N=1 predecessor is assumed. -/
theorem epsilon_one_predecessor {d s e n : ℤ} (hd : 0 < d)
    (hs : 0 ≤ s) (hsd : s < d) (he : 0 < e) (hed : e < d)
    (hek : d-s ≤ e) (hphase : 2*e ≤ d+1) (hn : 1 ≤ n)
    (heps : epsilon d s e n = 1) :
    2 ≤ n ∧ carry d s e (n-1) = carry d s e n := by
  have hr := epsilon_one_residue hd hs hsd heps
  have hn2 : 2 ≤ n := by
    by_contra h
    have hn1 : n = 1 := by omega
    rw [hn1, one_mul, Int.emod_eq_of_lt he.le hed] at hr
    omega
  refine ⟨hn2, ?_⟩
  have heq := (Int.ediv_mul_add_emod (n*e) d).symm
  have hr0 := Int.emod_nonneg (n*e) (ne_of_gt hd)
  have hrd := Int.emod_lt_of_pos (n*e) hd
  have hc := carry_of_residue hd hs hsd hr0 hrd heq
  simp only [hr.2, ↓reduceIte, add_zero] at hc
  rw [hc]
  dsimp [carry]
  apply div_eq_of_bounds hd
  · nlinarith
  · nlinarith

/-- PHASE follows from the first stable point, never from an assumed carry bound. -/
theorem crosscore_phase {d s e w rho theta L₀ : ℤ} (hd : 0 < d)
    (hs : 0 ≤ s) (hsd : s < d) (he : 0 < e) (hed : e < d)
    (hw : 0 < w) (hL : 0 < L₀) (htheta : theta = rho+L₀)
    (hmw : e*w+d*theta < w) (hfs : 0 ≤ tau d s e w rho theta 1) :
    theta < 0 ∧ d-s ≤ e ∧ (e-1)*w < d*(-theta) ∧
      2*d*(-theta) < d*w ∧ 2*e ≤ d+1 := by
  have htheta0 : theta < 0 := by
    have he1 : 1 ≤ e := by omega
    have hp := mul_nonneg (show 0 ≤ e-1 by omega) hw.le
    nlinarith
  have hc := carry_of_residue hd hs hsd he.le hed (show (1:ℤ)*e = 0*d+e by ring)
  have hsek : d ≤ s+e := by
    by_contra hn
    have hc0 : carry d s e 1 = 0 := by simpa [show s+e < d by omega] using hc
    dsimp [tau] at hfs
    rw [hc0] at hfs
    nlinarith
  have hc1 : carry d s e 1 = 1 := by simpa [show ¬s+e < d by omega] using hc
  dsimp [tau] at hfs
  rw [hc1] at hfs
  have htw : 2*(-theta) < w := by nlinarith
  have htw' := mul_lt_mul_of_pos_left htw hd
  have hl : (e-1)*w < d*(-theta) := by nlinarith
  have hephase : 2*e ≤ d+1 := by
    by_contra hn
    have hp := mul_nonneg (show 0 ≤ 2*e-(d+2) by omega) hw.le
    nlinarith
  exact ⟨htheta0,by omega,hl,by nlinarith,hephase⟩

/-- The translation criterion used in the cross-core argument, proved by normal form. -/
theorem shift_gap_has_axis (T : TwoGeneratorData) {A D t : ℤ}
    (hA : 0 ≤ A) (hAD : A+D=T.v) (ht : t ∈ T.T)
    (hgap : t+A*T.u-T.v ∉ T.T) :
    ∃ j : ℤ, 0 ≤ j ∧ j < D ∧ t=j*T.u := by
  obtain ⟨a,b,hb,hbu,he⟩ := T.normal_form_exists t
  have ha : 0 ≤ a := (T.normal_form_mem_iff hb hbu).1 (by rw [← he]; exact ht)
  have hb0 : b = 0 := by
    by_contra hn
    apply hgap
    refine ⟨a+A,b-1,by omega,by omega,?_⟩
    linear_combination he
  have ht' : t = a*T.u := by simpa [hb0] using he
  have he' : t+A*T.u-T.v = (a-D)*T.u+(T.u-1)*T.v := by
    rw [ht']
    linear_combination T.u*hAD
  have hgap' : ¬0 ≤ a-D := by
    intro h
    apply hgap
    rw [he']
    exact (T.normal_form_mem_iff (by have := T.u_pos; omega) (by omega)).2 h
  exact ⟨a,ha,by omega,ht'⟩

/-- Cross-core exclusion: all positive translated points lie in T. The only
geometric premise is the actual complementary gap, supplied from ALL-AP. -/
theorem crosscore_shift_mem (T : TwoGeneratorData)
    {d s e w rho theta A B D P Q : ℤ}
    (hd : 0 < d) (hs : 0 ≤ s) (hsd : s < d) (he : 0 < e) (hed : e < d)
    (hek : d-s ≤ e) (hphase : 2*e ≤ d+1)
    (hA : 0 ≤ A) (hAD : A+D=T.v) (hP : P ≤ A-1)
    (hQ : 0 < Q) (hQu : Q < T.u)
    (htheta : theta = -P*T.u+Q*T.v)
    (hrho : rho = T.u*T.v-A*T.u-B*T.v)
    (hfs : ∀ n : ℤ, 1 ≤ n → tau d s e w rho theta n ∈ T.T)
    (hY : ∀ n : ℤ, 1 ≤ n → complement d e w B T.v theta n ∉ T.T)
    (n : ℤ) (hn : 1 ≤ n) :
    tau d s e w rho theta n + A*T.u-T.v ∈ T.T := by
  by_contra hgap
  obtain ⟨j,hj,hjD,hjEq⟩ := shift_gap_has_axis T hA hAD (hfs n hn) hgap
  have hcomp := complement_add_tau (n := n) (d := d) (s := s) (e := e)
    (w := w) (theta := theta) hrho hAD
  rcases epsilon_zero_or_one hd hs hsd (e := e) (n := n) with heps | heps
  · have hyeq : complement d e w B T.v theta n = (D-j)*T.u := by
      rw [heps, hjEq] at hcomp
      linear_combination hcomp
    apply hY n hn
    rw [hyeq]
    exact ⟨D-j,0,by omega,by norm_num,by ring⟩
  · obtain ⟨hn2,hprev⟩ := epsilon_one_predecessor hd hs hsd he hed hek hphase hn heps
    have hpreveq : tau d s e w rho theta (n-1) = (j+P)*T.u-Q*T.v := by
      dsimp [tau] at hjEq ⊢
      rw [hprev]
      linear_combination hjEq - htheta
    have hprevmem := hfs (n-1) (by omega)
    rw [hpreveq] at hprevmem
    have hsub : (j+P)*T.u+(-Q)*T.v ∈ T.T := by
      convert hprevmem using 1; ring
    have hnQ := (T.subcritical_nonneg (P := j+P) (Q := -Q)
      (by omega) (by have := T.u_pos; omega) hsub).2
    omega

def layer (d s e n : ℤ) : ℤ := s+n*e-d*carry d s e n
def complementLayer (d e n : ℤ) : ℤ := -n*e+d*ceiling d e n

theorem layer_bounds {d s e n : ℤ} (hd : 0 < d) :
    0 ≤ layer d s e n ∧ layer d s e n < d := by
  have he : layer d s e n = (s+n*e)%d := by
    dsimp [layer,carry]
    have hh := Int.ediv_mul_add_emod (s+n*e) d
    linear_combination -hh
  rw [he]
  exact ⟨Int.emod_nonneg _ (ne_of_gt hd),Int.emod_lt_of_pos _ hd⟩

theorem complementLayer_bounds {d e n : ℤ} (hd : 0 < d) :
    0 ≤ complementLayer d e n ∧ complementLayer d e n < d := by
  have he := (Int.ediv_mul_add_emod (n*e) d).symm
  have hr := Int.emod_nonneg (n*e) (ne_of_gt hd)
  have hrd := Int.emod_lt_of_pos (n*e) hd
  dsimp [complementLayer]
  rw [ceiling_of_residue hd hr hrd he]
  split_ifs with h
  · constructor <;> nlinarith
  · have hr1 : 1 ≤ (n*e)%d := by omega
    constructor <;> nlinarith

theorem stable_coordinate_identity {d s e n w rho theta r m : ℤ}
    (hr : r=s*w+d*rho) (hm : m=e*w+d*theta) :
    r+n*m = layer d s e n*w+d*tau d s e w rho theta n := by
  dsimp [layer,tau]
  linear_combination hr+n*hm

theorem complement_coordinate_identity {d e n w B v theta m : ℤ}
    (hm : m=e*w+d*theta) :
    B*(d*v)-n*m = complementLayer d e n*w+d*complement d e w B v theta n := by
  dsimp [complementLayer,complement]
  linear_combination -n*hm

end P21.Symmetric.BranchII




