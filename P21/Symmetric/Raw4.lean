import P21.Symmetric.TwoGeneratorIdeal
import P21.Symmetric.GlueNormalForm
import P21.Symmetric.TypeBridge

namespace P21.Symmetric

/-- Exact RAW4 coefficients and actual minimal/Apéry witnesses, derived below
from the assumption that the type is at least five. -/
structure Raw4Data {g : Generators} (G : SymmetricGlueData g) (setting : g.Setting) (F : ℤ) where
  s : ℤ
  rho : ℤ
  A : ℤ
  B : ℤ
  C : ℤ
  D : ℤ
  Ap : ℤ
  Bp : ℤ
  Cp : ℤ
  Dp : ℤ
  hspos : 0 < s
  hslt : s < G.d
  A_pos : 0 < A
  B_pos : 0 < B
  C_pos : 0 < C
  D_pos : 0 < D
  Ap_pos : 0 < Ap
  Bp_pos : 0 < Bp
  Cp_pos : 0 < Cp
  Dp_pos : 0 < Dp
  sumAD : A+D = G.two.v
  sumBC : B+C = G.two.u
  sumApDp : Ap+Dp = G.two.v
  sumBpCp : Bp+Cp = G.two.u
  rdef : G.frobenius-F-g.m = s*G.w+G.d*rho
  rho_eq : rho = -A*G.two.u+C*G.two.v
  rhop_eq : rho+G.w = -Ap*G.two.u+Cp*G.two.v
  rows : ∀ c ∈ ({A*(G.d*G.two.u),B*(G.d*G.two.v),
      (G.d-s)*G.w+Ap*(G.d*G.two.u),
      (G.d-s)*G.w+Bp*(G.d*G.two.v)} : Set ℤ),
    idealMin g.H (tailIntersection g (G.frobenius-F-g.m)) c ∧
      c ∈ setting.semigroup.Apery g.m

namespace SymmetricGlueData
variable {g : Generators} (D : SymmetricGlueData g)

theorem intersection_low {s rho j t : ℤ} (hj : 0 ≤ j) (hjd : j < D.d)
    (hsj : 0 ≤ j+s) (hsjd : j+s < D.d) :
    j*D.w+D.d*t ∈ tailIntersection g (s*D.w+D.d*rho) ↔
      t ∈ D.two.intersectionIdeal rho := by
  change (_ ∈ g.H ∧ _ ∈ g.H) ↔ (_ ∈ D.two.T ∧ _ ∈ D.two.T)
  have he : j*D.w+D.d*t+(s*D.w+D.d*rho) = (j+s)*D.w+D.d*(t+rho) := by ring
  rw [he,D.normal_form_mem_iff hj hjd,D.normal_form_mem_iff hsj hsjd]

theorem intersection_high {s rho j t : ℤ} (hj : 0 ≤ j) (hjd : j < D.d)
    (hsj : 0 ≤ j+s-D.d) (hsjd : j+s-D.d < D.d) :
    j*D.w+D.d*t ∈ tailIntersection g (s*D.w+D.d*rho) ↔
      t ∈ D.two.intersectionIdeal (rho+D.w) := by
  change (_ ∈ g.H ∧ _ ∈ g.H) ↔ (_ ∈ D.two.T ∧ _ ∈ D.two.T)
  have he : j*D.w+D.d*t+(s*D.w+D.d*rho) =
      (j+s-D.d)*D.w+D.d*(t+(rho+D.w)) := by ring
  rw [he,D.normal_form_mem_iff hj hjd,D.normal_form_mem_iff hsj hsjd]

/-- A raw minimum can only occur at one of the two carry boundaries. -/
theorem raw_min_layers (setting : g.Setting) {s rho j t : ℤ}
    (hs : 0 ≤ s) (hsd : s < D.d) (hj : 0 ≤ j) (hjd : j < D.d)
    (hc : idealMin g.H (tailIntersection g (s*D.w+D.d*rho)) (j*D.w+D.d*t)) :
    (j = 0 ∧ idealMin D.two.T (D.two.intersectionIdeal rho) t) ∨
    (0 < s ∧ j = D.d-s ∧ idealMin D.two.T (D.two.intersectionIdeal (rho+D.w)) t) := by
  by_cases hcarry : j+s < D.d
  · have ht := (D.intersection_low hj hjd (by omega) hcarry).mp hc.1
    have hj0 : j = 0 := by
      by_contra hn
      have hb := (D.intersection_low (s := s) (t := t) (rho := rho) (j := j-1)
        (by omega) (by omega) (by omega) (by omega)).mpr ht
      have he := hc.2 ((j-1)*D.w+D.d*t) hb (by
        convert D.w_mem_tail using 1; ring)
      have := D.w_pos setting
      nlinarith
    left
    refine ⟨hj0,ht,?_⟩
    intro b hb hd
    have hb' := (D.intersection_low (s := s) (rho := rho) (t := b) hj hjd (by omega) hcarry).mpr hb
    have he := hc.2 (j*D.w+D.d*b) hb' (by
      convert D.d_mul_mem_tail hd using 1; ring)
    nlinarith [D.d_pos]
  · have ht := (D.intersection_high (s := s) (rho := rho) hj hjd (by omega) (by omega)).mp hc.1
    have hj0 : j = D.d-s := by
      by_contra hn
      have hb := (D.intersection_high (s := s) (t := t) (rho := rho) (j := j-1)
        (by omega) (by omega) (by omega) (by omega)).mpr ht
      have he := hc.2 ((j-1)*D.w+D.d*t) hb (by
        convert D.w_mem_tail using 1; ring)
      have := D.w_pos setting
      nlinarith
    right
    refine ⟨by omega,hj0,ht,?_⟩
    intro b hb hd
    have hb' := (D.intersection_high (s := s) (rho := rho) (t := b) hj hjd (by omega) (by omega)).mpr hb
    have he := hc.2 (j*D.w+D.d*b) hb' (by
      convert D.d_mul_mem_tail hd using 1; ring)
    nlinarith [D.d_pos]

def rawCandidates (s p q pp qq : ℤ) : Set ℤ :=
  {D.d*D.two.firstThreshold p, D.d*D.two.secondThreshold p q,
   (D.d-s)*D.w+D.d*D.two.firstThreshold pp,
   (D.d-s)*D.w+D.d*D.two.secondThreshold pp qq}

theorem raw_min_subset (setting : g.Setting) {s rho p q pp qq : ℤ}
    (hs : 0 ≤ s) (hsd : s < D.d) (hq : 0 ≤ q) (hqu : q < D.two.u)
    (hqq : 0 ≤ qq) (hqqu : qq < D.two.u)
    (he : rho = p*D.two.u+q*D.two.v) (he' : rho+D.w = pp*D.two.u+qq*D.two.v) :
    {c | idealMin g.H (tailIntersection g (s*D.w+D.d*rho)) c} ⊆
      D.rawCandidates s p q pp qq := by
  intro c hc
  obtain ⟨j,t,hj,hjd,rfl⟩ := D.normal_form_exists c
  rcases D.raw_min_layers setting hs hsd hj hjd hc with ⟨rfl,ht⟩ | ⟨_,rfl,ht⟩
  · rw [he] at ht
    rcases D.two.minimal_mem_pair hq hqu ht with rfl | rfl <;>
      simp [rawCandidates]
  · rw [he'] at ht
    rcases D.two.minimal_mem_pair hqq hqqu ht with rfl | rfl <;>
      simp [rawCandidates]

theorem rawCandidates_ncard_le (s p q pp qq : ℤ) :
    (D.rawCandidates s p q pp qq).ncard ≤ 4 := by
  unfold rawCandidates
  have h1 := Set.ncard_insert_le (D.d*D.two.firstThreshold p)
    {D.d*D.two.secondThreshold p q,(D.d-s)*D.w+D.d*D.two.firstThreshold pp,
      (D.d-s)*D.w+D.d*D.two.secondThreshold pp qq}
  have h2 := Set.ncard_insert_le (D.d*D.two.secondThreshold p q)
    {(D.d-s)*D.w+D.d*D.two.firstThreshold pp,(D.d-s)*D.w+D.d*D.two.secondThreshold pp qq}
  have h3 := Set.ncard_insert_le ((D.d-s)*D.w+D.d*D.two.firstThreshold pp)
    {(D.d-s)*D.w+D.d*D.two.secondThreshold pp qq}
  simp only [Set.ncard_singleton] at h3
  omega

include D in
theorem raw_min_ncard_le_four (setting : g.Setting) (r : ℤ) :
    {c | idealMin g.H (tailIntersection g r) c}.ncard ≤ 4 := by
  obtain ⟨s,rho,hs,hsd,rfl⟩ := D.normal_form_exists r
  obtain ⟨p,q,hq,hqu,he⟩ := D.two.normal_form_exists rho
  obtain ⟨pp,qq,hqq,hqqu,he'⟩ := D.two.normal_form_exists (rho+D.w)
  exact (Set.ncard_le_ncard (D.raw_min_subset setting hs hsd hq hqu hqq hqqu he he')
    (by unfold rawCandidates; exact Set.toFinite _)).trans (D.rawCandidates_ncard_le _ _ _ _ _)

theorem raw_min_zero_subset (setting : g.Setting) {rho p q : ℤ}
    (hq : 0 ≤ q) (hqu : q < D.two.u) (he : rho = p*D.two.u+q*D.two.v) :
    {c | idealMin g.H (tailIntersection g (D.d*rho)) c} ⊆
      {D.d*D.two.firstThreshold p,D.d*D.two.secondThreshold p q} := by
  intro c hc
  obtain ⟨j,t,hj,hjd,rfl⟩ := D.normal_form_exists c
  have hc' : idealMin g.H (tailIntersection g (0*D.w+D.d*rho)) (j*D.w+D.d*t) := by
    simpa using hc
  rcases D.raw_min_layers setting (by omega : 0 ≤ (0:ℤ)) D.d_pos hj hjd hc'
    with ⟨rfl,ht⟩ | ⟨hs,_,_⟩
  · rw [he] at ht
    rcases D.two.minimal_mem_pair hq hqu ht with rfl | rfl <;> simp
  · omega

theorem raw_min_zero_ncard_le_two (setting : g.Setting) (rho : ℤ) :
    {c | idealMin g.H (tailIntersection g (D.d*rho)) c}.ncard ≤ 2 := by
  obtain ⟨p,q,hq,hqu,he⟩ := D.two.normal_form_exists rho
  apply (Set.ncard_le_ncard (D.raw_min_zero_subset setting hq hqu he)).trans
  simpa using Set.ncard_insert_le (D.d*D.two.firstThreshold p) {D.d*D.two.secondThreshold p q}

theorem surviving_eq_candidates (setting : g.Setting) {F f s rho p q pp qq : ℤ}
    (hF : setting.semigroup.IsFrobenius F) (hcan : setting.semigroup.Canonical F g.m)
    (hsym : SymmetricAt g.H f) (htype : 5 ≤ setting.semigroup.type)
    (hs : 0 ≤ s) (hsd : s < D.d) (hr : f-F-g.m = s*D.w+D.d*rho)
    (hq : 0 ≤ q) (hqu : q < D.two.u) (hqq : 0 ≤ qq) (hqqu : qq < D.two.u)
    (he : rho = p*D.two.u+q*D.two.v) (he' : rho+D.w = pp*D.two.u+qq*D.two.v) :
    {c | idealMin g.H (tailIntersection g (f-F-g.m)) c ∧ c ∈ setting.semigroup.Apery g.m} =
      D.rawCandidates s p q pp qq := by
  have ht := type_bridge setting hF hcan hsym
  have hsub : {c | idealMin g.H (tailIntersection g (f-F-g.m)) c ∧
      c ∈ setting.semigroup.Apery g.m} ⊆ D.rawCandidates s p q pp qq := by
    intro c hc
    apply D.raw_min_subset setting hs hsd hq hqu hqq hqqu he he'
    simpa [← hr] using hc.1
  apply Set.eq_of_subset_of_ncard_le hsub ?_ (by unfold rawCandidates; exact Set.toFinite _)
  have hle := D.rawCandidates_ncard_le s p q pp qq
  omega

theorem four_set_pair_distinct {a b c d : ℤ} (h : 4 ≤ ({a,b,c,d} : Set ℤ).ncard) :
    a ≠ b ∧ c ≠ d := by
  constructor
  · intro he
    rw [he] at h
    simp only [Set.insert_idem] at h
    have h1 := Set.ncard_insert_le b {c,d}
    have h2 := Set.ncard_insert_le c {d}
    simp only [Set.ncard_singleton] at h2
    omega
  · intro he
    rw [he] at h
    have hset : ({a,b,d,d} : Set ℤ) = {a,b,d} := by ext; simp
    rw [hset] at h
    have h1 := Set.ncard_insert_le a {b,d}
    have h2 := Set.ncard_insert_le b {d}
    simp only [Set.ncard_singleton] at h2
    omega

/-- All four rows are extracted from the exact bridge and the complete raw
classification. No raw-row existence or survival is assumed. -/
theorem exists_raw4 (setting : g.Setting) {F : ℤ}
    (hF : setting.semigroup.IsFrobenius F) (hcan : setting.semigroup.Canonical F g.m)
    (htype : 5 ≤ setting.semigroup.type) : Nonempty (Raw4Data D setting F) := by
  obtain ⟨s,rho,hs,hsd,hr⟩ := D.normal_form_exists (D.frobenius-F-g.m)
  obtain ⟨p,q,hq,hqu,he⟩ := D.two.normal_form_exists rho
  obtain ⟨pp,qq,hqq,hqqu,he'⟩ := D.two.normal_form_exists (rho+D.w)
  have hsym := D.symmetry
  have ht := type_bridge setting hF hcan hsym
  have heq := D.surviving_eq_candidates setting hF hcan hsym htype hs hsd hr hq hqu hqq hqqu he he'
  have hcard : 4 ≤ (D.rawCandidates s p q pp qq).ncard := by
    rw [heq] at ht
    omega
  have hspos : 0 < s := by
    by_contra hn
    have hs0 : s = 0 := by omega
    have hr0 : D.frobenius-F-g.m = D.d*rho := by simpa [hs0] using hr
    have hsub : {c | idealMin g.H (tailIntersection g (D.frobenius-F-g.m)) c ∧
        c ∈ setting.semigroup.Apery g.m} ⊆
          {D.d*D.two.firstThreshold p,D.d*D.two.secondThreshold p q} := by
      intro c hc
      apply D.raw_min_zero_subset setting hq hqu he
      simpa [hr0] using hc.1
    have hle := Set.ncard_le_ncard hsub
    have htwo := Set.ncard_insert_le (D.d*D.two.firstThreshold p) {D.d*D.two.secondThreshold p q}
    simp only [Set.ncard_singleton] at htwo
    omega
  have hrows : ∀ c ∈ D.rawCandidates s p q pp qq,
      idealMin g.H (tailIntersection g (D.frobenius-F-g.m)) c ∧
        c ∈ setting.semigroup.Apery g.m := by
    intro c hc
    rw [← heq] at hc
    exact hc
  have hlow : ∀ t ∈ ({D.two.firstThreshold p,D.two.secondThreshold p q} : Set ℤ),
      idealMin D.two.T (D.two.intersectionIdeal rho) t := by
    intro t ht
    have hc : idealMin g.H (tailIntersection g (s*D.w+D.d*rho)) (0*D.w+D.d*t) := by
      have hh := (hrows (D.d*t) (by rcases ht with rfl | rfl <;> simp [rawCandidates])).1
      simpa [← hr] using hh
    rcases D.raw_min_layers setting hs hsd (by omega : 0 ≤ (0:ℤ)) D.d_pos hc with h | h
    · exact h.2
    · omega
  have hhigh : ∀ t ∈ ({D.two.firstThreshold pp,D.two.secondThreshold pp qq} : Set ℤ),
      idealMin D.two.T (D.two.intersectionIdeal (rho+D.w)) t := by
    intro t ht
    have hc : idealMin g.H (tailIntersection g (s*D.w+D.d*rho)) ((D.d-s)*D.w+D.d*t) := by
      have hh := (hrows ((D.d-s)*D.w+D.d*t)
        (by rcases ht with rfl | rfl <;> simp [rawCandidates])).1
      simpa [← hr] using hh
    rcases D.raw_min_layers setting hs hsd (by omega : 0 ≤ D.d-s) (by omega) hc with h | h
    · omega
    · exact h.2.2
  obtain ⟨hne,hne'⟩ := four_set_pair_distinct hcard
  have hn : D.two.firstThreshold p ≠ D.two.secondThreshold p q := by
    intro h
    apply hne
    rw [h]
  have hn' : D.two.firstThreshold pp ≠ D.two.secondThreshold pp qq := by
    intro h
    apply hne'
    rw [h]
  have hleft := hlow (D.two.firstThreshold p) (by simp)
  have hright := hlow (D.two.secondThreshold p q) (by simp)
  rw [he] at hleft hright
  obtain ⟨hqpos,hpv,hp⟩ := D.two.two_minima_forces_bounds hq hqu hleft hright hn
  have hleft' := hhigh (D.two.firstThreshold pp) (by simp)
  have hright' := hhigh (D.two.secondThreshold pp qq) (by simp)
  rw [he'] at hleft' hright'
  obtain ⟨hqqpos,hppv,hpp⟩ := D.two.two_minima_forces_bounds hqq hqqu hleft' hright' hn'
  refine ⟨{
    s := s, rho := rho, A := -p, B := D.two.u-q, C := q, D := D.two.v+p
    Ap := -pp, Bp := D.two.u-qq, Cp := qq, Dp := D.two.v+pp
    hspos := hspos, hslt := hsd
    A_pos := by omega, B_pos := by omega, C_pos := hqpos, D_pos := by omega
    Ap_pos := by omega, Bp_pos := by omega, Cp_pos := hqqpos, Dp_pos := by omega
    sumAD := by ring, sumBC := by ring, sumApDp := by ring, sumBpCp := by ring
    rdef := hr, rho_eq := by simpa using he, rhop_eq := by simpa using he'
    rows := ?_ }⟩
  intro c hc
  apply hrows c
  have hM : max 0 (-p) = -p := max_eq_right (by omega)
  have hN : max 0 (-p-D.two.v) = 0 := max_eq_left (by omega)
  have hMp : max 0 (-pp) = -pp := max_eq_right (by omega)
  have hNp : max 0 (-pp-D.two.v) = 0 := max_eq_left (by omega)
  simpa only [rawCandidates,TwoGeneratorData.firstThreshold,TwoGeneratorData.secondThreshold,
    hM,hN,hMp,hNp,zero_mul,zero_add,mul_left_comm D.d] using hc
end SymmetricGlueData
end P21.Symmetric
