import P21.Symmetric.TwoGenerator
import P21.Symmetric.StableCore

namespace P21.Symmetric.TwoGeneratorData
variable (D : TwoGeneratorData)

def intersectionIdeal (eta : ℤ) : Set ℤ := {t | t ∈ D.T ∧ t + eta ∈ D.T}

theorem intersectionIdeal_add {eta t z : ℤ} (ht : t ∈ D.intersectionIdeal eta)
    (hz : z ∈ D.T) : t + z ∈ D.intersectionIdeal eta := by
  refine ⟨D.T.add_mem ht.1 hz, ?_⟩
  convert D.T.add_mem ht.2 hz using 1; ring

def firstThreshold (p : ℤ) : ℤ := max 0 (-p) * D.u
def secondThreshold (p q : ℤ) : ℤ := max 0 (-p-D.v) * D.u + (D.u-q)*D.v

theorem firstThreshold_mem (p q : ℤ) (hq : 0 ≤ q) :
    D.firstThreshold p ∈ D.intersectionIdeal (p*D.u+q*D.v) := by
  constructor
  · exact ⟨max 0 (-p),0,le_max_left _ _,le_rfl,by unfold firstThreshold; ring⟩
  · refine ⟨max 0 (-p)+p,q,?_,hq,?_⟩
    · have := le_max_right 0 (-p); omega
    · unfold firstThreshold; ring

theorem secondThreshold_mem (p q : ℤ) (hqu : q < D.u) :
    D.secondThreshold p q ∈ D.intersectionIdeal (p*D.u+q*D.v) := by
  constructor
  · exact ⟨max 0 (-p-D.v),D.u-q,le_max_left _ _,by omega,rfl⟩
  · refine ⟨max 0 (-p-D.v)+p+D.v,0,?_,le_rfl,?_⟩
    · have := le_max_right 0 (-p-D.v); omega
    · unfold secondThreshold; ring

/-- The two threshold generators from the publication generate the entire ideal. -/
theorem intersectionIdeal_generators {p q t : ℤ} (hq : 0 ≤ q) (hqu : q < D.u) :
    t ∈ D.intersectionIdeal (p*D.u+q*D.v) ↔
      t-D.firstThreshold p ∈ D.T ∨ t-D.secondThreshold p q ∈ D.T := by
  constructor
  · rintro ⟨ht,hte⟩
    obtain ⟨a,b,hb,hbu,rfl⟩ := D.normal_form_exists t
    have ha := (D.normal_form_mem_iff hb hbu).mp ht
    by_cases hcarry : b+q < D.u
    · left
      have he : a*D.u+b*D.v+(p*D.u+q*D.v) = (a+p)*D.u+(b+q)*D.v := by ring
      rw [he, D.normal_form_mem_iff (by omega) hcarry] at hte
      refine ⟨a-max 0 (-p),b,?_,hb,?_⟩
      · have : max 0 (-p) ≤ a := max_le ha (by omega)
        omega
      · unfold firstThreshold; ring
    · right
      have hbq : 0 ≤ b+q-D.u := by omega
      have hbqu : b+q-D.u < D.u := by omega
      have he : a*D.u+b*D.v+(p*D.u+q*D.v) =
          (a+p+D.v)*D.u+(b+q-D.u)*D.v := by ring
      rw [he, D.normal_form_mem_iff hbq hbqu] at hte
      refine ⟨a-max 0 (-p-D.v),b+q-D.u,?_,hbq,?_⟩
      · have : max 0 (-p-D.v) ≤ a := max_le ha (by omega)
        omega
      · unfold secondThreshold; ring
  · intro ht
    rcases ht with ht | ht
    · have h := D.intersectionIdeal_add (D.firstThreshold_mem p q hq) ht
      simpa using h
    · have h := D.intersectionIdeal_add (D.secondThreshold_mem p q hqu) ht
      simpa using h

theorem minimal_mem_pair {p q t : ℤ} (hq : 0 ≤ q) (hqu : q < D.u)
    (ht : idealMin D.T (D.intersectionIdeal (p*D.u+q*D.v)) t) :
    t = D.firstThreshold p ∨ t = D.secondThreshold p q := by
  rcases (D.intersectionIdeal_generators hq hqu).mp ht.1 with h | h
  · exact Or.inl (ht.2 _ (D.firstThreshold_mem p q hq) h).symm
  · exact Or.inr (ht.2 _ (D.secondThreshold_mem p q hqu) h).symm

theorem minimal_finite (eta : ℤ) :
    {t | idealMin D.T (D.intersectionIdeal eta) t}.Finite := by
  obtain ⟨p,q,hq,hqu,rfl⟩ := D.normal_form_exists eta
  apply (Set.toFinite {D.firstThreshold p,D.secondThreshold p q}).subset
  intro t ht
  simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using D.minimal_mem_pair hq hqu ht

theorem minimal_ncard_le_two (eta : ℤ) :
    {t | idealMin D.T (D.intersectionIdeal eta) t}.ncard ≤ 2 := by
  obtain ⟨p,q,hq,hqu,rfl⟩ := D.normal_form_exists eta
  apply le_trans (Set.ncard_le_ncard (s := {t | idealMin D.T
      (D.intersectionIdeal (p*D.u+q*D.v)) t}) (t := {D.firstThreshold p,D.secondThreshold p q}) ?_)
    (by simpa using Set.ncard_insert_le (D.firstThreshold p) {D.secondThreshold p q})
  intro t ht
  simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using D.minimal_mem_pair hq hqu ht

theorem minima_incomparable {eta a b : ℤ}
    (ha : idealMin D.T (D.intersectionIdeal eta) a)
    (hb : idealMin D.T (D.intersectionIdeal eta) b) (hab : a ≠ b) :
    a-b ∉ D.T ∧ b-a ∉ D.T := by
  exact ⟨fun h => hab (ha.2 b hb.1 h).symm, fun h => hab (hb.2 a ha.1 h)⟩

theorem two_minima_forces_bounds {p q a b : ℤ} (hq : 0 ≤ q) (hqu : q < D.u)
    (ha : idealMin D.T (D.intersectionIdeal (p*D.u+q*D.v)) a)
    (hb : idealMin D.T (D.intersectionIdeal (p*D.u+q*D.v)) b) (hab : a ≠ b) :
    0 < q ∧ -D.v < p ∧ p < 0 := by
  have hfirst : idealMin D.T (D.intersectionIdeal (p*D.u+q*D.v)) (D.firstThreshold p) := by
    rcases D.minimal_mem_pair hq hqu ha with rfl | he
    · exact ha
    · rcases D.minimal_mem_pair hq hqu hb with rfl | he'
      · exact hb
      · exact False.elim (hab (he.trans he'.symm))
  have hsecond : idealMin D.T (D.intersectionIdeal (p*D.u+q*D.v)) (D.secondThreshold p q) := by
    rcases D.minimal_mem_pair hq hqu ha with he | rfl
    · rcases D.minimal_mem_pair hq hqu hb with he' | rfl
      · exact False.elim (hab (he.trans he'.symm))
      · exact hb
    · exact ha
  have hne : D.firstThreshold p ≠ D.secondThreshold p q := by
    intro he
    have ha' := D.minimal_mem_pair hq hqu ha
    have hb' := D.minimal_mem_pair hq hqu hb
    rw [he] at ha' hb'
    exact hab ((ha'.elim id id).trans (hb'.elim id id).symm)
  obtain ⟨h12,h21⟩ := D.minima_incomparable hfirst hsecond hne
  have hp : p < 0 := by
    by_contra hp
    have hz : max 0 (-p) = 0 := max_eq_left (by omega)
    apply h21
    simpa [firstThreshold,hz] using (D.secondThreshold_mem p q hqu).1
  have hpv : -D.v < p := by
    by_contra hpv
    have hM : max 0 (-p) = -p := max_eq_right (by omega)
    have hN : max 0 (-p-D.v) = -p-D.v := max_eq_right (by omega)
    apply h12
    refine ⟨0,q,le_rfl,hq,?_⟩
    simp only [firstThreshold,secondThreshold,hM,hN]
    ring
  have hq0 : 0 < q := by
    by_contra hq0
    have heq : q = 0 := by omega
    have hM : max 0 (-p) = -p := max_eq_right (by omega)
    have hN : max 0 (-p-D.v) = 0 := max_eq_left (by omega)
    apply h21
    refine ⟨D.v+p,0,by omega,le_rfl,?_⟩
    simp only [firstThreshold,secondThreshold,hM,hN,heq]
    ring
  exact ⟨hq0,hpv,hp⟩

/-- In the strict interior regime the two threshold generators are exactly
the two incomparable minima, with no extra uniqueness premise. -/
theorem minimal_pair_eq {p q : ℤ} (hq : 0 < q) (hqu : q < D.u)
    (hpv : -D.v < p) (hp : p < 0) :
    {t | idealMin D.T (D.intersectionIdeal (p*D.u+q*D.v)) t} =
      {-p*D.u,(D.u-q)*D.v} := by
  have hM : max 0 (-p) = -p := max_eq_right (by omega)
  have hN : max 0 (-p-D.v) = 0 := max_eq_left (by omega)
  have hf : D.firstThreshold p = -p*D.u := by simp [firstThreshold,hM]
  have hs : D.secondThreshold p q = (D.u-q)*D.v := by simp [secondThreshold,hN]
  have hgap1 : -p*D.u - (D.u-q)*D.v ∉ D.T := by
    intro ht
    have he : -p*D.u - (D.u-q)*D.v = (-p)*D.u+(q-D.u)*D.v := by ring
    rw [he] at ht
    have hh := D.subcritical_nonneg (by omega : -p < D.v) (by omega : q-D.u < D.u) ht
    omega
  have hgap2 : (D.u-q)*D.v - -p*D.u ∉ D.T := by
    intro ht
    have he : (D.u-q)*D.v - -p*D.u = p*D.u+(D.u-q)*D.v := by ring
    rw [he] at ht
    have hh := D.subcritical_nonneg (by have := D.v_pos; omega : p < D.v)
      (by omega : D.u-q < D.u) ht
    omega
  ext t
  constructor
  · intro ht
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,hf,hs] using D.minimal_mem_pair hq.le hqu ht
  · rintro (rfl | rfl)
    · refine ⟨hf ▸ D.firstThreshold_mem p q hq.le, ?_⟩
      intro b hb hd
      rcases (D.intersectionIdeal_generators hq.le hqu).mp hb with hb | hb
      · rw [hf] at hb
        have := D.nonneg hb
        have := D.nonneg hd
        omega
      · rw [hs] at hb
        apply False.elim
        apply hgap1
        convert D.T.add_mem hd hb using 1; ring
    · refine ⟨hs ▸ D.secondThreshold_mem p q hqu, ?_⟩
      intro b hb hd
      rcases (D.intersectionIdeal_generators hq.le hqu).mp hb with hb | hb
      · rw [hf] at hb
        apply False.elim
        apply hgap2
        convert D.T.add_mem hd hb using 1; ring
      · rw [hs] at hb
        have := D.nonneg hb
        have := D.nonneg hd
        omega

theorem two_minima_iff {p q : ℤ} (hq : 0 ≤ q) (hqu : q < D.u) :
    (∃ a b, idealMin D.T (D.intersectionIdeal (p*D.u+q*D.v)) a ∧
      idealMin D.T (D.intersectionIdeal (p*D.u+q*D.v)) b ∧ a ≠ b) ↔
        0 < q ∧ -D.v < p ∧ p < 0 := by
  constructor
  · rintro ⟨a,b,ha,hb,hab⟩
    exact D.two_minima_forces_bounds hq hqu ha hb hab
  · rintro ⟨hq0,hpv,hp⟩
    have he := D.minimal_pair_eq hq0 hqu hpv hp
    have ha : idealMin D.T (D.intersectionIdeal (p*D.u+q*D.v)) (-p*D.u) := by
      change -p*D.u ∈ {t | idealMin D.T (D.intersectionIdeal (p*D.u+q*D.v)) t}
      rw [he]; simp
    have hb : idealMin D.T (D.intersectionIdeal (p*D.u+q*D.v)) ((D.u-q)*D.v) := by
      change (D.u-q)*D.v ∈ {t | idealMin D.T (D.intersectionIdeal (p*D.u+q*D.v)) t}
      rw [he]; simp
    refine ⟨_,_,ha,hb,?_⟩
    intro hab
    have hd := D.normal_form_unique (a := -p) (b := 0) (c := 0) (d := D.u-q)
      (by omega) D.u_pos (by omega) (by omega) (by simpa using hab)
    omega

end P21.Symmetric.TwoGeneratorData
