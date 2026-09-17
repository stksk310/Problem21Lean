import P21.Nonsymmetric.Arms
import P21.Nonsymmetric.Herzog.PseudoFrobenius

namespace P21.Nonsymmetric

theorem support_trichotomy (S : Set (Fin 3)) (hne : S.Nonempty) :
    (∃ i, S = {i}) ∨ (∃ i, S = {j | j ≠ i}) ∨ S = Set.univ := by
  classical
  by_cases h0 : 0 ∈ S <;> by_cases h1 : 1 ∈ S <;> by_cases h2 : 2 ∈ S
  · right; right; ext i; fin_cases i <;> simp_all
  · right; left; refine ⟨2, ?_⟩; ext i; fin_cases i <;> simp_all
  · right; left; refine ⟨1, ?_⟩; ext i; fin_cases i <;> simp_all
  · left; refine ⟨0, ?_⟩; ext i; fin_cases i <;> simp_all
  · right; left; refine ⟨0, ?_⟩; ext i; fin_cases i <;> simp_all
  · left; refine ⟨1, ?_⟩; ext i; fin_cases i <;> simp_all
  · left; refine ⟨2, ?_⟩; ext i; fin_cases i <;> simp_all
  · obtain ⟨i, hi⟩ := hne; fin_cases i <;> contradiction

def IsArmA {g : Generators} (D : HerzogCriticalData g) (q : ℤ) (i : Fin 3) : Prop :=
  ∃ l : ℤ, 1 ≤ l ∧ l ≤ D.a i-1 ∧ q = D.fA-l*g.n i

def IsArmB {g : Generators} (D : HerzogCriticalData g) (q : ℤ) (i : Fin 3) : Prop :=
  ∃ l : ℤ, 1 ≤ l ∧ l ≤ D.b i-1 ∧ q = D.fB-l*g.n i

theorem actual_row_atlas {g : Generators} (s : g.Setting) {F q : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g) (hq : q ∈ s.semigroup.Q F) :
    (∃ i, IsSingleton g q i) ∨
    (∃ i, IsArmA D.toHerzogCriticalData q i ∨ IsArmB D.toHerzogCriticalData q i) ∨
    (q = D.fA ∨ q = D.fB) := by
  have hnonempty := (s.key_support_inclusion hF hc hq).1.mono
    (s.key_support_inclusion hF hc hq).2
  have hgap : q ∉ g.H := fun h => hq.1.1 (g.h_subset_gamma h)
  rcases support_trichotomy (g.SH q) hnonempty with ⟨i,hi⟩ | ⟨i,hi⟩ | hi
  · exact Or.inl ⟨i,hi⟩
  · right; left; refine ⟨i, ?_⟩
    exact six_arm_atlas (fun i => lt_trans s.m_pos (s.n_gt i))
      (s.tail_cofinite hF hc ⟨q,hq⟩) D i hgap
      (by change i ∉ g.SH q; rw [hi]; simp)
      (by intro j hj; change j ∈ g.SH q; rw [hi]; exact hj)
  · right; right
    have hp := tail_pf_of_generator_returns hgap (fun i => by
      change i ∈ g.SH q; rw [hi]; trivial)
    rw [D.pf_exact] at hp
    exact hp

/-- Equal-color rows on the same ray coincide; no depth uniqueness is assumed. -/
theorem pf_ray_unique (S : NumericalSemigroup) {n f q r a b : ℤ}
    (hn : n ∈ S.carrier) (hq : q ∈ S.PF) (hr : r ∈ S.PF)
    (heq : q = f-a*n) (her : r = f-b*n) : q = r := by
  by_contra hne
  rcases le_total a b with hab | hba
  · have hm := S.carrier.nsmul_mem hn (b-a).toNat
    have hd : q-r = (b-a)*n := by rw [heq,her]; ring
    apply pf_antichain S hr hq (Ne.symm hne)
    simpa [hd,nsmul_eq_mul,Int.toNat_of_nonneg (sub_nonneg.mpr hab)] using hm
  · have hm := S.carrier.nsmul_mem hn (a-b).toNat
    have hd : r-q = (a-b)*n := by rw [heq,her]; ring
    apply pf_antichain S hq hr hne
    simpa [hd,nsmul_eq_mul,Int.toNat_of_nonneg (sub_nonneg.mpr hba)] using hm

theorem same_A_arm_unique {g : Generators} {s : g.Setting} {F q r : ℤ}
    (D : HerzogCriticalData g) (hq : q ∈ s.semigroup.Q F) (hr : r ∈ s.semigroup.Q F)
    {i : Fin 3} (ha : IsArmA D q i) (hb : IsArmA D r i) : q = r := by
  obtain ⟨a,_,_,heq⟩ := ha
  obtain ⟨b,_,_,her⟩ := hb
  exact pf_ray_unique s.semigroup (g.n_mem i) hq.1 hr.1 heq her

theorem same_B_arm_unique {g : Generators} {s : g.Setting} {F q r : ℤ}
    (D : HerzogCriticalData g) (hq : q ∈ s.semigroup.Q F) (hr : r ∈ s.semigroup.Q F)
    {i : Fin 3} (ha : IsArmB D q i) (hb : IsArmB D r i) : q = r := by
  obtain ⟨a,_,_,heq⟩ := ha
  obtain ⟨b,_,_,her⟩ := hb
  exact pf_ray_unique s.semigroup (g.n_mem i) hq.1 hr.1 heq her

theorem corner_A_same_arm_excluded {g : Generators} (s : g.Setting) {F q : ℤ}
    (D : HerzogCriticalData g) (hf : D.fA ∈ s.semigroup.Q F)
    (hq : q ∈ s.semigroup.Q F) {i : Fin 3} (ha : IsArmA D q i) : False := by
  obtain ⟨l,hl,_,he⟩ := ha
  have hh := pf_ray_unique s.semigroup (g.n_mem i) hf.1 hq.1
    (show D.fA = D.fA-0*g.n i by ring) he
  have hn := lt_trans s.m_pos (s.n_gt i)
  nlinarith

theorem corner_B_same_arm_excluded {g : Generators} (s : g.Setting) {F q : ℤ}
    (D : HerzogCriticalData g) (hf : D.fB ∈ s.semigroup.Q F)
    (hq : q ∈ s.semigroup.Q F) {i : Fin 3} (ha : IsArmB D q i) : False := by
  obtain ⟨l,hl,_,he⟩ := ha
  have hh := pf_ray_unique s.semigroup (g.n_mem i) hf.1 hq.1
    (show D.fB = D.fB-0*g.n i by ring) he
  have hn := lt_trans s.m_pos (s.n_gt i)
  nlinarith

end P21.Nonsymmetric
