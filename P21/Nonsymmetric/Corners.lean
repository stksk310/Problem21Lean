import P21.Nonsymmetric.RowAtlas
import P21.Nonsymmetric.Singletons

namespace P21.Nonsymmetric

theorem corner_A_singleton_excluded {g : Generators} (s : g.Setting) {F q : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (hcorner : D.fA ∈ s.semigroup.Q F)
    (hq : q ∈ s.semigroup.Q F) (i : Fin 3) (hs : IsSingleton g q i) : False := by
  obtain ⟨k,_,he⟩ := singleton_pure_complement s hF hc hq hs
  have hk := singleton_critical_bound s hF hc hq hs (D.critical i) he
  rw [D.coeff_rho] at hk
  have hm := pair_nonnegative_mem (g:=g) i (next i)
    (show 0 ≤ (D.rho i : ℤ)-1-k by omega)
    (show 0 ≤ (D.a (next i) : ℤ)-1 by have := D.a_pos (next i); omega)
  have hcomp := s.apery_in_tail (s.semigroup.complement_of_q_mem_apery hF hc hcorner)
  have hsum := g.H.add_mem hm hcomp
  have form := D.fA_cyclic i
  have hret : q + g.n (prev i) ∈ g.H := by
    convert hsum using 1
    dsimp [complement,W] at he
    linear_combination form - he
  have hbad : prev i ∈ g.SH q := hret
  rw [hs] at hbad
  exact (cyclic_distinct i).2.1 hbad.symm

theorem corner_B_singleton_excluded {g : Generators} (s : g.Setting) {F q : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (hcorner : D.fB ∈ s.semigroup.Q F)
    (hq : q ∈ s.semigroup.Q F) (i : Fin 3) (hs : IsSingleton g q i) : False := by
  obtain ⟨k,_,he⟩ := singleton_pure_complement s hF hc hq hs
  have hk := singleton_critical_bound s hF hc hq hs (D.critical i) he
  rw [D.coeff_rho] at hk
  have hm := pair_nonnegative_mem (g:=g) i (prev i)
    (show 0 ≤ (D.rho i : ℤ)-1-k by omega)
    (show 0 ≤ (D.b (prev i) : ℤ)-1 by have := D.b_pos (prev i); omega)
  have hcomp := s.apery_in_tail (s.semigroup.complement_of_q_mem_apery hF hc hcorner)
  have hsum := g.H.add_mem hm hcomp
  have form := D.fB_cyclic i
  have hret : q + g.n (next i) ∈ g.H := by
    convert hsum using 1
    dsimp [complement,W] at he
    linear_combination form - he
  have hbad : next i ∈ g.SH q := hret
  rw [hs] at hbad
  exact (cyclic_distinct i).1 hbad.symm

theorem frobenius_le_higher_corner {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hQ : (s.semigroup.Q F).Nonempty) (D : NonsymmetricHerzogData g) :
    F ≤ max D.fA D.fB := by
  let H := s.tailSemigroup hF hc hQ
  obtain ⟨f,hf⟩ := H.exists_frobenius
  have hgap : F ∉ H.carrier := fun hh => hF.1 (g.h_subset_gamma hh)
  obtain ⟨p,hp,hd⟩ := H.gap_below_pf hf hgap
  have hle : F ≤ p := by have := H.nonneg _ hd; omega
  have hp' : p ∈ TailPF g := hp
  rw [D.pf_exact] at hp'
  rcases hp' with ha | hb
  · exact hle.trans (ha ▸ le_max_left _ _)
  · exact hle.trans (hb ▸ le_max_right _ _)

theorem higher_corner_excluded {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g) : max D.fA D.fB ∉ s.semigroup.Q F := by
  intro hq
  have hlo := frobenius_le_higher_corner s hF hc ⟨_,hq⟩ D
  have hhi := s.semigroup.q_lt_frobenius hF hq
  omega

theorem both_corners_excluded {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g) (ha : D.fA ∈ s.semigroup.Q F)
    (hb : D.fB ∈ s.semigroup.Q F) : False := by
  apply higher_corner_excluded s hF hc D
  rcases le_total D.fA D.fB with h | h
  · simpa [max_eq_right h] using hb
  · simpa [max_eq_left h] using ha

end P21.Nonsymmetric
