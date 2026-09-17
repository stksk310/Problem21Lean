import P21.Nonsymmetric.ColorCap.ActualMinimum

namespace P21.Nonsymmetric.ColorCap

abbrev Point := Fin 3 → ℤ

def weight (n u : Point) : ℤ := ∑ i, u i * n i

def InBox (upper u : Point) : Prop := ∀ i, 1 ≤ u i ∧ u i ≤ upper i - 1

def fire (C : Fin 3 → Point) (i : Fin 3) (u : Point) : Point := fun j => u j - C i j

/-- Every edge is an actual positive in-box state; the count records its length. -/
inductive BoxPath (upper : Point) (C : Fin 3 → Point) : ℕ → Point → Point → Prop
  | nil {u} : InBox upper u → BoxPath upper C 0 u u
  | snoc {t u v} : BoxPath upper C t u v → (i : Fin 3) →
      InBox upper (fire C i v) → BoxPath upper C (t+1) u (fire C i v)

theorem BoxPath.endpoint {upper : Point} {C : Fin 3 → Point} {t u v}
    (h : BoxPath upper C t u v) : InBox upper v := by
  cases h with
  | nil hb => exact hb
  | snoc _ _ hb => exact hb

theorem fire_weight (n : Point) (C : Fin 3 → Point) (i : Fin 3) (u : Point) :
    weight n (fire C i u) = weight n u - weight n (C i) := by
  simp [weight, fire, sub_mul, Finset.sum_sub_distrib]

/-- All firings lower the same semigroup weight by exactly m. -/
theorem BoxPath.weight_eq {upper n : Point} {C : Fin 3 → Point} {m : ℤ}
    (hrows : ∀ i, weight n (C i) = m) {t u v}
    (h : BoxPath upper C t u v) : weight n v = weight n u - (t : ℤ) * m := by
  induction h with
  | nil _ => simp
  | @snoc t u v h i hb ih =>
    rw [fire_weight, hrows, ih]
    push_cast
    ring

/-- SAME-F: every path endpoint retains the original socle element and semigroup. -/
theorem BoxPath.same_element {g : Generators} {upper p : Point}
    {C : Fin 3 → Point} {f : ℤ}
    (hrows : ∀ i, weight g.n (C i) = g.m)
    (hf : f = g.m + ∑ i, (p i - 1) * g.n i) {t u}
    (h : BoxPath upper C t p u) :
    f = ((t : ℤ) + 1) * g.m + ∑ i, (u i - 1) * g.n i := by
  have hw := h.weight_eq hrows
  simp only [weight, sub_mul, one_mul, Finset.sum_sub_distrib] at hw hf ⊢
  linear_combination hf - hw

/-- The usual finite-path endpoint exists by the strictly decreasing nonnegative weight. -/
theorem maximal_box_path (upper p n : Point) (C : Fin 3 → Point) (m : ℤ)
    (hm : 0 < m) (hn : ∀ i, 0 ≤ n i) (hp : InBox upper p)
    (hrows : ∀ i, weight n (C i) = m) :
    ∃ t u, BoxPath upper C t p u ∧ ∀ i, ¬ InBox upper (fire C i u) := by
  classical
  have nonneg (u : Point) (hu : InBox upper u) : 0 ≤ weight n u := by
    exact Finset.sum_nonneg fun i _ => mul_nonneg (by have := (hu i).1; omega) (hn i)
  have hex : ∃ w : ℕ, ∃ t u, BoxPath upper C t p u ∧ (weight n u).toNat = w :=
    ⟨(weight n p).toNat,0,p,BoxPath.nil hp,rfl⟩
  obtain ⟨t,u,hpath,hw⟩ := Nat.find_spec hex
  refine ⟨t,u,hpath,?_⟩
  intro i hi
  have hnext := BoxPath.snoc hpath i hi
  have hmin := Nat.find_min' hex ⟨t+1,fire C i u,hnext,rfl⟩
  have hu0 := nonneg u hpath.endpoint
  have hv0 := nonneg (fire C i u) hi
  have he := fire_weight n C i u
  rw [hrows] at he
  have hcast1 := Int.toNat_of_nonneg hu0
  have hcast2 := Int.toNat_of_nonneg hv0
  omega

/-- A positive exit from a path is enough for the actual three-arm contradiction. -/
theorem path_exit_contradiction (g : Generators) (f : ℤ) (upper p depth : Point)
    (C : Fin 3 → Point) (hrows : ∀ i, weight g.n (C i) = g.m)
    (hf : f = g.m + ∑ j, (p j - 1) * g.n j)
    (hgaps : ∀ i, f - depth i * g.n i ∉ g.Gamma)
    (hbound : ∀ i, depth i ≤ upper i - 1)
    {t u} (hpath : BoxPath upper C t p u) (i : Fin 3)
    (hpositive : ∀ j, 1 ≤ fire C i u j) (hexit : ¬ InBox upper (fire C i u)) : False := by
  have hw := hpath.weight_eq hrows
  have hfire := fire_weight g.n C i u
  rw [hrows] at hfire
  have he : f = ((t : ℤ) + 2) * g.m + ∑ j, (fire C i u j - 1) * g.n j := by
    simp only [weight, sub_mul, one_mul, Finset.sum_sub_distrib] at hw hfire hf ⊢
    linear_combination hf - hw - hfire
  apply same_element_positive_exit g f ((t : ℤ) + 2) (fire C i u) depth upper
    (by positivity) hpositive he hgaps hbound
  by_contra hn
  push Not at hn
  apply hexit
  intro j
  exact ⟨hpositive j, by have := hn j; omega⟩

end P21.Nonsymmetric.ColorCap

