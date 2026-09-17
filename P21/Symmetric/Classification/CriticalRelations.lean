import P21.Basic

namespace P21.Symmetric.Classification

/-- The first positive multiple representable without its own generator. -/
structure CriticalRelation (g : Generators) (i : Fin 3) where
  coeff : ℕ
  coeff_pos : 0 < coeff
  otherCoeff : Fin 3 → ℕ
  zero_self : otherCoeff i = 0
  equality : (coeff : ℤ) * g.n i = value g.n otherCoeff
  minimal : ∀ c : ℕ, 0 < c → ∀ a : Fin 3 → ℕ,
    a i = 0 → (c : ℤ) * g.n i = value g.n a → coeff ≤ c

/-- Positivity alone supplies a nonnegative off-direction relation. -/
theorem criticalRelation_exists (g : Generators) (hpos : ∀ i, 0 < g.n i)
    (i : Fin 3) : Nonempty (CriticalRelation g i) := by
  classical
  let P : ℕ → Prop := fun c => 0 < c ∧ ∃ a : Fin 3 → ℕ,
    a i = 0 ∧ (c : ℤ) * g.n i = value g.n a
  have hex : ∃ c, P c := by
    obtain ⟨j, hj⟩ : ∃ j : Fin 3, j ≠ i := by
      fin_cases i
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
    refine ⟨(g.n j).natAbs, ?_, (fun k => if k = j then (g.n i).natAbs else 0), ?_, ?_⟩
    · exact Int.natAbs_pos.mpr (ne_of_gt (hpos j))
    · simp [Ne.symm hj]
    · simp [value, abs_of_pos (hpos i), abs_of_pos (hpos j), mul_comm]
  obtain ⟨hpositive, a, ha, he⟩ := Nat.find_spec hex
  refine ⟨⟨Nat.find hex, hpositive, a, ha, he, ?_⟩⟩
  intro c hc b hb heq
  exact Nat.find_min' hex ⟨hc, b, hb, heq⟩

namespace CriticalRelation

variable {g : Generators} {i : Fin 3}

theorem ge_two (r : CriticalRelation g i) (hmin : g.TailMinimal) : 2 ≤ r.coeff := by
  have hn : r.coeff ≠ 1 := by
    intro he
    exact hmin i r.otherCoeff r.zero_self (by simpa [he] using r.equality.symm)
  have := r.coeff_pos
  omega

theorem coeff_unique (r s : CriticalRelation g i) : r.coeff = s.coeff := by
  exact Nat.le_antisymm
    (r.minimal s.coeff s.coeff_pos s.otherCoeff s.zero_self s.equality)
    (s.minimal r.coeff r.coeff_pos r.otherCoeff r.zero_self r.equality)

theorem not_offDirection (r : CriticalRelation g i) {c : ℕ}
    (hc : 0 < c) (hlt : c < r.coeff) : ¬ g.OffDirection i ((c : ℤ) * g.n i) := by
  rintro ⟨a, ha⟩
  exact (Nat.not_le_of_gt hlt) (r.minimal c hc a.coeff ha a.equation.symm)

/-- Each smaller positive pure multiple has no other factorization. -/
theorem below_unique (r : CriticalRelation g i) (hpos : ∀ j, 0 < g.n j)
    {c : ℕ} (hlt : c < r.coeff) (a : Fin 3 → ℕ)
    (he : value g.n a = (c : ℤ) * g.n i) : a i = c := by
  classical
  let b : Fin 3 → ℕ := fun j => if j = i then 0 else a j
  have hb : b i = 0 := by simp [b]
  have hv : value g.n a = (a i : ℤ) * g.n i + value g.n b := by
    have hh : a = fun j => (if j = i then a i else 0) + b j := by
      funext j
      by_cases hj : j = i <;> simp [b, hj]
    conv_lhs => rw [hh]
    simp [value, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  have hnonneg : 0 ≤ value g.n b :=
    Finset.sum_nonneg fun j _ => mul_nonneg (Int.natCast_nonneg _) (hpos j).le
  have hle : a i ≤ c := by
    have : (a i : ℤ) * g.n i ≤ (c : ℤ) * g.n i := by omega
    exact_mod_cast (mul_le_mul_iff_left₀ (hpos i)).mp this
  by_contra hn
  have hlt' : a i < c := Nat.lt_of_le_of_ne hle hn
  have he' : ((c - a i : ℕ) : ℤ) * g.n i = value g.n b := by
    rw [Nat.cast_sub hle]
    nlinarith [hv, he]
  have hbound := r.minimal (c - a i) (Nat.sub_pos_of_lt hlt') b hb he'
  omega

end CriticalRelation
end P21.Symmetric.Classification

