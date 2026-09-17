import P21.Symmetric.Classification.TailNumericalSemigroup

namespace P21.Symmetric.Classification

variable {g : Generators}

theorem tail_apery_lower {i : Fin 3} {a b : ℤ}
    (ha : a ∈ g.H) (hb : TailApery g i b) (hd : b - a ∈ g.H) :
    TailApery g i a := by
  refine ⟨ha, ?_⟩
  intro h
  apply hb.2
  convert g.H.add_mem h hd using 1; ring

theorem tail_apery_le_of_emod (s : g.Setting) {i : Fin 3} {a b : ℤ}
    (ha : TailApery g i a) (hb : b ∈ g.H)
    (he : a % g.n i = b % g.n i) : a ≤ b := by
  by_contra hn
  have hpos := tail_generator_pos s i
  have hdiv : g.n i ∣ a - b := by
    apply Int.dvd_of_emod_eq_zero
    rw [Int.sub_emod, he]
    simp
  obtain ⟨k, hk⟩ := hdiv
  have hkpos : 0 < k := by nlinarith
  have hk0 : 0 ≤ k - 1 := by omega
  have hm : (k - 1) * g.n i ∈ g.H := by
    have h := g.H.nsmul_mem (generator_mem g.n i) (k - 1).toNat
    simpa only [nsmul_eq_mul, Int.toNat_of_nonneg hk0] using h
  apply ha.2
  convert g.H.add_mem hb hm using 1; nlinarith [hk]

theorem tail_apery_emod_le (s : g.Setting) {i : Fin 3} {a b : ℤ}
    (ha : TailApery g i a) (hb : TailApery g i b)
    (he : a % g.n i = b % g.n i) : a ≤ b :=
  tail_apery_le_of_emod s ha hb.1 he

theorem tail_apery_emod_injective (s : g.Setting) {i : Fin 3} :
    Set.InjOn (fun a : ℤ => a % g.n i) {a | TailApery g i a} := by
  intro a ha b hb he
  exact le_antisymm (tail_apery_emod_le s ha hb he)
    (tail_apery_emod_le s hb ha he.symm)

theorem tail_apery_emod_surjective (s : g.Setting) (hsym : SymmetricTail g)
    (i : Fin 3) {r : ℤ} (hr0 : 0 ≤ r) (hr : r < g.n i) :
    ∃ a : ℤ, TailApery g i a ∧ a % g.n i = r := by
  classical
  obtain ⟨B, hB⟩ := tail_cofinite s hsym
  have hm := tail_generator_pos s i
  let x : ℤ := (max B 0 + 1) * g.n i + r
  have hx : B ≤ x := by
    have hb : B ≤ max B 0 := le_max_left _ _
    have hb0 : 0 ≤ max B 0 := le_max_right _ _
    have hmul := mul_nonneg hb0 (show 0 ≤ g.n i - 1 by omega)
    dsimp [x]
    nlinarith
  have hxmem := hB x hx
  have hx0 := tail_nonneg s hxmem
  have hxmod : x % g.n i = r := by
    simp [x, Int.add_emod, Int.emod_eq_of_lt hr0 hr]
  have hex : ∃ n : ℕ, (n : ℤ) ∈ g.H ∧ (n : ℤ) % g.n i = r := by
    refine ⟨x.toNat, ?_, ?_⟩
    · simpa only [Int.toNat_of_nonneg hx0] using hxmem
    · simpa only [Int.toNat_of_nonneg hx0] using hxmod
  let n := Nat.find hex
  have hn := Nat.find_spec hex
  refine ⟨(n : ℤ), ⟨hn.1, ?_⟩, hn.2⟩
  intro hsub
  have hsub0 := tail_nonneg s hsub
  have hecast : (((n : ℤ) - g.n i).toNat : ℤ) = n - g.n i :=
    Int.toNat_of_nonneg hsub0
  have hsm : (((n : ℤ) - g.n i).toNat : ℤ) % g.n i = r := by
    rw [hecast]
    simpa using hn.2
  have hleast := Nat.find_min' hex (show
      ((((n : ℤ) - g.n i).toNat : ℤ) ∈ g.H ∧
        (((n : ℤ) - g.n i).toNat : ℤ) % g.n i = r) from
      ⟨by rwa [hecast], hsm⟩)
  change n ≤ ((n : ℤ) - g.n i).toNat at hleast
  omega

theorem tail_apery_card (s : g.Setting) (hsym : SymmetricTail g) (i : Fin 3) :
    {a | TailApery g i a}.ncard = (g.n i).toNat := by
  have hm := tail_generator_pos s i
  have hbij : Set.BijOn (fun a : ℤ => a % g.n i)
      {a | TailApery g i a} (Set.Ico 0 (g.n i)) := by
    refine ⟨?_, tail_apery_emod_injective s, ?_⟩
    · intro a _
      exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hm⟩
    · intro r hr
      obtain ⟨a, ha, he⟩ := tail_apery_emod_surjective s hsym i hr.1 hr.2
      exact ⟨a, ha, he⟩
  rw [hbij.ncard_eq]
  rw [← Finset.coe_Ico, Set.ncard_coe_finset, Int.card_Ico]
  simp

/-- Every actual member reduces to its Apéry representative by a nonnegative multiple. -/
theorem tail_apery_reduce (s : g.Setting) (hsym : SymmetricTail g)
    (i : Fin 3) {w : ℤ} (hw : w ∈ g.H) :
    ∃ q a : ℤ, 0 ≤ q ∧ TailApery g i a ∧ w = q * g.n i + a := by
  have hm := tail_generator_pos s i
  obtain ⟨a, ha, he⟩ := tail_apery_emod_surjective s hsym i
    (Int.emod_nonneg w (by omega)) (Int.emod_lt_of_pos w hm)
  have hle := tail_apery_le_of_emod s ha hw he
  have hd : g.n i ∣ w - a := by
    apply Int.dvd_of_emod_eq_zero
    rw [Int.sub_emod, he]
    simp
  obtain ⟨q, hq⟩ := hd
  refine ⟨q, a, ?_, ha, ?_⟩ <;> nlinarith

/-- A unique-expression rectangular Apéry set has the product cardinality. -/
theorem tail_apery_rectangle_card (s : g.Setting) (hsym : SymmetricTail g)
    (i : Fin 3) (y z A B : ℤ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrep : ∀ w, TailApery g i w → ∃ a b : ℤ,
      0 ≤ a ∧ 0 ≤ b ∧ w = a * y + b * z)
    (hrectangle : ∀ a b : ℤ, 0 ≤ a → 0 ≤ b →
      (TailApery g i (a*y+b*z) ↔ a ≤ A ∧ b ≤ B))
    (hinj : ∀ a b c d : ℤ, 0 ≤ a → a ≤ A → 0 ≤ b → b ≤ B →
      0 ≤ c → c ≤ A → 0 ≤ d → d ≤ B →
      a*y+b*z=c*y+d*z → a=c ∧ b=d) :
    g.n i = (A + 1) * (B + 1) := by
  classical
  let R : Finset (ℤ × ℤ) := (Finset.Icc 0 A) ×ˢ (Finset.Icc 0 B)
  have hbij : Set.BijOn (fun ab : ℤ × ℤ => ab.1*y+ab.2*z)
      (R : Set (ℤ × ℤ)) {w | TailApery g i w} := by
    refine ⟨?_, ?_, ?_⟩
    · intro ab hab
      have h : 0 ≤ ab.1 ∧ ab.1 ≤ A ∧ 0 ≤ ab.2 ∧ ab.2 ≤ B := by
        simpa only [R, Finset.mem_coe, Finset.mem_product, Finset.mem_Icc,
          and_assoc] using hab
      exact (hrectangle _ _ h.1 h.2.2.1).2 ⟨h.2.1,h.2.2.2⟩
    · intro ab hab cd hcd he
      have hab' : (0 ≤ ab.1 ∧ ab.1 ≤ A) ∧ (0 ≤ ab.2 ∧ ab.2 ≤ B) := by
        simpa only [R, Finset.mem_coe, Finset.mem_product, Finset.mem_Icc] using hab
      have hcd' : (0 ≤ cd.1 ∧ cd.1 ≤ A) ∧ (0 ≤ cd.2 ∧ cd.2 ≤ B) := by
        simpa only [R, Finset.mem_coe, Finset.mem_product, Finset.mem_Icc] using hcd
      obtain ⟨he1,he2⟩ := hinj _ _ _ _ hab'.1.1 hab'.1.2 hab'.2.1 hab'.2.2
        hcd'.1.1 hcd'.1.2 hcd'.2.1 hcd'.2.2 he
      exact Prod.ext he1 he2
    · intro w hw
      obtain ⟨a,b,ha,hb,he⟩ := hrep w hw
      have hr : TailApery g i (a*y+b*z) := by rwa [← he]
      have hbounds := (hrectangle a b ha hb).1 hr
      refine ⟨(a,b), ?_, he.symm⟩
      simp only [R, Finset.mem_coe, Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨ha,hbounds.1⟩,⟨hb,hbounds.2⟩⟩
  have hc := hbij.ncard_eq
  rw [Set.ncard_coe_finset, tail_apery_card s hsym i] at hc
  dsimp [R] at hc
  rw [Finset.card_product, Int.card_Icc, Int.card_Icc] at hc
  have hc' : ((A + 1 - 0).toNat : ℤ) * ((B + 1 - 0).toNat : ℤ) =
      ((g.n i).toNat : ℤ) := by exact_mod_cast hc
  have hm := tail_generator_pos s i
  simpa only [sub_zero, Int.toNat_of_nonneg (by omega : 0 ≤ A+1),
    Int.toNat_of_nonneg (by omega : 0 ≤ B+1), Int.toNat_of_nonneg hm.le] using hc'.symm

end P21.Symmetric.Classification
