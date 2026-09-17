import P21.Nonsymmetric.ColorCap.DPE.Rotation

namespace P21.Nonsymmetric.ColorCap

/-- Arithmetic data proved from the actual chronological successful crossings.
The later path layer constructs this structure; no DPE theorem receives it as input. -/
structure SuccessfulPrefix (x A B v b c : ℤ) (q : ℕ) where
  N : ℕ → ℤ
  x_pos : 0 < x
  B_pos : 0 < B
  b_nonneg : 0 ≤ b
  c_nonneg : 0 ≤ c
  corridor : A * B < x * v
  residues : ∀ h : ℕ, 1 ≤ h → h ≤ q →
    0 < N h * x - (h : ℤ) * A ∧
    N h * x - (h : ℤ) * A ≤ x - b - 1 ∧
    0 < (h : ℤ) * v - (N h - 1) * B ∧
    (h : ℤ) * v - (N h - 1) * B ≤ B - c - 1

namespace SuccessfulPrefix

def E {x A B v b c : ℤ} {q : ℕ} (P : SuccessfulPrefix x A B v b c q)
    (h : ℕ) : ℤ := P.N h * x - (h : ℤ) * A

def U {x A B v b c : ℤ} {q : ℕ} (P : SuccessfulPrefix x A B v b c q)
    (h : ℕ) : ℤ := (h : ℤ) * v - (P.N h - 1) * B

theorem separator {x A B v b c : ℤ} {q : ℕ}
    (P : SuccessfulPrefix x A B v b c q) :
    ∀ h : ℕ, 1 ≤ h → h ≤ q →
      ¬ ∃ k : ℤ, (h : ℤ) * A ≤ k * x ∧ k * B ≤ (h : ℤ) * v := by
  apply successful_prefix_separator x A B v q P.N P.x_pos P.B_pos
  intro h hh hq
  obtain ⟨hE0,hEx,hU0,hUB⟩ := P.residues h hh hq
  have hb := P.b_nonneg
  have hc := P.c_nonneg
  exact ⟨hE0,by omega,hU0,by omega⟩

theorem coordinate_injective {x A B v b c : ℤ} {q : ℕ}
    (P : SuccessfulPrefix x A B v b c q)
    {i j : ℕ} (hi : 1 ≤ i) (hiq : i ≤ q) (hj : 1 ≤ j) (hjq : j ≤ q)
    (he : P.E i = P.E j) : i = j := by
  by_contra hn
  rcases lt_or_gt_of_ne hn with hij | hji
  · exact (prefix_residue_distinct x A B v q P.N P.x_pos P.B_pos P.corridor
      P.separator i j hij hjq).1 he
  · exact (prefix_residue_distinct x A B v q P.N P.x_pos P.B_pos P.corridor
      P.separator j i hji hiq).1 he.symm

theorem coordinateU_injective {x A B v b c : ℤ} {q : ℕ}
    (P : SuccessfulPrefix x A B v b c q)
    {i j : ℕ} (hi : 1 ≤ i) (hiq : i ≤ q) (hj : 1 ≤ j) (hjq : j ≤ q)
    (he : P.U i = P.U j) : i = j := by
  by_contra hn
  rcases lt_or_gt_of_ne hn with hij | hji
  · exact (prefix_residue_distinct x A B v q P.N P.x_pos P.B_pos P.corridor
      P.separator i j hij hjq).2 he
  · exact (prefix_residue_distinct x A B v q P.N P.x_pos P.B_pos P.corridor
      P.separator j i hji hiq).2 he.symm

/-- The successful `E` residues occupy distinct integer slots in
`[1,x-b-1]`. -/
theorem E_slot_count {x A B v b c : ℤ} {q : ℕ}
    (P : SuccessfulPrefix x A B v b c q) (hrange : 0 ≤ x - b - 1) :
    (q : ℤ) ≤ x - b - 1 := by
  let s : Finset ℕ := Finset.Icc 1 q
  have himage : s.image P.E ⊆ Finset.Icc (1 : ℤ) (x - b - 1) := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    obtain ⟨hi1, hiq⟩ := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨(P.residues i hi1 hiq).1,
      (P.residues i hi1 hiq).2.1⟩
  have hinj : Set.InjOn P.E (s : Set ℕ) := by
    intro i hi j hj he
    exact P.coordinate_injective (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 he
  have hcardeq : (s.image P.E).card = s.card := Finset.card_image_iff.mpr hinj
  have hcard := Finset.card_le_card himage
  rw [hcardeq] at hcard
  simp [s, Nat.card_Icc, Int.card_Icc] at hcard
  have hx : 0 ≤ x - b := by omega
  have heq : (x - b).toNat = (x - b - 1).toNat + 1 := by
    apply Int.ofNat_inj.mp
    push_cast
    rw [Int.toNat_of_nonneg hx, Int.toNat_of_nonneg hrange]
    ring
  rw [heq] at hcard
  have hq : q ≤ (x - b - 1).toNat := by omega
  have hcast := Int.toNat_of_nonneg hrange
  have hz : (q : ℤ) ≤ ((x - b - 1).toNat : ℤ) := by exact_mod_cast hq
  rwa [hcast] at hz

/-- The successful `U` residues occupy distinct integer slots in
`[1,B-c-1]`. -/
theorem U_slot_count {x A B v b c : ℤ} {q : ℕ}
    (P : SuccessfulPrefix x A B v b c q) (hrange : 0 ≤ B - c - 1) :
    (q : ℤ) ≤ B - c - 1 := by
  let s : Finset ℕ := Finset.Icc 1 q
  have himage : s.image P.U ⊆ Finset.Icc (1 : ℤ) (B - c - 1) := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    obtain ⟨hi1, hiq⟩ := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨(P.residues i hi1 hiq).2.2.1,
      (P.residues i hi1 hiq).2.2.2⟩
  have hinj : Set.InjOn P.U (s : Set ℕ) := by
    intro i hi j hj he
    exact P.coordinateU_injective (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 he
  have hcardeq : (s.image P.U).card = s.card := Finset.card_image_iff.mpr hinj
  have hcard := Finset.card_le_card himage
  rw [hcardeq] at hcard
  simp [s, Nat.card_Icc, Int.card_Icc] at hcard
  have hB : 0 ≤ B - c := by omega
  have heq : (B - c).toNat = (B - c - 1).toNat + 1 := by
    apply Int.ofNat_inj.mp
    push_cast
    rw [Int.toNat_of_nonneg hB, Int.toNat_of_nonneg hrange]
    ring
  rw [heq] at hcard
  have hq : q ≤ (B - c - 1).toNat := by omega
  have hcast := Int.toNat_of_nonneg hrange
  have hz : (q : ℤ) ≤ ((B - c - 1).toNat : ℤ) := by exact_mod_cast hq
  rwa [hcast] at hz

/-- LR: finite slot counting against the last successful crossing. -/
theorem last_rank {x A B v b c : ℤ} {q : ℕ}
    (P : SuccessfulPrefix x A B v b c q) (hq : 1 ≤ q) :
    (q : ℤ) + P.E q + P.U q ≤ (x - b) + (B - c) - 1 := by
  let s := Finset.Ico 1 q
  have hs := residue_slot_bound s P.E P.U (P.E q) (P.U q)
    (x-b-1) (B-c-1)
  have hE : ∀ i ∈ s, P.E i ≤ x-b-1 := by
    intro i hi
    obtain ⟨hi1,hiq⟩ := Finset.mem_Ico.mp hi
    exact (P.residues i hi1 (by omega)).2.1
  have hU : ∀ i ∈ s, P.U i ≤ B-c-1 := by
    intro i hi
    obtain ⟨hi1,hiq⟩ := Finset.mem_Ico.mp hi
    exact (P.residues i hi1 (by omega)).2.2.2
  have hEinj : Set.InjOn P.E (s : Set ℕ) := by
    intro i hi j hj he
    obtain ⟨hi1,hiq⟩ := Finset.mem_Ico.mp hi
    obtain ⟨hj1,hjq⟩ := Finset.mem_Ico.mp hj
    exact P.coordinate_injective hi1 (by omega) hj1 (by omega) he
  have hUinj : Set.InjOn P.U (s : Set ℕ) := by
    intro i hi j hj he
    obtain ⟨hi1,hiq⟩ := Finset.mem_Ico.mp hi
    obtain ⟨hj1,hjq⟩ := Finset.mem_Ico.mp hj
    exact P.coordinateU_injective hi1 (by omega) hj1 (by omega) he
  have hcover : ∀ i ∈ s, P.E q < P.E i ∨ P.U q < P.U i := by
    intro i hi
    obtain ⟨hi1,hiq⟩ := Finset.mem_Ico.mp hi
    exact prefix_residue_antichain x A B v q P.N P.separator i q
      hiq (le_rfl)
  have hcard := hs hE hU hEinj hUinj hcover
  have hEq := P.residues q hq le_rfl
  have hdiffE : 0 ≤ x-b-1-P.E q := by simpa [E] using sub_nonneg.mpr hEq.2.1
  have hdiffU : 0 ≤ B-c-1-P.U q := by simpa [U] using sub_nonneg.mpr hEq.2.2.2
  have hcardZ : (s.card : ℤ) ≤
      ((x-b-1-P.E q).toNat : ℤ) + ((B-c-1-P.U q).toNat : ℤ) := by
    exact_mod_cast hcard
  simp [s, Int.toNat_of_nonneg hdiffE, Int.toNat_of_nonneg hdiffU] at hcardZ
  omega

/-- ELR in the exact positive terminal ranges. The cover is proved from
chronological PREFIX at each call site. -/
theorem terminal_rank {x A B v b c E U : ℤ} {q : ℕ}
    (P : SuccessfulPrefix x A B v b c q)
    (hE0 : 1 ≤ E) (hEx : E ≤ x-b-1)
    (hU0 : 1 ≤ U) (hUB : U ≤ B-c-1)
    (hcover : ∀ i : ℕ, 1 ≤ i → i ≤ q → E < P.E i ∨ U < P.U i) :
    (q : ℤ) ≤ (x-b-1-E)+(B-c-1-U) := by
  let s := Finset.Icc 1 q
  have hE : ∀ i ∈ s, P.E i ≤ x-b-1 := by
    intro i hi
    exact (P.residues i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2).2.1
  have hU : ∀ i ∈ s, P.U i ≤ B-c-1 := by
    intro i hi
    exact (P.residues i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2).2.2.2
  have hEinj : Set.InjOn P.E (s : Set ℕ) := by
    intro i hi j hj he
    exact P.coordinate_injective (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 he
  have hUinj : Set.InjOn P.U (s : Set ℕ) := by
    intro i hi j hj he
    exact P.coordinateU_injective (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 he
  have hc := residue_slot_bound s P.E P.U E U (x-b-1) (B-c-1)
    hE hU hEinj hUinj (by
      intro i hi
      exact hcover i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2)
  have hdE : 0 ≤ x-b-1-E := by omega
  have hdU : 0 ≤ B-c-1-U := by omega
  have hcZ : (s.card : ℤ) ≤ ((x-b-1-E).toNat : ℤ) + ((B-c-1-U).toNat : ℤ) := by
    exact_mod_cast hc
  simp [s, Int.toNat_of_nonneg hdE, Int.toNat_of_nonneg hdU] at hcZ
  omega

end SuccessfulPrefix
end P21.Nonsymmetric.ColorCap
