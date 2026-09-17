import P21.Nonsymmetric.White.WidthOne
import Mathlib.Data.Int.LeastGreatest

namespace P21.Nonsymmetric.White

def NonzeroClasses (k n : ℤ) : Prop :=
  ∀ j : ℤ, 0 < j → j < k → (j*n)%k ≠ 0

theorem nonzeroClasses_complement (k n : ℤ) (h : NonzeroClasses k n) :
    NonzeroClasses k (k-n) := by
  intro j hj hjk hz
  have hd : k ∣ j*(k-n) := Int.dvd_of_emod_eq_zero hz
  have hd' : k ∣ j*n := by
    have := dvd_sub (dvd_mul_left k j) hd
    have heq : j*k-j*(k-n) = j*n := by ring
    rwa [heq] at this
  exact h j hj hjk (Int.emod_eq_zero_of_dvd hd')

theorem floorJump_complement (k n j : ℤ) (hk : 0 < k)
    (h0 : (j*n)%k ≠ 0) (h1 : ((j+1)*n)%k ≠ 0) :
    floorJump k (k-n) j = 1 - floorJump k n j := by
  have hn0 := Int.emod_nonneg (j*n) (by omega : k ≠ 0)
  have hn1 := Int.emod_lt_of_pos (j*n) hk
  have hn2 := Int.emod_nonneg ((j+1)*n) (by omega : k ≠ 0)
  have hn3 := Int.emod_lt_of_pos ((j+1)*n) hk
  have hp0 : 0 < (j*n)%k := by omega
  have hp1 : 0 < ((j+1)*n)%k := by omega
  have he0 := Int.emod_add_mul_ediv (j*n) k
  have he1 := Int.emod_add_mul_ediv ((j+1)*n) k
  have hd0 : (j*(k-n))/k = j-1-(j*n)/k := by
    rw [Int.ediv_eq_iff_of_pos hk]
    constructor <;> nlinarith
  have hd1 : ((j+1)*(k-n))/k = j-((j+1)*n)/k := by
    rw [Int.ediv_eq_iff_of_pos hk]
    constructor <;> nlinarith
  simp [floorJump, hd0, hd1]
  ring

theorem beatty_div_antitone (k b e : ℤ) (hk : 0 ≤ k) (hb : 0 < b) (hbe : b ≤ e) :
    k/e ≤ k/b := by
  have he : 0 < e := by omega
  have hq : 0 ≤ k/e := Int.ediv_nonneg hk he.le
  have hqe := Int.ediv_mul_le k (by omega : e ≠ 0)
  rw [Int.le_ediv_iff_mul_le hb]
  nlinarith

theorem beatty_index_lt (k n i j : ℤ) (hk : 0 ≤ k) (hn : 0 < n)
    (h : (i*k)/n < (j*k)/n) : i < j := by
  by_contra hle
  have hm : j*k ≤ i*k := mul_le_mul_of_nonneg_right (by omega) hk
  have := Int.ediv_le_ediv hn hm
  omega

theorem beatty_last (k n : ℤ) (_hk : 0 < k) (hn : 1 < n) (hnk : n < k)
    (hclasses : NonzeroClasses k n) : ((n-1)*k)/n = k-1-k/n := by
  have h0 := Int.emod_nonneg k (by omega : n ≠ 0)
  have h1 := Int.emod_lt_of_pos k (by omega : 0 < n)
  have h2 := Int.emod_add_mul_ediv k n
  have hpos : 0 < k%n := by
    by_contra h
    have hz : k%n = 0 := by omega
    have he : (k/n)*n = k := by nlinarith
    have hj : 0 < k/n := by nlinarith
    have hjk : k/n < k := by nlinarith
    have hh := hclasses (k/n) hj hjk
    rw [he] at hh
    simp at hh
  rw [Int.ediv_eq_iff_of_pos (by omega : 0 < n)]
  constructor <;> nlinarith

/-- The elementary support partition in White's proof cannot have three
nonempty components. This theorem is entirely integer arithmetic. -/
theorem beatty_partition_impossible (k b d e : ℤ) (hk : 0 < k)
    (hd : 1 < d) (hdb : d ≤ b) (hbe : b < e) (hek : 2*e < k)
    (hbclasses : NonzeroClasses k b) (hdclasses : NonzeroClasses k d)
    (heclasses : NonzeroClasses k e)
    (hpartition : ∀ j : ℤ, 0 < j → j+1 < k →
      floorJump k b j + floorJump k d j = floorJump k e j) : False := by
  have hb : 0 < b := by omega
  have hd0 : 0 < d := by omega
  have he : 0 < e := by omega
  have hbk : b < k := by omega
  have hdk : d < k := by omega
  have hek0 : e < k := by omega
  have firstB := floorJump_of_support k b 1 hk hb hbk (by omega) (by omega) hbclasses
  have firstD := floorJump_of_support k d 1 hk hd0 hdk (by omega) hd hdclasses
  have firstE := floorJump_of_support k e 1 hk he hek0 (by omega) (by omega) heclasses
  simp only [one_mul] at firstB firstD firstE
  have hdisjoint (j : ℤ) (hj : 0 < j) (hjk : j+1 < k)
      (hjb : floorJump k b j = 1) (hjd : floorJump k d j = 1) : False := by
    have hp := hpartition j hj hjk
    have hbound := (floorJump_bounds k e j hk he hek0).2
    omega
  have hbToE (j : ℤ) (hj : 0 < j) (hjk : j+1 < k)
      (hjb : floorJump k b j = 1) : floorJump k e j = 1 := by
    have hp := hpartition j hj hjk
    have hdBound := (floorJump_bounds k d j hk hd0 hdk).1
    have heBound := (floorJump_bounds k e j hk he hek0).2
    omega
  have hdToE (j : ℤ) (hj : 0 < j) (hjk : j+1 < k)
      (hjd : floorJump k d j = 1) : floorJump k e j = 1 := by
    have hp := hpartition j hj hjk
    have hbBound := (floorJump_bounds k b j hk hb hbk).1
    have heBound := (floorJump_bounds k e j hk he hek0).2
    omega
  have hfirst : k/b = k/e := by
    have hle := beatty_div_antitone k b e hk.le hb hbe.le
    have hpart := hpartition (k/e) firstE.1 firstE.2.1
    have hbb := floorJump_bounds k b (k/e) hk hb hbk
    have hdd := floorJump_bounds k d (k/e) hk hd0 hdk
    have hcases : floorJump k b (k/e) = 1 ∨ floorJump k d (k/e) = 1 := by omega
    rcases hcases with h | h
    · obtain ⟨t, ht, _, heq⟩ := floorJump_support k b (k/e) hk hb firstE.1
        firstE.2.1 (hbclasses _ (by omega) (by omega)) h
      have hm : k ≤ t*k := by nlinarith
      have hdiv := Int.ediv_le_ediv hb hm
      omega
    · obtain ⟨t, ht, _, heq⟩ := floorJump_support k d (k/e) hk hd0 firstE.1
        firstE.2.1 (hdclasses _ (by omega) (by omega)) h
      have hm : k ≤ t*k := by nlinarith
      have hdiv := Int.ediv_le_ediv hd0 hm
      have hdbdiv := beatty_div_antitone k d b hk.le hd0 hdb
      omega
  have hlarge : 2 ≤ k/e := (Int.le_ediv_iff_mul_le he).2 (by omega)
  have hbefore : k/b < k/d := by
    have hle := beatty_div_antitone k d b hk.le hd0 hdb
    by_contra h
    have heq : k/b = k/d := by omega
    exact hdisjoint (k/b) firstB.1 firstB.2.1 firstB.2.2 (heq ▸ firstD.2.2)
  have hbLast := beatty_last k b hk (by omega) hbk hbclasses
  have hdLast := beatty_last k d hk hd hdk hdclasses
  have hDmid : k/d ≤ ((d-1)*k)/d := by
    apply Int.ediv_le_ediv hd0
    nlinarith
  have hafter : k/d < ((b-1)*k)/b := by omega
  obtain ⟨s, hs, hsmax⟩ := Int.exists_greatest_of_bdd
    (P := fun s : ℤ => 0 < s ∧ s < b ∧ (s*k)/b < k/d)
    ⟨b, by intro s hs; omega⟩ ⟨1, by simpa only [one_mul] using And.intro (by omega : 0 < (1:ℤ)) (And.intro (by omega : 1 < b) hbefore)⟩
  have hsnext : s+1 < b := by
    by_contra h
    have heq : s = b-1 := by omega
    rw [heq] at hs
    omega
  have nextB := floorJump_of_support k b (s+1) hk hb hbk (by omega) hsnext hbclasses
  have currB := floorJump_of_support k b s hk hb hbk hs.1 hs.2.1 hbclasses
  have hnextge : k/d ≤ ((s+1)*k)/b := by
    by_contra h
    have := hsmax (s+1) ⟨by omega, hsnext, by omega⟩
    omega
  have hnextgt : k/d < ((s+1)*k)/b := by
    by_contra h
    have heq : ((s+1)*k)/b = k/d := by omega
    exact hdisjoint (k/d) firstD.1 firstD.2.1 (heq ▸ nextB.2.2) firstD.2.2
  obtain ⟨i, _, _, hi⟩ := floorJump_support k e ((s*k)/b) hk he currB.1 currB.2.1
    (heclasses _ (by omega) (by omega)) (hbToE _ currB.1 currB.2.1 currB.2.2)
  obtain ⟨j, _, _, hj⟩ := floorJump_support k e (k/d) hk he firstD.1 firstD.2.1
    (heclasses _ (by omega) (by omega)) (hdToE _ firstD.1 firstD.2.1 firstD.2.2)
  obtain ⟨l, _, _, hl⟩ := floorJump_support k e (((s+1)*k)/b) hk he nextB.1 nextB.2.1
    (heclasses _ (by omega) (by omega)) (hbToE _ nextB.1 nextB.2.1 nextB.2.2)
  apply beatty_interleaving_impossible k b e s i j l hk.le hb he hfirst hlarge
  · apply beatty_index_lt k e i j hk.le he
    omega
  · apply beatty_index_lt k e j l hk.le he
    omega
  · exact hi
  · exact hl

/-- Sorted nontrivial residues contradict the age identities. -/
theorem cyclicWhite_sorted_impossible (k a b d : ℤ) (hk : 1 < k)
    (ha : 1 < a) (hb : 1 < b) (hd : 1 < d)
    (hak : a < k) (hbk : b < k) (hdk : d < k)
    (hba : b ≤ a) (hdb : d ≤ b) (hage : CyclicAge k ![a,b,d]) : False := by
  have hbounds : ∀ i, 0 < (![a,b,d] : Fin 3 → ℤ) i ∧ (![a,b,d] : Fin 3 → ℤ) i < k := by
    intro i
    fin_cases i <;> simp <;> omega
  have hsum : a+b+d = k+1 := by
    have hh := cyclicAge_sum k ![a,b,d] hk hbounds hage
    simpa [Fin.sum_univ_three] using hh
  have hna : NonzeroClasses k a := by
    intro j hj hjk
    simpa using cyclicAge_nonzero k ![a,b,d] hk hage j hj hjk 0
  have hnb : NonzeroClasses k b := by
    intro j hj hjk
    simpa using cyclicAge_nonzero k ![a,b,d] hk hage j hj hjk 1
  have hnd : NonzeroClasses k d := by
    intro j hj hjk
    simpa using cyclicAge_nonzero k ![a,b,d] hk hage j hj hjk 2
  have hbig : k < 2*a := by
    by_contra h
    have hneq : 2*a ≠ k := by
      intro heq
      have hh := hna 2 (by omega) (by omega)
      rw [heq] at hh
      simp at hh
    have hsmall : 2*a < k := by omega
    have hf (n : ℤ) (hn : 0 < n) (hna : n ≤ a) : floorJump k n 1 = 0 := by
      have hnk : n < k := by omega
      have h2 : 2*n < k := by omega
      simp only [floorJump, one_add_one_eq_two, one_mul,
        Int.ediv_eq_zero_of_lt (by omega : 0 ≤ 2*n) h2,
        Int.ediv_eq_zero_of_lt hn.le hnk, sub_self]
    have hh := cyclicAge_jump_sum k ![a,b,d] hk hbounds hage 1 (by omega) (by omega)
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] at hh
    change floorJump k a 1 + floorJump k b 1 + floorJump k d 1 = 1 at hh
    rw [hf a (by omega) le_rfl, hf b (by omega) hba, hf d (by omega) (by omega)] at hh
    omega
  apply beatty_partition_impossible k b d (k-a) (by omega) hd hdb (by omega) (by omega)
    hnb hnd (nonzeroClasses_complement k a hna)
  intro j hj hjk
  have hh := cyclicAge_jump_sum k ![a,b,d] hk hbounds hage j hj hjk
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at hh
  change floorJump k a j + floorJump k b j + floorJump k d j = 1 at hh
  have hc := floorJump_complement k a j (by omega) (hna j hj (by omega))
    (hna (j+1) (by omega) hjk)
  omega

/-- The required specialized arithmetic White theorem, proved internally
by the disjoint Beatty-support gap argument. -/
theorem cyclic_white_proved : CyclicWhiteStatement := by
  intro k a hk ha hage
  by_contra hnone
  push Not at hnone
  have hgt (i : Fin 3) : 1 < a i := by have := ha i; have := hnone i; omega
  have hagePerm (x y z : ℤ)
      (hperm : ∀ t : ℤ, (t*x)%k+(t*y)%k+(t*z)%k =
        (t*a 0)%k+(t*a 1)%k+(t*a 2)%k) : CyclicAge k ![x,y,z] := by
    intro t ht htk
    have hh := hage t ht htk
    simp only [Fin.sum_univ_three] at hh
    simp only [Fin.sum_univ_three]
    change (t*x)%k+(t*y)%k+(t*z)%k = k+t
    exact (hperm t).trans hh
  have hcontr (i j l : Fin 3) (hji : a j ≤ a i) (hlj : a l ≤ a j)
      (hperm : ∀ t : ℤ, (t*a i)%k+(t*a j)%k+(t*a l)%k =
        (t*a 0)%k+(t*a 1)%k+(t*a 2)%k) : False :=
    cyclicWhite_sorted_impossible k (a i) (a j) (a l) hk (hgt i) (hgt j) (hgt l)
      (ha i).2 (ha j).2 (ha l).2 hji hlj (hagePerm _ _ _ hperm)
  rcases le_total (a 0) (a 1) with h01 | h10
  · rcases le_total (a 1) (a 2) with h12 | h21
    · exact hcontr 2 1 0 h12 h01 (by intro t; ring)
    · rcases le_total (a 0) (a 2) with h02 | h20
      · exact hcontr 1 2 0 h21 h02 (by intro t; ring)
      · exact hcontr 1 0 2 h01 h20 (by intro t; ring)
  · rcases le_total (a 0) (a 2) with h02 | h20
    · exact hcontr 2 0 1 h02 h10 (by intro t; ring)
    · rcases le_total (a 1) (a 2) with h12 | h21
      · exact hcontr 0 2 1 h20 h12 (by intro t; ring)
      · exact hcontr 0 1 2 h10 h21 (by intro t; ring)

end P21.Nonsymmetric.White
