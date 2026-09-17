import P21.Nonsymmetric.ColorCap.RelativeLattice

namespace P21.Nonsymmetric.White

/-- The cyclic age equalities, before any width-one conclusion is known. -/
def CyclicAge (k : ℤ) (a : Fin 3 → ℤ) : Prop :=
  ∀ j : ℤ, 0 < j → j < k → ∑ i, (j * a i) % k = k + j

/-- The exact arithmetic form of White's theorem. Its proof is
`cyclic_white_proved` in `WidthOneBeatty.lean`. -/
def CyclicWhiteStatement : Prop :=
  ∀ (k : ℤ) (a : Fin 3 → ℤ), 1 < k →
    (∀ i, 0 < a i ∧ a i < k) → CyclicAge k a → ∃ i, a i = 1

theorem complementary_remainder (k x : ℤ) (hk : 0 < k) :
    x % k + (-x) % k = if k ∣ x then 0 else k := by
  rw [Int.neg_emod, Int.natCast_natAbs, abs_of_pos hk]
  split_ifs with h
  · simp [Int.emod_eq_zero_of_dvd h]
  · omega

/-- Age and the negative class already exclude every zero coordinate. -/
theorem cyclicAge_nonzero (k : ℤ) (a : Fin 3 → ℤ) (hk : 1 < k)
    (hage : CyclicAge k a) (j : ℤ) (hj : 0 < j) (hjk : j < k) :
    ∀ i, (j * a i) % k ≠ 0 := by
  have hpos := hage j hj hjk
  have hneg := hage (k-j) (by omega) (by omega)
  have hpair i := complementary_remainder k (j*a i) (by omega)
  have hrem i : ((k-j)*a i)%k = (- (j*a i))%k := by
    have hh : (k-j)*a i = -(j*a i) + a i*k := by ring
    rw [hh, Int.add_mul_emod_self_right]
  simp only [Fin.sum_univ_three] at hpos hneg
  simp only [hrem] at hneg
  have hle i : (j*a i)%k + (-(j*a i))%k ≤ k := by
    rw [hpair i]
    split_ifs <;> omega
  have h0 := hle 0
  have h1 := hle 1
  have h2 := hle 2
  intro i hi
  have hd : k ∣ j*a i := Int.dvd_of_emod_eq_zero hi
  have hi' : (-(j*a i))%k = 0 := by simp [Int.neg_emod, hd]
  fin_cases i
  · change j*a 0%k = 0 at hi
    change (-(j*a 0))%k = 0 at hi'
    omega
  · change j*a 1%k = 0 at hi
    change (-(j*a 1))%k = 0 at hi'
    omega
  · change j*a 2%k = 0 at hi
    change (-(j*a 2))%k = 0 at hi'
    omega

/-- The age-one equation fixes the sum of the three initial residues. -/
theorem cyclicAge_sum (k : ℤ) (a : Fin 3 → ℤ) (hk : 1 < k)
    (ha : ∀ i, 0 < a i ∧ a i < k) (hage : CyclicAge k a) :
    ∑ i, a i = k + 1 := by
  have h := hage 1 (by omega) hk
  simpa only [one_mul, Int.emod_eq_of_lt (ha _).1.le (ha _).2] using h

/-- A jump in the integer floor sequence used in the elementary White proof. -/
def floorJump (k n j : ℤ) : ℤ := ((j+1)*n)/k - (j*n)/k

/-- Every floor jump is zero or one when the slope lies in `(0,1)`. -/
theorem floorJump_bounds (k n j : ℤ) (hk : 0 < k) (hn : 0 < n) (hnk : n < k) :
    0 ≤ floorJump k n j ∧ floorJump k n j ≤ 1 := by
  have h0 := Int.emod_nonneg (j*n) (by omega : k ≠ 0)
  have h1 := Int.emod_lt_of_pos (j*n) hk
  have h2 := Int.emod_nonneg ((j+1)*n) (by omega : k ≠ 0)
  have h3 := Int.emod_lt_of_pos ((j+1)*n) hk
  have h4 := Int.emod_add_mul_ediv (j*n) k
  have h5 := Int.emod_add_mul_ediv ((j+1)*n) k
  dsimp [floorJump]
  constructor <;> nlinarith

/-- The cyclic age equations force exactly one of the three floor jumps
at each position away from the endpoints. -/
theorem cyclicAge_jump_sum (k : ℤ) (a : Fin 3 → ℤ) (hk : 1 < k)
    (ha : ∀ i, 0 < a i ∧ a i < k) (hage : CyclicAge k a)
    (j : ℤ) (hj : 0 < j) (hjk : j+1 < k) :
    ∑ i, floorJump k (a i) j = 1 := by
  have hsum := cyclicAge_sum k a hk ha hage
  have hpos := hage j hj (by omega)
  have hnext := hage (j+1) (by omega) hjk
  have hdiv (i : Fin 3) := Int.emod_add_mul_ediv (j*a i) k
  have hdivnext (i : Fin 3) := Int.emod_add_mul_ediv ((j+1)*a i) k
  simp only [Fin.sum_univ_three] at hsum hpos hnext ⊢
  dsimp [floorJump]
  have h0 := hdiv 0
  have h1 := hdiv 1
  have h2 := hdiv 2
  have h3 := hdivnext 0
  have h4 := hdivnext 1
  have h5 := hdivnext 2
  have hh : k * (((j+1)*a 0/k-j*a 0/k) +
      ((j+1)*a 1/k-j*a 1/k) + ((j+1)*a 2/k-j*a 2/k) - 1) = 0 := by
    linear_combination h3 + h4 + h5 - h0 - h1 - h2 -
      hnext + hpos + hsum
  rcases mul_eq_zero.mp hh with h | h <;> omega

/-- Adjacent members of a rational Beatty sequence have one of two gap sizes. -/
theorem beatty_adjacent_gap (k n t : ℤ) (hn : 0 < n) :
    k/n ≤ ((t+1)*k)/n - (t*k)/n ∧
    ((t+1)*k)/n - (t*k)/n ≤ k/n + 1 := by
  have h0 := Int.emod_nonneg (t*k) (by omega : n ≠ 0)
  have h1 := Int.emod_lt_of_pos (t*k) hn
  have h2 := Int.emod_nonneg ((t+1)*k) (by omega : n ≠ 0)
  have h3 := Int.emod_lt_of_pos ((t+1)*k) hn
  have h4 := Int.emod_add_mul_ediv (t*k) n
  have h5 := Int.emod_add_mul_ediv ((t+1)*k) n
  have h6 := Int.emod_nonneg k (by omega : n ≠ 0)
  have h7 := Int.emod_lt_of_pos k hn
  have h8 := Int.emod_add_mul_ediv k n
  constructor <;> nlinarith

/-- Any two distinct indices have at least the minimum Beatty gap. -/
theorem beatty_gap (k n s t : ℤ) (hk : 0 ≤ k) (hn : 0 < n) (hst : s < t) :
    k/n ≤ (t*k)/n - (s*k)/n := by
  have hgap := (beatty_adjacent_gap k n s hn).1
  have hmul : (s+1)*k ≤ t*k := mul_le_mul_of_nonneg_right (by omega) hk
  have hdiv := Int.ediv_le_ediv hn hmul
  omega

/-- A disjoint extra point cannot split a Beatty gap into two minimum gaps
when both sequences have the same initial gap, at least two. -/
theorem beatty_interleaving_impossible (k b e s i j l : ℤ)
    (hk : 0 ≤ k) (hb : 0 < b) (he : 0 < e)
    (hfirst : k/b = k/e) (hlarge : 2 ≤ k/e)
    (hij : i < j) (hjl : j < l)
    (hleft : (s*k)/b = (i*k)/e)
    (hright : ((s+1)*k)/b = (l*k)/e) : False := by
  have hgap := (beatty_adjacent_gap k b s hb).2
  have hgap1 := beatty_gap k e i j hk he hij
  have hgap2 := beatty_gap k e j l hk he hjl
  rw [hfirst, hleft, hright] at hgap
  omega

/-- A floor jump produces the corresponding member of the Beatty support. -/
theorem floorJump_support (k n j : ℤ) (hk : 0 < k) (hn : 0 < n)
    (hj : 0 < j) (hjk : j+1 < k)
    (hnonzero : ((j+1)*n)%k ≠ 0) (hjump : floorJump k n j = 1) :
    ∃ t : ℤ, 0 < t ∧ t < n ∧ j = (t*k)/n := by
  let t := ((j+1)*n)/k
  have h0 := Int.emod_nonneg (j*n) (by omega : k ≠ 0)
  have h1 := Int.emod_lt_of_pos (j*n) hk
  have h2 := Int.emod_nonneg ((j+1)*n) (by omega : k ≠ 0)
  have h3 := Int.emod_lt_of_pos ((j+1)*n) hk
  have h4 := Int.emod_add_mul_ediv (j*n) k
  have h5 := Int.emod_add_mul_ediv ((j+1)*n) k
  have ht1 : j*n < t*k := by dsimp [t]; dsimp [floorJump] at hjump; nlinarith
  have h2pos : 0 < ((j+1)*n)%k := by omega
  have ht2 : t*k < (j+1)*n := by dsimp [t]; nlinarith
  refine ⟨t, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · symm
    rw [Int.ediv_eq_iff_of_pos hn]
    constructor <;> nlinarith

/-- A member of the Beatty support yields a floor jump. Nonvanishing at
integer classes excludes the ambiguous boundary case. -/
theorem floorJump_of_support (k n t : ℤ) (hk : 0 < k) (hn : 0 < n)
    (hnk : n < k) (ht : 0 < t) (htn : t < n)
    (hnonzero : ∀ j : ℤ, 0 < j → j < k → (j*n)%k ≠ 0) :
    0 < (t*k)/n ∧ (t*k)/n + 1 < k ∧ floorJump k n ((t*k)/n) = 1 := by
  let j := (t*k)/n
  have hrem0 := Int.emod_nonneg (t*k) (by omega : n ≠ 0)
  have hrem1 := Int.emod_lt_of_pos (t*k) hn
  have hdiv := Int.emod_add_mul_ediv (t*k) n
  have hjlow : j*n ≤ t*k := by dsimp [j]; nlinarith
  have hjhigh : t*k < (j+1)*n := by dsimp [j]; nlinarith
  have hjpos : 0 < j := by nlinarith
  have hjk : j+1 < k := by nlinarith
  have hjstrict : j*n < t*k := by
    by_contra h
    have heq : j*n = t*k := by omega
    have hz := hnonzero j hjpos (by omega)
    apply hz
    rw [heq]
    simp
  have hbefore : (j*n)/k = t-1 := by
    rw [Int.ediv_eq_iff_of_pos hk]
    constructor <;> nlinarith
  have hafter : ((j+1)*n)/k = t := by
    rw [Int.ediv_eq_iff_of_pos hk]
    constructor <;> nlinarith
  refine ⟨hjpos, hjk, ?_⟩
  change floorJump k n j = 1
  simp [floorJump, hbefore, hafter]

end P21.Nonsymmetric.White
