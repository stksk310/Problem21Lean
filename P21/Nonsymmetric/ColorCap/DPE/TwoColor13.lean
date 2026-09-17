import P21.Nonsymmetric.ColorCap.DPE.TwoColor12

namespace P21.Nonsymmetric.ColorCap

def X13 (D : BoxInput) (N R : ℤ) : ℤ := R * (D.y 0 + D.b 0) - N * D.x 0
def Y13 (D : BoxInput) (N R : ℤ) : ℤ := N * D.y 2 - R * D.x 2

theorem terminal13_count_bounds (D : BoxInput)
    {l : List (Fin 3)} {u : Point}
    (ht : FiringTrace D.upper D.rows D.x l u)
    (hp : ProperNonzeroPredecessors l) (hno1 : l.count 1 = 0)
    (hcount2 : 1 ≤ l.count 2) (hstart : D.x 0 < D.y 0) :
    ((l.count 0 + 1 : ℕ) : ℤ) ≤ D.y 0 ∧
      ((l.count 2 + 1 : ℕ) : ℤ) ≤ D.x 0 - D.b 0 ∧
      ((l.count 2 + 1 : ℕ) : ℤ) ≤ D.y 2 := by
  let q := l.count 2
  let P := trace_successfulPrefix13 D ht hp hno1 (q := q) le_rfl
  have h1q : 1 ≤ q := by simpa [q] using hcount2
  have hqx := P.E_slot_count (by
    have he := P.residues 1 (by omega) h1q
    omega)
  have hqy := P.U_slot_count (by have := D.y_pos 2; omega)
  have hu0 := ht.endpoint_eq_sub_sum 0
  have hu0box := ht.endpoint_inBox 0
  simp [BoxInput.rows, Fin.sum_univ_succ, hno1] at hu0
  dsimp [BoxInput.upper] at hu0box
  have hNy : ((l.count 0 + 1 : ℕ) : ℤ) ≤ D.y 0 := by
    by_contra hn
    push Not at hn
    push_cast at hn
    have hqX : (l.count 2 : ℤ) ≤ D.x 0 - D.b 0 - 1 := by
      simpa [q, P] using hqx
    have huUpper := hu0box.2
    have hb := D.b_pos 0
    have hfactor : 0 < D.b 0 + D.y 0 - D.x 0 + 1 := by omega
    have hprod := mul_pos hb hfactor
    nlinarith
  refine ⟨hNy, ?_, ?_⟩
  · simpa [q, P] using (show (q : ℤ) + 1 ≤ D.x 0 - D.b 0 by omega)
  · simpa [q, P] using (show (q : ℤ) + 1 ≤ D.y 2 by omega)

theorem terminal13_not_sinkB (D : BoxInput) (N R : ℤ) (hN : 0 < N)
    (hB : 0 ≤ X13 D N R ∧ 0 ≤ Y13 D N R) : False := by
  exact D.two_color13_not_sinkB N R hN (by simpa [X13, Y13] using hB)

/-- B.18 sink D certificate `(N,1,R)`. -/
theorem terminal13_sinkD_impossible (D : BoxInput) (N R : ℤ)
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hNy : N ≤ D.y 0) (hRy : R ≤ D.y 2)
    (u : Point)
    (hu0 : u 0 = D.y 0 + D.b 0 - X13 D N R)
    (hu1 : u 1 = D.x 1 - (N - 1) * (D.y 1 + D.b 1) - (R - 1) * D.y 1)
    (hu2 : u 2 = D.y 2 - Y13 D N R)
    (hD : u 0 ≤ D.y 0 + D.b 0 ∧ u 1 ≤ D.y 1 + D.b 1 ∧
      u 2 ≤ D.y 2 + D.b 2) : False := by
  let w : Point := ![D.y 0 + X13 D N R,
    2 * D.y 1 + D.b 1 - u 1,
    D.y 2 + D.b 2 + Y13 D N R]
  apply weighted_certificate_impossible D.m (N + R + 1) D.n w
    D.m_pos (by omega) D.n_gt
  · intro i
    fin_cases i
    · simp [w]
      have hX : 0 ≤ X13 D N R := by omega
      have := D.y_pos 0
      omega
    · simp [w]
      have := D.y_pos 1
      omega
    · simp [w]
      have hY : -D.b 2 ≤ Y13 D N R := by omega
      have := D.y_pos 2
      omega
  · simp [w, Fin.sum_univ_succ]
    have hy0 := D.y_pos 0
    have hy1 := D.y_pos 1
    have hy2 := D.y_pos 2
    have hb1 := D.b_pos 1
    have hb2 := D.b_pos 2
    omega
  · simp [w, weight, X13, Y13, Fin.sum_univ_succ]
    rw [hu1]
    linear_combination -N * D.row0 - D.row1 - R * D.row2

/-- B.18.1, independently proved for the `{1,3}` orientation. -/
theorem terminal13_last_row2_of_prefix (D : BoxInput) (q : ℕ)
    (P : SuccessfulPrefix (D.x 0) (D.y 0 + D.b 0) (D.y 2)
      (D.x 2) (D.b 0) 0 q)
    (hq : 1 ≤ q) (hstart : D.x 0 < D.y 0 + D.b 0)
    (N : ℤ) (hN : N = P.N q) (u : Point)
    (hu0 : u 0 = P.E q) (hu2 : u 2 = D.x 2 + P.U q)
    (hu1 : u 1 = D.x 1 - (N - 1) * (D.y 1 + D.b 1) -
      (q : ℤ) * D.y 1)
    (hA : u 0 ≤ D.y 0 ∧ u 1 ≤ D.y 1 + D.b 1) : False := by
  have hres := P.residues q hq le_rfl
  have hqx := P.E_slot_count (by
    have hx := D.x_pos 0
    have hb := D.b_pos 0
    have he := hres.2.1
    omega)
  have hqy := P.U_slot_count (by have := D.y_pos 2; omega)
  subst N
  have hNq : P.N q - (q : ℤ) ≤ D.y 0 + D.b 0 - D.x 0 := by
    have hE := hres.1
    have hEx := hres.2.1
    have hx := D.x_pos 0
    have hb := D.b_pos 0
    have hprod : (q : ℤ) * (D.y 0 + D.b 0 - D.x 0) <
        D.x 0 * (D.y 0 + D.b 0 - D.x 0) := by nlinarith
    nlinarith
  have hLR := P.last_rank hq
  let w : Point := ![D.y 0 -
      (P.N q * D.x 0 - (q : ℤ) * (D.y 0 + D.b 0)),
    D.y 1 + D.b 1 - u 1,
    2 * D.y 2 + D.b 2 -
      ((q : ℤ) * D.x 2 - (P.N q - 1) * D.y 2)]
  have hEdef : P.E q = P.N q * D.x 0 -
      (q : ℤ) * (D.y 0 + D.b 0) := rfl
  have hUdef : P.U q = (q : ℤ) * D.x 2 - (P.N q - 1) * D.y 2 := rfl
  apply weighted_certificate_impossible D.m (P.N q + (q : ℤ) + 1) D.n w
    D.m_pos (by
      have hE := hres.1
      have := D.x_pos 0
      have := D.y_pos 0
      nlinarith) D.n_gt
  · intro i
    fin_cases i
    · simp [w]
      have huE : u 0 = P.N q * D.x 0 -
          (q : ℤ) * (D.y 0 + D.b 0) := hu0.trans hEdef
      omega
    · simp [w]
      omega
    · simp [w]
      have hU := hres.2.2.2
      have := D.y_pos 2
      have := D.b_pos 2
      omega
  · simp [w, Fin.sum_univ_succ]
    rw [hEdef, hUdef] at hLR
    have hb2 := D.b_pos 2
    omega
  · simp [w, weight, Fin.sum_univ_succ]
    rw [hu1]
    linear_combination -(P.N q) * D.row0 - D.row1 - (q : ℤ) * D.row2

/-- B.18.2 reciprocal-rank certificate for sink A. -/
theorem terminal13_sinkA_certificate (D : BoxInput) (N R : ℤ)
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hRy : R ≤ D.y 2)
    (u : Point)
    (hu1 : u 1 = D.x 1 - (N - 1) * (D.y 1 + D.b 1) - (R - 1) * D.y 1)
    (hA : u 0 ≤ D.y 0 ∧ u 1 ≤ D.y 1 + D.b 1)
    (hX : D.b 0 ≤ X13 D N R)
    (hcoef2 : 0 ≤ D.x 2 + D.y 2 + D.b 2 + Y13 D N R)
    (hrank : (N - R) + (-Y13 D N R) +
      ((D.y 0 + D.b 0 - D.x 0) - X13 D N R) ≤
      (D.x 2 - D.y 2) + (D.y 0 + D.b 0 - D.x 0) - D.b 0) : False := by
  let w : Point := ![X13 D N R - D.b 0,
    D.y 1 + D.b 1 - u 1,
    D.x 2 + D.y 2 + D.b 2 + Y13 D N R]
  apply weighted_certificate_impossible D.m (N + R) D.n w D.m_pos (by omega) D.n_gt
  · intro i
    fin_cases i
    · simp [w]; omega
    · simp [w]; omega
    · simpa [w]
  · simp [w, Fin.sum_univ_succ]
    have hb2 := D.b_pos 2
    omega
  · simp [w, weight, X13, Y13, Fin.sum_univ_succ]
    rw [hu1]
    linear_combination -N * D.row0 - D.row1 - (R - 1) * D.row2

/-- B.18.3 ELR certificate for sink C. -/
theorem terminal13_sinkC_certificate (D : BoxInput) (N R : ℤ)
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hNy : N ≤ D.y 0)
    (u : Point)
    (hu1 : u 1 = D.x 1 - (N - 1) * (D.y 1 + D.b 1) - (R - 1) * D.y 1)
    (hC : u 1 ≤ D.y 1 ∧ u 2 ≤ D.y 2 + D.b 2)
    (hcoef0 : 0 ≤ D.x 0 + D.y 0 + X13 D N R)
    (hY : -D.b 2 ≤ Y13 D N R)
    (hELR : 0 ≤ D.x 0 + X13 D N R + D.b 2 + Y13 D N R - R) : False := by
  let w : Point := ![D.x 0 + D.y 0 + X13 D N R,
    D.y 1 - u 1,
    D.b 2 + Y13 D N R]
  apply weighted_certificate_impossible D.m (N + R) D.n w D.m_pos (by omega) D.n_gt
  · intro i
    fin_cases i
    · simpa [w]
    · simp [w]; omega
    · simp [w]; omega
  · simp [w, Fin.sum_univ_succ]
    omega
  · simp [w, weight, X13, Y13, Fin.sum_univ_succ]
    rw [hu1]
    linear_combination -(N - 1) * D.row0 - D.row1 - R * D.row2

/-- B.18.3: the late successful residues occupy the two exact ELR strips.
The first `b₁` indices are discarded exactly as in the publication. -/
theorem terminal13_sinkC_ELR_bound (D : BoxInput) (q R : ℕ) (N : ℤ)
    (P : SuccessfulPrefix (D.x 0) (D.y 0 + D.b 0) (D.y 2)
      (D.x 2) (D.b 0) 0 q)
    (hR : R = q + 1)
    (hX : X13 D N R = (R : ℤ) * (D.y 0 + D.b 0) - N * D.x 0)
    (hY : Y13 D N R = N * D.y 2 - (R : ℤ) * D.x 2)
    (hpred : D.b 0 + 1 ≤ D.x 0 + X13 D N R)
    (hYlower : -D.b 2 ≤ Y13 D N R) :
    0 ≤ D.x 0 + X13 D N R + D.b 2 + Y13 D N R - (R : ℤ) := by
  by_cases hsmall : q ≤ D.b 0
  · have hb2 := D.b_pos 2
    omega
  let s := Finset.Icc (D.b 0).toNat.succ q
  let E : ℤ := -X13 D N R
  let U : ℤ := D.y 2 - D.b 2 - Y13 D N R - 1
  have hb0z : 0 ≤ D.b 0 := by have := D.b_pos 0; omega
  have hb0cast : (((D.b 0).toNat : ℕ) : ℤ) = D.b 0 := by
    simp [Int.toNat_of_nonneg hb0z]
  have hcover : ∀ i ∈ s, E < P.E i ∨ U < P.U i := by
    intro i hi
    have hir := Finset.mem_Icc.mp hi
    have hi1 : 1 ≤ i := by
      have hb := D.b_pos 0
      omega
    have hiq : i ≤ q := hir.2
    by_contra hn
    push Not at hn
    have hiR : i < R := by omega
    have hsub : ((R - i : ℕ) : ℤ) = (R : ℤ) - (i : ℤ) := by
      rw [Nat.cast_sub (by omega)]
    apply P.separator (R - i) (by omega) (by omega)
    refine ⟨N - P.N i, ?_, ?_⟩
    · have hEdef : P.E i = P.N i * D.x 0 -
          (i : ℤ) * (D.y 0 + D.b 0) := rfl
      rw [hEdef] at hn
      rw [hsub]
      dsimp [E] at hn
      nlinarith [hX]
    · have hUdef : P.U i = (i : ℤ) * D.x 2 -
          (P.N i - 1) * D.y 2 := rfl
      rw [hUdef] at hn
      rw [hsub]
      dsimp [U] at hn
      have hb2 := D.b_pos 2
      nlinarith [hY]
  have hEupper : ∀ i ∈ s, P.E i ≤ D.x 0 - D.b 0 - 1 := by
    intro i hi
    exact (P.residues i (by
      have hir := Finset.mem_Icc.mp hi
      have hb := D.b_pos 0
      omega) (Finset.mem_Icc.mp hi).2).2.1
  have hUupper : ∀ i ∈ s, P.U i ≤ D.y 2 - 1 := by
    intro i hi
    have hu := (P.residues i (by
      have hir := Finset.mem_Icc.mp hi
      have hb := D.b_pos 0
      omega) (Finset.mem_Icc.mp hi).2).2.2.2
    change (i : ℤ) * D.x 2 - (P.N i - 1) * D.y 2 ≤ D.y 2 - 1
    omega
  have hEinj : Set.InjOn P.E (s : Set ℕ) := by
    intro i hi j hj he
    exact P.coordinate_injective (by
      have hir := Finset.mem_Icc.mp hi; have hb := D.b_pos 0; omega)
      (Finset.mem_Icc.mp hi).2 (by
        have hjr := Finset.mem_Icc.mp hj; have hb := D.b_pos 0; omega)
      (Finset.mem_Icc.mp hj).2 he
  have hUinj : Set.InjOn P.U (s : Set ℕ) := by
    intro i hi j hj he
    exact P.coordinateU_injective (by
      have hir := Finset.mem_Icc.mp hi; have hb := D.b_pos 0; omega)
      (Finset.mem_Icc.mp hi).2 (by
        have hjr := Finset.mem_Icc.mp hj; have hb := D.b_pos 0; omega)
      (Finset.mem_Icc.mp hj).2 he
  have hc := residue_slot_bound s P.E P.U E U
    (D.x 0 - D.b 0 - 1) (D.y 2 - 1) hEupper hUupper hEinj hUinj hcover
  have hdE : 0 ≤ D.x 0 - D.b 0 - 1 - E := by dsimp [E]; omega
  have hdU : 0 ≤ D.y 2 - 1 - U := by dsimp [U]; omega
  have hcZ : (s.card : ℤ) ≤
      ((D.x 0 - D.b 0 - 1 - E).toNat : ℤ) +
      ((D.y 2 - 1 - U).toNat : ℤ) := by exact_mod_cast hc
  simp [s, E, U, Int.toNat_of_nonneg hdE, Int.toNat_of_nonneg hdU,
    hb0cast] at hcZ
  omega

set_option maxHeartbeats 2000000 in
/-- B.18.2 reciprocal rank.  The strict shifted bound is read from the
original chronological path, including the `K = 1` initial-run case. -/
theorem terminal13_reciprocal_rank (D : BoxInput)
    {l : List (Fin 3)} {u : Point} (ht : FiringTrace D.upper D.rows D.x l u)
    (hp : ProperNonzeroPredecessors l) (hno1 : l.count 1 = 0)
    (q R H N : ℕ)
    (P : SuccessfulPrefix (D.x 0) (D.y 0 + D.b 0) (D.y 2)
      (D.x 2) (D.b 0) 0 q)
    (hactual : ∀ h : ℕ, 1 ≤ h → h ≤ q → CrossingWitness l 2 h (P.N h))
    (hR : R = q + 1) (hN : N = H + R) (hH : 1 ≤ H)
    (hstart : D.x 0 < D.y 0)
    (hcount2 : l.count 2 = R - 1) (hcount0 : l.count 0 = N - 1)
    (hX : D.b 0 ≤ X13 D N R)
    (hE0 : 1 ≤ -Y13 D N R)
    (hEa : -Y13 D N R ≤ D.x 2 - D.y 2 - 1)
    (hV0 : 1 ≤ (D.y 0 + D.b 0 - D.x 0) - X13 D N R) :
    (H : ℤ) + (-Y13 D N R) +
      ((D.y 0 + D.b 0 - D.x 0) - X13 D N R) ≤
      (D.x 2 - D.y 2) + (D.y 0 + D.b 0 - D.x 0) - D.b 0 := by
  let a := D.x 2 - D.y 2
  let d := D.y 0 + D.b 0 - D.x 0
  have hd : 0 < d := by
    dsimp [d]
    have hb := D.b_pos 0
    omega
  have ha : 0 < a := by
    dsimp [a]
    have hx := D.x_pos 0
    have hB := P.B_pos
    nlinarith [P.corridor]
  have hNcast : (N : ℤ) = (H : ℤ) + (R : ℤ) := by exact_mod_cast hN
  have hbracket : (H : ℤ) * D.x 0 ≤ (R : ℤ) * d := by
    have hXN : (N : ℤ) * D.x 0 ≤ (R : ℤ) * (D.y 0 + D.b 0) := by
      have hb := D.b_pos 0
      simp only [X13] at hX
      omega
    dsimp [d]
    calc
      (H : ℤ) * D.x 0 = (N : ℤ) * D.x 0 - (R : ℤ) * D.x 0 := by
        rw [hNcast]; ring
      _ ≤ (R : ℤ) * (D.y 0 + D.b 0) - (R : ℤ) * D.x 0 :=
        sub_le_sub_right hXN _
      _ = (R : ℤ) * (D.y 0 + D.b 0 - D.x 0) := by ring
  have hcolors : ∀ i ∈ l, i = 0 ∨ i = 2 := by
    intro i hi
    fin_cases i
    · exact Or.inl rfl
    · have : (1 : Fin 3) ∈ l := hi
      rw [List.count_eq_zero] at hno1
      exact (hno1 this).elim
    · exact Or.inr rfl
  have hstrict : ∀ s : ℕ, 1 ≤ s → s ≤ H - 1 →
      let K := ((s : ℤ) * D.y 2) / a + 1
      (s : ℤ) * D.x 0 - (K - 1) * d ≤ d - D.b 0 - 1 := by
    intro s hs hsH
    dsimp
    let qz : ℤ := ((s : ℤ) * D.y 2) / a
    have hsB : 0 < (s : ℤ) * D.y 2 := mul_pos (by exact_mod_cast hs) P.B_pos
    have ha0 : a ≠ 0 := ne_of_gt ha
    have hdecomp := Int.ediv_mul_add_emod ((s : ℤ) * D.y 2) a
    have hrem0 := Int.emod_nonneg ((s : ℤ) * D.y 2) ha0
    have hrema := Int.emod_lt_of_pos ((s : ℤ) * D.y 2) ha
    have hq0 : 0 ≤ qz := Int.ediv_nonneg hsB.le ha.le
    let K : ℕ := (qz + 1).toNat
    have hKcast : (K : ℤ) = qz + 1 := by
      simp [K, Int.toNat_of_nonneg (by omega : 0 ≤ qz + 1)]
    have hKz : (1 : ℤ) ≤ (K : ℤ) := by rw [hKcast]; omega
    have hK : 1 ≤ K := by exact_mod_cast hKz
    have hfirst : (s : ℤ) * D.y 2 ≤ (K : ℤ) * a := by
      rw [hKcast]
      dsimp [qz]
      nlinarith
    have hKR : K ≤ R := by
      by_contra hn
      push Not at hn
      have hfloor : (K : ℤ) * a - a ≤ (s : ℤ) * D.y 2 := by
        rw [hKcast]
        dsimp [qz]
        nlinarith
      have hRa : (R : ℤ) * a ≤ (s : ℤ) * D.y 2 := by
        have hcast : (R : ℤ) ≤ (K : ℤ) - 1 := by exact_mod_cast (show R ≤ K - 1 by omega)
        nlinarith
      have hcorr := P.corridor
      have hslt : (s : ℤ) * D.x 0 < (H : ℤ) * D.x 0 := by
        have hx := P.x_pos
        have : (s : ℤ) < (H : ℤ) := by exact_mod_cast (show s < H by omega)
        nlinarith
      have hsZ : (0 : ℤ) < (s : ℤ) := by exact_mod_cast hs
      have hscaled := mul_lt_mul_of_pos_left P.corridor hsZ
      nlinarith
    have hVweak : (s : ℤ) * D.x 0 - ((K : ℤ) - 1) * d ≤ d - 1 := by
      by_contra hn
      push Not at hn
      have hsecond : (K : ℤ) * d ≤ (s : ℤ) * D.x 0 := by nlinarith
      exact (P.reciprocal_separator ha hd hR hbracket s K hs (by omega) hK)
        ⟨hfirst, hsecond⟩
    let V : ℤ := (s : ℤ) * D.x 0 - ((K : ℤ) - 1) * d
    have hV0' : 1 ≤ V := by
      dsimp [V, d]
      have hfloor : (K : ℤ) * a - a ≤ (s : ℤ) * D.y 2 := by
        rw [hKcast]
        dsimp [qz]
        nlinarith
      have hcorr := P.corridor
      have hsZ : (0 : ℤ) < (s : ℤ) := by exact_mod_cast hs
      have hscaled := mul_lt_mul_of_pos_left P.corridor hsZ
      nlinarith
    obtain ⟨p, state, hstate, hpref, hp0, hp2, plast, hplast⟩ :=
      reciprocal_residue_actual P ht 2 (by decide) hactual hR hN hcount2 hcount0
        s K hs (by omega) hK hKR V rfl hV0' (by simpa [V] using hVweak)
    have hstate0 : execute D.rows p D.x 0 = D.x 0 + V := by
      have heq := hstate.endpoint_eq_sub_sum 0
      have hp1 : p.count 1 = 0 := by
        rw [List.count_eq_zero]
        intro hm
        have := hpref.sublist.mem hm
        rw [List.count_eq_zero] at hno1
        exact hno1 this
      rw [hstate.execute_eq, heq]
      simp [Fin.sum_univ_succ, BoxInput.rows, hp1, hp0, hp2]
      dsimp [V, d]
      rw [Nat.cast_sub (by omega : 1 ≤ s + K), Nat.cast_sub hK]
      rw [Nat.cast_add]
      ring
    have hnext : p ++ [0] <+: l := by
      by_cases hKlt : K < R
      · have hKq : K ≤ q := by omega
        obtain ⟨source, tail, hsplit, hsource2, hsource0⟩ := hactual K hK hKq
        have hsource : source <+: l := ⟨2 :: tail, by simpa using hsplit.symm⟩
        have hpSource : p <+: source := by
          rcases List.prefix_or_prefix_of_prefix hpref hsource with h | h
          · exact h
          · have hc := h.count_le 0
            have hE := (P.residues K hK hKq).1
            have hx := P.x_pos
            have hsx : ((s + K : ℕ) : ℤ) * D.x 0 < (K : ℤ) * (D.y 0 + D.b 0) := by
              push_cast
              dsimp [V, d] at hVweak
              nlinarith
            have : ((s + K : ℕ) : ℤ) < P.N K :=
              (Int.mul_lt_mul_right hx).mp (by nlinarith)
            have hltNat : s + K < source.count 0 + 1 := by
              exact_mod_cast (show ((s + K : ℕ) : ℤ) <
                (source.count 0 : ℤ) + 1 by rw [← hsource0]; exact this)
            omega
        apply prefix_continues_zero hpSource hsource hcolors (by decide)
        · omega
        · have hE := (P.residues K hK hKq).1
          have hx := P.x_pos
          have hsx : ((s + K : ℕ) : ℤ) * D.x 0 <
              (K : ℤ) * (D.y 0 + D.b 0) := by
            push_cast
            dsimp [V, d] at hVweak
            nlinarith
          have hlt : ((s + K : ℕ) : ℤ) < P.N K :=
            (Int.mul_lt_mul_right hx).mp (by nlinarith)
          have hltNat : s + K < source.count 0 + 1 := by
            exact_mod_cast (show ((s + K : ℕ) : ℤ) <
              (source.count 0 : ℤ) + 1 by rw [← hsource0]; exact hlt)
          omega
      · have hKR' : K = R := by omega
        apply prefix_continues_zero hpref (List.prefix_refl l) hcolors (by decide)
        · omega
        · omega
    have hv := continued_zero_shift_bound D ht hnext V hstate0
    have hKm : (K : ℤ) - 1 = qz := by omega
    dsimp [V, d] at hv ⊢
    rw [hKm] at hv
    convert hv using 1 <;> simp [qz] <;> ring
  let DP := P.dual_prefix_of_actuality ha hd hR hbracket (by
    simpa [a, d] using hstrict)
  have hEnext : -Y13 D N R = (R : ℤ) * a - (H : ℤ) * D.y 2 := by
    simp [Y13, a]
    rw [hNcast]
    ring
  have hVnext : (D.y 0 + D.b 0 - D.x 0) - X13 D N R =
      (H : ℤ) * D.x 0 - ((R : ℤ) - 1) * d := by
    simp [X13, d]
    rw [hNcast]
    ring
  have hVd : (D.y 0 + D.b 0 - D.x 0) - X13 D N R ≤ d - D.b 0 := by
    dsimp [d]
    omega
  simpa [a, d] using
    DP.dual_next_residue_rank hH hEnext hVnext hE0 (by simpa [a] using hEa)
      hV0 (by simpa [d] using hVd)

/-- Appendix B.18 assembled independently on the actual chronological
`{1,3}` trace. -/
theorem two_color13_trace_sink_impossible (D : BoxInput)
    {l : List (Fin 3)} {u : Point}
    (ht : FiringTrace D.upper D.rows D.x l u)
    (hp : ProperNonzeroPredecessors l) (hno1 : l.count 1 = 0)
    (hcount2 : 1 ≤ l.count 2) (hstart : D.x 0 < D.y 0)
    (hsink : ¬ ∃ i, ∀ j, 1 ≤ fire D.rows i u j) : False := by
  let Nn : ℕ := l.count 0 + 1
  let Rn : ℕ := l.count 2 + 1
  let N : ℤ := Nn
  let R : ℤ := Rn
  have hN : 1 ≤ N := by simp [N, Nn]
  have hR : 1 ≤ R := by simp [R, Rn]
  have hbounds := terminal13_count_bounds D ht hp hno1 hcount2 hstart
  have hNy : N ≤ D.y 0 := by simpa [N, Nn] using hbounds.1
  have hRx : R ≤ D.x 0 - D.b 0 := by simpa [R, Rn] using hbounds.2.1
  have hRy : R ≤ D.y 2 := by simpa [R, Rn] using hbounds.2.2
  have hut := trace_terminal13 D ht hno1
  have hcoords := terminal13Point_coordinates D Nn Rn
  have hu0 : u 0 = D.y 0 + D.b 0 - X13 D N R := by
    rw [hut]
    simpa [N, R, Nn, Rn, X13] using hcoords.1
  have hu1 : u 1 = D.x 1 - (N - 1) * (D.y 1 + D.b 1) -
      (R - 1) * D.y 1 := by
    rw [hut]
    simpa [N, R] using hcoords.2.1
  have hu2 : u 2 = D.y 2 - Y13 D N R := by
    rw [hut]
    simpa [N, R, Nn, Rn, Y13] using hcoords.2.2
  have huPos : ∀ j, 1 ≤ u j := fun j => (ht.endpoint_inBox j).1
  have hAC_impossible :
      ((u 0 ≤ D.y 0 ∧ u 1 ≤ D.y 1 + D.b 1) ∨
       (u 1 ≤ D.y 1 ∧ u 2 ≤ D.y 2 + D.b 2)) → False := by
    intro hsinkRegion
    have hne : l ≠ [] := by
      intro he
      subst l
      simp at hcount2
    generalize hlastEq : l.getLast hne = last
    have hlastSome := List.getLast?_eq_getLast hne
    rw [hlastEq] at hlastSome
    rw [List.getLast?_eq_some_iff] at hlastSome
    obtain ⟨pre, hlast⟩ := hlastSome
    change l = pre ++ [last] at hlast
    let q : ℕ := l.count 2
    let P := trace_successfulPrefix13 D ht hp hno1 (q := q) (by simp [q])
    have hq : 1 ≤ q := by simpa [q] using hcount2
    have hactual := trace_successfulPrefix13_actual D ht hp hno1
      (q := q) (by simp [q])
    fin_cases last
    · obtain ⟨v, hv⟩ := ht.prefix_trace (show pre <+: l by
          refine ⟨[0], ?_⟩
          simpa using hlast.symm)
      have hfire : u = fire D.rows 0 v := by
        rw [← ht.execute_eq, ← hv.execute_eq, hlast]
        simp [execute_append]
      have hf0 := congrFun hfire 0
      have hf2 := congrFun hfire 2
      simp [fire, BoxInput.rows] at hf0 hf2
      have hv0 := hv.endpoint_inBox 0
      have hv2 := hv.endpoint_inBox 2
      dsimp [BoxInput.upper] at hv0 hv2
      rcases hsinkRegion with hA | hC
      · have hX : D.b 0 ≤ X13 D N R := by omega
        have hYneg : Y13 D N R < 0 := by
          by_contra hn
          push Not at hn
          exact terminal13_not_sinkB D N R (by omega) ⟨by
            have := D.b_pos 0
            omega, hn⟩
        have hE0 : 1 ≤ -Y13 D N R := by omega
        have hEa : -Y13 D N R ≤ D.x 2 - D.y 2 - 1 := by omega
        have hV0 : 1 ≤ (D.y 0 + D.b 0 - D.x 0) - X13 D N R := by omega
        have hlt := hp.count_lt_zero_of_last_zero (by simpa using hlast) 2 (by decide)
        let H : ℕ := Nn - Rn
        have hHN : Nn = H + Rn := by dsimp [H, Nn, Rn]; omega
        have hH : 1 ≤ H := by dsimp [H, Nn, Rn]; omega
        have hrank := terminal13_reciprocal_rank D ht hp hno1 q Rn H Nn P
          hactual (by simp [q, Rn]) hHN hH hstart
          (by simp [Rn]) (by simp [Nn]) (by simpa [N, R] using hX)
          (by simpa [N, R] using hE0) (by simpa [N, R] using hEa)
          (by simpa [N, R] using hV0)
        have hRN : Rn ≤ Nn := by omega
        rw [Nat.cast_sub hRN] at hrank
        have hcoef2 : 0 ≤ D.x 2 + D.y 2 + D.b 2 + Y13 D N R := by
          have huUpper := (ht.endpoint_inBox 2).2
          dsimp [BoxInput.upper] at huUpper
          have hb := D.b_pos 2
          omega
        exact terminal13_sinkA_certificate D N R hN hR hRy u hu1 hA hX hcoef2
          (by simpa [N, R, H] using hrank)
      · have hY : -D.b 2 ≤ Y13 D N R := by omega
        have hpred : D.b 0 + 1 ≤ D.x 0 + X13 D N R := by
          have huUpper := (ht.endpoint_inBox 0).2
          dsimp [BoxInput.upper] at huUpper
          omega
        have hELR := terminal13_sinkC_ELR_bound D q Rn N P (by simp [q, Rn])
          (by simp [X13, N, R, Nn, Rn]) (by simp [Y13, N, R, Nn, Rn])
          (by simpa [N, R] using hpred) (by simpa [N, R] using hY)
        have hcoef0 : 0 ≤ D.x 0 + D.y 0 + X13 D N R := by
          have hx := D.x_pos 0
          have hy := D.y_pos 0
          have hb := D.b_pos 0
          nlinarith [hpred]
        exact terminal13_sinkC_certificate D N R hN hR hNy u hu1 hC hcoef0 hY
          (by simpa [N, R] using hELR)
    · have hm : (1 : Fin 3) ∈ l := by rw [hlast]; simp
      rw [List.count_eq_zero] at hno1
      exact (hno1 hm).elim
    · have hw := hactual q hq le_rfl
      have hPN := hw.at_last (by decide) (by simpa using hlast)
      have hu0E : u 0 = P.E q := by
        rw [hu0]
        simp [X13, SuccessfulPrefix.E, P, q, N, R, Nn, Rn]
        rw [hPN]
        push_cast
        ring
      have hu2U : u 2 = D.x 2 + P.U q := by
        rw [hu2]
        simp [Y13, SuccessfulPrefix.U, P, q, N, R, Nn, Rn]
        rw [hPN]
        push_cast
        ring
      have hNPN : N = P.N q := by simpa [N, Nn] using hPN.symm
      have hstartA : D.x 0 < D.y 0 + D.b 0 := by
        have hb := D.b_pos 0
        omega
      have hu1q : u 1 = D.x 1 - (N - 1) * (D.y 1 + D.b 1) -
          (q : ℤ) * D.y 1 := by
        simpa [R, Rn, q] using hu1
      rcases hsinkRegion with hA | hC
      · exact terminal13_last_row2_of_prefix D q P hq hstartA N hNPN u
          hu0E hu2U hu1q hA
      · have hA' : u 0 ≤ D.y 0 ∧ u 1 ≤ D.y 1 + D.b 1 := by
          constructor
          · have hEupper := (P.residues q hq le_rfl).2.1
            have hb := D.b_pos 0
            calc
              u 0 = P.E q := hu0E
              _ ≤ D.x 0 - D.b 0 - 1 := hEupper
              _ ≤ D.y 0 := by omega
          · have hb := D.b_pos 1
            omega
        exact terminal13_last_row2_of_prefix D q P hq hstartA N hNPN u
          hu0E hu2U hu1q hA'
  rcases D.sink_cover u huPos hsink with hA | hB | hC | hD
  · exact hAC_impossible (Or.inl hA)
  · apply terminal13_not_sinkB D N R (by omega)
    constructor <;> omega
  · exact hAC_impossible (Or.inr hC)
  · exact terminal13_sinkD_impossible D N R hN hR hNy hRy u hu0 hu1 hu2 hD

end P21.Nonsymmetric.ColorCap
