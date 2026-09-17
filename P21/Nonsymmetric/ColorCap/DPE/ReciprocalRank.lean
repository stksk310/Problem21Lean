import P21.Nonsymmetric.ColorCap.DPE.Canonical

namespace P21.Nonsymmetric.ColorCap

/-- `K < Q`: the shifted original count pair is an actual prefix before the
`K`-th successful crossing.  The `K = 1` branch uses the initial row-zero run
and never asks for a crossing numbered zero. -/
theorem actual_shifted_before_crossing
    {x A B v b c : ℤ} {q : ℕ}
    (P : SuccessfulPrefix x A B v b c q)
    {l : List (Fin 3)} {upper : Point} {C : Fin 3 → Point}
    {start endpoint : Point} (ht : FiringTrace upper C start l endpoint)
    (r : Fin 3) (hr : r ≠ 0)
    (hactual : ∀ h : ℕ, 1 ≤ h → h ≤ q → CrossingWitness l r h (P.N h))
    (K Ns : ℕ) (hK : 1 ≤ K) (hKq : K ≤ q) (hNs : 2 ≤ Ns)
    (hupperN : (Ns : ℤ) < P.N K)
    (hlowerN : K = 1 ∨ P.N (K - 1) < (Ns : ℤ)) :
    ∃ p state, FiringTrace upper C start p state ∧
      p.count 0 = Ns - 1 ∧ p.count r = K - 1 ∧ ∃ a, p = a ++ [0] := by
  obtain ⟨source, tail, hsplit, hsourceR, hsource0⟩ := hactual K hK hKq
  have hsourcePrefix : source <+: l := by
    refine ⟨r :: tail, ?_⟩
    simpa using hsplit.symm
  have htargetUpper : Ns - 1 ≤ source.count 0 := by
    have hNsCast : ((Ns - 1 : ℕ) : ℤ) = (Ns : ℤ) - 1 := by omega
    have hint : ((Ns - 1 : ℕ) : ℤ) ≤ (source.count 0 : ℤ) := by
      rw [hNsCast]
      omega
    exact_mod_cast hint
  have hlower : K = 1 ∨ ∃ lower, lower <+: l ∧
      lower.count r = K - 1 ∧ lower.count 0 < Ns - 1 := by
    by_cases hK1 : K = 1
    · exact Or.inl hK1
    · have hprevN : P.N (K - 1) < (Ns : ℤ) := by
        rcases hlowerN with h | h
        · contradiction
        · exact h
      have hKm1 : 1 ≤ K - 1 := by omega
      have hKm1q : K - 1 ≤ q := by omega
      obtain ⟨prev, rest, hprevSplit, hprevR, hprev0⟩ := hactual (K - 1) hKm1 hKm1q
      let lower := prev ++ [r]
      refine Or.inr ⟨lower, ?_, ?_, ?_⟩
      · refine ⟨rest, ?_⟩
        simpa [lower, List.append_assoc] using hprevSplit.symm
      · simp [lower, hprevR, hr]
        omega
      · have hNsCast : ((Ns - 1 : ℕ) : ℤ) = (Ns : ℤ) - 1 := by omega
        have hint : (prev.count 0 : ℤ) < ((Ns - 1 : ℕ) : ℤ) := by
          rw [hNsCast]
          omega
        simp [lower, hr]
        exact_mod_cast hint
  obtain ⟨p, hp, hp0, hpR, a, ha⟩ := shifted_prefix_actual l r K (Ns - 1) hK
    source hsourcePrefix hsourceR (by omega) htargetUpper hlower
  obtain ⟨state, hstate⟩ := ht.prefix_trace hp
  exact ⟨p, state, hstate, hp0, hpR, a, ha⟩

/-- `K = Q`: the shifted state lies on the current terminal row-zero run.
For `Q = 1` this again uses the initial run directly. -/
theorem actual_shifted_terminal
    {x A B v b c : ℤ} {q Q : ℕ}
    (P : SuccessfulPrefix x A B v b c q)
    {l : List (Fin 3)} {upper : Point} {C : Fin 3 → Point}
    {start endpoint : Point} (ht : FiringTrace upper C start l endpoint)
    (r : Fin 3) (hr : r ≠ 0)
    (hactual : ∀ h : ℕ, 1 ≤ h → h ≤ q → CrossingWitness l r h (P.N h))
    (hQ : Q = q + 1) (N Ns : ℕ)
    (hcountR : l.count r = Q - 1) (hcount0 : l.count 0 = N - 1)
    (hNs : 2 ≤ Ns) (hNsN : Ns < N)
    (hlowerN : Q = 1 ∨ P.N (Q - 1) < (Ns : ℤ)) :
    ∃ p state, FiringTrace upper C start p state ∧
      p.count 0 = Ns - 1 ∧ p.count r = Q - 1 ∧ ∃ a, p = a ++ [0] := by
  have htargetUpper : Ns - 1 ≤ l.count 0 := by omega
  have hlower : Q = 1 ∨ ∃ lower, lower <+: l ∧
      lower.count r = Q - 1 ∧ lower.count 0 < Ns - 1 := by
    by_cases hQ1 : Q = 1
    · exact Or.inl hQ1
    · have hprevN : P.N (Q - 1) < (Ns : ℤ) := by
        rcases hlowerN with h | h
        · contradiction
        · exact h
      have hqm : Q - 1 = q := by omega
      have hq1 : 1 ≤ q := by omega
      obtain ⟨prev, rest, hsplit, hprevR, hprev0⟩ := hactual q hq1 le_rfl
      let lower := prev ++ [r]
      refine Or.inr ⟨lower, ?_, ?_, ?_⟩
      · refine ⟨rest, ?_⟩
        simpa [lower, List.append_assoc] using hsplit.symm
      · simp [lower, hprevR, hqm, hr]
        omega
      · have hNsCast : ((Ns - 1 : ℕ) : ℤ) = (Ns : ℤ) - 1 := by omega
        have hint : (prev.count 0 : ℤ) < ((Ns - 1 : ℕ) : ℤ) := by
          rw [hNsCast]
          rw [hqm] at hprevN
          omega
        simp [lower, hr]
        exact_mod_cast hint
  obtain ⟨p, hp, hp0, hpR, a, ha⟩ := shifted_prefix_actual l r Q (Ns - 1)
    (by omega) l (by rfl) hcountR (by omega) htargetUpper hlower
  obtain ⟨state, hstate⟩ := ht.prefix_trace hp
  exact ⟨p, state, hstate, hp0, hpR, a, ha⟩

/-- Appendix B.2.4.2 in path form.  A dual residue `(s,K)` is sent back to
the original count pair `(s+K-1,K-1)` and an actual chronological state.
The proof explicitly separates `K<Q`, `K=Q`, and the predecessor-free
`K=1` initial-run boundary. -/
theorem reciprocal_residue_actual
    {x A B v b c : ℤ} {q Q H N : ℕ}
    (P : SuccessfulPrefix x A B v b c q)
    {l : List (Fin 3)} {upper : Point} {C : Fin 3 → Point}
    {start endpoint : Point} (ht : FiringTrace upper C start l endpoint)
    (r : Fin 3) (hr : r ≠ 0)
    (hactual : ∀ h : ℕ, 1 ≤ h → h ≤ q → CrossingWitness l r h (P.N h))
    (hQ : Q = q + 1) (hN : N = H + Q)
    (hcountR : l.count r = Q - 1) (hcount0 : l.count 0 = N - 1)
    (s K : ℕ) (hs : 1 ≤ s) (hsH : s < H)
    (hK : 1 ≤ K) (hKQ : K ≤ Q)
    (V : ℤ) (hV : V = (s : ℤ) * x - ((K : ℤ) - 1) * (A - x))
    (hV0 : 1 ≤ V) (hVd : V ≤ A - x - 1) :
    ∃ p state, FiringTrace upper C start p state ∧
      p.count 0 = s + K - 1 ∧ p.count r = K - 1 ∧ ∃ a, p = a ++ [0] := by
  have hNs : 2 ≤ s + K := by omega
  by_cases hKQlt : K < Q
  · have hKq : K ≤ q := by omega
    have hupperN : ((s + K : ℕ) : ℤ) < P.N K := by
      have hE := (P.residues K hK hKq).1
      have hx := P.x_pos
      have hsx : ((s + K : ℕ) : ℤ) * x < (K : ℤ) * A := by
        push_cast
        nlinarith [hVd]
      have hPK : (K : ℤ) * A < P.N K * x := by nlinarith
      exact (Int.mul_lt_mul_right hx).mp (lt_trans hsx hPK)
    have hlowerN : K = 1 ∨ P.N (K - 1) < ((s + K : ℕ) : ℤ) := by
      by_cases hK1 : K = 1
      · exact Or.inl hK1
      · right
        have hKm1 : 1 ≤ K - 1 := by omega
        have hKm1q : K - 1 ≤ q := by omega
        have hEprev := (P.residues (K - 1) hKm1 hKm1q).1
        have hEprevUpper := (P.residues (K - 1) hKm1 hKm1q).2.1
        have hx := P.x_pos
        have hid : ((s + K : ℕ) : ℤ) * x -
            ((K - 1 : ℕ) : ℤ) * A - x = V := by
          push_cast
          rw [Nat.cast_sub (by omega : 1 ≤ K)]
          rw [hV]
          ring
        have hgt : P.N (K - 1) * x < ((s + K : ℕ) : ℤ) * x := by
          nlinarith [hid, hEprevUpper, hV0, P.b_nonneg]
        exact (Int.mul_lt_mul_right hx).mp hgt
    simpa [Nat.add_sub_cancel] using
      actual_shifted_before_crossing P ht r hr hactual K (s + K) hK hKq hNs hupperN hlowerN
  · have hKeq : K = Q := by omega
    subst K
    have hNsN : s + Q < N := by omega
    have hlowerN : Q = 1 ∨ P.N (Q - 1) < ((s + Q : ℕ) : ℤ) := by
      by_cases hQ1 : Q = 1
      · exact Or.inl hQ1
      · right
        have hqm : Q - 1 = q := by omega
        have hq1 : 1 ≤ q := by omega
        have hEprev := (P.residues q hq1 le_rfl).1
        have hEprevUpper := (P.residues q hq1 le_rfl).2.1
        have hx := P.x_pos
        have hEprev' : 0 < P.N (Q - 1) * x - ((Q - 1 : ℕ) : ℤ) * A := by
          simpa [hqm] using hEprev
        have hEprevUpper' : P.N (Q - 1) * x - ((Q - 1 : ℕ) : ℤ) * A ≤ x - b - 1 := by
          simpa [hqm] using hEprevUpper
        have hid : ((s + Q : ℕ) : ℤ) * x -
            ((Q - 1 : ℕ) : ℤ) * A - x = V := by
          push_cast
          rw [Nat.cast_sub (by omega : 1 ≤ Q)]
          rw [hV]
          ring
        have hgt : P.N (Q - 1) * x < ((s + Q : ℕ) : ℤ) * x := by
          nlinarith [hid, hEprevUpper', hV0, P.b_nonneg]
        exact (Int.mul_lt_mul_right hx).mp hgt
    simpa [Nat.add_sub_cancel] using
      actual_shifted_terminal P ht r hr hactual hQ N (s + Q) hcountR hcount0 hNs hNsN hlowerN

end P21.Nonsymmetric.ColorCap

namespace P21.Nonsymmetric.ColorCap.SuccessfulPrefix

/-- Build the finite dual prefix by Euclidean ceiling.  The final `V` bound
is supplied by the proved original-path correspondence, rather than by a
formal symmetry argument. -/
noncomputable def dual_prefix_of_actuality
    {x A B v b c : ℤ} {q H Q : ℕ}
    (P : SuccessfulPrefix x A B v b c q)
    (ha : 0 < v - B) (hd : 0 < A - x) (hQ : Q = q + 1)
    (hbracket : (H : ℤ) * x ≤ (Q : ℤ) * (A - x))
    (hactualV : ∀ s : ℕ, 1 ≤ s → s ≤ H - 1 →
      let K := ((s : ℤ) * B) / (v - B) + 1
      (s : ℤ) * x - (K - 1) * (A - x) ≤ A - x - b - 1) :
    SuccessfulPrefix (v - B) B (A - x) x 0 b (H - 1) := by
  let a := v - B
  let d := A - x
  let K : ℕ → ℤ := fun s => ((s : ℤ) * B) / a + 1
  refine {
    N := K
    x_pos := ha
    B_pos := hd
    b_nonneg := by omega
    c_nonneg := P.b_nonneg
    corridor := by change B * (A - x) < (v - B) * x; nlinarith [P.corridor]
    residues := ?_ }
  intro s hs hsH
  have hslt : s < H := by omega
  have hsB : 0 < (s : ℤ) * B := mul_pos (by exact_mod_cast hs) P.B_pos
  have ha0 : a ≠ 0 := ne_of_gt ha
  let qz : ℤ := ((s : ℤ) * B) / a
  have hq0 : 0 ≤ qz := Int.ediv_nonneg hsB.le ha.le
  have hdecomp := Int.ediv_mul_add_emod ((s : ℤ) * B) a
  have hrem0 := Int.emod_nonneg ((s : ℤ) * B) ha0
  have hrema := Int.emod_lt_of_pos ((s : ℤ) * B) ha
  have hrempos : 0 < ((s : ℤ) * B) % a := by
    by_contra hn
    have hremzero : ((s : ℤ) * B) % a = 0 := by omega
    have hqpos : 1 ≤ qz := by nlinarith
    have hcdual : B * d < a * x := by dsimp [a, d]; nlinarith [P.corridor]
    have hsZ : 0 < (s : ℤ) := by exact_mod_cast hs
    have hscaled := mul_pos hsZ (sub_pos.mpr hcdual)
    have hqa : qz * a = (s : ℤ) * B := by nlinarith
    have hmul : qz * d * a < (s : ℤ) * x * a := by nlinarith
    have hqd : qz * d < (s : ℤ) * x := (Int.mul_lt_mul_right ha).mp (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)
    have hsxH : (s : ℤ) * x < (H : ℤ) * x := by
      exact (Int.mul_lt_mul_right P.x_pos).2 (by exact_mod_cast hslt)
    have hqQ : qz < (Q : ℤ) := by
      have hqdQd : qz * d < (Q : ℤ) * d := lt_of_lt_of_le (lt_trans hqd hsxH) hbracket
      exact (Int.mul_lt_mul_right hd).mp hqdQd
    have hkNat : ((qz.toNat : ℕ) : ℤ) = qz := by simp [Int.toNat_of_nonneg hq0]
    have hkqz : qz ≤ (q : ℤ) := by omega
    have hkq : qz.toNat ≤ q := by
      have hint : ((qz.toNat : ℕ) : ℤ) ≤ (q : ℤ) := by simpa [hkNat] using hkqz
      exact_mod_cast hint
    have hkpos : 1 ≤ qz.toNat := by
      have hint : (1 : ℤ) ≤ ((qz.toNat : ℕ) : ℤ) := by simpa [hkNat] using hqpos
      exact_mod_cast hint
    apply P.separator qz.toNat hkpos hkq
    refine ⟨qz + (s : ℤ), ?_, ?_⟩
    · rw [hkNat]
      dsimp [d] at hqd
      nlinarith
    · rw [hkNat]
      dsimp [a] at hqa
      nlinarith
  have hE0 : 0 < K s * a - (s : ℤ) * B := by
    dsimp [K, qz]
    nlinarith [hdecomp, hrempos]
  have hEa : K s * a - (s : ℤ) * B ≤ a - 1 := by
    dsimp [K, qz]
    have hrema' : ((s : ℤ) * B) % a < a := by simpa [a] using hrema
    nlinarith [hdecomp, hrema']
  have hV0 : 0 < (s : ℤ) * x - (K s - 1) * d := by
    have hcdual : B * d < a * x := by dsimp [a, d]; nlinarith [P.corridor]
    have hsZ : 0 < (s : ℤ) := by exact_mod_cast hs
    have hscaled := mul_pos hsZ (sub_pos.mpr hcdual)
    have hqa := Int.ediv_mul_le ((s : ℤ) * B) ha0
    have hqad : qz * a * d ≤ (s : ℤ) * B * d := by
      dsimp [qz]
      exact mul_le_mul_of_nonneg_right hqa hd.le
    have hmul : qz * d * a < (s : ℤ) * x * a := by
      nlinarith [hqad, hscaled]
    have hqd : qz * d < (s : ℤ) * x := (Int.mul_lt_mul_right ha).mp (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)
    dsimp [K]
    nlinarith
  have hVupper := hactualV s hs hsH
  change (s : ℤ) * x - (K s - 1) * d ≤ d - b - 1 at hVupper
  simpa [a, d] using And.intro hE0 (And.intro hEa (And.intro hV0 hVupper))

/-- The dual PREFIX is an algebraic consequence of the original successful
PREFIX.  Its denominator `k` is bounded by the original chronological range;
no symmetric or imaginary path is introduced. -/
theorem reciprocal_separator {x A B v b c : ℤ} {q H Q : ℕ}
    (P : SuccessfulPrefix x A B v b c q)
    (ha : 0 < v - B) (hd : 0 < A - x) (hQ : Q = q + 1)
    (hbracket : (H : ℤ) * x ≤ (Q : ℤ) * (A - x)) :
    ∀ s k : ℕ, 1 ≤ s → s < H → 1 ≤ k →
      ¬ ((s : ℤ) * B ≤ (k : ℤ) * (v - B) ∧
         (k : ℤ) * (A - x) ≤ (s : ℤ) * x) := by
  intro s k hs hsH hk hdual
  have hx := P.x_pos
  have hsd : (s : ℤ) * x < (H : ℤ) * x := by
    have : (s : ℤ) < (H : ℤ) := by exact_mod_cast hsH
    nlinarith
  have hkQ : k < Q := by
    have hkQi : (k : ℤ) < (Q : ℤ) := by
      nlinarith [mul_pos (show (0 : ℤ) < (Q : ℤ) - (k : ℤ) by
        by_contra hn; push Not at hn; nlinarith) hd]
    exact_mod_cast hkQi
  have hkq : k ≤ q := by omega
  apply P.separator k hk hkq
  refine ⟨(k : ℤ) + (s : ℤ), ?_, ?_⟩
  · nlinarith
  · nlinarith

/-- DR slot count, including the upper boundary `V = d-b`.  The supplied
dual prefix contains only residues already certified by the path layer. -/
theorem dual_rank {a B d x b : ℤ} {q H : ℕ}
    (P : SuccessfulPrefix a B d x 0 b q) (hH : H = q + 1)
    {E V : ℤ} (hE0 : 1 ≤ E) (hEa : E ≤ a - 1)
    (hV0 : 1 ≤ V) (hVd : V ≤ d - b)
    (hcover : ∀ i : ℕ, 1 ≤ i → i ≤ q → E < P.E i ∨ V < P.U i) :
    (H : ℤ) + E + V ≤ a + d - b := by
  by_cases hv : V ≤ d - b - 1
  · have hr := P.terminal_rank hE0 (by simpa using hEa) hV0 hv hcover
    omega
  · have hveq : V = d - b := by omega
    by_cases hq0 : q = 0
    · subst q
      norm_num at hH
      omega
    have hq1 : 1 ≤ q := by omega
    have hcover' : ∀ i : ℕ, 1 ≤ i → i ≤ q →
        E < P.E i ∨ d - b - 1 < P.U i := by
      intro i hi hiq
      rcases hcover i hi hiq with he | hu
      · exact Or.inl he
      · have hui := (P.residues i hi hiq).2.2.2
        omega
    have hr := P.terminal_rank hE0 (by simpa using hEa)
      (show 1 ≤ d - b - 1 by
        have hU := (P.residues 1 (by omega) hq1).2.2.1
        have hUb := (P.residues 1 (by omega) hq1).2.2.2
        omega)
      (le_rfl) hcover'
    omega

end P21.Nonsymmetric.ColorCap.SuccessfulPrefix
