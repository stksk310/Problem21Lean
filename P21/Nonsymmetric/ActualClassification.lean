import P21.Nonsymmetric.ActualMixed
import P21.Nonsymmetric.ActualLabels
import P21.Nonsymmetric.Relabel
import P21.Nonsymmetric.Corners
import P21.Nonsymmetric.ReturnLevels
import P21.Nonsymmetric.SameColor
import P21.Nonsymmetric.MixedColor
import P21.Nonsymmetric.ColorCap.Residuals

namespace P21.Nonsymmetric

/-- Arm support has two returns, so no arm is a singleton in any direction. -/
theorem armA_not_singleton {g : Generators} (D : NonsymmetricHerzogData g)
    {q : ℤ} {i j : Fin 3} (ha : IsArmA D.toHerzogCriticalData q i)
    (hs : IsSingleton g q j) : False := by
  obtain ⟨l,hl,hu,he⟩ := ha
  have hr := (armA_returns D i hl hu).2.2
  have hnext : next i ∈ g.SH q := by rw [he]; exact hr _ (Ne.symm (cyclic_distinct i).1)
  have hprev : prev i ∈ g.SH q := by rw [he]; exact hr _ (Ne.symm (cyclic_distinct i).2.1)
  rw [hs] at hnext hprev
  exact (cyclic_distinct i).2.2 (hnext.trans hprev.symm)

theorem armB_not_singleton {g : Generators} (D : NonsymmetricHerzogData g)
    {q : ℤ} {i j : Fin 3} (ha : IsArmB D.toHerzogCriticalData q i)
    (hs : IsSingleton g q j) : False := by
  obtain ⟨l,hl,hu,he⟩ := ha
  have hr := (armB_returns D i hl hu).2.2
  have hnext : next i ∈ g.SH q := by rw [he]; exact hr _ (Ne.symm (cyclic_distinct i).1)
  have hprev : prev i ∈ g.SH q := by rw [he]; exact hr _ (Ne.symm (cyclic_distinct i).2.1)
  rw [hs] at hnext hprev
  exact (cyclic_distinct i).2.2 (hnext.trans hprev.symm)

theorem actual_A_box {g : Generators} (s : g.Setting) {F q : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g) (hq : q ∈ s.semigroup.Q F) {i : Fin 3}
    (ha : IsArmA D.toHerzogCriticalData q i) :
    ∃ y z : ℕ, y < D.rho (next i) ∧ z < D.rho (prev i) ∧
      complement F g.m q = (y : ℤ)*g.n (next i)+(z : ℤ)*g.n (prev i) := by
  obtain ⟨l,hl,hu,he⟩ := ha
  apply arm_complement_pair s hF hc D.toHerzogCriticalData hq
  change q + g.n i ∉ g.H
  rw [he]
  exact (armA_returns D i hl hu).2.1

theorem actual_B_box {g : Generators} (s : g.Setting) {F q : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g) (hq : q ∈ s.semigroup.Q F) {i : Fin 3}
    (ha : IsArmB D.toHerzogCriticalData q i) :
    ∃ y z : ℕ, y < D.rho (next i) ∧ z < D.rho (prev i) ∧
      complement F g.m q = (y : ℤ)*g.n (next i)+(z : ℤ)*g.n (prev i) := by
  obtain ⟨l,hl,hu,he⟩ := ha
  apply arm_complement_pair s hF hc D.toHerzogCriticalData hq
  change q + g.n i ∉ g.H
  rw [he]
  exact (armB_returns D i hl hu).2.1

theorem actual_matched_data {g : Generators} (s : g.Setting) {F qA qB : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g)
    (hqA : qA ∈ s.semigroup.Q F) (hqB : qB ∈ s.semigroup.Q F)
    (ha : IsArmA D.toHerzogCriticalData qA 0) (hb : IsArmB D.toHerzogCriticalData qB 0) :
    Nonempty (MatchedPairData g F D.toHerzogCriticalData qA qB) := by
  obtain ⟨y,z,hy,hz,heA⟩ := actual_A_box s hF hc D hqA ha
  obtain ⟨y',z',hy',hz',heB⟩ := actual_B_box s hF hc D hqB hb
  obtain ⟨l,hl,hu,hA⟩ := ha
  obtain ⟨m,hm,hv,hB⟩ := hb
  apply matched_pair_data (fun i => lt_trans s.m_pos (s.n_gt i)) D.toHerzogCriticalData
    (lam := l.toNat) (mu := m.toNat) (y := y) (z := z) (y' := y') (z' := z')
  · omega
  · omega
  · omega
  · omega
  · simpa [Int.toNat_of_nonneg (by omega : 0 ≤ l)] using hA
  · simpa [Int.toNat_of_nonneg (by omega : 0 ≤ m)] using hB
  · exact heA
  · exact heB
  · exact hy
  · exact hz
  · exact hy'
  · exact hz'

/-- Both same-color exclusions with all coefficient witnesses extracted from
these actual complements. -/
theorem actual_AA_exclusions {g : Generators} (s : g.Setting) {F q0 q2 : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g)
    (hq0 : q0 ∈ s.semigroup.Q F) (hq2 : q2 ∈ s.semigroup.Q F)
    (ha0 : IsArmA D.toHerzogCriticalData q0 0) (ha2 : IsArmA D.toHerzogCriticalData q2 2) :
    (∀ q ∈ s.semigroup.Q F, ¬ IsSingleton g q 1) ∧
    (∀ qI ∈ s.semigroup.Q F, ∀ qK ∈ s.semigroup.Q F,
      IsSingleton g qI 0 → IsSingleton g qK 2 → False) := by
  obtain ⟨y,z,hy,hz,hci⟩ := actual_A_box s hF hc D hq0 ha0
  obtain ⟨x,y',hx,hy',hck⟩ := actual_A_box s hF hc D hq2 ha2
  obtain ⟨l,hl,hla,he0⟩ := ha0
  obtain ⟨n,hn,hna,he2⟩ := ha2
  have hci' : complement F g.m (D.fA-l*g.n 0) = (y:ℤ)*g.n 1+(z:ℤ)*g.n 2 := by simpa [← he0,next,prev] using hci
  have hck' : complement F g.m (D.fA-n*g.n 2) = (x:ℤ)*g.n 0+(y':ℤ)*g.n 1 := by simpa [← he2,next,prev] using hck
  constructor
  · intro q hq hs
    exact same_color_no_middle_singleton s hF hc D.toHerzogCriticalData l n hl (by omega) hn (by omega)
      x y z y' hx hy hz hy' hci' hck' hq hs
  · intro qI hqI qK hqK hsI hsK
    apply same_color_no_two_endpoint_singletons s hF hc D.toHerzogCriticalData l n hl (by omega) hn (by omega)
      x y z y' hx hy hz hy' hci' hck' (he0 ▸ hq0) (he2 ▸ hq2) hqI hqK hsI hsK
    · intro he
      apply armA_not_singleton D (q := qI) (i := 2) _ hsI
      exact ⟨n,hn,hna,he.symm⟩
    · intro he
      apply armA_not_singleton D (q := qK) (i := 0) _ hsK
      exact ⟨l,hl,hla,he.symm⟩



/-- Actual matched-pair restrictions transported to every cyclic direction. -/
theorem actual_matched_exclusions {g : Generators} (s : g.Setting) {F qA qB : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g) (i : Fin 3)
    (hqA : qA ∈ s.semigroup.Q F) (hqB : qB ∈ s.semigroup.Q F)
    (ha : IsArmA D.toHerzogCriticalData qA i) (hb : IsArmB D.toHerzogCriticalData qB i) :
    (∀ q ∈ s.semigroup.Q F, ∀ j, ¬ IsSingleton g q j) ∧
    (∀ q ∈ s.semigroup.Q F, ¬ IsArmA D.toHerzogCriticalData q (next i)) ∧
    (∀ q ∈ s.semigroup.Q F, ¬ IsArmB D.toHerzogCriticalData q (prev i)) := by
  let s' := relabelSetting s (rotatePerm i)
  let D' := rotateFullHerzog D i
  have hsem : s'.semigroup = s.semigroup := relabel_semigroup s _
  have hF' : s'.semigroup.IsFrobenius F := by simpa only [hsem] using hF
  have hc' : s'.semigroup.Canonical F g.m := by simpa only [hsem] using hc
  have hqA' : qA ∈ s'.semigroup.Q F := by simpa only [hsem] using hqA
  have hqB' : qB ∈ s'.semigroup.Q F := by simpa only [hsem] using hqB
  have ha' : IsArmA D'.toHerzogCriticalData qA 0 := by simpa [D',rotateFullHerzog] using ha
  have hb' : IsArmB D'.toHerzogCriticalData qB 0 := by simpa [D',rotateFullHerzog] using hb
  obtain ⟨M⟩ := actual_matched_data s' hF' hc' D' hqA' hqB' ha' hb'
  refine ⟨?_, ?_, ?_⟩
  · intro q hq j hs
    have hq' : q ∈ s'.semigroup.Q F := by simpa only [hsem] using hq
    have hs' : IsSingleton (relabel g (rotatePerm i)) q ((rotatePerm i).symm j) := by
      rw [relabel_singleton_iff]
      simpa using hs
    exact matched_pair_no_singleton s' hF' hc' M hqA' hqB' hq' _ hs'
  · intro q hq hqarm
    have hq' : q ∈ s'.semigroup.Q F := by simpa only [hsem] using hq
    have harr : IsArmA D'.toHerzogCriticalData q 1 := by simpa [D',rotateFullHerzog] using hqarm
    obtain ⟨l,_,hl,he⟩ := harr
    exact matched_pair_excludes_A_one s' hF' M hqA' hqB' hq' l (by omega) he
  · intro q hq hqarm
    have hq' : q ∈ s'.semigroup.Q F := by simpa only [hsem] using hq
    have harr : IsArmB D'.toHerzogCriticalData q 2 := by simpa [D',rotateFullHerzog] using hqarm
    obtain ⟨l,_,hl,he⟩ := harr
    exact matched_pair_excludes_B_two s' hF' M hqA' hqB' hq' l (by omega) he

/-- Cyclic form of the actual same-A-color exclusions. -/
theorem actual_AA_cyclic {g : Generators} (s : g.Setting) {F qI qK : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g) (i : Fin 3)
    (hqI : qI ∈ s.semigroup.Q F) (hqK : qK ∈ s.semigroup.Q F)
    (haI : IsArmA D.toHerzogCriticalData qI i)
    (haK : IsArmA D.toHerzogCriticalData qK (prev i)) :
    (∀ q ∈ s.semigroup.Q F, ¬ IsSingleton g q (next i)) ∧
    (∀ q0 ∈ s.semigroup.Q F, ∀ q2 ∈ s.semigroup.Q F,
      IsSingleton g q0 i → IsSingleton g q2 (prev i) → False) := by
  let s' := relabelSetting s (rotatePerm i)
  let D' := rotateFullHerzog D i
  have hsem : s'.semigroup = s.semigroup := relabel_semigroup s _
  have hF' : s'.semigroup.IsFrobenius F := by simpa only [hsem] using hF
  have hc' : s'.semigroup.Canonical F g.m := by simpa only [hsem] using hc
  have hqI' : qI ∈ s'.semigroup.Q F := by simpa only [hsem] using hqI
  have hqK' : qK ∈ s'.semigroup.Q F := by simpa only [hsem] using hqK
  have haI' : IsArmA D'.toHerzogCriticalData qI 0 := by simpa [D',rotateFullHerzog] using haI
  have haK' : IsArmA D'.toHerzogCriticalData qK 2 := by simpa [D',rotateFullHerzog] using haK
  obtain ⟨hmid, hend⟩ := actual_AA_exclusions s' hF' hc' D' hqI' hqK' haI' haK'
  constructor
  · intro q hq hs
    apply hmid q (by simpa only [hsem] using hq)
    rw [relabel_singleton_iff]
    simpa using hs
  · intro q0 hq0 q2 hq2 hs0 hs2
    apply hend q0 (by simpa only [hsem] using hq0) q2 (by simpa only [hsem] using hq2)
    · rw [relabel_singleton_iff]; simpa using hs0
    · rw [relabel_singleton_iff]; simpa using hs2

/-- Full color reversal gives the corresponding B-color restrictions. -/
theorem actual_BB_cyclic {g : Generators} (s : g.Setting) {F qI qK : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g) (i : Fin 3)
    (hqI : qI ∈ s.semigroup.Q F) (hqK : qK ∈ s.semigroup.Q F)
    (haI : IsArmB D.toHerzogCriticalData qI i)
    (haK : IsArmB D.toHerzogCriticalData qK (next i)) :
    (∀ q ∈ s.semigroup.Q F, ¬ IsSingleton g q (prev i)) ∧
    (∀ q0 ∈ s.semigroup.Q F, ∀ q2 ∈ s.semigroup.Q F,
      IsSingleton g q0 i → IsSingleton g q2 (next i) → False) := by
  let s' := relabelSetting s reversePerm
  let D' := reverseFullHerzog D
  have hsem : s'.semigroup = s.semigroup := relabel_semigroup s _
  have hF' : s'.semigroup.IsFrobenius F := by simpa only [hsem] using hF
  have hc' : s'.semigroup.Canonical F g.m := by simpa only [hsem] using hc
  have hqI' : qI ∈ s'.semigroup.Q F := by simpa only [hsem] using hqI
  have hqK' : qK ∈ s'.semigroup.Q F := by simpa only [hsem] using hqK
  have haI' : IsArmA D'.toHerzogCriticalData qI (reversePerm i) := by
    simpa [D',reverseFullHerzog] using haI
  have haK' : IsArmA D'.toHerzogCriticalData qK (prev (reversePerm i)) := by
    simpa [D',reverseFullHerzog] using haK
  obtain ⟨hmid, hend⟩ := actual_AA_cyclic s' hF' hc' D' (reversePerm i) hqI' hqK' haI' haK'
  constructor
  · intro q hq hs
    apply hmid q (by simpa only [hsem] using hq)
    rw [relabel_singleton_iff]
    simpa using hs
  · intro q0 hq0 q2 hq2 hs0 hs2
    apply hend q0 (by simpa only [hsem] using hq0) q2 (by simpa only [hsem] using hq2)
    · rw [relabel_singleton_iff]; simpa using hs0
    · rw [relabel_singleton_iff]; simpa using hs2



/-- Excluding the third direction and the two endpoints excludes every pair
of distinct singleton directions. -/
theorem no_two_singletons_of_three_directions {g : Generators} {s : g.Setting} {F : ℤ}
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hmid : ∀ q ∈ s.semigroup.Q F, ¬ IsSingleton g q k)
    (hend : ∀ qI ∈ s.semigroup.Q F, ∀ qJ ∈ s.semigroup.Q F,
      IsSingleton g qI i → IsSingleton g qJ j → False)
    {q r : ℤ} (hq : q ∈ s.semigroup.Q F) (hr : r ∈ s.semigroup.Q F)
    (u v : Fin 3) (huv : u ≠ v) (hsu : IsSingleton g q u) (hsv : IsSingleton g r v) : False := by
  have hex (a : Fin 3) : a = i ∨ a = j ∨ a = k := by omega
  rcases hex u with rfl | rfl | rfl <;> rcases hex v with rfl | rfl | rfl
  all_goals first | exact huv rfl | exact hmid q hq hsu | exact hmid r hr hsv |
    exact hend q hq r hr hsu hsv | exact hend r hr q hq hsv hsu

theorem actual_AA_no_two_singletons {g : Generators} (s : g.Setting) {F qI qJ : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g) (i j : Fin 3) (hij : i ≠ j)
    (hqI : qI ∈ s.semigroup.Q F) (hqJ : qJ ∈ s.semigroup.Q F)
    (haI : IsArmA D.toHerzogCriticalData qI i) (haJ : IsArmA D.toHerzogCriticalData qJ j)
    {q r : ℤ} (hq : q ∈ s.semigroup.Q F) (hr : r ∈ s.semigroup.Q F)
    (u v : Fin 3) (huv : u ≠ v) (hsu : IsSingleton g q u) (hsv : IsSingleton g r v) : False := by
  have hor : j = prev i ∨ i = prev j := by fin_cases i <;> fin_cases j <;> simp_all [prev]
  rcases hor with rfl | rfl
  · obtain ⟨hmid,hend⟩ := actual_AA_cyclic s hF hc D i hqI hqJ haI haJ
    exact no_two_singletons_of_three_directions i (prev i) (next i)
      (cyclic_distinct i).2.1 (cyclic_distinct i).1 (Ne.symm (cyclic_distinct i).2.2)
      hmid hend hq hr u v huv hsu hsv
  · obtain ⟨hmid,hend⟩ := actual_AA_cyclic s hF hc D j hqJ hqI haJ haI
    exact no_two_singletons_of_three_directions j (prev j) (next j)
      (cyclic_distinct j).2.1 (cyclic_distinct j).1 (Ne.symm (cyclic_distinct j).2.2)
      hmid hend hq hr u v huv hsu hsv

theorem actual_BB_no_two_singletons {g : Generators} (s : g.Setting) {F qI qJ : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g) (i j : Fin 3) (hij : i ≠ j)
    (hqI : qI ∈ s.semigroup.Q F) (hqJ : qJ ∈ s.semigroup.Q F)
    (haI : IsArmB D.toHerzogCriticalData qI i) (haJ : IsArmB D.toHerzogCriticalData qJ j)
    {q r : ℤ} (hq : q ∈ s.semigroup.Q F) (hr : r ∈ s.semigroup.Q F)
    (u v : Fin 3) (huv : u ≠ v) (hsu : IsSingleton g q u) (hsv : IsSingleton g r v) : False := by
  have hor : j = next i ∨ i = next j := by fin_cases i <;> fin_cases j <;> simp_all [next]
  rcases hor with rfl | rfl
  · obtain ⟨hmid,hend⟩ := actual_BB_cyclic s hF hc D i hqI hqJ haI haJ
    exact no_two_singletons_of_three_directions i (next i) (prev i)
      (cyclic_distinct i).1 (cyclic_distinct i).2.1 (cyclic_distinct i).2.2
      hmid hend hq hr u v huv hsu hsv
  · obtain ⟨hmid,hend⟩ := actual_BB_cyclic s hF hc D j hqJ hqI haJ haI
    exact no_two_singletons_of_three_directions j (next j) (prev j)
      (cyclic_distinct j).1 (cyclic_distinct j).2.1 (cyclic_distinct j).2.2
      hmid hend hq hr u v huv hsu hsv

/-- Four selected distinct actual rows give a lower bound, never Q=4. -/
theorem selected_four_Q_card {g : Generators} {s : g.Setting} {F : ℤ}
    (rows : FourDistinctActualQRows s F) : 4 ≤ (s.semigroup.Q F).ncard := by
  have hsub : Set.range (fun i => (rows.row i).q) ⊆ s.semigroup.Q F := by
    rintro q ⟨i,rfl⟩
    exact (rows.row i).mem
  have hle := Set.ncard_le_ncard hsub (s.semigroup.q_finite F)
  simpa [Set.ncard_range_of_injective rows.distinct] using hle




theorem actual_three_A_excluded
    (hminimum : ColorCap.MinimumOneStatement) (hdpe : ColorCap.BoxPositiveExitStatement)
    {g : Generators} (s : g.Setting) {F : ℤ} (D : NonsymmetricHerzogData g)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (ha : ∀ i, ∃ q, q ∈ s.semigroup.Q F ∧ IsArmA D.toHerzogCriticalData q i) : False := by
  classical
  have hex : ∀ i, ∃ l : ℤ, 1 ≤ l ∧ l < D.a i ∧ D.fA-l*g.n i ∈ s.semigroup.PF := by
    intro i
    obtain ⟨q,hq,l,hl,hu,he⟩ := ha i
    exact ⟨l,hl,by omega,he ▸ hq.1⟩
  choose depth hlo hhi hq using hex
  exact ColorCap.three_arms_impossible_of_residuals hminimum hdpe g s hcof D.toHerzogCriticalData true
    depth hlo hhi hq

theorem actual_three_B_excluded
    (hminimum : ColorCap.MinimumOneStatement) (hdpe : ColorCap.BoxPositiveExitStatement)
    {g : Generators} (s : g.Setting) {F : ℤ} (D : NonsymmetricHerzogData g)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (ha : ∀ i, ∃ q, q ∈ s.semigroup.Q F ∧ IsArmB D.toHerzogCriticalData q i) : False := by
  classical
  have hex : ∀ i, ∃ l : ℤ, 1 ≤ l ∧ l < D.b i ∧ D.fB-l*g.n i ∈ s.semigroup.PF := by
    intro i
    obtain ⟨q,hq,l,hl,hu,he⟩ := ha i
    exact ⟨l,hl,by omega,he ▸ hq.1⟩
  choose depth hlo hhi hq using hex
  exact ColorCap.three_arms_impossible_of_residuals hminimum hdpe g s hcof D.toHerzogCriticalData false
    depth hlo hhi hq

/-- Actual local geometry supplies every finite compatibility constraint.
The only remaining assumptions are the two precise Appendix-B propositions. -/
theorem actual_labels_compatible
    (hminimum : ColorCap.MinimumOneStatement) (hdpe : ColorCap.BoxPositiveExitStatement)
    {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g) (rows : FourDistinctActualQRows s F)
    (L : ActualLabeling D.toHerzogCriticalData rows) : RowLabel.Compatible L.labels := by
  have hcof := s.tail_cofinite hF hc ⟨(rows.row 0).q,(rows.row 0).mem⟩
  have hrow {l : RowLabel} (hl : l ∈ L.labels) :
      ∃ q, q ∈ s.semigroup.Q F ∧ Realizes D.toHerzogCriticalData q l := by
    obtain ⟨i,_,hi⟩ := L.mem_labels hl
    exact ⟨(rows.row i).q,(rows.row i).mem,hi⟩
  refine ⟨L.labels_card hF hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨ha,hb⟩
    obtain ⟨q,hq,heq⟩ := hrow ha
    obtain ⟨r,hr,her⟩ := hrow hb
    exact both_corners_excluded s hF hc D (heq ▸ hq) (her ▸ hr)
  · intro c i hcorner
    obtain ⟨q,hq,hqcorner⟩ := hrow hcorner
    cases c
    · constructor
      · intro hs
        obtain ⟨r,hr,hsr⟩ := hrow hs
        exact corner_A_singleton_excluded s hF hc D.toHerzogCriticalData (hqcorner ▸ hq) hr i hsr
      · intro ha
        obtain ⟨r,hr,har⟩ := hrow ha
        exact corner_A_same_arm_excluded s D.toHerzogCriticalData (hqcorner ▸ hq) hr har
    · constructor
      · intro hs
        obtain ⟨r,hr,hsr⟩ := hrow hs
        exact corner_B_singleton_excluded s hF hc D.toHerzogCriticalData (hqcorner ▸ hq) hr i hsr
      · intro ha
        obtain ⟨r,hr,har⟩ := hrow ha
        exact corner_B_same_arm_excluded s D.toHerzogCriticalData (hqcorner ▸ hq) hr har
  · intro c hthree
    have hall : ∀ i, RowLabel.arm c i ∈ L.labels := by
      intro i
      fin_cases i
      · exact hthree.1
      · exact hthree.2.1
      · exact hthree.2.2
    cases c
    · apply actual_three_A_excluded hminimum hdpe s D hcof
      intro i
      exact hrow (hall i)
    · apply actual_three_B_excluded hminimum hdpe s D hcof
      intro i
      exact hrow (hall i)
  · rintro ⟨hs0,hs1,hs2⟩
    obtain ⟨q0,hq0,h0⟩ := hrow hs0
    obtain ⟨q1,hq1,h1⟩ := hrow hs1
    obtain ⟨q2,hq2,h2⟩ := hrow hs2
    have hc3 := three_singletons_force_Q_three s hF hc ![q0,q1,q2]
      (by intro i; fin_cases i <;> simp <;> assumption)
      (by intro i; fin_cases i <;> simp <;> assumption)
    have hc4 := selected_four_Q_card rows
    omega
  · intro i ha hb
    obtain ⟨qA,hqA,hA⟩ := hrow ha
    obtain ⟨qB,hqB,hB⟩ := hrow hb
    obtain ⟨hS,hAn,hBp⟩ := actual_matched_exclusions s hF hc D i hqA hqB hA hB
    refine ⟨?_,?_,?_⟩
    · intro j hs
      obtain ⟨q,hq,hsq⟩ := hrow hs
      exact hS q hq j hsq
    · intro hn
      obtain ⟨q,hq,haq⟩ := hrow hn
      exact hAn q hq haq
    · intro hn
      obtain ⟨q,hq,hbq⟩ := hrow hn
      exact hBp q hq hbq
  · intro i ha hk hs
    obtain ⟨qI,hqI,hI⟩ := hrow ha
    obtain ⟨qK,hqK,hK⟩ := hrow hk
    obtain ⟨q,hq,hqs⟩ := hrow hs
    exact (actual_AA_cyclic s hF hc D i hqI hqK hI hK).1 q hq hqs
  · intro i ha hk hs
    obtain ⟨qI,hqI,hI⟩ := hrow ha
    obtain ⟨qK,hqK,hK⟩ := hrow hk
    obtain ⟨q,hq,hqs⟩ := hrow hs
    exact (actual_BB_cyclic s hF hc D i hqI hqK hI hK).1 q hq hqs
  · intro c i j hij hi hj k l hkl hs
    obtain ⟨qI,hqI,hI⟩ := hrow hi
    obtain ⟨qJ,hqJ,hJ⟩ := hrow hj
    obtain ⟨q,hq,hqs⟩ := hrow hs.1
    obtain ⟨r,hr,hrs⟩ := hrow hs.2
    cases c
    · exact actual_AA_no_two_singletons s hF hc D i j hij hqI hqJ hI hJ hq hr k l hkl hqs hrs
    · exact actual_BB_no_two_singletons s hF hc D i j hij hqI hqJ hI hJ hq hr k l hkl hqs hrs
  · intro i hb ha hs
    obtain ⟨qB,hqB,hB⟩ := hrow hb
    obtain ⟨qA,hqA,hA⟩ := hrow ha
    obtain ⟨q,hq,hqs⟩ := hrow hs
    exact actual_BA_excludes_middle s hF hc D i hqB hqA hB hA hq hqs
  · intro i ha hb
    obtain ⟨qA,hqA,hA⟩ := hrow ha
    obtain ⟨qB,hqB,hB⟩ := hrow hb
    constructor
    · intro hs
      obtain ⟨q,hq,hqs⟩ := hrow hs
      exact (actual_AB_excludes_endpoints s hF hc D i hqA hqB hA hB hq).1 hqs
    · intro hs
      obtain ⟨q,hq,hqs⟩ := hrow hs
      exact (actual_AB_excludes_endpoints s hF hc D i hqA hqB hA hB hq).2 hqs

/-- The selected actual label set has one of exactly the publication terminal
shapes, including the allowed cyclic permutations and full color reversal. -/
theorem actual_labels_terminal
    (hminimum : ColorCap.MinimumOneStatement) (hdpe : ColorCap.BoxPositiveExitStatement)
    {g : Generators} (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g) (rows : FourDistinctActualQRows s F)
    (L : ActualLabeling D.toHerzogCriticalData rows) : RowLabel.Terminal L.labels :=
  RowLabel.four_labels_classification L.labels
    (actual_labels_compatible hminimum hdpe s hF hc D rows L)

end P21.Nonsymmetric
