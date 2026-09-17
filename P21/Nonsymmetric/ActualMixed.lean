import P21.Nonsymmetric.MixedColor
import P21.Nonsymmetric.Relabel
import P21.Nonsymmetric.RowAtlas

namespace P21.Nonsymmetric
variable {g : Generators}

theorem rotate_isArmA_iff (D : HerzogCriticalData g) (i j : Fin 3) (q : ℤ) :
    IsArmA (rotateHerzog D i) q j ↔ IsArmA D q (rotatePerm i j) := by
  simp only [IsArmA,rotateHerzog_fA]
  rfl

theorem rotate_isArmB_iff (D : HerzogCriticalData g) (i j : Fin 3) (q : ℤ) :
    IsArmB (rotateHerzog D i) q j ↔ IsArmB D q (rotatePerm i j) := by
  simp only [IsArmB,rotateHerzog_fB]
  rfl

theorem mixed_A_not_singleton (D : NonsymmetricHerzogData g) {q : ℤ} {i j : Fin 3}
    (ha : IsArmA D.toHerzogCriticalData q i) (hs : IsSingleton g q j) : False := by
  obtain ⟨l,hl,hu,he⟩ := ha
  have hr := (armA_returns D i hl hu).2.2
  have h1 : next i ∈ g.SH q := by rw [he]; exact hr _ (Ne.symm (cyclic_distinct i).1)
  have h2 : prev i ∈ g.SH q := by rw [he]; exact hr _ (Ne.symm (cyclic_distinct i).2.1)
  rw [hs] at h1 h2
  exact (cyclic_distinct i).2.2 (h1.trans h2.symm)

theorem mixed_B_not_singleton (D : NonsymmetricHerzogData g) {q : ℤ} {i j : Fin 3}
    (ha : IsArmB D.toHerzogCriticalData q i) (hs : IsSingleton g q j) : False := by
  obtain ⟨l,hl,hu,he⟩ := ha
  have hr := (armB_returns D i hl hu).2.2
  have h1 : next i ∈ g.SH q := by rw [he]; exact hr _ (Ne.symm (cyclic_distinct i).1)
  have h2 : prev i ∈ g.SH q := by rw [he]; exact hr _ (Ne.symm (cyclic_distinct i).2.1)
  rw [hs] at h1 h2
  exact (cyclic_distinct i).2.2 (h1.trans h2.symm)

theorem actual_BA_excludes_middle_zero (s : g.Setting) {F qB qA q : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g)
    (hqB : qB ∈ s.semigroup.Q F) (hqA : qA ∈ s.semigroup.Q F)
    (hB : IsArmB D.toHerzogCriticalData qB 0) (hA : IsArmA D.toHerzogCriticalData qA 2)
    (hq : q ∈ s.semigroup.Q F) (hs : IsSingleton g q 1) : False := by
  obtain ⟨l,hl,hlb,rfl⟩ := hB
  obtain ⟨n,hn,hna,rfl⟩ := hA
  obtain ⟨y,z,hy,hz,hci⟩ := arm_complement_pair s hF hc D.toHerzogCriticalData hqB
    (show (0:Fin 3) ∉ g.SH (D.fB-l*g.n 0) from (armB_returns D 0 hl hlb).2.1)
  obtain ⟨x,y',hx,hy',hck⟩ := arm_complement_pair s hF hc D.toHerzogCriticalData hqA
    (show (2:Fin 3) ∉ g.SH (D.fA-n*g.n 2) from (armA_returns D 2 hn hna).2.1)
  change y < D.rho 1 at hy
  change z < D.rho 2 at hz
  change x < D.rho 0 at hx
  change y' < D.rho 1 at hy'
  change complement F g.m (D.fB-l*g.n 0) = (y:ℤ)*g.n 1+(z:ℤ)*g.n 2 at hci
  change complement F g.m (D.fA-n*g.n 2) = (x:ℤ)*g.n 0+(y':ℤ)*g.n 1 at hck
  obtain ⟨ez,_,_⟩ := mixed_right_complement_geometry D.toHerzogCriticalData
    (fun i => lt_trans s.m_pos (s.n_gt i)) F l n hl (by omega) hn (by omega)
    x y z y' hx hy hz hy' hci hck
  exact mixed_right_no_middle_singleton s hF hc D.toHerzogCriticalData l n y
    (by omega) (by omega) (by simpa [ez] using hci) hq hs

theorem actual_AB_excludes_endpoints_zero (s : g.Setting) {F qA qB q : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g)
    (hqA : qA ∈ s.semigroup.Q F) (hqB : qB ∈ s.semigroup.Q F)
    (hA : IsArmA D.toHerzogCriticalData qA 0) (hB : IsArmB D.toHerzogCriticalData qB 2)
    (hq : q ∈ s.semigroup.Q F) : ¬ IsSingleton g q 0 ∧ ¬ IsSingleton g q 2 := by
  have hAkeep := hA
  have hBkeep := hB
  obtain ⟨l,hl,hla,rfl⟩ := hA
  obtain ⟨n,hn,hnb,rfl⟩ := hB
  obtain ⟨y,z,hy,hz,hci⟩ := arm_complement_pair s hF hc D.toHerzogCriticalData hqA
    (show (0:Fin 3) ∉ g.SH (D.fA-l*g.n 0) from (armA_returns D 0 hl hla).2.1)
  obtain ⟨x,y',hx,hy',hck⟩ := arm_complement_pair s hF hc D.toHerzogCriticalData hqB
    (show (2:Fin 3) ∉ g.SH (D.fB-n*g.n 2) from (armB_returns D 2 hn hnb).2.1)
  change y < D.rho 1 at hy
  change z < D.rho 2 at hz
  change x < D.rho 0 at hx
  change y' < D.rho 1 at hy'
  change complement F g.m (D.fA-l*g.n 0) = (y:ℤ)*g.n 1+(z:ℤ)*g.n 2 at hci
  change complement F g.m (D.fB-n*g.n 2) = (x:ℤ)*g.n 0+(y':ℤ)*g.n 1 at hck
  constructor
  · intro hs
    apply mixed_left_no_first_singleton s hF hc D.toHerzogCriticalData l n hl (by omega) hn (by omega)
      x y z y' hx hy hz hy' hci hck hqB hq hs
    intro he
    exact mixed_B_not_singleton D hBkeep (by simpa [he] using hs)
  · intro hs
    apply mixed_left_no_last_singleton s hF hc D.toHerzogCriticalData l n hl (by omega) hn (by omega)
      x y z y' hx hy hz hy' hci hck hqA hq hs
    intro he
    exact mixed_A_not_singleton D hAkeep (by simpa [he] using hs)

/-- Right-oriented mixed pair excludes the remaining singleton, in any cyclic
coordinate system, with no extra coefficient hypotheses. -/
theorem actual_BA_excludes_middle (s : g.Setting) {F qB qA q : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g) (i : Fin 3)
    (hqB : qB ∈ s.semigroup.Q F) (hqA : qA ∈ s.semigroup.Q F)
    (hB : IsArmB D.toHerzogCriticalData qB i)
    (hA : IsArmA D.toHerzogCriticalData qA (prev i))
    (hq : q ∈ s.semigroup.Q F) (hs : IsSingleton g q (next i)) : False := by
  apply actual_BA_excludes_middle_zero (relabelSetting s (rotatePerm i))
    (F:=F) (qB:=qB) (qA:=qA) (q:=q)
    (by rw [relabel_semigroup]; exact hF) (by rw [relabel_semigroup]; exact hc)
    (rotateFullHerzog D i) (by rw [relabel_Q]; exact hqB) (by rw [relabel_Q]; exact hqA) ?_ ?_
    (by rw [relabel_Q]; exact hq) ?_
  · change IsArmB (rotateHerzog D.toHerzogCriticalData i) qB 0
    rw [rotate_isArmB_iff,rotatePerm_zero]
    exact hB
  · change IsArmA (rotateHerzog D.toHerzogCriticalData i) qA 2
    rw [rotate_isArmA_iff,rotatePerm_two]
    exact hA
  · apply (relabel_singleton_iff g (rotatePerm i) q 1).mpr
    simpa using hs

/-- Opposite mixed pair excludes either endpoint singleton in any cyclic
coordinate system. -/
theorem actual_AB_excludes_endpoints (s : g.Setting) {F qA qB q : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : NonsymmetricHerzogData g) (i : Fin 3)
    (hqA : qA ∈ s.semigroup.Q F) (hqB : qB ∈ s.semigroup.Q F)
    (hA : IsArmA D.toHerzogCriticalData qA i)
    (hB : IsArmB D.toHerzogCriticalData qB (prev i))
    (hq : q ∈ s.semigroup.Q F) : ¬ IsSingleton g q i ∧ ¬ IsSingleton g q (prev i) := by
  have hh := actual_AB_excludes_endpoints_zero (relabelSetting s (rotatePerm i))
    (F:=F) (qA:=qA) (qB:=qB) (q:=q)
    (by rw [relabel_semigroup]; exact hF) (by rw [relabel_semigroup]; exact hc)
    (rotateFullHerzog D i) (by rw [relabel_Q]; exact hqA) (by rw [relabel_Q]; exact hqB)
    (by change IsArmA (rotateHerzog D.toHerzogCriticalData i) qA 0
        rw [rotate_isArmA_iff,rotatePerm_zero]; exact hA)
    (by change IsArmB (rotateHerzog D.toHerzogCriticalData i) qB 2
        rw [rotate_isArmB_iff,rotatePerm_two]; exact hB)
    (by rw [relabel_Q]; exact hq)
  simpa only [relabel_singleton_iff,rotatePerm_zero,rotatePerm_two] using hh

end P21.Nonsymmetric
