import P21.Nonsymmetric.RowAtlas
import P21.Nonsymmetric.Arms
import P21.Nonsymmetric.Herzog.PseudoFrobenius

namespace P21.Nonsymmetric

/-- Rename only the three tail coordinates; m and all actual integer elements
remain unchanged. -/
def relabel (g : Generators) (e : Equiv.Perm (Fin 3)) : Generators :=
  ⟨g.m, fun i => g.n (e i)⟩

theorem value_perm {k : ℕ} (n : Fin k → ℤ) (a : Fin k → ℕ)
    (e : Equiv.Perm (Fin k)) :
    value (fun i => n (e i)) (fun i => a (e i)) = value n a := by
  exact Equiv.sum_comp e (fun i => (a i : ℤ) * n i)

theorem value_relabel (g : Generators) (e : Equiv.Perm (Fin 3)) (a : Fin 3 → ℕ) :
    value (relabel g e).n a = value g.n (fun j => a (e.symm j)) := by
  simpa [relabel] using value_perm g.n (fun j => a (e.symm j)) e

@[simp] theorem relabel_H (g : Generators) (e : Equiv.Perm (Fin 3)) :
    (relabel g e).H = g.H := by
  ext x
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨fun j => a (e.symm j), by rw [← value_relabel]; exact ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨fun j => a (e j), by simpa [value_relabel] using ha⟩

theorem value_relabel_all (g : Generators) (e : Equiv.Perm (Fin 3)) (a : Fin 4 → ℕ) :
    value (relabel g e).all a =
      value g.all (Fin.cons (a 0) (fun j => a (e.symm j).succ)) := by
  simp only [value, Generators.all, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  change (a 0 : ℤ) * g.m + value (relabel g e).n (fun j => a j.succ) =
    (a 0 : ℤ) * g.m + value g.n (fun j => a (e.symm j).succ)
  rw [value_relabel]

@[simp] theorem relabel_Gamma (g : Generators) (e : Equiv.Perm (Fin 3)) :
    (relabel g e).Gamma = g.Gamma := by
  ext x
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨Fin.cons (a 0) (fun j => a (e.symm j).succ), by rw [← value_relabel_all]; exact ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨Fin.cons (a 0) (fun j => a (e j).succ), ?_⟩
    rw [value_relabel_all]
    have heta : Fin.cons (a 0) (fun j => a j.succ) = a := by
      funext i
      exact Fin.cases rfl (fun j => rfl) i
    simpa [heta] using ha

/-- The same setting, after a permutation of the indexed tail. -/
def relabelSetting {g : Generators} (s : g.Setting) (e : Equiv.Perm (Fin 3)) :
    (relabel g e).Setting where
  m_pos := s.m_pos
  n_gt i := s.n_gt (e i)
  minimal := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro a ha he
      rw [value_relabel_all] at he
      exact s.minimal 0 (Fin.cons (a 0) (fun j => a (e.symm j).succ))
        (by simpa using ha) (by simpa [relabel, Generators.all] using he)
    · intro a ha he
      rw [value_relabel_all] at he
      exact s.minimal (e j).succ (Fin.cons (a 0) (fun j => a (e.symm j).succ))
        (by simpa using ha) (by simpa [relabel, Generators.all] using he)
  multiplicity := by intro x hx hn; exact s.multiplicity x (by simpa using hx) hn
  cofinite := by simpa using s.cofinite

@[simp] theorem relabel_semigroup {g : Generators} (s : g.Setting) (e : Equiv.Perm (Fin 3)) :
    (relabelSetting s e).semigroup = s.semigroup := by
  unfold Generators.Setting.semigroup
  congr 1
  exact relabel_Gamma g e

@[simp] theorem relabel_SH (g : Generators) (e : Equiv.Perm (Fin 3)) (q : ℤ) :
    (relabel g e).SH q = e ⁻¹' g.SH q := by
  ext i
  change q + g.n (e i) ∈ (relabel g e).H ↔ q + g.n (e i) ∈ g.H
  rw [relabel_H]

@[simp] theorem relabel_TailPF (g : Generators) (e : Equiv.Perm (Fin 3)) :
    TailPF (relabel g e) = TailPF g := by simp [TailPF]

theorem relabel_singleton_iff (g : Generators) (e : Equiv.Perm (Fin 3)) (q : ℤ) (i : Fin 3) :
    IsSingleton (relabel g e) q i ↔ IsSingleton g q (e i) := by
  simp only [IsSingleton, relabel_SH]
  constructor
  · intro he
    ext j
    have hh := Set.ext_iff.mp he (e.symm j)
    simpa [Equiv.symm_apply_eq] using hh
  · intro he
    ext j
    simp [he]

/-- Minimal critical data transport through the same coordinate permutation. -/
def relabelCritical {g : Generators} (e : Equiv.Perm (Fin 3)) (i : Fin 3)
    (r : Symmetric.Classification.CriticalRelation g (e i)) :
    Symmetric.Classification.CriticalRelation (relabel g e) i where
  coeff := r.coeff
  coeff_pos := r.coeff_pos
  otherCoeff j := r.otherCoeff (e j)
  zero_self := r.zero_self
  equality := by simpa [relabel, value_perm] using r.equality
  minimal := by
    intro c hc a ha he
    apply r.minimal c hc (fun j => a (e.symm j)) (by simpa using ha)
    rw [value_relabel] at he
    exact he

def cyclePerm : Equiv.Perm (Fin 3) where
  toFun := next
  invFun := prev
  left_inv i := by fin_cases i <;> decide
  right_inv i := by fin_cases i <;> decide

def rotatePerm (i : Fin 3) : Equiv.Perm (Fin 3) :=
  ![Equiv.refl _, cyclePerm, cyclePerm.symm] i

@[simp] theorem rotatePerm_zero (i : Fin 3) : rotatePerm i 0 = i := by
  fin_cases i <;> rfl

@[simp] theorem rotatePerm_one (i : Fin 3) : rotatePerm i 1 = next i := by
  fin_cases i <;> rfl

@[simp] theorem rotatePerm_two (i : Fin 3) : rotatePerm i 2 = prev i := by
  fin_cases i <;> rfl




/-- Cyclic relabeling preserves the A/B colors. -/
def rotateHerzog {g : Generators} (D : HerzogCriticalData g) (i : Fin 3) :
    HerzogCriticalData (relabel g (rotatePerm i)) where
  a j := D.a (rotatePerm i j)
  b j := D.b (rotatePerm i j)
  rho j := D.rho (rotatePerm i j)
  a_pos j := D.a_pos _
  b_pos j := D.b_pos _
  rho_eq j := D.rho_eq _
  relation_zero := by
    fin_cases i <;> simp [relabel, rotatePerm, cyclePerm, next, prev] <;>
      nlinarith [D.relation_zero, D.relation_one, D.relation_two]
  relation_one := by
    fin_cases i <;> simp [relabel, rotatePerm, cyclePerm, next, prev] <;>
      nlinarith [D.relation_zero, D.relation_one, D.relation_two]
  relation_two := by
    fin_cases i <;> simp [relabel, rotatePerm, cyclePerm, next, prev] <;>
      nlinarith [D.relation_zero, D.relation_one, D.relation_two]
  critical j := relabelCritical (rotatePerm i) j (D.critical _)
  coeff_rho j := D.coeff_rho _

@[simp] theorem rotateHerzog_fA {g : Generators} (D : HerzogCriticalData g) (i : Fin 3) :
    (rotateHerzog D i).fA = D.fA := by
  simpa [HerzogCriticalData.fA, rotateHerzog, relabel] using (D.fA_cyclic i).symm

@[simp] theorem rotateHerzog_fB {g : Generators} (D : HerzogCriticalData g) (i : Fin 3) :
    (rotateHerzog D i).fB = D.fB := by
  simpa [HerzogCriticalData.fB, rotateHerzog, relabel] using (D.fB_cyclic i).symm

def rotateFullHerzog {g : Generators} (D : NonsymmetricHerzogData g) (i : Fin 3) :
    NonsymmetricHerzogData (relabel g (rotatePerm i)) where
  toHerzogCriticalData := rotateHerzog D.toHerzogCriticalData i
  distinct := by simpa using D.distinct
  pf_exact := by simpa using D.pf_exact

/-- Reverse the cyclic order and exchange A and B. -/
def reversePerm : Equiv.Perm (Fin 3) where
  toFun := ![0, 2, 1]
  invFun := ![0, 2, 1]
  left_inv i := by fin_cases i <;> decide
  right_inv i := by fin_cases i <;> decide

def reverseHerzog {g : Generators} (D : HerzogCriticalData g) :
    HerzogCriticalData (relabel g reversePerm) where
  a j := D.b (reversePerm j)
  b j := D.a (reversePerm j)
  rho j := D.rho (reversePerm j)
  a_pos j := D.b_pos _
  b_pos j := D.a_pos _
  rho_eq j := by rw [D.rho_eq]; omega
  relation_zero := by
    simp [relabel, reversePerm]
    nlinarith [D.relation_zero]
  relation_one := by
    simpa [relabel, reversePerm] using D.relation_two
  relation_two := by
    simpa [relabel, reversePerm] using D.relation_one
  critical j := relabelCritical reversePerm j (D.critical _)
  coeff_rho j := D.coeff_rho _

@[simp] theorem reverseHerzog_fA {g : Generators} (D : HerzogCriticalData g) :
    (reverseHerzog D).fA = D.fB := by
  simp [HerzogCriticalData.fA, HerzogCriticalData.fB, reverseHerzog, relabel, reversePerm]
  ring

@[simp] theorem reverseHerzog_fB {g : Generators} (D : HerzogCriticalData g) :
    (reverseHerzog D).fB = D.fA := by
  simp [HerzogCriticalData.fA, HerzogCriticalData.fB, reverseHerzog, relabel, reversePerm]
  ring

def reverseFullHerzog {g : Generators} (D : NonsymmetricHerzogData g) :
    NonsymmetricHerzogData (relabel g reversePerm) where
  toHerzogCriticalData := reverseHerzog D.toHerzogCriticalData
  distinct := by simpa using Ne.symm D.distinct
  pf_exact := by simpa [Set.pair_comm] using D.pf_exact

@[simp] theorem relabel_complement (g : Generators) (e : Equiv.Perm (Fin 3)) (F q : ℤ) :
    complement F (relabel g e).m q = complement F g.m q := rfl

@[simp] theorem relabel_W (g : Generators) (e : Equiv.Perm (Fin 3)) (F : ℤ) :
    W F (relabel g e).m = W F g.m := rfl

/-- Actual Q rows are exactly the same integers after relabeling. -/
@[simp] theorem relabel_Q {g : Generators} (s : g.Setting) (e : Equiv.Perm (Fin 3)) (F : ℤ) :
    (relabelSetting s e).semigroup.Q F = s.semigroup.Q F := by rw [relabel_semigroup]

/-- Cyclic A-arm equations transport with their original depth. -/
theorem rotate_A_arm_iff {g : Generators} (D : HerzogCriticalData g) (i j : Fin 3) (q l : ℤ) :
    (1 ≤ l ∧ l < (rotateHerzog D i).a j ∧
      q = (rotateHerzog D i).fA - l * (relabel g (rotatePerm i)).n j) ↔
    (1 ≤ l ∧ l < D.a (rotatePerm i j) ∧ q = D.fA - l * g.n (rotatePerm i j)) := by
  rw [rotateHerzog_fA]
  rfl

theorem rotate_B_arm_iff {g : Generators} (D : HerzogCriticalData g) (i j : Fin 3) (q l : ℤ) :
    (1 ≤ l ∧ l < (rotateHerzog D i).b j ∧
      q = (rotateHerzog D i).fB - l * (relabel g (rotatePerm i)).n j) ↔
    (1 ≤ l ∧ l < D.b (rotatePerm i j) ∧ q = D.fB - l * g.n (rotatePerm i j)) := by
  rw [rotateHerzog_fB]
  rfl

theorem reverse_A_arm_iff {g : Generators} (D : HerzogCriticalData g) (j : Fin 3) (q l : ℤ) :
    (1 ≤ l ∧ l < (reverseHerzog D).a j ∧
      q = (reverseHerzog D).fA - l * (relabel g reversePerm).n j) ↔
    (1 ≤ l ∧ l < D.b (reversePerm j) ∧ q = D.fB - l * g.n (reversePerm j)) := by
  rw [reverseHerzog_fA]
  rfl

theorem reverse_B_arm_iff {g : Generators} (D : HerzogCriticalData g) (j : Fin 3) (q l : ℤ) :
    (1 ≤ l ∧ l < (reverseHerzog D).b j ∧
      q = (reverseHerzog D).fB - l * (relabel g reversePerm).n j) ↔
    (1 ≤ l ∧ l < D.a (reversePerm j) ∧ q = D.fA - l * g.n (reversePerm j)) := by
  rw [reverseHerzog_fB]
  rfl






/-- Actual coefficient vectors are transported by the same permutation. -/
def relabelFactorization {g : Generators} (e : Equiv.Perm (Fin 3)) {x : ℤ}
    (a : g.ActualFactorization3 x) : (relabel g e).ActualFactorization3 x where
  coeff j := a.coeff (e j)
  equation := by simpa [relabel, value_perm] using a.equation

/-- Inverse transport of a named actual vector; no factorization is reselected. -/
def unlabelFactorization {g : Generators} (e : Equiv.Perm (Fin 3)) {x : ℤ}
    (a : (relabel g e).ActualFactorization3 x) : g.ActualFactorization3 x where
  coeff j := a.coeff (e.symm j)
  equation := by rw [← value_relabel]; exact a.equation

def relabelActualRow {g : Generators} {s : g.Setting} (e : Equiv.Perm (Fin 3)) {F : ℤ}
    (q : ActualQRow s F) : ActualQRow (relabelSetting s e) F where
  q := q.q
  mem := by
    change q.q ∈ (relabelSetting s e).semigroup.Q F
    rw [relabel_semigroup]
    exact q.mem

def relabelFourRows {g : Generators} {s : g.Setting} (e : Equiv.Perm (Fin 3)) {F : ℤ}
    (rows : FourDistinctActualQRows s F) : FourDistinctActualQRows (relabelSetting s e) F where
  row i := relabelActualRow e (rows.row i)
  distinct := rows.distinct

@[simp] theorem relabel_D (g : Generators) (e : Equiv.Perm (Fin 3)) (c : ℤ) :
    (relabel g e).D c = e ⁻¹' g.D c := by
  ext i
  change c - g.n (e i) ∈ (relabel g e).H ↔ c - g.n (e i) ∈ g.H
  rw [relabel_H]

@[simp] theorem relabel_id (g : Generators) : relabel g (Equiv.refl _) = g := by
  cases g
  rfl

theorem relabel_comp (g : Generators) (e f : Equiv.Perm (Fin 3)) :
    relabel (relabel g e) f = relabel g (f.trans e) := rfl




@[simp] theorem rotate_isArmA {g : Generators} (D : HerzogCriticalData g) (i j : Fin 3) (q : ℤ) :
    IsArmA (rotateHerzog D i) q j ↔ IsArmA D q (rotatePerm i j) := by
  unfold IsArmA
  rw [rotateHerzog_fA]
  rfl

@[simp] theorem rotate_isArmB {g : Generators} (D : HerzogCriticalData g) (i j : Fin 3) (q : ℤ) :
    IsArmB (rotateHerzog D i) q j ↔ IsArmB D q (rotatePerm i j) := by
  unfold IsArmB
  rw [rotateHerzog_fB]
  rfl

@[simp] theorem reverse_isArmA {g : Generators} (D : HerzogCriticalData g) (j : Fin 3) (q : ℤ) :
    IsArmA (reverseHerzog D) q j ↔ IsArmB D q (reversePerm j) := by
  unfold IsArmA IsArmB
  rw [reverseHerzog_fA]
  rfl

@[simp] theorem reverse_isArmB {g : Generators} (D : HerzogCriticalData g) (j : Fin 3) (q : ℤ) :
    IsArmB (reverseHerzog D) q j ↔ IsArmA D q (reversePerm j) := by
  unfold IsArmA IsArmB
  rw [reverseHerzog_fB]
  rfl

@[simp] theorem reversePerm_self (i : Fin 3) : reversePerm (reversePerm i) = i := by fin_cases i <;> rfl
@[simp] theorem reversePerm_next (i : Fin 3) : reversePerm (next i) = prev (reversePerm i) := by fin_cases i <;> rfl
@[simp] theorem reversePerm_prev (i : Fin 3) : reversePerm (prev i) = next (reversePerm i) := by fin_cases i <;> rfl

end P21.Nonsymmetric
