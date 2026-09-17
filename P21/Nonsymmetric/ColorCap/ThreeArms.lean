import P21.Nonsymmetric.ColorCap.BoxInput
import P21.Nonsymmetric.Herzog.PseudoFrobenius

namespace P21.Nonsymmetric.ColorCap

/-- A positive-depth actual PF arm puts its own socle element in the original Γ. -/
theorem socle_mem_of_actual_arm (g : Generators) (s : g.Setting) (f depth : ℤ)
    (i : Fin 3) (hd : 1 ≤ depth) (hq : f-depth*g.n i ∈ s.semigroup.PF) : f ∈ g.Gamma := by
  have hn : 0 < g.n i := lt_trans s.m_pos (s.n_gt i)
  have hmem : depth*g.n i ∈ g.Gamma := by
    simpa only [nsmul_eq_mul, Int.toNat_of_nonneg (by omega : 0 ≤ depth)] using
      g.Gamma.nsmul_mem (g.n_mem i) depth.toNat
  have hnonzero : depth*g.n i ≠ 0 := ne_of_gt (mul_pos (by omega) hn)
  have hreturn := hq.2 _ hmem hnonzero
  change f-depth*g.n i+depth*g.n i ∈ g.Gamma at hreturn
  simpa using hreturn

/-- Actual PF arms, with no supplied factorization, produce the attained MIN input. -/
theorem actual_three_arm_minimum (g : Generators) (s : g.Setting) (f : ℤ)
    (depth : Point) (hdepth : ∀ i, 1 ≤ depth i)
    (harms : ∀ i, f-depth i*g.n i ∈ s.semigroup.PF) (hgap : f ∉ g.H) :
    ∃ k : ℕ, ∃ p : Point,
      0 < k ∧ (∀ i, 1 ≤ p i ∧ p i ≤ depth i) ∧
      f = (k : ℤ)*g.m+∑ i, (p i-1)*g.n i ∧
      ∀ k' : ℕ, ∀ x' : Fin 3 → ℕ,
        f = (k' : ℤ)*g.m+value g.n x' → k ≤ k' := by
  apply minimal_positive_arm_box g f depth
  · exact socle_mem_of_actual_arm g s f (depth 0) 0 (hdepth 0) (harms 0)
  · exact hgap
  · exact fun i => (harms i).1

/-- Color A inherits MIN from true Herzog data and its actual PF arms. -/
theorem colorA_actual_minimum (g : Generators) (s : g.Setting)
    (D : HerzogCriticalData g) (depth : Point) (hdepth : ∀ i, 1 ≤ depth i)
    (harms : ∀ i, D.fA-depth i*g.n i ∈ s.semigroup.PF) :
    ∃ k : ℕ, ∃ p : Point,
      0 < k ∧ (∀ i, 1 ≤ p i ∧ p i ≤ depth i) ∧
      D.fA = (k : ℤ)*g.m+∑ i, (p i-1)*g.n i ∧
      ∀ k' : ℕ, ∀ x' : Fin 3 → ℕ,
        D.fA = (k' : ℤ)*g.m+value g.n x' → k ≤ k' :=
  actual_three_arm_minimum g s D.fA depth hdepth harms
    (D.fA_gap (fun i => lt_trans s.m_pos (s.n_gt i)))

/-- The second color has exactly the same actual-minimum construction. -/
theorem colorB_actual_minimum (g : Generators) (s : g.Setting)
    (D : HerzogCriticalData g) (depth : Point) (hdepth : ∀ i, 1 ≤ depth i)
    (harms : ∀ i, D.fB-depth i*g.n i ∈ s.semigroup.PF) :
    ∃ k : ℕ, ∃ p : Point,
      0 < k ∧ (∀ i, 1 ≤ p i ∧ p i ≤ depth i) ∧
      D.fB = (k : ℤ)*g.m+∑ i, (p i-1)*g.n i ∧
      ∀ k' : ℕ, ∀ x' : Fin 3 → ℕ,
        D.fB = (k' : ℤ)*g.m+value g.n x' → k ≤ k' :=
  actual_three_arm_minimum g s D.fB depth hdepth harms
    (D.fB_gap (fun i => lt_trans s.m_pos (s.n_gt i)))

/-- MINBOX at level one yields precisely INPUT, with the same original generators. -/
def colorA_boxInput (g : Generators) (s : g.Setting) (D : HerzogCriticalData g)
    (p : Point) (hp : ∀ i, 1 ≤ p i ∧ p i < D.a i)
    (hf : D.fA = g.m+∑ i, (p i-1)*g.n i) : BoxInput where
  m := g.m
  n := g.n
  x := p
  y := fun i => (D.a i : ℤ)-p i
  b := fun i => D.b i
  m_pos := s.m_pos
  n_gt := s.n_gt
  x_pos := fun i => (hp i).1
  y_pos := fun i => by have := (hp i).2; omega
  b_pos := fun i => by have := D.b_pos i; omega
  row0 := by
    have ha := D.fA_apery_formula
    have hr : (D.rho 1 : ℤ) = D.a 1+D.b 1 := by exact_mod_cast D.rho_eq 1
    simp [Fin.sum_univ_succ] at hf
    linear_combination hf - ha - g.n 1*hr
  row1 := by
    have hr : (D.rho 0 : ℤ) = D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
    dsimp [HerzogCriticalData.fA] at hf
    simp [Fin.sum_univ_succ] at hf
    have hr2 : (D.rho 2 : ℤ) = D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
    linear_combination hf + D.relation_two - g.n 0*hr - g.n 2*hr2
  row2 := by
    have hr : (D.rho 0 : ℤ) = D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
    dsimp [HerzogCriticalData.fA] at hf
    simp [Fin.sum_univ_succ] at hf
    linear_combination hf - g.n 0*hr

/-- Exact remaining dynamics input, recorded as a proposition, not an assumed theorem. -/
def BoxPositiveExitStatement : Prop :=
  ∀ (D : BoxInput) (t : ℕ) (u : Point), BoxPath D.upper D.rows t D.x u →
    (∀ i, ¬ InBox D.upper (fire D.rows i u)) → ∃ i, ∀ j, 1 ≤ fire D.rows i u j

/-- Conditional endpoint: MINBOX and DPE exclude the original actual color-A arms. -/
theorem colorA_three_arm_contradiction_of_minbox
    (hdpe : BoxPositiveExitStatement) (g : Generators) (s : g.Setting)
    (D : HerzogCriticalData g) (depth p : Point)
    (hp : ∀ i, 1 ≤ p i ∧ p i ≤ depth i) (hcap : ∀ i, depth i < D.a i)
    (hf : D.fA = g.m+∑ i, (p i-1)*g.n i)
    (harms : ∀ i, D.fA-depth i*g.n i ∈ s.semigroup.PF) : False := by
  let B := colorA_boxInput g s D p (fun i => ⟨(hp i).1,lt_of_le_of_lt (hp i).2 (hcap i)⟩) hf
  obtain ⟨t,u,hpath,hmax⟩ := B.maximal_path
  obtain ⟨i,hpositive⟩ := hdpe B t u hpath hmax
  apply path_exit_contradiction g D.fA B.upper p depth B.rows B.rows_weight hf
    (fun j => (harms j).1) _ hpath i hpositive (hmax i)
  intro j
  have := hcap j
  change depth j ≤ p j + ((D.a j : ℤ)-p j) - 1
  omega

end P21.Nonsymmetric.ColorCap


namespace P21.Nonsymmetric.ColorCap

/-- The odd swap (1 2) carries color B to the canonical box matrix, swapping a/b. -/
def colorB_boxInput (g : Generators) (s : g.Setting) (D : HerzogCriticalData g)
    (p : Point) (hp : ∀ i, 1 ≤ p i ∧ p i < D.b i)
    (hf : D.fB = g.m+∑ i, (p i-1)*g.n i) : BoxInput where
  m := g.m
  n := ![g.n 0,g.n 2,g.n 1]
  x := ![p 0,p 2,p 1]
  y := ![(D.b 0 : ℤ)-p 0,(D.b 2 : ℤ)-p 2,(D.b 1 : ℤ)-p 1]
  b := ![D.a 0,D.a 2,D.a 1]
  m_pos := s.m_pos
  n_gt := by intro i; fin_cases i <;> simp <;> apply s.n_gt
  x_pos := by intro i; fin_cases i <;> simp <;> exact (hp _).1
  y_pos := by
    intro i
    have hp0 := (hp 0).2; have hp1 := (hp 1).2; have hp2 := (hp 2).2
    fin_cases i <;> simp <;> omega
  b_pos := by
    intro i
    have ha0 := D.a_pos 0; have ha1 := D.a_pos 1; have ha2 := D.a_pos 2
    fin_cases i <;> simp <;> omega
  row0 := by
    simp
    have ha := D.fB_apery_formula
    have hr : (D.rho 2 : ℤ) = D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
    simp [Fin.sum_univ_succ] at hf
    linear_combination hf-ha-g.n 2*hr
  row1 := by
    simp
    have hr0 : (D.rho 0 : ℤ) = D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
    have hr1 : (D.rho 1 : ℤ) = D.a 1+D.b 1 := by exact_mod_cast D.rho_eq 1
    dsimp [HerzogCriticalData.fB] at hf
    simp [Fin.sum_univ_succ] at hf
    linear_combination hf+D.relation_one-g.n 0*hr0-g.n 1*hr1
  row2 := by
    simp
    have hr : (D.rho 0 : ℤ) = D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
    dsimp [HerzogCriticalData.fB] at hf
    simp [Fin.sum_univ_succ] at hf
    linear_combination hf-g.n 0*hr

/-- The color-B exit is transported back to the same original actual PF arms. -/
theorem colorB_three_arm_contradiction_of_minbox
    (hdpe : BoxPositiveExitStatement) (g : Generators) (s : g.Setting)
    (D : HerzogCriticalData g) (depth p : Point)
    (hp : ∀ i, 1 ≤ p i ∧ p i ≤ depth i) (hcap : ∀ i, depth i < D.b i)
    (hf : D.fB = g.m+∑ i, (p i-1)*g.n i)
    (harms : ∀ i, D.fB-depth i*g.n i ∈ s.semigroup.PF) : False := by
  let B := colorB_boxInput g s D p (fun i => ⟨(hp i).1,lt_of_le_of_lt (hp i).2 (hcap i)⟩) hf
  obtain ⟨t,u,hpath,hmax⟩ := B.maximal_path
  obtain ⟨i,hpositive⟩ := hdpe B t u hpath hmax
  let w := fire B.rows i u
  let v : Point := ![w 0,w 2,w 1]
  have hw := hpath.weight_eq B.rows_weight
  have hfire := fire_weight B.n B.rows i u
  rw [B.rows_weight] at hfire
  have hv : ∀ j, 1 ≤ v j := by
    intro j
    fin_cases j <;> simp [v,w] <;> exact hpositive _
  have he : D.fB = ((t : ℤ)+2)*g.m+∑ j, (v j-1)*g.n j := by
    change weight B.n w = weight B.n u-B.m at hfire
    simp [B,colorB_boxInput,weight,Fin.sum_univ_succ,v] at hw hfire hf ⊢
    linear_combination hf-hw-hfire
  apply same_element_positive_exit g D.fB ((t : ℤ)+2) v depth (fun j => D.b j)
    (by positivity) hv he (fun j => (harms j).1) (fun j => by have := hcap j; omega)
  have hex : ∃ j, B.upper j ≤ w j := by
    by_contra hn
    push Not at hn
    apply hmax i
    intro j
    exact ⟨hpositive j,by change w j ≤ B.upper j-1; have := hn j; omega⟩
  obtain ⟨j,hj⟩ := hex
  fin_cases j
  · refine ⟨0,?_⟩
    simpa [B,colorB_boxInput,BoxInput.upper,v] using hj
  · refine ⟨2,?_⟩
    simpa [B,colorB_boxInput,BoxInput.upper,v] using hj
  · refine ⟨1,?_⟩
    simpa [B,colorB_boxInput,BoxInput.upper,v] using hj

end P21.Nonsymmetric.ColorCap

