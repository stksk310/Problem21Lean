import P21.Nonsymmetric.ColorCap.Residuals
import P21.Nonsymmetric.PrimitiveGenerators
import P21.Nonsymmetric.HerzogCoordinates

namespace P21.Nonsymmetric.ColorCap.MinimumOne
variable {g : Generators}

def socleRows (D : HerzogCriticalData g) (colorA : Bool) : Matrix (Fin 3) (Fin 3) ℤ :=
  if colorA then
    ![![0,D.rho 1,D.a 2],![D.a 0,0,D.rho 2],![D.rho 0,D.a 1,0]]
  else
    ![![0,D.b 1,D.rho 2],![D.rho 0,0,D.b 2],![D.b 0,D.rho 1,0]]

def socle (D : HerzogCriticalData g) (colorA : Bool) : ℤ :=
  (if colorA then D.fA else D.fB)+∑ i, g.n i

def socleMatrix (D : HerzogCriticalData g) (colorA : Bool) (p : Point) :
    Matrix (Fin 3) (Fin 3) ℤ := fun i j => socleRows D colorA i j-p j

theorem socleRows_diagonal (D : HerzogCriticalData g) (c : Bool) (i : Fin 3) :
    socleRows D c i i = 0 := by cases c <;> fin_cases i <;> rfl

theorem socleRows_off_diagonal (D : HerzogCriticalData g) (c : Bool)
    (i j : Fin 3) (h : i ≠ j) : 0 < socleRows D c i j := by
  cases c <;> fin_cases i <;> fin_cases j <;>
    simp_all [socleRows,D.a_pos,D.b_pos,D.rho_pos]

theorem socleRows_nonneg (D : HerzogCriticalData g) (c : Bool) (i j : Fin 3) :
    0 ≤ socleRows D c i j := by
  by_cases h : i = j
  · subst j; rw [socleRows_diagonal]
  · exact (socleRows_off_diagonal D c i j h).le

theorem socleRows_weight (D : HerzogCriticalData g) (c : Bool) (i : Fin 3) :
    weight g.n (socleRows D c i) = socle D c := by
  have eA0 := D.fA_cyclic 0
  have eA1 := D.fA_cyclic 1
  have eA2 := D.fA_cyclic 2
  have eB0 := D.fB_cyclic 0
  have eB1 := D.fB_cyclic 1
  have eB2 := D.fB_cyclic 2
  simp [next,prev] at eA0 eA1 eA2 eB0 eB1 eB2
  cases c <;> fin_cases i <;>
    simp [socleRows,socle,weight,Fin.sum_univ_succ] <;> linarith

theorem socle_minimum_weight (D : HerzogCriticalData g) (c : Bool) (p : Point) (k : ℕ)
    (he : (if c then D.fA else D.fB) = (k:ℤ)*g.m+∑ i,(p i-1)*g.n i) :
    socle D c-weight g.n p = (k:ℤ)*g.m := by
  simp only [socle,weight,sub_mul,one_mul,Finset.sum_sub_distrib] at *
  linarith

theorem socleMatrix_weight (D : HerzogCriticalData g) (c : Bool) (p : Point) (k : ℕ)
    (he : (if c then D.fA else D.fB) = (k:ℤ)*g.m+∑ i,(p i-1)*g.n i) (i : Fin 3) :
    weight g.n (socleMatrix D c p i) = (k:ℤ)*g.m := by
  change weight g.n (socleRows D c i-p) = _
  rw [weight_sub,socleRows_weight,socle_minimum_weight D c p k he]

/-- Primitivity is supplied by tail cofiniteness, not by kernel saturation. -/
theorem socleMatrix_det (D : HerzogCriticalData g) (c : Bool) (p : Point)
    (hp : ∀ i, 0 < g.n i) (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H) :
    (socleMatrix D c p).det = socle D c-weight g.n p := by
  obtain ⟨h0,h1,h2⟩ := primitive_generator_formulas D hp hcof
  have hr (i) : (D.rho i:ℤ) = D.a i+D.b i := by exact_mod_cast D.rho_eq i
  rw [Matrix.det_fin_three]
  cases c <;> simp [socleMatrix,socleRows,socle,weight,HerzogCriticalData.fA,
    HerzogCriticalData.fB,Fin.sum_univ_succ,h0,h1,h2,hr] <;> ring

theorem socleMatrix_det_level (D : HerzogCriticalData g) (c : Bool) (p : Point) (k : ℕ)
    (hp : ∀ i, 0 < g.n i) (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (he : (if c then D.fA else D.fB) = (k:ℤ)*g.m+∑ i,(p i-1)*g.n i) :
    (socleMatrix D c p).det = (k:ℤ)*g.m := by
  rw [socleMatrix_det D c p hp hcof,socle_minimum_weight D c p k he]

end P21.Nonsymmetric.ColorCap.MinimumOne
