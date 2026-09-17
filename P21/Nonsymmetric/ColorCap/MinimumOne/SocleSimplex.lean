import P21.Nonsymmetric.ColorCap.MinimumOne.Setup
import P21.Nonsymmetric.White.RelativeIndex

namespace P21.Nonsymmetric.ColorCap.MinimumOne
variable {g : Generators}

/-- The signed row differences are exactly the frozen saturated kernel basis. -/
theorem socleMatrix_kernelJ (D : HerzogCriticalData g) (c : Bool) (p : Point) (j : Fin 3) :
    kernelRowJ D j = if c then socleMatrix D c p 1 j-socleMatrix D c p 0 j
      else socleMatrix D c p 1 j-socleMatrix D c p 2 j := by
  have hr (i) : (D.rho i:ℤ) = D.a i+D.b i := by exact_mod_cast D.rho_eq i
  cases c <;> fin_cases j <;> simp [kernelRowJ,socleMatrix,socleRows,hr] <;> ring

theorem socleMatrix_kernelK (D : HerzogCriticalData g) (c : Bool) (p : Point) (j : Fin 3) :
    kernelRowK D j = if c then socleMatrix D c p 2 j-socleMatrix D c p 1 j
      else socleMatrix D c p 2 j-socleMatrix D c p 0 j := by
  have hr (i) : (D.rho i:ℤ) = D.a i+D.b i := by exact_mod_cast D.rho_eq i
  cases c <;> fin_cases j <;> simp [kernelRowK,socleMatrix,socleRows,hr] <;> ring

/-- Exact integer row coordinates, with their sum equal to the prescribed height.
This avoids conflating saturated kernel with primitive weight vector. -/
theorem socleMatrix_span_level (D : HerzogCriticalData g) (c : Bool) (p : Point)
    (hp : ∀ i, 0 < g.n i) (d : ℤ)
    (hrows : ∀ i, weight g.n (socleMatrix D c p i) = d)
    (z : Point) (l : ℤ) (hz : weight g.n z = l*d) :
    ∃ a : Point, (∀ j, z j = ∑ i, a i*socleMatrix D c p i j) ∧ ∑ i,a i = l := by
  let v : Point := fun j => z j-l*socleMatrix D c p 0 j
  have hv : integerValue g v = 0 := by
    change (∑ j,(z j-l*socleMatrix D c p 0 j)*g.n j) = 0
    simp only [sub_mul,mul_assoc,Finset.sum_sub_distrib,← Finset.mul_sum]
    change weight g.n z-l*weight g.n (socleMatrix D c p 0) = 0
    rw [hz,hrows]; ring
  obtain ⟨S,T,hst⟩ := integer_kernel_span hp D v hv
  cases c
  · refine ⟨![l-T,S,T-S],?_,by simp [Fin.sum_univ_succ]⟩
    intro j
    have h := hst j
    rw [socleMatrix_kernelJ D false p j,socleMatrix_kernelK D false p j] at h
    dsimp [v] at h
    simp [Fin.sum_univ_succ]
    linear_combination h
  · refine ⟨![l-S,S-T,T],?_,by simp [Fin.sum_univ_succ]⟩
    intro j
    have h := hst j
    rw [socleMatrix_kernelJ D true p j,socleMatrix_kernelK D true p j] at h
    dsimp [v] at h
    simp [Fin.sum_univ_succ]
    linear_combination h

/-- Source LAT in explicit coordinates: the integer row span is L_d. -/
theorem socleMatrix_row_lattice (D : HerzogCriticalData g) (c : Bool) (p : Point)
    (hp : ∀ i, 0 < g.n i) (d : ℤ)
    (hrows : ∀ i, weight g.n (socleMatrix D c p i) = d) (z : Point) :
    z ∈ relativeLattice g.n d ↔ ∃ a : Point, ∀ j, z j = ∑ i,a i*socleMatrix D c p i j := by
  constructor
  · intro hz
    obtain ⟨l,hl⟩ := hz
    obtain ⟨a,ha,_⟩ := socleMatrix_span_level D c p hp d hrows z l (by linarith [hl])
    exact ⟨a,ha⟩
  · rintro ⟨a,ha⟩
    change d ∣ weight g.n z
    refine ⟨∑ i,a i,?_⟩
    have he : weight g.n z = ∑ i,a i*weight g.n (socleMatrix D c p i) := by
      simp only [weight,ha,Finset.sum_mul,Finset.mul_sum,mul_assoc]
      rw [Finset.sum_comm]
    rw [he]
    simp only [hrows,← Finset.sum_mul]
    ring

end P21.Nonsymmetric.ColorCap.MinimumOne
