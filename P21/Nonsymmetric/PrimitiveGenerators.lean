import P21.Nonsymmetric.Kernel
import P21.Nonsymmetric.Herzog.PseudoFrobenius
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace P21.Nonsymmetric
variable {g : Generators}

/-- Consecutive actual tail elements give an integer vector pairing to one. -/
theorem tail_bezout_vector (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H) :
    ∃ v : Fin 3 → ℤ, integerValue g v = 1 := by
  obtain ⟨B,hB⟩ := hcof
  obtain ⟨a,ha⟩ := hB B le_rfl
  obtain ⟨b,hb⟩ := hB (B+1) (by omega)
  refine ⟨fun i => (b i:ℤ)-a i, ?_⟩
  simp only [integerValue,sub_mul,Finset.sum_sub_distrib]
  change value g.n b-value g.n a = 1
  rw [ha,hb]
  ring

/-- Cofiniteness and the saturated integer kernel identify the primitive
cross-product minors, including their positive common scale. -/
theorem primitive_generator_minors (D : HerzogCriticalData g)
    (hp : ∀ i, 0 < g.n i)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H) :
    g.n 0 = (D.rho 1:ℤ)*D.rho 2-(D.a 1:ℤ)*D.b 2 ∧
    g.n 1 = (D.a 0:ℤ)*D.rho 2+(D.b 0:ℤ)*D.b 2 ∧
    g.n 2 = (D.a 0:ℤ)*D.a 1+(D.b 0:ℤ)*D.rho 1 := by
  classical
  obtain ⟨v,hv⟩ := tail_bezout_vector hcof
  let w : Fin 3 → Fin 3 → ℤ := fun j i => (if i=j then 1 else 0)-g.n j*v i
  have hw (j : Fin 3) : integerValue g (w j) = 0 := by
    have hh : integerValue g (w j) = g.n j-g.n j*integerValue g v := by
      simp [integerValue,w,sub_mul,Finset.sum_sub_distrib,Finset.mul_sum,mul_assoc]
    rw [hh,hv]
    ring
  choose S T hst using fun j => integer_kernel_span hp D (w j) (hw j)
  let A : Matrix (Fin 3) (Fin 3) ℤ := fun i j => ![v i,kernelRowJ D i,kernelRowK D i] j
  let B : Matrix (Fin 3) (Fin 3) ℤ := fun i j => ![g.n j,S j,T j] i
  have hAB : A*B = 1 := by
    ext i j
    have hh := hst j i
    dsimp [w] at hh
    rw [Matrix.mul_apply,Matrix.one_apply]
    simp [A,B,Fin.sum_univ_succ]
    nlinarith [hh]
  have hdet : A.det*B.det = 1 := by
    rw [← Matrix.det_mul,hAB,Matrix.det_one]
  have hv' : v 0*g.n 0+v 1*g.n 1+v 2*g.n 2 = 1 := by
    simpa [integerValue,Fin.sum_univ_succ,add_assoc] using hv
  have hminor : A.det*g.n 0 = (D.rho 1:ℤ)*D.rho 2-(D.a 1:ℤ)*D.b 2 := by
    rw [Matrix.det_fin_three]
    simp [A,kernelRowJ,kernelRowK]
    linear_combination ((D.rho 1:ℤ)*D.rho 2-(D.a 1:ℤ)*D.b 2)*hv' -
      (v 1*D.rho 2+v 2*D.a 1)*D.relation_one -
      (v 1*D.b 2+v 2*D.rho 1)*D.relation_two
  have hdetpos : 0 < A.det :=
    (mul_pos_iff_of_pos_right (hp 0)).mp (by rw [hminor]; exact kernel_minor_pos D)
  have hBpos : 0 < B.det :=
    (mul_pos_iff_of_pos_left hdetpos).mp (by rw [hdet]; norm_num)
  have hdetone : A.det = 1 := by
    have hle : A.det ≤ A.det*B.det := by
      simpa using mul_le_mul_of_nonneg_left (show (1:ℤ) ≤ B.det by omega) hdetpos.le
    omega
  rw [hdetone,one_mul] at hminor
  refine ⟨hminor,?_,?_⟩
  · have he : g.n 0*((D.a 0:ℤ)*D.rho 2+(D.b 0:ℤ)*D.b 2-g.n 1) = 0 := by
      linear_combination -(D.rho 2:ℤ)*D.relation_one-(D.b 2:ℤ)*D.relation_two-
        g.n 1*hminor
    have hz := (mul_eq_zero.mp he).resolve_left (ne_of_gt (hp 0))
    omega
  · have he : g.n 0*((D.a 0:ℤ)*D.a 1+(D.b 0:ℤ)*D.rho 1-g.n 2) = 0 := by
      linear_combination -(D.a 1:ℤ)*D.relation_one-(D.rho 1:ℤ)*D.relation_two-
        g.n 2*hminor
    have hz := (mul_eq_zero.mp he).resolve_left (ne_of_gt (hp 0))
    omega

/-- The primitive generator formulas in the publication's exact a/b convention. -/
theorem primitive_generator_formulas (D : HerzogCriticalData g)
    (hp : ∀ i, 0 < g.n i)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H) :
    g.n 0 = (D.a 1:ℤ)*D.a 2+(D.a 2:ℤ)*D.b 1+(D.b 1:ℤ)*D.b 2 ∧
    g.n 1 = (D.a 0:ℤ)*D.a 2+(D.a 0:ℤ)*D.b 2+(D.b 0:ℤ)*D.b 2 ∧
    g.n 2 = (D.a 0:ℤ)*D.a 1+(D.a 1:ℤ)*D.b 0+(D.b 0:ℤ)*D.b 1 := by
  obtain ⟨h0,h1,h2⟩ := primitive_generator_minors D hp hcof
  have hr1 : (D.rho 1:ℤ) = D.a 1+D.b 1 := by exact_mod_cast D.rho_eq 1
  have hr2 : (D.rho 2:ℤ) = D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
  refine ⟨?_,?_,?_⟩
  · rw [hr1,hr2] at h0
    nlinarith [h0]
  · rw [hr2] at h1
    nlinarith [h1]
  · rw [hr1] at h2
    nlinarith [h2]

end P21.Nonsymmetric


namespace P21.Nonsymmetric

/-- Complete publication §2.2.2 package: positive least critical relations,
exact distinct PF pair, and primitive generator identities for the same data. -/
theorem nonsymmetric_herzog_primitive_exists (g : Generators) (s : g.Setting)
    (hcof : ∃ B : ℤ, ∀ x : ℤ, B ≤ x → x ∈ g.H)
    (hns : ¬ P21.Symmetric.SymmetricTail g) :
    ∃ D : NonsymmetricHerzogData g,
      g.n 0 = (D.a 1:ℤ)*D.a 2+(D.a 2:ℤ)*D.b 1+(D.b 1:ℤ)*D.b 2 ∧
      g.n 1 = (D.a 0:ℤ)*D.a 2+(D.a 0:ℤ)*D.b 2+(D.b 0:ℤ)*D.b 2 ∧
      g.n 2 = (D.a 0:ℤ)*D.a 1+(D.a 1:ℤ)*D.b 0+(D.b 0:ℤ)*D.b 1 := by
  obtain ⟨D⟩ := nonsymmetric_herzog_exists g s hcof hns
  exact ⟨D,primitive_generator_formulas D.toHerzogCriticalData
    (fun i => lt_trans s.m_pos (s.n_gt i)) hcof⟩

end P21.Nonsymmetric
