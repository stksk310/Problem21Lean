import P21.Nonsymmetric.Path.Comparison

namespace P21.Nonsymmetric

variable {g : Generators}

/-- Arithmetic core of the `H₀ < J₀` seam.  All criticality calls occur after
the m-coordinate has disappeared. -/
theorem path_seam_rigidity (D : HerzogCriticalData g) (hp : ∀ i, 0 < g.n i)
    (Ac e Bc : ℤ) (hAc : 0 < Ac) (he : 0 < e) (hBc : 0 < Bc)
    (helt : e < D.rho 1)
    (haUpper : Ac - D.rho 0 < D.rho 0)
    (hvUpper : Bc - D.a 2 < D.rho 2)
    (hrel : Ac * g.n 0 = e * g.n 1 + Bc * g.n 2) :
    Ac = D.rho 0 ∧ e = D.b 1 ∧ Bc = D.a 2 := by
  have hcrit := herzog_critical_le_int D (by decide : (0 : Fin 3) ≠ 1)
    (by decide : (0 : Fin 3) ≠ 2) Ac e Bc hAc he.le hBc.le hrel
  let a := Ac - (D.rho 0 : ℤ)
  let u := e - (D.b 1 : ℤ)
  let v := Bc - (D.a 2 : ℤ)
  have ha : 0 ≤ a := by dsimp [a]; omega
  have hau : a < D.rho 0 := by simpa [a] using haUpper
  have hue : u < D.rho 1 := by
    dsimp [u]
    have := D.b_pos 1
    omega
  have hvv : v < D.rho 2 := by simpa [v] using hvUpper
  have hzero : a * g.n 0 = u * g.n 1 + v * g.n 2 := by
    dsimp [a, u, v]
    linear_combination hrel - D.relation_zero
  by_cases hu : 0 ≤ u
  · by_cases hv : 0 ≤ v
    · have haz : a = 0 := by
        by_contra han
        have hac := herzog_critical_le_int D (by decide : (0 : Fin 3) ≠ 1)
          (by decide : (0 : Fin 3) ≠ 2) a u v (by omega) hu hv hzero
        omega
      have huz : u = 0 := by
        have hz : u * g.n 1 + v * g.n 2 = 0 := by rw [← hzero, haz, zero_mul]
        have h1 := mul_nonneg hu (hp 1).le
        have h2 := mul_nonneg hv (hp 2).le
        have : u * g.n 1 = 0 := by omega
        exact (mul_eq_zero.mp this).resolve_right (ne_of_gt (hp 1))
      have hvz : v = 0 := by
        have hz : v * g.n 2 = 0 := by
          rw [haz, huz, zero_mul, zero_mul, zero_add] at hzero
          exact hzero.symm
        exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt (hp 2))
      dsimp [a, u, v] at haz huz hvz
      omega
    · have hvneg : 0 < -v := by omega
      have huPos : 0 < u := by
        by_contra huz
        have : u = 0 := by omega
        have hneg := mul_pos hvneg (hp 2)
        rw [this, zero_mul, zero_add] at hzero
        have hleft := mul_nonneg ha (hp 0).le
        have hright : v * g.n 2 < 0 := mul_neg_of_neg_of_pos (by omega) (hp 2)
        omega
      have hc := herzog_critical_le_int D (by decide : (1 : Fin 3) ≠ 0)
        (by decide : (1 : Fin 3) ≠ 2) u a (-v) huPos ha hvneg.le (by
          nlinarith [hzero])
      omega
  · by_cases hv : 0 ≤ v
    · have hvPos : 0 < v := by
        by_contra hvz
        have : v = 0 := by omega
        have hneg := mul_pos (show 0 < -u by omega) (hp 1)
        rw [this, zero_mul, add_zero] at hzero
        have hleft := mul_nonneg ha (hp 0).le
        have hright : u * g.n 1 < 0 := mul_neg_of_neg_of_pos (by omega) (hp 1)
        omega
      have hc := herzog_critical_le_int D (by decide : (2 : Fin 3) ≠ 0)
        (by decide : (2 : Fin 3) ≠ 1) v a (-u) hvPos ha (by omega) (by
          nlinarith [hzero])
      omega
    · have hleft := mul_nonneg ha (hp 0).le
      have hright : u * g.n 1 + v * g.n 2 < 0 := by
        have h1 := mul_neg_of_neg_of_pos (by omega : u < 0) (hp 1)
        have h2 := mul_neg_of_neg_of_pos (by omega : v < 0) (hp 2)
        omega
      nlinarith [hzero]

end P21.Nonsymmetric
