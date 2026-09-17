import P21.Nonsymmetric.ColorCap.BoxInput

namespace P21.Nonsymmetric.ColorCap

/-- The common mass estimate behind both White-class multiplicity contradictions. -/
theorem failure_cone_mass (k s R p e1 e2 e3 u y v : ℤ)
    (hk : 2 ≤ k) (hs : 1 ≤ s) (hR : 1 ≤ R) (hRk : k ≤ R+1)
    (hp : 1 ≤ p) (he1 : 1 ≤ e1) (he2 : 1 ≤ e2) (he3 : 1 ≤ e3)
    (hu : 0 ≤ u) (hy : 0 ≤ y) (hv : 0 ≤ v) :
    let w1 := (1+R)*e1+k*u
    let w2 := (1+R)*e2+s*k*y
    let w3 := ((k-1)*R-1)*p+s*(1+R)*e3+R*k*v
    0 ≤ w1 ∧ 0 ≤ w2 ∧ 0 ≤ w3 ∧ k*(1+s+R) ≤ w1+w2+w3 := by
  dsimp
  have hA : 0 ≤ (k-1)*R-1 := by nlinarith
  have he1' : 0 ≤ e1-1 := by omega
  have he2' : 0 ≤ e2-1 := by omega
  have he3' : 0 ≤ e3-1 := by omega
  have hp' : 0 ≤ p-1 := by omega
  have hbase : 0 ≤ (s+1)*(R+1-k) := by positivity
  have hrest : 0 ≤ (R+1)*(e1-1)+(R+1)*(e2-1)+s*(R+1)*(e3-1)+
      ((k-1)*R-1)*(p-1)+k*u+s*k*y+R*k*v := by positivity
  refine ⟨by positivity,by positivity,by positivity,?_⟩
  nlinarith only [hbase,hrest]

/-- Color A: the source AP parametrization alone already forces multiplicity failure. -/
theorem colorA_parameter_contradiction (m : ℤ) (n e p b : Point)
    (k r q ell u y v : ℤ) (hm : 0 < m) (hn : ∀ i, m < n i)
    (he : ∀ i, 1 ≤ e i) (hp : ∀ i, 1 ≤ p i)
    (hk : 2 ≤ k) (hr : 1 ≤ r) (_hrk : r < k) (_hq : 1 ≤ q) (hqk : q < k)
    (hinverse : r*q = 1+ell*k) (hu : 0 ≤ u) (hy : 0 ≤ y) (hv : 0 ≤ v)
    (hb0 : b 0 = (k-q)*p 0+k*u)
    (hb1 : b 1 = p 1+(r-1)*(e 1+p 1)+k*y)
    (hb2 : b 2 = q*p 2+(k-q-1)*(e 2+p 2)+k*v)
    (hrow0 : k*m = (e 0+b 0)*n 0+e 1*n 1-p 2*n 2)
    (hrow1 : k*m = -p 0*n 0+(e 1+b 1)*n 1+e 2*n 2)
    (hrow2 : k*m = e 0*n 0-p 1*n 1+(e 2+b 2)*n 2) : False := by
  let s := k-q
  let R := r*s
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hR : 1 ≤ R := by dsimp [R]; nlinarith
  have hella : 1 ≤ r-ell := by nlinarith
  have hidentity : R+1 = k*(r-ell) := by dsimp [R,s]; nlinarith [hinverse]
  have hRk : k ≤ R+1 := by nlinarith
  obtain ⟨hw1,hw2,hw3,hmass⟩ := failure_cone_mass k s R (p 2)
    (e 0) (e 1) (e 2) u y v hk hs hR hRk (hp 2) (he 0) (he 1) (he 2) hu hy hv
  apply weighted_certificate_impossible m (k*(1+s+R)) n
    ![(1+R)*e 0+k*u,(1+R)*e 1+s*k*y,
      ((k-1)*R-1)*p 2+s*(1+R)*e 2+R*k*v] hm (by positivity) hn
  · intro i; fin_cases i <;> simp <;> assumption
  · simpa [Fin.sum_univ_succ, add_assoc] using hmass
  · simp [weight, Fin.sum_univ_succ]
    rw [hb0] at hrow0
    rw [hb1] at hrow1
    rw [hb2] at hrow2
    dsimp [R,s] at *
    linear_combination hrow0 + (k-q)*hrow1 + r*(k-q)*hrow2

end P21.Nonsymmetric.ColorCap

namespace P21.Nonsymmetric.ColorCap

/-- Color B: the source BP parametrization yields the second master contradiction. -/
theorem colorB_parameter_contradiction (m : ℤ) (n e p a : Point)
    (k r q ell u y v : ℤ) (hm : 0 < m) (hn : ∀ i, m < n i)
    (he : ∀ i, 1 ≤ e i) (hp : ∀ i, 1 ≤ p i)
    (hk : 2 ≤ k) (_hr : 1 ≤ r) (hrk : r < k) (hq : 1 ≤ q) (_hqk : q < k)
    (hinverse : r*q = 1+ell*k) (hu : 0 ≤ u) (hy : 0 ≤ y) (hv : 0 ≤ v)
    (ha0 : a 0 = q*p 0+k*u)
    (ha1 : a 1 = (q-1)*(e 1+p 1)+(k-q)*p 1+k*y)
    (ha2 : a 2 = p 2+(k-r-1)*(e 2+p 2)+k*v)
    (hrow0 : k*m = -p 0*n 0+e 1*n 1+(a 2+e 2)*n 2)
    (hrow1 : k*m = (a 0+e 0)*n 0-p 1*n 1+e 2*n 2)
    (hrow2 : k*m = e 0*n 0+(a 1+e 1)*n 1-p 2*n 2) : False := by
  let t := k-r
  let R := q*t
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hR : 1 ≤ R := by dsimp [R]; nlinarith
  have hella : 1 ≤ q-ell := by nlinarith
  have hidentity : R+1 = k*(q-ell) := by dsimp [R,t]; nlinarith [hinverse]
  have hRk : k ≤ R+1 := by nlinarith
  obtain ⟨hw1,hw2,hw3,hmass⟩ := failure_cone_mass k q R (p 1)
    (e 0) (e 2) (e 1) u v y hk hq hR hRk (hp 1) (he 0) (he 2) (he 1) hu hv hy
  apply weighted_certificate_impossible m (k*(1+q+R)) n
    ![(1+R)*e 0+k*u,((k-1)*R-1)*p 1+q*(1+R)*e 1+R*k*y,
      (1+R)*e 2+q*k*v] hm (by positivity) hn
  · intro i; fin_cases i <;> simp <;> assumption
  · simpa [Fin.sum_univ_succ, add_comm, add_left_comm, add_assoc] using hmass
  · simp [weight, Fin.sum_univ_succ]
    rw [ha0] at hrow1
    rw [ha1] at hrow2
    rw [ha2] at hrow0
    dsimp [R,t] at *
    linear_combination q*hrow0 + hrow1 + q*(k-r)*hrow2

end P21.Nonsymmetric.ColorCap


