import P21.Nonsymmetric.ColorCap.MinimumOne.Setup
import P21.Nonsymmetric.ColorCap.MinimumOne.ColorA
import P21.Nonsymmetric.ColorCap.MinimumOne.ColorB
import P21.Nonsymmetric.Relabel

namespace P21.Nonsymmetric.ColorCap.MinimumOne

theorem rowsA_eq_socleRows {g : Generators} (D : HerzogCriticalData g) :
    rowsA (fun i=>(D.a i:ℤ)) (fun i=>(D.b i:ℤ))=socleRows D true := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rowsA,socleRows,D.rho_eq]

theorem rowsB_eq_socleRows {g : Generators} (D : HerzogCriticalData g) :
    rowsB (fun i=>(D.a i:ℤ)) (fun i=>(D.b i:ℤ))=socleRows D false := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rowsB,socleRows,D.rho_eq]

/-- The two arithmetic closures applied to the actual Herzog rows. -/
theorem integral_class_contradiction (g : Generators) (s : g.Setting)
    (D : HerzogCriticalData g) (c : Bool) (k : ℕ) (p : Point)
    (r q ell : ℤ) (z : Point)
    (hp : ∀ i, 1≤p i ∧ p i<(if c then (D.a i:ℤ) else (D.b i:ℤ)))
    (he : (if c then D.fA else D.fB)=(k:ℤ)*g.m+∑ i,(p i-1)*g.n i)
    (hmin : ∀ k' : ℕ, ∀ x' : Fin 3 → ℕ,
      (if c then D.fA else D.fB)=(k':ℤ)*g.m+value g.n x' → k≤k')
    (hk : 2≤(k:ℤ)) (hr : 1≤r) (hrk : r<k) (hq : 1≤q) (hqk : q<k)
    (hinv : r*q=1+ell*(k:ℤ))
    (hz : ∀ l, (k:ℤ)*z l=socleRows D c 0 l+
      r*(socleRows D c 1 l-socleRows D c 2 l)-p l) : False := by
  have hpw : weight g.n p=socle D c-(k:ℤ)*g.m := by
    have := socle_minimum_weight D c p k he
    omega
  have ha : ∀ i, 1≤(D.a i:ℤ) := by intro i; have:=D.a_pos i; omega
  have hb : ∀ i, 1≤(D.b i:ℤ) := by intro i; have:=D.b_pos i; omega
  cases c
  · apply colorB_integral_class_contradiction g D.fB (socle D false) k
      (fun i=>(D.a i:ℤ)) (fun i=>(D.b i:ℤ)) p z r q ell s.m_pos s.n_gt
      (by rfl) hmin (fun i=>(hp i).1) (fun i=>(hp i).2) ha
      hk hr hrk hq hqk hinv hpw
    · intro i; rw [rowsB_eq_socleRows]; exact socleRows_weight D false i
    · simpa only [rowsB_eq_socleRows] using hz
  · apply colorA_integral_class_contradiction g D.fA (socle D true) k
      (fun i=>(D.a i:ℤ)) (fun i=>(D.b i:ℤ)) p z r q ell s.m_pos s.n_gt
      (by rfl) hmin (fun i=>(hp i).1) (fun i=>(hp i).2) hb
      hk hr hrk hq hqk hinv hpw
    · intro i; rw [rowsA_eq_socleRows]; exact socleRows_weight D true i
    · simpa only [rowsA_eq_socleRows] using hz

theorem socleRows_rotate {g : Generators} (D : HerzogCriticalData g) (c : Bool)
    (i j l : Fin 3) :
    socleRows (rotateHerzog D i) c j l =
      socleRows D c (rotatePerm i j) (rotatePerm i l) := by
  cases c <;> fin_cases i <;> fin_cases j <;> fin_cases l <;> rfl

/-- Any distinguished row is reduced by an honest cyclic relabeling of the same
actual minimum; no generator or row ordering is imposed on the input. -/
theorem rotated_integral_class_contradiction (g : Generators) (s : g.Setting)
    (D : HerzogCriticalData g) (c : Bool) (k : ℕ) (p : Point) (i : Fin 3)
    (r q ell : ℤ) (z : Point)
    (hp : ∀ l, 1≤p l ∧ p l<(if c then (D.a l:ℤ) else (D.b l:ℤ)))
    (he : (if c then D.fA else D.fB)=(k:ℤ)*g.m+∑ l,(p l-1)*g.n l)
    (hmin : ∀ k' : ℕ, ∀ x' : Fin 3 → ℕ,
      (if c then D.fA else D.fB)=(k':ℤ)*g.m+value g.n x' → k≤k')
    (hk : 2≤(k:ℤ)) (hr : 1≤r) (hrk : r<k) (hq : 1≤q) (hqk : q<k)
    (hinv : r*q=1+ell*(k:ℤ))
    (hz : ∀ l, (k:ℤ)*z l=socleRows D c i l+
      r*(socleRows D c (next i) l-socleRows D c (prev i) l)-p l) : False := by
  apply integral_class_contradiction (relabel g (rotatePerm i))
    (relabelSetting s (rotatePerm i)) (rotateHerzog D i) c k
    (fun l=>p (rotatePerm i l)) r q ell (fun l=>z (rotatePerm i l))
  · intro l; exact hp (rotatePerm i l)
  · simp only [rotateHerzog_fA,rotateHerzog_fB]
    change (if c then D.fA else D.fB)=(k:ℤ)*g.m+
      ∑ l,(p (rotatePerm i l)-1)*g.n (rotatePerm i l)
    rw [Equiv.sum_comp (rotatePerm i) (fun l=>(p l-1)*g.n l)]
    exact he
  · intro k' x' hx
    simp only [rotateHerzog_fA,rotateHerzog_fB,value_relabel] at hx
    exact hmin k' (fun l=>x' ((rotatePerm i).symm l)) hx
  · exact hk
  · exact hr
  · exact hrk
  · exact hq
  · exact hqk
  · exact hinv
  · intro l
    simpa only [socleRows_rotate,rotatePerm_zero,rotatePerm_one,rotatePerm_two]
      using hz (rotatePerm i l)

end P21.Nonsymmetric.ColorCap.MinimumOne

