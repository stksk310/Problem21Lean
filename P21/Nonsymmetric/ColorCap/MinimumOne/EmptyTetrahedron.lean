import P21.Nonsymmetric.ColorCap.MinimumOne.SocleSimplex

namespace P21.Nonsymmetric.ColorCap.MinimumOne

/-- Rational barycentric presentation in the tetrahedron. All coordinates are
explicit; integral relative-lattice points remain integer vectors. -/
def InSocleSimplex (p : Point) (R : Fin 3 → Point) (u : Point) : Prop :=
  ∃ t : Fin 3 → ℚ, (∀ i, 0 ≤ t i) ∧ (∑ i,t i) ≤ 1 ∧
    ∀ j, (u j:ℚ) = (1-∑ i,t i)*(p j:ℚ)+∑ i,t i*(R i j:ℚ)

/-- Any nonvertex integral point of this simplex has every coordinate positive. -/
theorem simplex_positive_or_row (p : Point) (R : Fin 3 → Point) (u : Point)
    (hp : ∀ j, 1 ≤ p j) (hdiag : ∀ j,R j j=0)
    (hpos : ∀ i j,i ≠ j → 0 < R i j)
    (hu : InSocleSimplex p R u) : (∀ j,1 ≤ u j) ∨ ∃ i,u=R i := by
  classical
  obtain ⟨t,ht,ht1,he⟩ := hu
  have hR (i j) : (0:ℚ) ≤ R i j := by
    by_cases hij : i=j
    · subst j; rw [hdiag]; norm_num
    · exact_mod_cast (hpos i j hij).le
  by_cases hall : ∀ j,1 ≤ u j
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨j,hj⟩ := hall
  have hj' : (u j:ℚ) ≤ 0 := by exact_mod_cast (show u j ≤ 0 by omega)
  have hpj : (1:ℚ) ≤ p j := by exact_mod_cast hp j
  have hsnonneg : (0:ℚ) ≤ ∑ i,t i*(R i j:ℚ) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (ht i) (hR i j))
  have htEq : (∑ i,t i) = 1 := by nlinarith [he j]
  have hs0 : (∑ i,t i*(R i j:ℚ)) = 0 := by rw [htEq] at he; nlinarith [he j]
  have hzero (i) (hij : i ≠ j) : t i = 0 := by
    have hle : t i*(R i j:ℚ) ≤ ∑ a,t a*(R a j:ℚ) :=
      Finset.single_le_sum (fun a _ => mul_nonneg (ht a) (hR a j)) (Finset.mem_univ i)
    have hpij : (0:ℚ) < R i j := by exact_mod_cast hpos i j hij
    nlinarith [ht i]
  have hsum : (∑ i,t i) = t j := by
    apply Finset.sum_eq_single j
    · intro b _ hb; exact hzero b hb
    · simp
  have htj : t j = 1 := by linarith
  refine ⟨j,?_⟩
  funext a
  have he' := he a
  rw [htEq] at he'
  have hs : (∑ i,t i*(R i a:ℚ)) = (R j a:ℚ) := by
    rw [Finset.sum_eq_single j]
    · rw [htj,one_mul]
    · intro b _ hb; rw [hzero b hb,zero_mul]
    · simp
  rw [hs] at he'
  exact_mod_cast (show (u a:ℚ) = R j a by linarith)

/-- The height of a barycentric point is exactly (1-sum t) times the original height. -/
theorem barycentric_weight (n p : Point) (R : Fin 3 → Point) (u : Point)
    (t : Fin 3 → ℚ) (s : ℤ) (hR : ∀ i,weight n (R i)=s)
    (he : ∀ j,(u j:ℚ)=(1-∑ i,t i)*(p j:ℚ)+∑ i,t i*(R i j:ℚ)) :
    (s:ℚ)-(weight n u:ℚ)=(1-∑ i,t i)*((s:ℚ)-(weight n p:ℚ)) := by
  have hw (i) : (∑ j,(R i j:ℚ)*(n j:ℚ)) = (s:ℚ) := by exact_mod_cast hR i
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  simp only [weight,Fin.sum_univ_three,Int.cast_add,Int.cast_mul] at *
  linear_combination -(n 0:ℚ)*h0-(n 1:ℚ)*h1-(n 2:ℚ)*h2-
    t 0*hw 0-t 1*hw 1-t 2*hw 2

/-- Exact lattice emptiness, derived from an actual minimum and the actual tail gap. -/
theorem minimum_simplex_empty (g : Generators) (s : g.Setting) (f : ℤ) (k : ℕ)
    (p : Point) (R : Fin 3 → Point) (hk : 0 < k) (hp : ∀ j,1 ≤ p j)
    (hf : f ∉ g.H) (hR : ∀ i,weight g.n (R i)=f+∑ j,g.n j)
    (hdiag : ∀ j,R j j=0) (hpos : ∀ i j,i ≠ j → 0 < R i j)
    (hlevel : f+∑ j,g.n j-weight g.n p=(k:ℤ)*g.m)
    (hmin : ∀ k' : ℕ,∀ x' : Fin 3 → ℕ,
      f=(k':ℤ)*g.m+value g.n x' → k ≤ k')
    (u : Point) (hu : InSocleSimplex p R u)
    (hlattice : u-p ∈ relativeLattice g.n g.m) : u=p ∨ ∃ i,u=R i := by
  obtain ⟨l,hl⟩ := relative_lattice_level g.n p u (f+∑ j,g.n j) g.m k hlevel hlattice
  obtain ⟨t,ht,ht1,he⟩ := hu
  have hw := barycentric_weight g.n p R u t (f+∑ j,g.n j) hR he
  have hlevel' : ((f+∑ j,g.n j:ℤ):ℚ)-(weight g.n p:ℚ)=(k:ℚ)*(g.m:ℚ) := by exact_mod_cast hlevel
  have hl' : ((f+∑ j,g.n j:ℤ):ℚ)-(weight g.n u:ℚ)=(l:ℚ)*(g.m:ℚ) := by exact_mod_cast hl
  have hm : (0:ℚ) < g.m := by exact_mod_cast s.m_pos
  have hk' : (0:ℚ) < k := by exact_mod_cast hk
  have ht0 : (0:ℚ) ≤ ∑ i,t i := Finset.sum_nonneg (fun i _ => ht i)
  have helevel : (l:ℚ)=(1-∑ i,t i)*(k:ℚ) := by rw [hlevel',hl'] at hw; nlinarith
  have hl0 : 0 ≤ l := by exact_mod_cast (show (0:ℚ) ≤ l by nlinarith)
  have hlk : l ≤ k := by exact_mod_cast (show (l:ℚ) ≤ k by nlinarith)
  by_cases heq : l = k
  · left
    have hsum0 : (∑ i,t i)=0 := by rw [heq] at helevel; norm_cast at helevel; nlinarith
    have htzero : ∀ i,t i=0 := by
      intro i
      have hi := Finset.single_le_sum (fun j _ => ht j) (Finset.mem_univ i)
      nlinarith [ht i]
    funext j
    have h := he j
    simp [htzero] at h
    exact_mod_cast h
  have hup := simplex_positive_or_row p R u hp hdiag hpos ⟨t,ht,ht1,he⟩
  rcases hup with hup | hrow
  · exfalso
    by_cases hz : l=0
    · apply top_face_positive_impossible g f u hf hup
      rw [hz,zero_mul] at hl
      linarith
    · apply lower_companion_impossible g f k hmin l (by omega) (by omega) u hup
      simp only [sub_mul,one_mul,Finset.sum_sub_distrib]
      change f=l*g.m+(weight g.n u-∑ i,g.n i)
      linarith
  · exact Or.inr hrow


/-- Both source socle tetrahedra are empty from the exact minimum premises.
No arm, width, class, or primitivity conclusion is assumed in this step. -/
theorem socle_simplex_empty {g : Generators} (s : g.Setting) (D : HerzogCriticalData g)
    (c : Bool) (k : ℕ) (p : Point) (hk : 0 < k) (hp : ∀ i,1 ≤ p i)
    (he : (if c then D.fA else D.fB)=(k:ℤ)*g.m+∑ i,(p i-1)*g.n i)
    (hmin : ∀ k' : ℕ,∀ x' : Fin 3 → ℕ,
      (if c then D.fA else D.fB)=(k':ℤ)*g.m+value g.n x' → k ≤ k')
    (u : Point) (hu : InSocleSimplex p (socleRows D c) u)
    (hlattice : u-p ∈ relativeLattice g.n g.m) :
    u=p ∨ ∃ i,u=socleRows D c i := by
  have hn : ∀ i,0 < g.n i := fun i => lt_trans s.m_pos (s.n_gt i)
  apply minimum_simplex_empty g s (if c then D.fA else D.fB) k p (socleRows D c)
    hk hp ?_ (socleRows_weight D c) (socleRows_diagonal D c) (socleRows_off_diagonal D c)
    (socle_minimum_weight D c p k he) hmin u hu hlattice
  cases c
  · exact D.fB_gap hn
  · exact D.fA_gap hn

end P21.Nonsymmetric.ColorCap.MinimumOne
