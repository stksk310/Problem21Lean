import P21.Nonsymmetric.ColorCap.MinimumOne.ClassArithmetic

namespace P21.Nonsymmetric.ColorCap.MinimumOne

/-- BB follows from the six actual companions in the natural B ordering. -/
theorem boundsB_of_actual (g : Generators) (f s : ℤ) (k : ℕ)
    (a b p z : Point) (j : ℤ)
    (hs : f+∑ i, g.n i=s)
    (hmin : ∀ k' : ℕ, ∀ x' : Fin 3 → ℕ,
      f=(k' : ℤ)*g.m+value g.n x' → k≤k')
    (hj : 0<j) (hjk : j<k)
    (hpw : weight g.n p=s-(k : ℤ)*g.m)
    (hRw : ∀ i, weight g.n (rowsB a b i)=s) (hzw : weight g.n z=j*g.m)
    (hp : ∀ i, 1≤p i) (hpb : ∀ i, p i<b i) (ha : ∀ i, 1≤a i)
    (hc : -p 0 < z 0 ∧ z 0 < a 0 ∧ 0 < -z 1 ∧ -z 1 < a 1+b 1 ∧
      0 < z 2 ∧ z 2 < a 2+b 2) :
    0 ≤ z 0 ∧ z 0 ≤ a 0-p 0 ∧ p 1 ≤ -z 1 ∧ -z 1 ≤ a 1 ∧
      b 2 ≤ z 2 ∧ z 2 ≤ a 2+b 2-p 2 := by
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := six_companion_failures g f s k hs hmin j hj hjk
    p z (rowsB a b) hpw hRw hzw
  apply colorB_companion_bounds a b p (z 0) (-z 1) (z 2) hp hpb ha
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2
  · intro h; apply h0; intro i
    fin_cases i <;> simp [rowsB, Matrix.vecHead, Matrix.vecTail] <;> omega
  · intro h; apply h1; intro i
    fin_cases i <;> simp [rowsB, Matrix.vecHead, Matrix.vecTail] <;> omega
  · intro h; apply h2; intro i
    fin_cases i <;> simp <;> omega
  · intro h; apply h3; intro i
    fin_cases i <;> simp [rowsB] <;> omega
  · intro h; apply h4; intro i
    fin_cases i <;> simp [rowsB] <;> omega
  · intro h; apply h5; intro i
    fin_cases i <;> simp [rowsB] <;> omega

theorem class_boundsB (a b p : Point) (k r X Y Z : ℤ)
    (hp : ∀ i, 1≤p i) (hpb : ∀ i, p i<b i) (ha : ∀ i, 1≤a i)
    (hk : 2≤k) (hr : 1≤r) (hrk : r<k)
    (heX : k*X=r*a 0-p 0)
    (heY : k*Y=r*(a 1+b 1)-b 1+p 1)
    (heZ : k*Z=a 2+(r+1)*b 2-p 2) :
    -p 0<X ∧ X<a 0 ∧ 0<Y ∧ Y<a 1+b 1 ∧ 0<Z ∧ Z<a 2+b 2 := by
  have hp0:=hp 0; have hp1:=hp 1; have hp2:=hp 2
  have hb0:=hpb 0; have hb1:=hpb 1; have hb2:=hpb 2
  have ha0:=ha 0; have ha1:=ha 1; have ha2:=ha 2
  have h1:=mul_pos (show 0<r by omega) (show 0<a 0 by omega)
  have h2:=mul_nonneg (show 0≤k-1 by omega) (show 0≤p 0 by omega)
  have h3:=mul_pos (show 0<k-r by omega) (show 0<a 0 by omega)
  have h4:=mul_nonneg (show 0≤r-1 by omega) (show 0≤a 1+b 1 by omega)
  have h5:=mul_pos (show 0<k-r by omega) (show 0<a 1+b 1 by omega)
  have h6:=mul_nonneg (show 0≤r by omega) (show 0≤b 2 by omega)
  have h7:=mul_nonneg (show 0≤k-1 by omega) (show 0≤a 2 by omega)
  have h8:=mul_nonneg (show 0≤k-r-1 by omega) (show 0≤b 2 by omega)
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> nlinarith

/-- All inverse B coarse bounds except Y positivity are immediate from the box. -/
theorem inverse_boundsB (a b p : Point) (k q X Y Z : ℤ)
    (hp : ∀ i, 1≤p i) (hpb : ∀ i, p i<b i) (ha : ∀ i, 1≤a i)
    (hk : 2≤k) (hq : 1≤q) (hqk : q<k)
    (heX : k*X=a 0-q*p 0)
    (heY : k*Y=a 1-(q-1)*b 1+q*p 1)
    (heZ : k*Z=q*a 2+(q+1)*b 2-q*p 2) :
    -p 0<X ∧ X<a 0 ∧ Y<a 1+b 1 ∧ 0<Z ∧ Z<a 2+b 2 := by
  have hp0:=hp 0; have hp1:=hp 1; have hp2:=hp 2
  have hb0:=hpb 0; have hb1:=hpb 1; have hb2:=hpb 2
  have ha0:=ha 0; have ha1:=ha 1; have ha2:=ha 2
  have h1:=mul_pos (show 0<k-q by omega) (show 0<p 0 by omega)
  have h2:=mul_nonneg (show 0≤k-1 by omega) (show 0≤a 0 by omega)
  have h3:=mul_pos (show 0<q by omega) (show 0<p 0 by omega)
  have h4:=mul_nonneg (show 0≤k-1 by omega) (show 0≤a 1+b 1 by omega)
  have h5:=mul_pos (show 0<q by omega) (show 0<b 1-p 1 by omega)
  have h6:=mul_pos (show 0<q by omega) (show 0<a 2+b 2-p 2 by omega)
  have h7:=mul_pos (show 0<k-q by omega) (show 0<a 2 by omega)
  have h8:=mul_nonneg (show 0≤k-q-1 by omega) (show 0≤b 2 by omega)
  have h9:=mul_pos (show 0<q by omega) (show 0<p 2 by omega)
  refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith

/-- Natural B arithmetic closure from explicitly supplied integral White class data. -/
theorem colorB_integral_class_contradiction (g : Generators) (f s : ℤ) (k : ℕ)
    (a b p z : Point) (r q ell : ℤ)
    (hm : 0<g.m) (hn : ∀ i, g.m<g.n i)
    (hs : f+∑ i, g.n i=s)
    (hmin : ∀ k' : ℕ, ∀ x' : Fin 3 → ℕ,
      f=(k' : ℤ)*g.m+value g.n x' → k≤k')
    (hp : ∀ i, 1≤p i) (hpb : ∀ i, p i<b i) (ha : ∀ i, 1≤a i)
    (hk : 2≤(k : ℤ)) (hr : 1≤r) (hrk : r<k) (hq : 1≤q) (hqk : q<k)
    (hinv : r*q=1+ell*(k : ℤ))
    (hpw : weight g.n p=s-(k : ℤ)*g.m)
    (hRw : ∀ i, weight g.n (rowsB a b i)=s)
    (hz : ∀ i, (k : ℤ)*z i=rowsB a b 0 i+r*(rowsB a b 1 i-rowsB a b 2 i)-p i) :
    False := by
  have hzw : weight g.n z=g.m := class_weight g.n p z (rowsB a b) s g.m k r
    (by omega) hpw hRw hz
  have hz0:=hz 0; have hz1:=hz 1; have hz2:=hz 2
  simp [rowsB] at hz0 hz1 hz2
  have heX : (k : ℤ)*z 0=r*a 0-p 0 := by linear_combination hz0
  have heY : (k : ℤ)*(-z 1)=r*(a 1+b 1)-b 1+p 1 := by linear_combination -hz1
  have heZ : (k : ℤ)*z 2=a 2+(r+1)*b 2-p 2 := by linear_combination hz2
  have hcoarse := class_boundsB a b p k r (z 0) (-z 1) (z 2)
    hp hpb ha hk hr hrk heX heY heZ
  have hbounds := boundsB_of_actual g f s k a b p z 1 hs hmin (by omega) (by omega)
    hpw hRw (by simpa using hzw) hp hpb ha hcoarse
  let zq:=inverseClass (rowsB a b) z q ell
  have hqeq:=inverseClass_identity (rowsB a b) p z k r q ell hinv hz
  have hq0:=hqeq 0; have hq1:=hqeq 1; have hq2:=hqeq 2
  change (k : ℤ)*zq 0=_ at hq0
  change (k : ℤ)*zq 1=_ at hq1
  change (k : ℤ)*zq 2=_ at hq2
  simp [rowsB] at hq0 hq1 hq2
  have heXq : (k : ℤ)*zq 0=a 0-q*p 0 := by linear_combination hq0
  have heYq : (k : ℤ)*(-zq 1)=a 1-(q-1)*b 1+q*p 1 := by linear_combination -hq1
  have heZq : (k : ℤ)*zq 2=q*a 2+(q+1)*b 2-q*p 2 := by linear_combination hq2
  have hcoarseq:=inverse_boundsB a b p k q (zq 0) (-zq 1) (zq 2)
    hp hpb ha hk hq hqk heXq heYq heZq
  have hzqw : weight g.n zq=q*g.m :=
    inverseClass_weight g.n z (rowsB a b) s g.m q ell hRw hzw
  have hqfailure := (six_companion_failures g f s k hs hmin q (by omega) hqk
    p zq (rowsB a b) hpw hRw hzqw).2.2.1
  have hYq : p 1≤ -zq 1 := by
    by_contra h
    apply hqfailure
    intro i
    have hp2:=hp 2
    fin_cases i <;> simp <;> omega
  have hboundsq:=boundsB_of_actual g f s k a b p zq q hs hmin (by omega) hqk hpw hRw
    hzqw hp hpb ha ⟨hcoarseq.1,hcoarseq.2.1,by have:=hp 1; omega,
      hcoarseq.2.2.1,hcoarseq.2.2.2.1,hcoarseq.2.2.2.2⟩
  obtain ⟨u,y,v,hu,hy,hv,ha0,ha1,ha2⟩:=colorB_parameters a b p k r q (zq 0) (-zq 1) (z 2)
    hboundsq.1 hboundsq.2.2.1 hbounds.2.2.2.2.1 heXq heYq heZ
  let e : Point:=fun i=>b i-p i
  have he : ∀ i, 1≤e i := by intro i; have:=hpb i; dsimp [e]; omega
  have hR0:=hRw 0; have hR1:=hRw 1; have hR2:=hRw 2
  simp [rowsB,weight,Fin.sum_univ_succ] at hR0 hR1 hR2 hpw
  apply colorB_parameter_contradiction g.m g.n e p a k r q ell u y v hm hn he hp
    hk hr hrk hq hqk hinv hu hy hv ha0
  · simpa [e] using ha1
  · simpa [e] using ha2
  · dsimp [e]; linear_combination hpw-hR0
  · dsimp [e]; linear_combination hpw-hR1
  · dsimp [e]; linear_combination hpw-hR2

end P21.Nonsymmetric.ColorCap.MinimumOne


