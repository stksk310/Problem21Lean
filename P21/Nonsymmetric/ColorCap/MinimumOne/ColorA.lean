import P21.Nonsymmetric.ColorCap.MinimumOne.ClassArithmetic

namespace P21.Nonsymmetric.ColorCap.MinimumOne

/-- BA follows from the six actual companions in the natural A ordering. -/
theorem boundsA_of_actual (g : Generators) (f s : ℤ) (k : ℕ)
    (a b p z : Point) (j : ℤ)
    (hs : f+∑ i, g.n i=s)
    (hmin : ∀ k' : ℕ, ∀ x' : Fin 3 → ℕ,
      f=(k' : ℤ)*g.m+value g.n x' → k≤k')
    (hj : 0<j) (hjk : j<k)
    (hpw : weight g.n p=s-(k : ℤ)*g.m)
    (hRw : ∀ i, weight g.n (rowsA a b i)=s) (hzw : weight g.n z=j*g.m)
    (hp : ∀ i, 1≤p i) (hpa : ∀ i, p i<a i) (hb : ∀ i, 1≤b i)
    (hc : 0 < -z 0 ∧ -z 0 < p 0+b 0 ∧ -a 1 < z 1 ∧ z 1 < b 1 ∧
      0 < z 2 ∧ z 2 < a 2+b 2) :
    p 0 ≤ -z 0 ∧ -z 0 ≤ b 0 ∧ 0 ≤ z 1 ∧ z 1 ≤ b 1-p 1 ∧
      a 2 ≤ z 2 ∧ z 2 ≤ a 2+b 2-p 2 := by
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := six_companion_failures g f s k hs hmin j hj hjk
    p z (rowsA a b) hpw hRw hzw
  apply colorA_companion_bounds a b p (-z 0) (z 1) (z 2) hp hpa hb
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2
  · intro h; apply h0; intro i
    fin_cases i <;> simp [rowsA, Matrix.vecHead, Matrix.vecTail] <;> omega
  · intro h; apply h1; intro i
    fin_cases i <;> simp [rowsA, Matrix.vecHead, Matrix.vecTail] <;> omega
  · intro h; apply h2; intro i
    fin_cases i <;> simp <;> omega
  · intro h; apply h3; intro i
    fin_cases i <;> simp [rowsA] <;> omega
  · intro h; apply h4; intro i
    fin_cases i <;> simp [rowsA] <;> omega
  · intro h; apply h5; intro i
    fin_cases i <;> simp [rowsA, Matrix.vecHead, Matrix.vecTail] <;> omega

/-- The inverse class has the same coarse A bounds; the Y bound uses rq=1+ell*k. -/
theorem inverse_boundsA (a b p : Point) (k r q ell X Y Z : ℤ)
    (hp : ∀ i, 1≤p i) (hpa : ∀ i, p i<a i) (hb : ∀ i, 1≤b i)
    (hk : 2≤k) (hr : 1≤r) (_hrk : r<k) (hq : 1≤q) (hqk : q<k)
    (hinv : r*q=1+ell*k) (hfirst : (r-1)*a 1 ≤ b 1-p 1)
    (heX : k*X=b 0+q*p 0)
    (heY : k*Y=q*(b 1-p 1)+(q-1)*a 1)
    (heZ : k*Z=(q+1)*a 2+b 2-q*p 2) :
    0<X ∧ X<p 0+b 0 ∧ -a 1<Y ∧ Y<b 1 ∧ 0<Z ∧ Z<a 2+b 2 := by
  have hp0:=hp 0; have hp1:=hp 1; have hp2:=hp 2
  have ha1:=hpa 1; have ha2:=hpa 2
  have hb0:=hb 0; have hb1:=hb 1; have hb2:=hb 2
  have hkr : 0<k-q := by omega
  have hq0 : 0≤q-1 := by omega
  have hkq : 0≤k-q-1 := by omega
  have hrell : 1≤r-ell := by nlinarith
  have hbase : 0≤r-ell-1 := by omega
  have hbpp : 0≤b 1-p 1 := by nlinarith
  have hYnonneg : 0≤Y := by
    have := mul_nonneg (show 0≤q by omega) hbpp
    have := mul_nonneg hq0 (show 0≤a 1 by omega)
    nlinarith
  have hybound : 0≤(k-q)*(b 1-p 1-(r-1)*a 1) :=
    mul_nonneg hkr.le (by omega)
  have hybase : 0≤k*(r-ell-1)*a 1 := mul_nonneg (mul_nonneg (by omega) hbase) (by omega)
  have hYlt : Y<b 1 := by
    have he : k*(b 1-Y-p 1) =
        (k-q)*(b 1-p 1-(r-1)*a 1)+k*(r-ell-1)*a 1 := by
      linear_combination -heY - a 1*hinv
    nlinarith
  have hxp := mul_pos (show 0<q by omega) (show 0<p 0 by omega)
  have hx1 := mul_nonneg (show 0≤k-1 by omega) (show 0≤b 0 by omega)
  have hx2 := mul_pos hkr (show 0<p 0 by omega)
  have hz1 := mul_pos (show 0<q by omega) (show 0<a 2-p 2 by omega)
  have hz2 := mul_nonneg hkq (show 0≤a 2 by omega)
  have hz3 := mul_nonneg (show 0≤k-1 by omega) (show 0≤b 2 by omega)
  have hz4 := mul_pos (show 0<q by omega) (show 0<p 2 by omega)
  refine ⟨?_,?_,?_,hYlt,?_,?_⟩ <;> nlinarith

/-- Conditional arithmetic closure, with the integral White input explicit in hz.
All companion exclusions are derived from the actual minimum. -/
theorem colorA_integral_class_contradiction (g : Generators) (f s : ℤ) (k : ℕ)
    (a b p z : Point) (r q ell : ℤ)
    (hm : 0<g.m) (hn : ∀ i, g.m<g.n i)
    (hs : f+∑ i, g.n i=s)
    (hmin : ∀ k' : ℕ, ∀ x' : Fin 3 → ℕ,
      f=(k' : ℤ)*g.m+value g.n x' → k≤k')
    (hp : ∀ i, 1≤p i) (hpa : ∀ i, p i<a i) (hb : ∀ i, 1≤b i)
    (hk : 2≤(k : ℤ)) (hr : 1≤r) (hrk : r<k) (hq : 1≤q) (hqk : q<k)
    (hinv : r*q=1+ell*(k : ℤ))
    (hpw : weight g.n p=s-(k : ℤ)*g.m)
    (hRw : ∀ i, weight g.n (rowsA a b i)=s)
    (hz : ∀ i, (k : ℤ)*z i=rowsA a b 0 i+r*(rowsA a b 1 i-rowsA a b 2 i)-p i) :
    False := by
  have hzw : weight g.n z=g.m := class_weight g.n p z (rowsA a b) s g.m k r
    (by omega) hpw hRw hz
  have hz0:=hz 0; have hz1:=hz 1; have hz2:=hz 2
  simp [rowsA] at hz0 hz1 hz2
  have heX : (k : ℤ)*(-z 0)=r*b 0+p 0 := by linear_combination -hz0
  have heY : (k : ℤ)*z 1=b 1-(r-1)*a 1-p 1 := by linear_combination hz1
  have heZ : (k : ℤ)*z 2=(r+1)*a 2+r*b 2-p 2 := by linear_combination hz2
  have hcoarse := colorA_class_bounds a b p k r (-z 0) (z 1) (z 2)
    hp hpa hb hk hr hrk heX heY heZ
  have hbounds := boundsA_of_actual g f s k a b p z 1 hs hmin (by omega) (by omega)
    hpw hRw (by simpa using hzw) hp hpa hb hcoarse
  let zq:=inverseClass (rowsA a b) z q ell
  have hqeq:=inverseClass_identity (rowsA a b) p z k r q ell hinv hz
  have hq0:=hqeq 0; have hq1:=hqeq 1; have hq2:=hqeq 2
  change (k : ℤ)*zq 0=_ at hq0
  change (k : ℤ)*zq 1=_ at hq1
  change (k : ℤ)*zq 2=_ at hq2
  simp [rowsA] at hq0 hq1 hq2
  have heXq : (k : ℤ)*(-zq 0)=b 0+q*p 0 := by linear_combination -hq0
  have heYq : (k : ℤ)*zq 1=q*(b 1-p 1)+(q-1)*a 1 := by linear_combination hq1
  have heZq : (k : ℤ)*zq 2=(q+1)*a 2+b 2-q*p 2 := by linear_combination hq2
  have hfirst : (r-1)*a 1≤b 1-p 1 := by
    have := mul_nonneg (show 0≤(k : ℤ) by omega) hbounds.2.2.1
    nlinarith [heY]
  have hcoarseq:=inverse_boundsA a b p k r q ell (-zq 0) (zq 1) (zq 2)
    hp hpa hb hk hr hrk hq hqk hinv hfirst heXq heYq heZq
  have hboundsq:=boundsA_of_actual g f s k a b p zq q hs hmin (by omega) hqk hpw hRw
    (inverseClass_weight g.n z (rowsA a b) s g.m q ell hRw hzw) hp hpa hb hcoarseq
  obtain ⟨u,y,v,hu,hy,hv,hb0,hb1,hb2⟩:=colorA_parameters a b p k r q (-zq 0) (z 1) (zq 2)
    hboundsq.1 hbounds.2.2.1 hboundsq.2.2.2.2.1 heXq heY heZq
  let e : Point:=fun i=>a i-p i
  have he : ∀ i, 1≤e i := by intro i; have:=hpa i; dsimp [e]; omega
  have hR0:=hRw 0; have hR1:=hRw 1; have hR2:=hRw 2
  simp [rowsA,weight,Fin.sum_univ_succ] at hR0 hR1 hR2 hpw
  apply colorA_parameter_contradiction g.m g.n e p b k r q ell u y v hm hn he hp
    hk hr hrk hq hqk hinv hu hy hv hb0
  · simpa [e] using hb1
  · simpa [e] using hb2
  · dsimp [e]; linear_combination hpw-hR2
  · dsimp [e]; linear_combination hpw-hR0
  · dsimp [e]; linear_combination hpw-hR1

end P21.Nonsymmetric.ColorCap.MinimumOne




