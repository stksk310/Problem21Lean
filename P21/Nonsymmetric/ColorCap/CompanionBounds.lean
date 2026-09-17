import P21.Nonsymmetric.ColorCap.WhiteCertificates

namespace P21.Nonsymmetric.ColorCap

/-- The six actual lower companions yield BA, in the publication's precise ordering. -/
theorem colorA_companion_bounds (a b p : Point) (X Y Z : ℤ)
    (hp : ∀ i, 1 ≤ p i) (hpa : ∀ i, p i < a i) (hb : ∀ i, 1 ≤ b i)
    (hX0 : 0 < X) (hX : X < p 0+b 0)
    (hY0 : -a 1 < Y) (hY : Y < b 1)
    (_hZ0 : 0 < Z) (hZ : Z < a 2+b 2)
    (hf0 : ¬ (0 < p 0+a 0+b 0-X ∧ 0 < p 1-b 1+Y ∧ 0 < p 2-a 2+Z))
    (hf1 : ¬ (0 < p 0+b 0-X ∧ 0 < p 1+a 1+Y ∧ 0 < p 2-a 2-b 2+Z))
    (hf2 : ¬ (0 < p 0-X ∧ 0 < p 1+Y ∧ 0 < p 2+Z))
    (hf3 : ¬ (0 < a 0+X ∧ 0 < -Y ∧ 0 < a 2+b 2-Z))
    (hf4 : ¬ (0 < X ∧ 0 < a 1+b 1-Y ∧ 0 < a 2-Z))
    (hf5 : ¬ (0 < X-b 0 ∧ 0 < b 1-Y ∧ 0 < 2*a 2+b 2-Z)) :
    p 0 ≤ X ∧ X ≤ b 0 ∧ 0 ≤ Y ∧ Y ≤ b 1-p 1 ∧ a 2 ≤ Z ∧ Z ≤ a 2+b 2-p 2 := by
  have hp0 := hp 0; have hp1 := hp 1; have hp2 := hp 2
  have ha0 := hpa 0; have ha1 := hpa 1; have ha2 := hpa 2
  have hb0 := hb 0; have hb1 := hb 1; have hb2 := hb 2
  omega

/-- The natural color-B companion failures yield BB without reversing an inequality. -/
theorem colorB_companion_bounds (a b p : Point) (X Y Z : ℤ)
    (hp : ∀ i, 1 ≤ p i) (hpb : ∀ i, p i < b i) (ha : ∀ i, 1 ≤ a i)
    (hX0 : -p 0 < X) (hX : X < a 0)
    (hY0 : 0 < Y) (hY : Y < a 1+b 1)
    (_hZ0 : 0 < Z) (hZ : Z < a 2+b 2)
    (hf0 : ¬ (0 < p 0+b 0+X ∧ 0 < p 1+a 1-Y ∧ 0 < p 2-a 2-b 2+Z))
    (hf1 : ¬ (0 < p 0-a 0+X ∧ 0 < p 1+a 1+b 1-Y ∧ 0 < p 2-b 2+Z))
    (hf2 : ¬ (0 < p 0+X ∧ 0 < p 1-Y ∧ 0 < p 2+Z))
    (hf3 : ¬ (0 < a 0+b 0-X ∧ 0 < Y ∧ 0 < b 2-Z))
    (hf4 : ¬ (0 < -X ∧ 0 < b 1+Y ∧ 0 < a 2+b 2-Z))
    (hf5 : ¬ (0 < a 0-X ∧ 0 < Y-a 1 ∧ 0 < a 2+2*b 2-Z)) :
    0 ≤ X ∧ X ≤ a 0-p 0 ∧ p 1 ≤ Y ∧ Y ≤ a 1 ∧ b 2 ≤ Z ∧ Z ≤ a 2+b 2-p 2 := by
  have hp0 := hp 0; have hp1 := hp 1; have hp2 := hp 2
  have hb0 := hpb 0; have hb1 := hpb 1; have hb2 := hpb 2
  have ha0 := ha 0; have ha1 := ha 1; have ha2 := ha 2
  omega

end P21.Nonsymmetric.ColorCap

namespace P21.Nonsymmetric.ColorCap

/-- BA at the two integral White classes supplies AP with actual nonnegative slack. -/
theorem colorA_parameters (a b p : Point) (k r q Xq Y Zq : ℤ)
    (hX : p 0 ≤ Xq) (hY : 0 ≤ Y) (hZ : a 2 ≤ Zq)
    (heX : k*Xq = b 0+q*p 0)
    (heY : k*Y = b 1-(r-1)*a 1-p 1)
    (heZ : k*Zq = (q+1)*a 2+b 2-q*p 2) :
    ∃ u y v : ℤ, 0 ≤ u ∧ 0 ≤ y ∧ 0 ≤ v ∧
      b 0 = (k-q)*p 0+k*u ∧
      b 1 = p 1+(r-1)*a 1+k*y ∧
      b 2 = q*p 2+(k-q-1)*a 2+k*v := by
  refine ⟨Xq-p 0,Y,Zq-a 2,by omega,hY,by omega,?_,?_,?_⟩
  · linear_combination -heX
  · linear_combination -heY
  · linear_combination -heZ

/-- BB at the two integral White classes supplies BP with nonnegative slack. -/
theorem colorB_parameters (a b p : Point) (k r q Xq Yq Z : ℤ)
    (hX : 0 ≤ Xq) (hY : p 1 ≤ Yq) (hZ : b 2 ≤ Z)
    (heX : k*Xq = a 0-q*p 0)
    (heY : k*Yq = a 1-(q-1)*b 1+q*p 1)
    (heZ : k*Z = a 2+(r+1)*b 2-p 2) :
    ∃ u y v : ℤ, 0 ≤ u ∧ 0 ≤ y ∧ 0 ≤ v ∧
      a 0 = q*p 0+k*u ∧
      a 1 = (q-1)*b 1+(k-q)*p 1+k*y ∧
      a 2 = p 2+(k-r-1)*b 2+k*v := by
  refine ⟨Xq,Yq-p 1,Z-b 2,hX,by omega,by omega,?_,?_,?_⟩
  · linear_combination -heX
  · linear_combination -heY
  · linear_combination -heZ

end P21.Nonsymmetric.ColorCap


namespace P21.Nonsymmetric.ColorCap

/-- The first color-A White class has the coarse bounds used before any companion failure. -/
theorem colorA_class_bounds (a b p : Point) (k r X Y Z : ℤ)
    (hp : ∀ i, 1 ≤ p i) (hpa : ∀ i, p i < a i) (hb : ∀ i, 1 ≤ b i)
    (hk : 2 ≤ k) (hr : 1 ≤ r) (hrk : r < k)
    (heX : k*X = r*b 0+p 0)
    (heY : k*Y = b 1-(r-1)*a 1-p 1)
    (heZ : k*Z = (r+1)*a 2+r*b 2-p 2) :
    0 < X ∧ X < p 0+b 0 ∧ -a 1 < Y ∧ Y < b 1 ∧ 0 < Z ∧ Z < a 2+b 2 := by
  have hp0 := hp 0; have hp1 := hp 1; have hp2 := hp 2
  have ha1 := hpa 1; have ha2 := hpa 2
  have hb0 := hb 0; have hb1 := hb 1; have hb2 := hb 2
  have hkr : 0 ≤ k-r-1 := by omega
  have hkr' : 0 < k-r := by omega
  have hr' : 0 ≤ r-1 := by omega
  have hk' : 0 < k-1 := by omega
  have h1 := mul_pos (show 0 < r by omega) (show 0 < b 0 by omega)
  have h2 := mul_pos hkr' (show 0 < b 0 by omega)
  have h3 := mul_pos hk' (show 0 < p 0 by omega)
  have h4 := mul_nonneg hkr'.le (show 0 ≤ a 1 by omega)
  have h5 := mul_nonneg hr' (show 0 ≤ a 1 by omega)
  have h6 := mul_pos hk' (show 0 < b 1 by omega)
  have h7 := mul_pos (show 0 < r by omega) (show 0 < a 2+b 2 by omega)
  have h8 := mul_nonneg hkr (show 0 ≤ a 2 by omega)
  have h9 := mul_pos hkr' (show 0 < b 2 by omega)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

end P21.Nonsymmetric.ColorCap
