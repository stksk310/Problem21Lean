import P21.Symmetric.TwoGenerator

namespace P21.Symmetric.Classification

/-- Closure under multiplication by a nonnegative integer retains an actual
natural additive-monoid witness. -/
theorem nonneg_mul_mem (H : AddSubmonoid ℤ) {a x : ℤ}
    (ha : 0 ≤ a) (hx : x ∈ H) : a * x ∈ H := by
  simpa [nsmul_eq_mul, Int.toNat_of_nonneg ha] using H.nsmul_mem hx a.toNat

/-- A primitive pair whose least common multiple is in the Apéry set already
gives the nonnegative gluing witness. This uses only the proved two-generator
Frobenius formula, not three-generator classification. -/
theorem primitive_mem_of_lcm_gap (H : AddSubmonoid ℤ) (D : TwoGeneratorData)
    {d x : ℤ} (hd : 1 ≤ d) (hx : x ∈ H)
    (hu : d * D.u ∈ H) (hv : d * D.v ∈ H)
    (hgap : d * D.u * D.v - x ∉ H) : x ∈ D.T := by
  by_contra hnot
  obtain ⟨a, b, ha, hb, he⟩ := (D.frobenius_symmetry x).mp hnot
  have hmem := H.add_mem
    (H.add_mem (nonneg_mul_mem H ha hu) (nonneg_mul_mem H hb hv))
    (H.add_mem (H.add_mem hu hv) (nonneg_mul_mem H (by omega : 0 ≤ d - 1) hx))
  apply hgap
  convert hmem using 1
  dsimp [TwoGeneratorData.frobenius] at he
  linear_combination d * he

/-- The determinant of two rectangular boundary relations is divisible by
the omitted generator. A Bezout witness records saturation explicitly. -/
theorem boundary_determinant_dvd {x y z L M a b q r : ℤ}
    (hbezout : ∃ α β γ : ℤ, α * x + β * y + γ * z = 1)
    (hy : L * y = q * x + b * z)
    (hz : M * z = r * x + a * y) : x ∣ L * M - a * b := by
  have hdy : x ∣ (L * M - a * b) * y := by
    refine ⟨M * q + b * r, ?_⟩
    linear_combination M * hy + b * hz
  have hdz : x ∣ (L * M - a * b) * z := by
    refine ⟨L * r + a * q, ?_⟩
    linear_combination L * hz + a * hy
  obtain ⟨α, β, γ, he⟩ := hbezout
  obtain ⟨u, hu⟩ := hdy
  obtain ⟨v, hv⟩ := hdz
  refine ⟨(L*M-a*b)*α + β*u + γ*v, ?_⟩
  linear_combination -(L*M-a*b)*he + β*hu + γ*hv

/-- A full rectangular Apéry domain cannot have both inward boundary
coefficients positive. -/
theorem rectangular_boundary_zero {x y z L M a b q r : ℤ}
    (hL : 0 < L) (hM : 0 < M)
    (ha : 0 ≤ a) (haL : a < L) (hb : 0 ≤ b) (hbM : b < M)
    (hcard : x = L * M)
    (hbezout : ∃ α β γ : ℤ, α * x + β * y + γ * z = 1)
    (hy : L * y = q * x + b * z)
    (hz : M * z = r * x + a * y) : a = 0 ∨ b = 0 := by
  have hd := boundary_determinant_dvd hbezout hy hz
  have hablt : a * b < L * M := by
    nlinarith [mul_pos (by omega : 0 < L-a) hM,
      mul_nonneg ha (by omega : 0 ≤ M-b)]
  have hpos : 0 < L * M - a*b := by omega
  have hxpos : 0 < x := by nlinarith
  have hle := Int.le_of_dvd hpos hd
  have hab : a * b = 0 := by nlinarith [mul_nonneg ha hb]
  exact mul_eq_zero.mp hab

/-- The zero boundary produces the actual nonnegative primitive expression;
the other zero case is obtained by exchanging the two rectangle axes. -/
theorem rectangular_zero_boundary_decomposition {x y z L M b q r : ℤ}
    (hL : 0 < L) (hM : 0 < M) (hcard : x = L * M)
    (hy : L * y = q * x + b * z)
    (hz : M * z = r * x) : z = L * r ∧ y = q * M + b * r := by
  have hez : z = L * r := by
    have he : M * (z-L*r) = 0 := by
      rw [hcard] at hz
      linear_combination hz
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (ne_of_gt hM))
  refine ⟨hez, ?_⟩
  have he : L * (y - (q*M+b*r)) = 0 := by
    rw [hez, hcard] at hy
    linear_combination hy
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (ne_of_gt hL))

end P21.Symmetric.Classification

namespace P21.Symmetric.Classification

/-- In the unique-factorization branch the Apéry set is a full rectangle.
All coefficients are nonnegative integers throughout. -/
theorem unique_top_apery_rectangle (H : AddSubmonoid ℤ)
    {x y z t A B : ℤ} (hy : y ∈ H) (hz : z ∈ H)
    (_hA : 0 ≤ A) (_hB : 0 ≤ B) (ht : t = A*y+B*z)
    (htgap : t-x ∉ H)
    (hrep : ∀ w : ℤ, w ∈ H → w-x ∉ H →
      ∃ a b : ℤ, 0 ≤ a ∧ 0 ≤ b ∧ w = a*y+b*z)
    (hcomp : ∀ w : ℤ, w ∈ H → w-x ∉ H →
      t-w ∈ H ∧ (t-w)-x ∉ H)
    (hunique : ∀ a b : ℤ, 0 ≤ a → 0 ≤ b → t = a*y+b*z → a=A ∧ b=B)
    {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a*y+b*z ∈ H ∧ a*y+b*z-x ∉ H) ↔ a ≤ A ∧ b ≤ B := by
  constructor
  · rintro ⟨hm, hg⟩
    obtain ⟨hc, hcg⟩ := hcomp _ hm hg
    obtain ⟨c,d,hc0,hd0,he⟩ := hrep _ hc hcg
    have hu := hunique (a+c) (b+d) (by omega) (by omega) (by linear_combination he)
    omega
  · rintro ⟨haA,hbB⟩
    refine ⟨H.add_mem (nonneg_mul_mem H ha hy) (nonneg_mul_mem H hb hz), ?_⟩
    intro hm
    apply htgap
    have hh := H.add_mem hm (H.add_mem
      (nonneg_mul_mem H (by omega : 0 ≤ A-a) hy)
      (nonneg_mul_mem H (by omega : 0 ≤ B-b) hz))
    convert hh using 1
    linear_combination ht

/-- Values on the top rectangle have unique two-coordinate expressions. -/
theorem unique_top_rectangle_injective {y z t A B : ℤ}
    (ht : t = A*y+B*z)
    (hunique : ∀ a b : ℤ, 0 ≤ a → 0 ≤ b → t = a*y+b*z → a=A ∧ b=B)
    {a b c d : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (_hc : 0 ≤ c) (hcA : c ≤ A) (_hd : 0 ≤ d) (hdB : d ≤ B)
    (he : a*y+b*z = c*y+d*z) : a=c ∧ b=d := by
  have hu := hunique (a+(A-c)) (b+(B-d)) (by omega) (by omega)
    (by linear_combination ht - he)
  omega

/-- Reduction of the first point outside a rectangular Apéry domain has no
coefficient along that same axis. -/
theorem rectangular_boundary_relation (H : AddSubmonoid ℤ)
    {x y z A B : ℤ} (hx : x ∈ H) (hy : y ∈ H) (hz : z ∈ H)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrectangle : ∀ a b : ℤ, 0 ≤ a → 0 ≤ b →
      ((a*y+b*z ∈ H ∧ a*y+b*z-x ∉ H) ↔ a ≤ A ∧ b ≤ B))
    (hreduce : ∀ w ∈ H, ∃ q a b : ℤ, 0 ≤ q ∧ 0 ≤ a ∧ a ≤ A ∧
      0 ≤ b ∧ b ≤ B ∧ w = q*x+a*y+b*z) :
    ∃ q b : ℤ, 0 < q ∧ 0 ≤ b ∧ b ≤ B ∧ (A+1)*y=q*x+b*z := by
  obtain ⟨q,a,b,hq,ha,haA,hb,hbB,he⟩ := hreduce ((A+1)*y)
    (nonneg_mul_mem H (by omega) hy)
  have hqpos : 0 < q := by
    by_contra hn
    have hq0 : q=0 := by omega
    have hr := (hrectangle a b ha hb).2 ⟨haA,hbB⟩
    have he' : (A+1)*y = a*y+b*z := by simpa [hq0] using he
    have hh : (A+1)*y+0*z ∈ H ∧ (A+1)*y+0*z-x ∉ H := by
      simpa only [zero_mul, add_zero, he'] using hr
    have := (hrectangle (A+1) 0 (by omega) (by omega)).1 hh
    omega
  have ha0 : a=0 := by
    by_contra hn
    have hap : 1 ≤ a := by omega
    have hrect := (hrectangle (A+1-a) 0 (by omega) (by omega)).2 ⟨by omega,hB⟩
    apply hrect.2
    have hmem := H.add_mem (nonneg_mul_mem H (by omega : 0 ≤ q-1) hx)
      (nonneg_mul_mem H hb hz)
    convert hmem using 1
    linear_combination he
  exact ⟨q,b,hqpos,hb,hbB,by simpa [ha0] using he⟩

end P21.Symmetric.Classification
