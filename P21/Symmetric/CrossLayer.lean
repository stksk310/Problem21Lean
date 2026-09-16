import P21.Symmetric.RawRows
import P21.Symmetric.GlueNormalForm

namespace P21.Symmetric

theorem nonnegative_mul_mem (H : AddSubmonoid ℤ) {a n : ℤ}
    (ha : a ∈ H) (hn : 0 ≤ n) : n * a ∈ H := by
  simpa only [nsmul_eq_mul, Int.toNat_of_nonneg hn] using H.nsmul_mem ha n.toNat

/-- A later-layer raw minimum cannot dominate a first-layer raw member. -/
theorem cross_layer_drop (H : AddSubmonoid ℤ) (I : Set ℤ) {w x k A A' : ℤ}
    (hw : w ∈ H) (hx : x ∈ H) (hwpos : 0 < w) (hxpos : 0 < x)
    (hk : 0 < k) (hA : A * x ∈ I)
    (hmin : idealMin H I (k * w + A' * x)) : A' < A := by
  by_contra hn
  have hcoeff : 0 ≤ A' - A := by omega
  have hdiff : (k * w + A' * x) - A * x ∈ H := by
    have h := H.add_mem (nonnegative_mul_mem H hw hk.le)
      (nonnegative_mul_mem H hx hcoeff)
    convert h using 1; ring
  have he := hmin.2 _ hA hdiff
  have hpos := mul_pos hk hwpos
  have hnonneg := mul_nonneg hcoeff hxpos.le
  nlinarith

theorem cross_layer_identity (T : TwoGeneratorData) {ρ w A B A' B' : ℤ}
    (hρ : ρ = T.u * T.v - A * T.u - B * T.v)
    (hρw : ρ + w = T.u * T.v - A' * T.u - B' * T.v) :
    w = (A - A') * T.u + (B - B') * T.v := by
  linear_combination hρw - hρ

/-- The two alternatives in SPLIT are an ordinary, non-exclusive disjunction. -/
theorem complete_split (T : TwoGeneratorData) {A B ρ θ : ℤ}
    (hA : 0 < A) (hAv : A < T.v) (hB : 0 < B) (hBu : B < T.u)
    (hρ : ρ = T.u * T.v - A * T.u - B * T.v)
    (hx : θ + (B - 1) * T.v - T.u ∈ T.T)
    (hy : θ + (A - 1) * T.u - T.v ∈ T.T) :
    θ - T.u - T.v ∈ T.T ∨ θ - ρ - T.u - T.v ∈ T.T := by
  have h := (T.two_generator_intersection_iff hA hAv hB hBu
    (t := θ + (A - 1) * T.u + (B - 1) * T.v)).mp
      ⟨by convert hx using 1; ring, by convert hy using 1; ring⟩
  rcases h with h | h
  · left
    convert h using 1; ring
  · right
    convert h using 1; rw [hρ]; ring

end P21.Symmetric
