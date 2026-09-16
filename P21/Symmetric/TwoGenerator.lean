import P21.NumericalSemigroup
import Mathlib.Tactic.LinearCombination

/-! Integer two-generator facts from Appendix A.1. All membership witnesses
have nonnegative coefficients; signed representations are kept separate. -/
namespace P21.Symmetric

structure TwoGeneratorData where
  u : ℤ
  v : ℤ
  u_ge_two : 2 ≤ u
  v_ge_two : 2 ≤ v
  coprime : Int.gcd u v = 1

namespace TwoGeneratorData
variable (D : TwoGeneratorData)

def T : AddSubmonoid ℤ where
  carrier := {t | ∃ a b : ℤ, 0 ≤ a ∧ 0 ≤ b ∧ t = a * D.u + b * D.v}
  zero_mem' := ⟨0, 0, le_rfl, le_rfl, by ring⟩
  add_mem' := by
    rintro x y ⟨a, b, ha, hb, rfl⟩ ⟨c, d, hc, hd, rfl⟩
    exact ⟨a+c, b+d, add_nonneg ha hc, add_nonneg hb hd, by ring⟩

theorem mem_T {t : ℤ} : t ∈ D.T ↔
    ∃ a b : ℤ, 0 ≤ a ∧ 0 ≤ b ∧ t = a * D.u + b * D.v := Iff.rfl

/-- The integer-coefficient presentation agrees with M1's actual natural
coefficient generated monoid. -/
theorem T_eq_generated : D.T = P21.generated ![D.u, D.v] := by
  ext t
  constructor
  · rintro ⟨a,b,ha,hb,rfl⟩
    refine ⟨![a.toNat,b.toNat], ?_⟩
    simp [P21.value, Fin.sum_univ_succ, Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb]
  · rintro ⟨c,rfl⟩
    refine ⟨c 0,c 1,Int.natCast_nonneg _,Int.natCast_nonneg _,?_⟩
    simp [P21.value, Fin.sum_univ_succ]

theorem u_pos : 0 < D.u := lt_of_lt_of_le (by norm_num) D.u_ge_two
theorem v_pos : 0 < D.v := lt_of_lt_of_le (by norm_num) D.v_ge_two

theorem nonneg {t : ℤ} (ht : t ∈ D.T) : 0 ≤ t := by
  obtain ⟨a,b,ha,hb,rfl⟩ := ht
  exact add_nonneg (mul_nonneg ha D.u_pos.le) (mul_nonneg hb D.v_pos.le)

theorem bezout : D.u * Int.gcdA D.u D.v + D.v * Int.gcdB D.u D.v = 1 := by
  simpa [D.coprime] using (Int.gcd_eq_gcd_ab D.u D.v).symm

/-- Every difference of integral representations is a primitive shift. -/
theorem representation_difference {a b c d : ℤ}
    (h : a * D.u + b * D.v = c * D.u + d * D.v) :
    ∃ k : ℤ, a - c = k * D.v ∧ b - d = -k * D.u := by
  refine ⟨(a-c) * Int.gcdB D.u D.v - (b-d) * Int.gcdA D.u D.v, ?_, ?_⟩
  · linear_combination -(a-c) * D.bezout + Int.gcdA D.u D.v * h
  · linear_combination -(b-d) * D.bezout + Int.gcdB D.u D.v * h

theorem normal_form_exists (t : ℤ) :
    ∃ a b : ℤ, 0 ≤ b ∧ b < D.u ∧ t = a * D.u + b * D.v := by
  let b₀ := t * Int.gcdB D.u D.v
  refine ⟨t * Int.gcdA D.u D.v + (b₀ / D.u) * D.v, b₀ % D.u,
    Int.emod_nonneg _ (ne_of_gt D.u_pos), Int.emod_lt_of_pos _ D.u_pos, ?_⟩
  have hdiv := Int.ediv_mul_add_emod b₀ D.u
  dsimp [b₀] at *
  linear_combination -t * D.bezout - D.v * hdiv

theorem normal_form_unique {a b c d : ℤ}
    (hb : 0 ≤ b) (hbu : b < D.u) (hd : 0 ≤ d) (hdu : d < D.u)
    (h : a * D.u + b * D.v = c * D.u + d * D.v) : a = c ∧ b = d := by
  obtain ⟨k, hak, hbk⟩ := D.representation_difference h
  have hk : k = 0 := by
    by_contra hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · have : k ≤ -1 := by omega
      nlinarith [D.u_pos]
    · have : 1 ≤ k := by omega
      nlinarith [D.u_pos]
  simp [hk] at hak hbk
  omega

theorem normal_form_mem_iff {a b : ℤ} (hb : 0 ≤ b) (hbu : b < D.u) :
    a * D.u + b * D.v ∈ D.T ↔ 0 ≤ a := by
  constructor
  · rintro ⟨c,d,hc,hd,he⟩
    obtain ⟨k,hak,hbk⟩ := D.representation_difference he
    have hk : 0 ≤ k := by
      by_contra hk
      have : k ≤ -1 := by omega
      nlinarith [D.u_pos]
    nlinarith [mul_nonneg hk D.v_pos.le]
  · intro ha
    exact ⟨a,b,ha,hb,rfl⟩

def frobenius : ℤ := D.u * D.v - D.u - D.v

theorem frobenius_symmetry (t : ℤ) : t ∉ D.T ↔ D.frobenius - t ∈ D.T := by
  obtain ⟨a,b,hb,hbu,rfl⟩ := D.normal_form_exists t
  have he : D.frobenius - (a * D.u + b * D.v) =
      (-a-1) * D.u + (D.u-b-1) * D.v := by unfold frobenius; ring
  rw [he, D.normal_form_mem_iff hb hbu,
    D.normal_form_mem_iff (by omega : 0 ≤ D.u-b-1) (by omega)]
  omega

theorem subcritical_nonneg {P Q : ℤ} (hP : P < D.v) (hQ : Q < D.u)
    (ht : P * D.u + Q * D.v ∈ D.T) : 0 ≤ P ∧ 0 ≤ Q := by
  obtain ⟨a,b,ha,hb,he⟩ := ht
  obtain ⟨k,hpk,hqk⟩ := D.representation_difference he
  have hk : k = 0 := by
    by_contra hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · have : k ≤ -1 := by omega
      nlinarith [D.u_pos]
    · have : 1 ≤ k := by omega
      nlinarith [D.v_pos]
  simp [hk] at hpk hqk
  omega

theorem interior_gap {P Q : ℤ} (hP : 0 < P) (hQ : 0 < Q) :
    D.u * D.v - P * D.u - Q * D.v ∉ D.T := by
  intro ht
  obtain ⟨a,b,ha,hb,he⟩ := ht
  have he' : (P+a) * D.u + (Q+b) * D.v = D.v * D.u + 0 * D.v := by
    nlinarith [he]
  obtain ⟨k,hpk,hqk⟩ := D.representation_difference he'
  have hk : k ≤ -1 := by
    by_contra hk
    have : 0 ≤ k := by omega
    nlinarith [mul_nonneg this D.u_pos.le]
  nlinarith [D.v_pos]

theorem subcritical_gap {P Q : ℤ} (_hP : 0 ≤ P) (hPv : P < D.v)
    (hQ : 0 ≤ Q) (hQu : Q < D.u) :
    P * D.u + Q * D.v - D.u * D.v ∉ D.T := by
  have he : P * D.u + Q * D.v - D.u * D.v = (P-D.v)*D.u + Q*D.v := by ring
  rw [he, D.normal_form_mem_iff hQ hQu]
  omega

/-- Pointwise exact form of (2GI), with translations expressed by subtraction. -/
theorem two_generator_intersection_iff {A B t : ℤ}
    (hA : 0 < A) (hAv : A < D.v) (hB : 0 < B) (hBu : B < D.u) :
    (t - A * D.u ∈ D.T ∧ t - B * D.v ∈ D.T) ↔
      t - (A * D.u + B * D.v) ∈ D.T ∨ t - D.u * D.v ∈ D.T := by
  constructor
  · rintro ⟨⟨p,q,hp,hq,hpqe⟩,⟨r,s,hr,hs,hrse⟩⟩
    have he : (A+p)*D.u + q*D.v = r*D.u + (B+s)*D.v := by
      linear_combination hrse - hpqe
    obtain ⟨k,hak,hbk⟩ := D.representation_difference he
    rcases lt_trichotomy k 0 with hk | hk | hk
    · right
      have hk' : k ≤ -1 := by omega
      refine ⟨A+p, q-D.u, by omega, ?_, ?_⟩
      · nlinarith [D.u_pos]
      · linear_combination hpqe
    · left
      refine ⟨p,s,hp,hs,?_⟩
      simp only [hk, neg_zero, zero_mul, sub_eq_zero] at hbk
      rw [hbk] at hpqe
      linear_combination hpqe
    · right
      have hk' : 1 ≤ k := by omega
      refine ⟨A+p-D.v,q,?_,hq,?_⟩
      · nlinarith [D.v_pos]
      · linear_combination hpqe
  · rintro (⟨p,q,hp,hq,he⟩ | ⟨p,q,hp,hq,he⟩)
    · constructor
      · refine ⟨p,B+q,hp,by omega,?_⟩
        linear_combination he
      · refine ⟨A+p,q,by omega,hq,?_⟩
        linear_combination he
    · constructor
      · refine ⟨D.v-A+p,q,by omega,hq,?_⟩
        linear_combination he
      · refine ⟨p,D.u-B+q,hp,by omega,?_⟩
        linear_combination he

/-- Additive translate of the exact nonnegative-coefficient semigroup. -/
def translate (a : ℤ) : Set ℤ := {t | t - a ∈ D.T}

/-- Appendix A.1 (2GI), as an equality of sets. -/
theorem two_generator_intersection {A B : ℤ}
    (hA : 0 < A) (hAv : A < D.v) (hB : 0 < B) (hBu : B < D.u) :
    D.translate (A*D.u) ∩ D.translate (B*D.v) =
      D.translate (A*D.u+B*D.v) ∪ D.translate (D.u*D.v) := by
  ext t
  exact D.two_generator_intersection_iff hA hAv hB hBu

theorem mem_of_gt_frobenius {t : ℤ} (ht : D.frobenius < t) : t ∈ D.T := by
  by_contra h
  have := D.nonneg ((D.frobenius_symmetry t).mp h)
  omega

/-- Bridge to the frozen M1 integer numerical-semigroup semantics. -/
def semigroup : P21.NumericalSemigroup where
  carrier := D.T
  nonneg := fun _ ht => D.nonneg ht
  cofinite := ⟨D.frobenius+1, fun _ ht => D.mem_of_gt_frobenius (by omega)⟩

theorem isFrobenius : D.semigroup.IsFrobenius D.frobenius := by
  refine ⟨?_, ?_⟩
  · change D.frobenius ∉ D.T
    apply (D.frobenius_symmetry D.frobenius).mpr
    simp
  · intro t ht
    by_contra h
    exact ht (D.mem_of_gt_frobenius (by omega))

theorem normal_form_existsUnique (t : ℤ) :
    ∃! ab : ℤ × ℤ, 0 ≤ ab.2 ∧ ab.2 < D.u ∧ t = ab.1*D.u+ab.2*D.v := by
  obtain ⟨a,b,hb,hbu,he⟩ := D.normal_form_exists t
  refine ⟨(a,b), ⟨hb,hbu,he⟩, ?_⟩
  rintro ⟨c,d⟩ ⟨hd,hdu,he'⟩
  obtain ⟨rfl,rfl⟩ := D.normal_form_unique hd hdu hb hbu (he'.symm.trans he)
  rfl

end TwoGeneratorData
end P21.Symmetric
