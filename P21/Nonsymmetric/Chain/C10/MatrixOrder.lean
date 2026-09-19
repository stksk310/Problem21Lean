import P21.Nonsymmetric.Chain.C10.CrossProductScale

namespace P21.Nonsymmetric
namespace EuclideanState

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

theorem p_ge_v_add_one (X : EuclideanState s F D) : X.v + 1 ≤ X.p := by
  have hnonneg_p : 0 ≤ X.p := by have := X.p_pos; omega
  have hnonneg_v : 0 ≤ X.v := by have := X.v_pos; omega
  have hnonneg_t : 0 ≤ X.t := by have := X.t_pos; omega
  have hnonneg_q : 0 ≤ X.q := by have := X.q_pos; omega
  by_contra h
  have hpv : X.p ≤ X.v := by omega
  have hqt : X.q < X.t := by
    by_contra hqt
    have htq : X.t ≤ X.q := by omega
    have hmul : X.p * X.t ≤ X.v * X.q :=
      mul_le_mul hpv htq hnonneg_t hnonneg_v
    nlinarith [X.det_one]
  have hLM := X.L_gt_M
  rw [X.L_eq, X.M_eq] at hLM
  omega

theorem q_ge_t (X : EuclideanState s F D) : X.t ≤ X.q := by
  have hpv := X.p_ge_v_add_one
  by_contra h
  have hqt : X.q + 1 ≤ X.t := by omega
  let a := X.p - X.v
  let b := X.t - X.q
  have ha : 1 ≤ a := by simp only [a]; omega
  have hb : 1 ≤ b := by simp only [b]; omega
  have hv : 0 < X.v := by have := X.v_pos; omega
  have hq : 0 < X.q := by have := X.q_pos; omega
  have ha' : 0 < a := by omega
  have hb' : 0 < b := by omega
  have hvb : 1 ≤ X.v * b := by have := mul_pos hv hb'; omega
  have haq : 1 ≤ a * X.q := by have := mul_pos ha' hq; omega
  have hab : 1 ≤ a * b := by have := mul_pos ha' hb'; omega
  have hid : X.p * X.t - X.q * X.v = X.v * b + a * X.q + a * b := by
    simp only [a, b]
    ring
  rw [X.det_one] at hid
  omega

theorem matrix_order (X : EuclideanState s F D) : X.v + 1 ≤ X.p ∧ X.t ≤ X.q :=
  ⟨X.p_ge_v_add_one, X.q_ge_t⟩

end EuclideanState
end P21.Nonsymmetric
