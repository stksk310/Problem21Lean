import P21.Nonsymmetric.Path.PairExclusion

namespace P21.Nonsymmetric
namespace PathInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

namespace PFreeI

def eta (D : HerzogCriticalData g) (P : PathInput s F D) (_p : PFreeI P) : ℤ :=
  P.nu - D.b 2
def A0 (P : PathInput s F D) (p : PFreeI P) : ℤ := p.Y + P.lambda + 1
def B0 (p : PFreeI P) : ℤ := p.H0 + 1
def C0 (P : PathInput s F D) (p : PFreeI P) : ℤ := P.T - p.K - 1
def D0 (P : PathInput s F D) (p : PFreeI P) : ℤ := P.P0 - p.Y - 1
def E0 (D : HerzogCriticalData g) (p : PFreeI P) : ℤ := p.H0 + D.b 1 + 1
def F0 (D : HerzogCriticalData g) (P : PathInput s F D) (p : PFreeI P) : ℤ :=
  p.K + p.eta D P + 1

/-- M+ is signed: its k coefficient is negative. -/
theorem Mplus (P : PathInput s F D) (p : PFreeI P) :
    g.m = p.A0 P * g.n 0 + p.B0 * g.n 1 - p.C0 P * g.n 2 := by
  have he := p.equationA
  have hq := P.qA_eq
  have hT := P.T_eq
  have hl : (P.lambda.toNat : ℤ) = P.lambda :=
    Int.toNat_of_nonneg (by have := P.lambda_range.1; omega)
  simp [value, Fin.sum_univ_succ, Nat.cast_add, hl] at he
  simp only [A0, B0, C0]
  linear_combination he - hq

/-- M- is signed until P5.4 proves `F0 ≥ 1`. -/
theorem Mminus (P : PathInput s F D) (p : PFreeI P) :
    g.m = -p.D0 P * g.n 0 + p.E0 D * g.n 1 + p.F0 D P * g.n 2 := by
  have he := p.equationB
  have hq := P.qB_eq
  have hn : (P.nu.toNat : ℤ) = P.nu :=
    Int.toNat_of_nonneg (by have := P.nu_range.1; omega)
  simp [value, Fin.sum_univ_succ, Nat.cast_add, hn] at he
  simp only [D0, E0, F0, eta]
  linear_combination he - hq

theorem A0_add_D0 (P : PathInput s F D) (p : PFreeI P) :
    p.A0 P + p.D0 P = D.rho 0 := by
  have hP := P.P0_eq
  have hb : P.beta = (D.b 0 : ℤ) - P.lambda := rfl
  have hr : (D.rho 0 : ℤ) = D.a 0 + D.b 0 := by exact_mod_cast D.rho_eq 0
  simp only [A0, D0]
  omega

theorem E0_sub_B0 (p : PFreeI P) : p.E0 D - p.B0 = D.b 1 := by
  simp [E0, B0]

theorem C0_add_F0 (P : PathInput s F D) (p : PFreeI P) :
    p.C0 P + p.F0 D P = D.a 2 := by
  have hT := P.T_eq
  have ha : P.alpha = (D.a 2 : ℤ) - P.nu := rfl
  simp only [C0, F0, eta]
  omega

theorem A0_pos (P : PathInput s F D) (p : PFreeI P) : 1 ≤ p.A0 P := by
  have := P.lambda_range.1
  simp only [A0]
  omega

theorem B0_pos (p : PFreeI P) : 1 ≤ p.B0 := by simp [B0]

end PFreeI
end PathInput
end P21.Nonsymmetric
