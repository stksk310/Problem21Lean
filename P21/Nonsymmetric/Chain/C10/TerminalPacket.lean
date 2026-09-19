import P21.Nonsymmetric.Chain.C10.TerminalSetup

namespace P21.Nonsymmetric
namespace EuclideanState

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

def posPart (z : ℤ) : ℕ := z.toNat
def negPart (z : ℤ) : ℕ := (-z).toNat

theorem posPart_sub_negPart (z : ℤ) : (posPart z : ℤ) - negPart z = z := by
  by_cases hz : 0 ≤ z
  · have hn : -z ≤ 0 := by omega
    rw [posPart, negPart, Int.toNat_of_nonneg hz, Int.toNat_of_nonpos hn]
    simp
  · have hz' : z ≤ 0 := by omega
    have hn : 0 ≤ -z := by omega
    rw [posPart, negPart, Int.toNat_of_nonpos hz', Int.toNat_of_nonneg hn]
    simp

theorem posPart_cast_nonneg (z : ℤ) : 0 ≤ (posPart z : ℤ) := by positivity
theorem negPart_cast_nonneg (z : ℤ) : 0 ≤ (negPart z : ℤ) := by positivity

theorem posPart_le_toNat {z bound : ℤ} (hz : z ≤ bound) (_hbound : 0 ≤ bound) :
    posPart z ≤ bound.toNat := by
  unfold posPart
  exact Int.toNat_le_toNat hz

theorem Acoef_pos (X : EuclideanState s F D) : 0 < X.Acoef := by
  have hp : 0 < X.p := by have := X.p_pos; omega
  have hq : 0 < X.q := by have := X.q_pos; omega
  have hrd : 0 < X.r + X.delta := by
    have := X.r_nonneg
    have := X.delta_pos
    omega
  have hrb : 0 < X.r + X.beta := by
    have := X.r_nonneg
    have := X.beta_pos
    omega
  rw [X.A_source]
  positivity

theorem Bcoef_pos (X : EuclideanState s F D) : 0 < X.Bcoef := by
  have hv : 0 < X.v := by have := X.v_pos; omega
  have ht : 0 < X.t := by have := X.t_pos; omega
  have hrd : 0 < X.r + X.delta := by
    have := X.r_nonneg
    have := X.delta_pos
    omega
  have hrb : 0 < X.r + X.beta := by
    have := X.r_nonneg
    have := X.beta_pos
    omega
  rw [X.B_source]
  positivity

theorem L_pos (X : EuclideanState s F D) : 0 < X.L := by
  rw [X.L_eq]
  have := X.p_pos
  have := X.q_pos
  omega

theorem M_pos (X : EuclideanState s F D) : 0 < X.M := by
  rw [X.M_eq]
  have := X.v_pos
  have := X.t_pos
  omega

theorem Z_pos (X : EuclideanState s F D) : 0 < X.Z := by
  rw [Z]
  have := X.nu_ge_two
  have := X.Acoef_pos
  have := X.Bcoef_pos
  nlinarith

theorem N_pos (X : EuclideanState s F D) : 0 < X.N := by
  rw [N]
  have := X.nu_ge_two
  have := X.L_pos
  have := X.M_pos
  nlinarith

def terminalSource (X : EuclideanState s F D) : Fin 4 → ℕ :=
  ![0, X.Z.toNat, posPart X.jstar, posPart X.kstar]

def terminalTarget (X : EuclideanState s F D) : Fin 4 → ℕ :=
  ![X.N.toNat, 0, negPart X.jstar, negPart X.kstar]

theorem terminal_positive_parts_packet (X : EuclideanState s F D) :
    value g.all X.terminalSource = value g.all X.terminalTarget := by
  have hZ : ((X.Z.toNat : ℕ) : ℤ) = X.Z := Int.toNat_of_nonneg X.Z_pos.le
  have hN : ((X.N.toNat : ℕ) : ℤ) = X.N := Int.toNat_of_nonneg X.N_pos.le
  have hj := posPart_sub_negPart X.jstar
  have hk := posPart_sub_negPart X.kstar
  have hpacket := X.terminal_signed_packet
  simp only [value, Fin.sum_univ_four]
  dsimp [terminalSource, terminalTarget, Generators.all]
  have hall0 : (@Fin.cons 3 (fun _ => ℤ) g.m g.n) (0 : Fin 4) = g.m := rfl
  have hall1 : (@Fin.cons 3 (fun _ => ℤ) g.m g.n) (1 : Fin 4) = g.n 0 := rfl
  have hall2 : (@Fin.cons 3 (fun _ => ℤ) g.m g.n) (2 : Fin 4) = g.n 1 := rfl
  have hall3 : (@Fin.cons 3 (fun _ => ℤ) g.m g.n) (3 : Fin 4) = g.n 2 := rfl
  rw [hall0, hall1, hall2, hall3]
  rw [hZ, hN]
  linear_combination hpacket + hj * g.n 1 + hk * g.n 2

def WFactorization (X : EuclideanState s F D) : g.ActualFactorization4 (W F g.m) := by
  let coefficients : Fin 4 → ℕ :=
    ![0, (X.P - 1).toNat, (X.R - 1).toNat, (X.T - 1).toNat]
  have hP : (((X.P - 1).toNat : ℕ) : ℤ) = X.P - 1 :=
    Int.toNat_of_nonneg (by have := X.P_pos; omega)
  have hR : (((X.R - 1).toNat : ℕ) : ℤ) = X.R - 1 :=
    Int.toNat_of_nonneg (by have := X.R_pos; omega)
  have hT : (((X.T - 1).toNat : ℕ) : ℤ) = X.T - 1 :=
    Int.toNat_of_nonneg (by have := X.T_pos; omega)
  exact {
    coeff := coefficients
    equation := by
      simp only [value, Fin.sum_univ_four]
      dsimp [coefficients, Generators.all]
      have hall0 : (@Fin.cons 3 (fun _ => ℤ) g.m g.n) (0 : Fin 4) = g.m := rfl
      have hall1 : (@Fin.cons 3 (fun _ => ℤ) g.m g.n) (1 : Fin 4) = g.n 0 := rfl
      have hall2 : (@Fin.cons 3 (fun _ => ℤ) g.m g.n) (2 : Fin 4) = g.n 1 := rfl
      have hall3 : (@Fin.cons 3 (fun _ => ℤ) g.m g.n) (3 : Fin 4) = g.n 2 := rfl
      rw [hall0, hall1, hall2, hall3]
      rw [hP, hR, hT]
      simpa [add_assoc] using X.W_face.symm }

end EuclideanState
end P21.Nonsymmetric
