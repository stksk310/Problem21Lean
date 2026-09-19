import P21.Nonsymmetric.Chain.C10.TerminalPacket

namespace P21.Nonsymmetric
namespace EuclideanState

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

def e (X : EuclideanState s F D) : ℤ := X.Epar / X.theta
def rhoRem (X : EuclideanState s F D) : ℤ := X.Epar % X.theta
def kappa (X : EuclideanState s F D) : ℤ := X.chi - X.e * X.Hp

theorem E_division (X : EuclideanState s F D) :
    X.Epar = X.e * X.theta + X.rhoRem := by
  simpa only [e, rhoRem] using (Int.ediv_mul_add_emod X.Epar X.theta).symm

theorem rhoRem_range (X : EuclideanState s F D) :
    0 ≤ X.rhoRem ∧ X.rhoRem < X.theta := by
  exact ⟨Int.emod_nonneg _ (ne_of_gt X.theta_pos'),
    Int.emod_lt_of_pos _ X.theta_pos'⟩

theorem e_pos (X : EuclideanState s F D) : 1 ≤ X.e := by
  rw [e, Int.le_ediv_iff_mul_le X.theta_pos]
  rw [X.E_source]
  have := X.R_pos
  have := X.theta_le
  omega

theorem chi_eq (X : EuclideanState s F D) : X.chi = X.e * X.Hp + X.kappa := by
  simp only [kappa]
  ring

theorem packet_det_remainder (X : EuclideanState s F D) :
    X.Dp = X.theta * X.kappa - X.rhoRem * X.Hp := by
  rw [Dp, X.E_division, X.chi_eq]
  ring

theorem Hp_pos (X : EuclideanState s F D) : 1 ≤ X.Hp := by
  rw [X.Hp_source]
  have := X.T_pos
  have := X.w_nonneg
  omega

theorem kappa_pos (X : EuclideanState s F D) : 1 ≤ X.kappa := by
  have hdet : 0 < X.Dp := by simpa only [Dp] using X.packet_det_pos
  rw [X.packet_det_remainder] at hdet
  have hrho := X.rhoRem_range.1
  have hHp := X.Hp_pos
  by_contra hk
  have hk0 : X.kappa ≤ 0 := by omega
  have htheta0 : 0 ≤ X.theta := le_of_lt X.theta_pos'
  have hrhoHp : 0 ≤ X.rhoRem * X.Hp := mul_nonneg hrho (by omega)
  have hthetaK : X.theta * X.kappa ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos htheta0 hk0
  linarith

theorem nonterminal_fail (X : EuclideanState s F D) (hnot : ¬ X.Terminal) :
    X.T ≤ X.kstar := by
  simp only [Terminal] at hnot
  omega

theorem nu_le_e_add_one (X : EuclideanState s F D) : X.nu ≤ X.e + 1 := by
  have huE : X.u ≤ X.Epar := by
    rw [X.E_source]
    have := X.R_pos
    omega
  have hdiv := Int.ediv_le_ediv X.theta_pos' huE
  simpa only [nu, e, add_comm] using add_le_add_right hdiv 1

theorem nu_eq_e_add_one (X : EuclideanState s F D) (hnot : ¬ X.Terminal) :
    X.nu = X.e + 1 := by
  have hle := X.nu_le_e_add_one
  have hfail := X.nonterminal_fail hnot
  have hk := X.kappa_pos
  have hHp := X.Hp_pos
  have hchi := X.chi_eq
  by_contra hne
  have hnue : X.nu ≤ X.e := by omega
  have hprod : X.nu * X.Hp ≤ X.e * X.Hp :=
    mul_le_mul_of_nonneg_right hnue (by have := X.Hp_pos; omega)
  simp only [kstar] at hfail
  have hneg : X.nu * X.Hp - X.chi < 0 := by
    rw [hchi]
    linarith
  have := X.T_pos
  omega

theorem u_division_e (X : EuclideanState s F D) (hnot : ¬ X.Terminal) :
    X.u = X.e * X.theta + X.z := by
  rw [X.u_division, X.nu_eq_e_add_one hnot]
  ring

theorem rhoRem_eq_R_add_z (X : EuclideanState s F D) (hnot : ¬ X.Terminal) :
    X.rhoRem = X.R + X.z := by
  have hE := X.E_division
  rw [X.E_source, X.u_division_e hnot] at hE
  linarith

theorem rhoRem_bounds (X : EuclideanState s F D) (hnot : ¬ X.Terminal) :
    X.R ≤ X.rhoRem ∧ X.rhoRem < X.theta := by
  constructor
  · rw [X.rhoRem_eq_R_add_z hnot]
    exact le_add_of_nonneg_right X.z_range.1
  · exact X.rhoRem_range.2

theorem kappa_le_w (X : EuclideanState s F D) (hnot : ¬ X.Terminal) :
    X.kappa ≤ X.w := by
  have hfail := X.nonterminal_fail hnot
  have hnu := X.nu_eq_e_add_one hnot
  have hchi := X.chi_eq
  have hHp := X.Hp_source
  simp only [kstar] at hfail
  rw [hnu, hchi, hHp] at hfail
  ring_nf at hfail
  linarith

theorem w_pos_of_nonterminal (X : EuclideanState s F D) (hnot : ¬ X.Terminal) :
    1 ≤ X.w := le_trans X.kappa_pos (X.kappa_le_w hnot)

theorem terminal_of_w_eq_zero (X : EuclideanState s F D) (hw : X.w = 0) : X.Terminal := by
  by_contra hnot
  have := X.w_pos_of_nonterminal hnot
  omega

theorem new_packet (X : EuclideanState s F D) :
    (X.Bcoef + X.e * X.Acoef) * g.n 0 + X.rhoRem * g.n 1 =
      (X.M + X.e * X.L) * g.m + X.kappa * g.n 2 := by
  have hE := X.E_division
  have hchi := X.chi_eq
  linear_combination X.DP + X.e * X.PP - hE * g.n 1 + hchi * g.n 2

theorem new_packet_coefficients (X : EuclideanState s F D) :
    0 ≤ X.Bcoef + X.e * X.Acoef ∧ 0 ≤ X.rhoRem ∧
      1 ≤ X.M + X.e * X.L ∧ 1 ≤ X.kappa := by
  have hA := X.Acoef_pos
  have hB := X.Bcoef_pos
  have he := X.e_pos
  have hL := X.L_pos
  have hM := X.M_pos
  exact ⟨by nlinarith, X.rhoRem_range.1, by nlinarith, X.kappa_pos⟩

end EuclideanState
end P21.Nonsymmetric
