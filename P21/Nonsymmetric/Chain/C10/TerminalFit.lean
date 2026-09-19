import P21.Nonsymmetric.Chain.C10.TerminalPacket
import P21.Nonsymmetric.Chain.C10.TerminalCertificate

namespace P21.Nonsymmetric
namespace EuclideanState

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

theorem phi_at_P (X : EuclideanState s F D) : X.Phi X.P = X.mhat - X.Kcal := by
  rw [Phi, mhat, KcalAt, Kcal, X.ai_source, X.bi_source]

theorem terminal_i_fit (X : EuclideanState s F D) (hterminal : X.Terminal) :
    X.Z + 1 ≤ X.P := by
  by_contra hfit
  have hPZ : X.P ≤ X.Z := by omega
  have hmono := X.phi_antitone_of_le hPZ
  have hphiZ := X.terminal_phi_pos hterminal
  have hphiP : 0 < X.Phi X.P := lt_of_lt_of_le hphiZ hmono
  rw [X.phi_at_P] at hphiP
  have hmk : X.Kcal < X.mhat := sub_pos.mp hphiP
  have hmhat : (X.Kcal : ℚ) < X.mhat := by exact_mod_cast hmk
  have hsigma := X.sigma_pos
  have hscaled := mul_lt_mul_of_pos_left hmhat hsigma
  rw [← X.nk_scale, ← X.mhat_scale] at hscaled
  have hscaledZ : g.n 2 < g.m := by exact_mod_cast hscaled
  exact (not_lt_of_ge (le_of_lt (s.n_gt 2))) hscaledZ

theorem terminal_source_contained (X : EuclideanState s F D) (hterminal : X.Terminal) :
    ∀ i, X.terminalSource i ≤ X.WFactorization.coeff i := by
  intro i
  fin_cases i
  · simp [terminalSource, WFactorization]
  · simp only [terminalSource, WFactorization, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact posPart_le_toNat (by have := X.terminal_i_fit hterminal; omega)
      (by have := X.P_pos; omega)
  · simp only [terminalSource, WFactorization, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact posPart_le_toNat X.jstar_le (by have := X.R_pos; omega)
  · simp only [terminalSource, WFactorization, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact posPart_le_toNat hterminal (by have := X.T_pos; omega)

def terminalReplacement (X : EuclideanState s F D) (hterminal : X.Terminal) :
    g.ActualFactorization4 (W F g.m) :=
  replaceWithinActualFactorization X.WFactorization X.terminalSource X.terminalTarget
    (X.terminal_source_contained hterminal) X.terminal_positive_parts_packet

theorem terminalReplacement_m_coeff (X : EuclideanState s F D) (hterminal : X.Terminal) :
    (X.terminalReplacement hterminal).coeff 0 = X.N.toNat := by
  have hN := X.N_pos.le
  simp [terminalReplacement, replaceWithinActualFactorization, terminalSource, terminalTarget,
    WFactorization, hN]

theorem terminalReplacement_m_pos (X : EuclideanState s F D) (hterminal : X.Terminal) :
    0 < (X.terminalReplacement hterminal).coeff 0 := by
  rw [X.terminalReplacement_m_coeff hterminal]
  refine Nat.pos_of_ne_zero ?_
  intro hzero
  have hnonpos : X.N ≤ 0 := Int.toNat_eq_zero.mp hzero
  have := X.N_pos
  omega

theorem terminal_f_mem (X : EuclideanState s F D) (hterminal : X.Terminal) : F ∈ g.Gamma := by
  have removed := removeOne (X.terminalReplacement hterminal) 0
    (X.terminalReplacement_m_pos hterminal)
  apply actual_iff_mem.mp
  refine ⟨?_⟩
  simpa [W, Generators.all] using removed

theorem jstar_terminal_sub (X : EuclideanState s F D) : X.jstar = X.R - X.hterm := by
  rw [X.jstar_eq, hterm]
  ring

theorem kstar_terminal_sub (X : EuclideanState s F D) :
    X.kstar = X.T - 1 - X.xterm := by
  simp only [kstar, xterm]
  ring

theorem final_exact (X : EuclideanState s F D) (_hterminal : X.Terminal) :
    F = (X.N - 1) * g.m + (X.P - 1 - X.Z) * g.n 0 +
      (X.hterm - 1) * g.n 1 + X.xterm * g.n 2 := by
  have hW := X.W_face
  rw [W] at hW
  have hpacket := X.terminal_signed_packet
  rw [X.jstar_terminal_sub, X.kstar_terminal_sub] at hpacket
  linear_combination hW + hpacket

theorem final_exact_coefficients (X : EuclideanState s F D) (hterminal : X.Terminal) :
    0 ≤ X.N - 1 ∧ 0 ≤ X.P - 1 - X.Z ∧ 0 ≤ X.hterm - 1 ∧ 0 ≤ X.xterm := by
  exact ⟨by have := X.N_pos; omega,
    by have := X.terminal_i_fit hterminal; omega,
    by have := X.hterm_pos; omega,
    X.xterm_nonneg hterminal⟩

end EuclideanState
end P21.Nonsymmetric
