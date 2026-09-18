import P21.Nonsymmetric.Chain.ShiftNew

namespace P21.Nonsymmetric
namespace ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

/-- The genuine `R_k` face of the fixed actual element `W`. -/
theorem w_face_k (K : ChainCore s F D) :
    W F g.m = (K.chain.delta-1)*g.n 0 + (K.chain.gapJ-1)*g.n 1 +
      ((D.rho 2 : ℤ)+K.chain.T-1)*g.n 2 := by
  have hw := K.chain.W_exact
  have hp := K.chain.P_eq_b_delta
  have hr := K.chain.R_exact
  rw [hp, hr] at hw
  linear_combination hw - D.relation_two

/-- The completed ROOT/`R_j` family. This is a signed equality only. -/
theorem hrj (K : ChainCore s F D) (zeta n : ℤ) :
    F = (n-1)*g.m +
      (K.chain.delta-1+n*K.d-zeta*(D.a 0 : ℤ))*g.n 0 +
      (K.chain.gapJ-1+zeta*(D.rho 1 : ℤ)-n*K.S)*g.n 1 +
      ((D.rho 2 : ℤ)+K.chain.T-1-n*K.Croot-zeta*(D.b 2 : ℤ))*g.n 2 := by
  have hw := K.w_face_k
  simp [W] at hw
  linear_combination hw - n*K.root - zeta*D.relation_one

/-- Exact integer ceiling used in §8.2.  For `zeta ≥ 1` its numerator is
positive, and this equals `ceil ((zeta*a_i-delta+1)/d)`. -/
def nZeta (K : ChainCore s F D) (zeta : ℤ) : ℤ :=
  (zeta*(D.a 0 : ℤ)-K.chain.delta) / K.d + 1

def IZeta (K : ChainCore s F D) (zeta : ℤ) : ℤ :=
  K.chain.delta-1+K.nZeta zeta*K.d-zeta*(D.a 0 : ℤ)

def JZeta (K : ChainCore s F D) (zeta : ℤ) : ℤ :=
  K.chain.gapJ-1+zeta*(D.rho 1 : ℤ)-K.nZeta zeta*K.S

theorem a0_gt_d (K : ChainCore s F D) : K.d < (D.a 0 : ℤ) := by
  have hd := K.d_range.2
  have ha := K.chain.a0_exact
  have hdelta := K.chain.scalar_ranges.1
  omega

theorem IZeta_remainder (K : ChainCore s F D) (zeta : ℤ) :
    K.IZeta zeta = K.d-1-
      ((zeta*(D.a 0 : ℤ)-K.chain.delta) % K.d) := by
  have hdiv := Int.ediv_mul_add_emod
    (zeta*(D.a 0 : ℤ)-K.chain.delta) K.d
  simp [IZeta, nZeta]
  linear_combination hdiv

theorem IZeta_bounds (K : ChainCore s F D) (zeta : ℤ) :
    0 ≤ K.IZeta zeta ∧ K.IZeta zeta ≤ K.d-1 := by
  have hd := K.d_range.1
  have hne : K.d ≠ 0 := by omega
  have hlo := Int.emod_nonneg (zeta*(D.a 0 : ℤ)-K.chain.delta) hne
  have hhi := Int.emod_lt_of_pos (zeta*(D.a 0 : ℤ)-K.chain.delta) (by omega : 0 < K.d)
  rw [K.IZeta_remainder]
  omega

theorem nZeta_strict (K : ChainCore s F D) {zeta eta : ℤ}
    (hz : zeta < eta) : K.nZeta zeta < K.nZeta eta := by
  let A : ℤ := (D.a 0 : ℤ)
  let Bz : ℤ := zeta*A-K.chain.delta
  let Be : ℤ := eta*A-K.chain.delta
  have hd0 := K.d_range.1
  have hd : 0 < K.d := by omega
  have ha : K.d < A := by simpa [A] using K.a0_gt_d
  have hgap : Bz+K.d < Be := by
    dsimp [Bz, Be]
    nlinarith
  have hrem0 := Int.emod_nonneg Be (show K.d ≠ 0 by omega)
  have hremd := Int.emod_lt_of_pos Be hd
  have hdecomp := Int.ediv_mul_add_emod Be K.d
  have hlt : Bz < (Be / K.d)*K.d := by nlinarith
  have hq : Bz / K.d < Be / K.d :=
    (Int.ediv_lt_iff_lt_mul hd).2 hlt
  simpa [nZeta, Bz, Be, A] using add_lt_add_right hq 1

theorem nZeta_one (K : ChainCore s F D) : K.nZeta 1 = K.q0 := by
  have ha := K.chain.a0_exact
  simp [nZeta, q0, h]
  rw [ha]
  ring_nf

theorem nZeta_one_ge_two (K : ChainCore s F D) : 2 ≤ K.nZeta 1 := by
  rw [K.nZeta_one]
  exact K.euclidean.q0_pos

theorem nZeta_d (K : ChainCore s F D) :
    K.nZeta K.d = (D.a 0 : ℤ)-((K.chain.delta-1)/K.d) := by
  have hd0 := K.d_range.1
  have hd : 0 < K.d := by omega
  let q := (K.chain.delta-1)/K.d
  let r := (K.chain.delta-1)%K.d
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (show K.d ≠ 0 by omega)
  have hrd : r < K.d := Int.emod_lt_of_pos _ hd
  have hdecomp := Int.ediv_mul_add_emod (K.chain.delta-1) K.d
  have hnum : K.d*(D.a 0 : ℤ)-K.chain.delta =
      ((D.a 0 : ℤ)-q-1)*K.d+(K.d-r-1) := by
    dsimp [q, r] at *
    linear_combination hdecomp
  have hrem : 0 ≤ K.d-r-1 ∧ K.d-r-1 < K.d := by omega
  have hquot : (K.d*(D.a 0 : ℤ)-K.chain.delta)/K.d =
      (D.a 0 : ℤ)-q-1 := by
    rw [Int.ediv_eq_iff_of_pos hd]
    constructor <;> nlinarith [hnum]
  simp [nZeta, hquot, q]

def fitV (K : ChainCore s F D) : ℤ :=
  K.d*(D.rho 1 : ℤ)-K.S*(D.a 0 : ℤ)

theorem fitV_pos (K : ChainCore s F D) : 0 < K.fitV := by
  exact K.slopes.j_pos

theorem JZeta_d (K : ChainCore s F D) :
    K.JZeta K.d = K.fitV +
      K.S*((K.chain.delta-1)/K.d)+K.chain.gapJ-1 := by
  rw [JZeta, K.nZeta_d]
  simp [fitV]
  ring

theorem JZeta_d_pos (K : ChainCore s F D) : 0 < K.JZeta K.d := by
  have hd0 := K.d_range.1
  have hd : 0 < K.d := by omega
  have hdelta : 0 ≤ K.chain.delta-1 := by have := K.chain.scalar_ranges.1; omega
  have hq : 0 ≤ (K.chain.delta-1)/K.d := Int.ediv_nonneg hdelta hd.le
  have hS : 1 ≤ K.S := by
    have := K.S_strong
    have := K.chain.scalar_ranges.2.2.1
    omega
  have hg := K.chain.scalar_ranges.2.2.1
  rw [K.JZeta_d]
  nlinarith [K.fitV_pos, mul_nonneg (show 0 ≤ K.S by omega) hq]

private theorem fit_exists (K : ChainCore s F D) :
    ∃ t : ℕ, 0 ≤ K.JZeta ((t : ℤ)+1) := by
  let t : ℕ := (K.d-1).toNat
  have hd := K.d_range.1
  have ht0 : (t : ℤ) = K.d-1 := by
    dsimp [t]
    exact Int.toNat_of_nonneg (by omega)
  have ht : (t : ℤ)+1 = K.d := by omega
  exact ⟨t, by rw [ht]; exact (K.JZeta_d_pos).le⟩

noncomputable def firstIndexNat (K : ChainCore s F D) : ℕ :=
  Nat.find K.fit_exists

noncomputable def zhat (K : ChainCore s F D) : ℤ := (K.firstIndexNat : ℤ)+1

theorem zhat_pos (K : ChainCore s F D) : 1 ≤ K.zhat := by
  simp [zhat]

theorem zhat_fits (K : ChainCore s F D) : 0 ≤ K.JZeta K.zhat := by
  simpa [zhat, firstIndexNat] using Nat.find_spec K.fit_exists

theorem zhat_minimal (K : ChainCore s F D) {zeta : ℤ}
    (hz : 1 ≤ zeta) (hfit : 0 ≤ K.JZeta zeta) : K.zhat ≤ zeta := by
  let t : ℕ := (zeta-1).toNat
  have ht0 : (t : ℤ)=zeta-1 := by
    dsimp [t]
    exact Int.toNat_of_nonneg (by omega)
  have ht : (t : ℤ)+1=zeta := by omega
  have hf : 0 ≤ K.JZeta ((t : ℤ)+1) := by simpa [ht] using hfit
  have hmin : K.firstIndexNat ≤ t := Nat.find_min' K.fit_exists hf
  simp only [zhat]
  have hminZ : (K.firstIndexNat : ℤ) ≤ (t : ℤ) := by exact_mod_cast hmin
  omega

theorem zhat_le_d (K : ChainCore s F D) : K.zhat ≤ K.d :=
  K.zhat_minimal K.d_range.1 (K.JZeta_d_pos).le

/-- The genuine first fitting point, with the minimum and its predecessor
property retained for downstream same-element arguments. -/
structure FirstFit (K : ChainCore s F D) where
  zhat : ℤ
  N : ℤ
  I : ℤ
  J : ℤ
  zhat_eq : zhat = K.zhat
  N_eq : N = K.nZeta zhat
  I_eq : I = K.IZeta zhat
  J_eq : J = K.JZeta zhat
  zhat_range : 1 ≤ zhat ∧ zhat ≤ K.d
  minimal : ∀ zeta : ℤ, 1 ≤ zeta → 0 ≤ K.JZeta zeta → zhat ≤ zeta
  predecessor : 1 < zhat → K.JZeta (zhat-1) < 0

noncomputable def firstFit (K : ChainCore s F D) : K.FirstFit where
  zhat := K.zhat
  N := K.nZeta K.zhat
  I := K.IZeta K.zhat
  J := K.JZeta K.zhat
  zhat_eq := rfl
  N_eq := rfl
  I_eq := rfl
  J_eq := rfl
  zhat_range := ⟨K.zhat_pos, K.zhat_le_d⟩
  minimal := fun _ hz hf => K.zhat_minimal hz hf
  predecessor := by
    intro hz
    by_contra hn
    have hf : 0 ≤ K.JZeta (K.zhat-1) := by omega
    have hm := K.zhat_minimal (zeta:=K.zhat-1) (by omega) hf
    omega

namespace FirstFit

variable {K : ChainCore s F D} (A : K.FirstFit)

theorem N_ge_two : 2 ≤ A.N := by
  rw [A.N_eq]
  have hz := A.zhat_range.1
  by_cases h : A.zhat=1
  · rw [h]
    exact K.nZeta_one_ge_two
  · have hh : K.nZeta 1 < K.nZeta A.zhat :=
      K.nZeta_strict (zeta:=1) (eta:=A.zhat) (by omega)
    have := K.nZeta_one_ge_two
    omega

theorem I_bounds : 0 ≤ A.I ∧ A.I ≤ K.d-1 := by
  rw [A.I_eq]
  exact K.IZeta_bounds A.zhat

theorem J_nonneg : 0 ≤ A.J := by
  rw [A.J_eq, A.zhat_eq]
  exact K.zhat_fits

theorem J_sharp (h : 1 < A.zhat) : A.J ≤ D.rho 1-K.S-1 := by
  have hz := A.zhat_range.1
  have hp := A.predecessor h
  have hn : K.nZeta (A.zhat-1) < K.nZeta A.zhat := K.nZeta_strict (by omega)
  rw [A.J_eq]
  simp [JZeta] at hp ⊢
  have hS : 1 ≤ K.S := by
    have := K.S_strong
    have := K.chain.scalar_ranges.2.2.1
    omega
  nlinarith

theorem J_upper : A.J ≤ D.rho 1-K.S+K.chain.gapJ-1 := by
  have hz := A.zhat_range.1
  by_cases h : A.zhat=1
  · rw [A.J_eq, h]
    simp [JZeta]
    have hN := K.nZeta_one_ge_two
    have hS : 1 ≤ K.S := by
      have := K.S_strong
      have := K.chain.scalar_ranges.2.2.1
      omega
    nlinarith
  · have hs := A.J_sharp (by omega)
    have hg := K.chain.scalar_ranges.2.2.1
    omega

theorem caps :
    2 ≤ A.N ∧ 0 ≤ A.I ∧ A.I ≤ K.d-1 ∧ 0 ≤ A.J ∧
      A.J ≤ D.rho 1-K.S+K.chain.gapJ-1 :=
  ⟨A.N_ge_two, A.I_bounds.1, A.I_bounds.2, A.J_nonneg, A.J_upper⟩

def Xi : ℤ := A.N*K.Croot+A.zhat*(D.b 2 : ℤ)-
  ((D.rho 2 : ℤ)+K.chain.T-1)

def omegaHat : ℤ := F+A.Xi*g.n 2

theorem hrj_at :
    F = (A.N-1)*g.m+A.I*g.n 0+A.J*g.n 1-A.Xi*g.n 2 := by
  have h := K.hrj A.zhat A.N
  rw [A.N_eq] at h ⊢
  rw [A.I_eq, A.J_eq]
  simp [IZeta, JZeta, Xi, A.N_eq] at h ⊢
  linear_combination h

theorem Xi_pos (hF : s.semigroup.IsFrobenius F) : 1 ≤ A.Xi := by
  by_contra hn
  have hm := four_mem (g:=g) (A.N-1) A.I A.J (-A.Xi)
    (by have := A.N_ge_two; omega) A.I_bounds.1 A.J_nonneg (by omega)
  apply hF.1
  change F ∈ g.Gamma
  rw [A.hrj_at]
  simpa [sub_eq_add_neg] using hm

theorem omegaHat_eq :
    A.omegaHat = (A.N-1)*g.m+A.I*g.n 0+A.J*g.n 1 := by
  have h := A.hrj_at
  simp [omegaHat]
  linear_combination h

noncomputable def omegaHat_factorization : g.ActualFactorization4 A.omegaHat := by
  let coeff : Fin 4 → ℕ := ![(A.N-1).toNat, A.I.toNat, A.J.toNat, 0]
  have hN : ((A.N-1).toNat : ℤ)=A.N-1 := Int.toNat_of_nonneg (by have := A.N_ge_two; omega)
  have hI : (A.I.toNat : ℤ)=A.I := Int.toNat_of_nonneg A.I_bounds.1
  have hJ : (A.J.toNat : ℤ)=A.J := Int.toNat_of_nonneg A.J_nonneg
  exact {
    coeff := coeff
    equation := by
      simp only [value, Fin.sum_univ_four]
      dsimp [coeff, Generators.all]
      rw [hN, hI, hJ]
      change (A.N-1)*g.m+A.I*g.n 0+A.J*g.n 1+0*g.n 2=A.omegaHat
      simpa [add_assoc] using A.omegaHat_eq.symm }

theorem omegaHat_actual : A.omegaHat ∈ g.Gamma :=
  ⟨A.omegaHat_factorization.coeff, A.omegaHat_factorization.equation⟩

theorem omegaHat_zero_k : A.omegaHat_factorization.coeff 3 = 0 := by
  rfl

end FirstFit
end ChainCore
end P21.Nonsymmetric
