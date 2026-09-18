import P21.Nonsymmetric.Chain.C9.RegionUExclusion

namespace P21.Nonsymmetric.ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D}

def Db (K : ChainCore s F D) : ℤ := K.r+K.chain.delta
def Dc (K : ChainCore s F D) : ℤ := K.r+K.chain.beta
def Dtau (K : ChainCore s F D) : ℤ := (D.rho 1 : ℤ)-K.h*K.S
def DV (K : ChainCore s F D) : ℤ := K.d*(D.rho 1 : ℤ)-K.S*(D.a 0 : ℤ)
def DDj (K : ChainCore s F D) : ℤ := K.d*(D.a 1 : ℤ)+K.S*(D.b 0 : ℤ)

namespace FirstFit

variable {A : K.FirstFit} {E : K.Returns} {hF : s.semigroup.IsFrobenius F}

def packetCount (A : K.FirstFit) : ℤ :=
  (K.Croot-K.chain.alpha)/A.chi+1

namespace RegionD

theorem e0_strong (RD : A.RegionD E hF) (hJ : K.J0<0) :
    K.chain.beta+K.chain.delta+1≤K.e0 :=
  (K.sum_notch E hF RD.caps hJ RD.strict).2

theorem tau_ge_R (RD : A.RegionD E hF) (hJ : K.J0<0) :
    K.chain.R+1≤K.Dtau := by
  simpa [ChainCore.Dtau, ChainCore.tau0] using
    (K.FK_strong E hF RD.caps hJ RD.strict).2.2

theorem tau_range (RD : A.RegionD E hF) (hJ : K.J0<0) :
    1≤K.Dtau ∧ K.Dtau≤K.S-K.chain.gapJ := by
  have C := K.compact_data hJ
  constructor
  · simpa [ChainCore.Dtau, ChainCore.tau0] using C.tau_pos
  · have hs := C.sum_exact
    have hd := C.Delta_pos
    simp only [ChainCore.Dtau, ChainCore.tau0] at hs ⊢
    omega

theorem ai_eq (RD : A.RegionD E hF) :
    (D.a 0 : ℤ)=K.h*K.d+K.Db := by
  have Eu := K.euclidean
  have ha := K.chain.a0_exact
  simp only [ChainCore.Db]
  nlinarith [Eu.lambda_eq]

theorem bi_eq (RD : A.RegionD E hF) :
    (D.b 0 : ℤ)=K.h*K.d+K.Dc := by
  have Eu := K.euclidean
  have hb := K.chain.b0_exact
  simp only [ChainCore.Dc]
  nlinarith [Eu.lambda_eq]

theorem rhoj_eq (RD : A.RegionD E hF) :
    (D.rho 1 : ℤ)=K.h*K.S+K.Dtau := by
  simp [ChainCore.Dtau]

theorem V_eq (RD : A.RegionD E hF) :
    K.DV=K.d*K.Dtau-K.Db*K.S := by
  have hai := RD.ai_eq
  have hrj := RD.rhoj_eq
  simp only [ChainCore.DV]
  rw [hai, hrj]
  ring

theorem V_pos (RD : A.RegionD E hF) : 0<K.DV := by
  simpa [ChainCore.DV, ChainCore.fitV] using RD.slopes.j_pos

theorem b_range (RD : A.RegionD E hF) (hJ : K.J0<0) :
    1≤K.Db ∧ K.Db≤K.d-K.chain.beta-1 ∧ K.Db<K.d := by
  have Eu := K.euclidean
  have he := RD.e0_strong hJ
  have hs := K.chain.scalar_ranges
  have heq := Eu.e0_eq
  have hr := Eu.r_range.1
  simp only [ChainCore.Db]
  constructor
  · omega
  constructor <;> omega

theorem deep_bound (RD : A.RegionD E hF) :
    (D.b 2 : ℤ)+2*K.chain.alpha+1≤K.Croot := RD.C_deep

theorem chi_pos (RD : A.RegionD E hF) : 1≤A.chi := by
  have hT := K.chain.T_exact
  have hb : (1:ℤ)≤D.b 2 := by exact_mod_cast D.b_pos 2
  have ha := K.chain.scalar_ranges.2.2.2
  have hgt := RD.chi_gt
  omega

theorem chi_upper (RD : A.RegionD E hF) : A.chi≤K.Croot-K.chain.alpha := by
  exact RD.chi_le

theorem packet_eq (RD : A.RegionD E hF) :
    A.DF*g.n 0+A.EF*g.n 1=(A.N-1)*g.m+A.chi*g.n 2 := by
  have hp := RD.packet.removed
  have hc := RD.chi_pos
  rw [max_eq_left (by omega : 0≤A.chi), max_eq_right (by omega : -A.chi≤0)] at hp
  simpa using hp.symm

theorem packet_coefficients (RD : A.RegionD E hF) :
    0≤A.DF ∧ 0≤A.EF ∧ 0≤A.N-1 ∧ 0≤A.chi := by
  exact ⟨A.DF_pos.le,A.EF_pos.le,by have := A.N_ge_two; omega,by have := RD.chi_pos; omega⟩

theorem omegaD_eq (RD : A.RegionD E hF) :
    F+(K.Croot-K.chain.alpha+1)*g.n 2=
      (K.d+K.chain.beta-1)*g.n 0+
      (K.chain.R+(D.rho 1 : ℤ)-K.S-1)*g.n 1 :=
  K.centralFKUpper

theorem packetCount_ge_two (RD : A.RegionD E hF) : 2≤A.packetCount := by
  have hc := RD.chi_pos
  have hle := RD.chi_upper
  have hdiv : 1≤(K.Croot-K.chain.alpha)/A.chi := by
    rw [Int.le_ediv_iff_mul_le (show 0<A.chi by omega)]
    simpa using hle
  simp only [packetCount]
  omega

end RegionD
end FirstFit
end P21.Nonsymmetric.ChainCore
