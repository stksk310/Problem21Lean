import P21.Nonsymmetric.Chain.C9.NonlinearFirst

namespace P21.Nonsymmetric.ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns}
variable {hF : s.semigroup.IsFrobenius F}

def DLk (A : K.FirstFit) : ℤ := A.zhat-1
def DLQ (K : ChainCore s F D) : ℤ := K.Dtau
def DLupsilon (K : ChainCore s F D) (A : K.FirstFit) : ℤ :=
  K.Dtau-1-A.J
def DLG (K : ChainCore s F D) (A : K.FirstFit) : ℤ :=
  K.chain.gapJ+K.DLupsilon A
def DLEpar (K : ChainCore s F D) (A : K.FirstFit) : ℤ :=
  K.chain.R+K.DLupsilon A
def DLBpkt (K : ChainCore s F D) (A : K.FirstFit) : ℤ :=
  DLk A*K.Db+K.Dc
def DLa (K : ChainCore s F D) (A : K.FirstFit) : ℤ :=
  K.d-DLk A*K.Db

namespace FirstFit.RegionD

theorem linear_parameters (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) :
    1≤DLk A ∧ 0≤K.DLupsilon A ∧ K.r+1≤K.DLa A ∧
    K.S=DLk A*K.DLQ+K.DLG A ∧
    (D.rho 1 : ℤ)=(DLk A+1)*K.DLQ+K.DLG A ∧
    (D.rho 2 : ℤ)=(DLk A+1)*K.Croot+DLk A*(D.b 2 : ℤ)+A.chi ∧
    (D.a 0 : ℤ)=K.d+K.Db ∧ (D.b 0 : ℤ)=K.d+K.Dc ∧
    K.d=K.DLa A+DLk A*K.Db ∧
    A.I=K.d+K.chain.delta-1-(DLk A+1)*K.Db ∧
    A.J=K.DLQ-K.DLupsilon A-1 ∧ K.DLBpkt A=A.DF := by
  have lin := RD.linear_first_survivor hJ hc
  have hh := lin.1
  have hN := lin.2
  have hk : 1≤DLk A := by
    simp only [DLk]
    have := RD.zhat_ge_two hJ
    omega
  have hu : 0≤K.DLupsilon A := by
    simp only [DLupsilon]
    have := (RD.sharp_caps hJ).2.1
    omega
  have hai := RD.ai_eq
  have hbi := RD.bi_eq
  have hrho := RD.rhoj_eq
  have hI : A.I=K.d+K.chain.delta-1-(DLk A+1)*K.Db := by
    rw [A.I_eq]
    simp only [IZeta]
    rw [←A.N_eq, hN, hai, hh]
    simp only [DLk]
    ring
  have ha : K.r+1≤K.DLa A := by
    have hI0 := A.I_bounds.1
    have heq : K.DLa A-(K.r+1)=A.I := by
      rw [hI]
      simp only [DLa, ChainCore.Db]
      ring
    omega
  have hS : K.S=DLk A*K.DLQ+K.DLG A := by
    have hJeq := A.J_eq
    simp only [JZeta] at hJeq
    rw [←A.N_eq, hN, hrho, hh] at hJeq
    simp only [DLk, DLQ, DLG, DLupsilon]
    linarith [hJeq]
  have hrj : (D.rho 1 : ℤ)=(DLk A+1)*K.DLQ+K.DLG A := by
    rw [hrho, hh, hS]
    simp only [DLQ]
    ring
  have hrk0 := RD.rhok_first
  have hrk : (D.rho 2 : ℤ)=
      (DLk A+1)*K.Croot+DLk A*(D.b 2 : ℤ)+A.chi := by
    rw [hrk0]
    simp only [DLk, FirstFit.chi]
    rw [hN]
    ring
  have haieq : (D.a 0 : ℤ)=K.d+K.Db := by rw [hai, hh]; ring
  have hbieq : (D.b 0 : ℤ)=K.d+K.Dc := by rw [hbi, hh]; ring
  have hdecomp : K.d=K.DLa A+DLk A*K.Db := by simp [DLa]
  have hJform : A.J=K.DLQ-K.DLupsilon A-1 := by
    simp only [DLQ, DLupsilon]
    ring
  have hB : K.DLBpkt A=A.DF := by
    simp only [DLBpkt, FirstFit.DF]
    rw [hI]
    simp only [DLk, ChainCore.Db, ChainCore.Dc]
    ring
  exact ⟨hk,hu,ha,hS,hrj,hrk,haieq,hbieq,hdecomp,hI,hJform,hB⟩

theorem d_linear_packet (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) :
    K.DLBpkt A*g.n 0+K.DLEpar A*g.n 1=
      (DLk A+1)*g.m+A.chi*g.n 2 := by
  rcases RD.linear_parameters hJ hc with
    ⟨hk, hu, ha, hS, hrj, hrk, hai, hbi, hd, hI, hJform, hB⟩
  have hp := RD.packet_eq
  have lin := RD.linear_first_survivor hJ hc
  have hEF : A.EF=K.DLEpar A := by
    simp only [FirstFit.EF, DLEpar, DLupsilon]
    have hrho := RD.rhoj_eq
    rw [hrho, lin.1]
    ring
  rw [hB, ←hEF]
  rw [lin.2] at hp
  convert hp using 1 <;> simp [DLk]

theorem d_linear_coefficients (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) :
    0≤K.DLBpkt A ∧ 0≤K.DLEpar A ∧ 0≤DLk A+1 ∧ 0≤A.chi := by
  rcases RD.linear_parameters hJ hc with
    ⟨hk, hu, ha, hS, hrj, hrk, hai, hbi, hd, hI, hJform, hB⟩
  have hp := RD.packet_coefficients
  have hEF : A.EF=K.DLEpar A := by
    simp only [FirstFit.EF, DLEpar, DLupsilon]
    have hrho := RD.rhoj_eq
    have hh := (RD.linear_first_survivor hJ hc).1
    rw [hrho, hh]
    ring
  exact ⟨by rw [hB]; exact hp.1, by rw [←hEF]; exact hp.2.1,
    by omega, hp.2.2.2⟩

theorem intrinsic_linear_packet (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) :
    g.m+K.DLQ*g.n 1=K.Db*g.n 0+
      (K.Croot+(D.b 2 : ℤ))*g.n 2 := by
  have hs := K.shift_new
  have hh := (RD.linear_first_survivor hJ hc).1
  have ht : K.tau0=K.DLQ := by simp [ChainCore.tau0, DLQ, ChainCore.Dtau]
  have hai := RD.ai_eq
  have hDb : (D.a 0 : ℤ)-K.d=K.Db := by rw [hai, hh]; ring
  rw [hh, one_mul, ht] at hs
  simp only [one_mul] at hs
  rw [hDb] at hs
  simpa [add_comm, add_left_comm, add_assoc] using hs

theorem intrinsic_linear_coefficients (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) :
    0≤1 ∧ 0≤K.DLQ ∧ 0≤K.Db ∧ 0≤K.Croot+(D.b 2 : ℤ) := by
  have ht := (RD.tau_range hJ).1
  have hb := (RD.b_range hJ).1
  have hC := K.C_lower
  have ha := K.chain.scalar_ranges.2.2.2
  have hbk : (1:ℤ)≤D.b 2 := by exact_mod_cast D.b_pos 2
  simp only [DLQ]
  omega

end FirstFit.RegionD
end P21.Nonsymmetric.ChainCore
