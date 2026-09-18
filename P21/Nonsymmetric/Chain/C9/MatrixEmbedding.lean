import P21.Nonsymmetric.Chain.C9.JShortage

namespace P21.Nonsymmetric.ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns}
variable {hF : s.semigroup.IsFrobenius F}

def DLp (K : ChainCore s F D) (A : K.FirstFit) : ℤ := K.DLf A*DLk A+1
def DLq (K : ChainCore s F D) (A : K.FirstFit) : ℤ := K.DLf A
def DLs (K : ChainCore s F D) (A : K.FirstFit) : ℤ := DLk A
def DLt (_K : ChainCore s F D) (_A : _K.FirstFit) : ℤ := 1
def DLL (K : ChainCore s F D) (A : K.FirstFit) : ℤ := K.DLp A+K.DLq A
def DLM (K : ChainCore s F D) (A : K.FirstFit) : ℤ := K.DLs A+K.DLt A
def DLA (K : ChainCore s F D) (A : K.FirstFit) : ℤ :=
  K.DLp A*K.Db+K.DLq A*K.Dc
def DLB (K : ChainCore s F D) (A : K.FirstFit) : ℤ :=
  K.DLs A*K.Db+K.DLt A*K.Dc
def DLHp (K : ChainCore s F D) (A : K.FirstFit) : ℤ :=
  K.chain.T+K.DLw A

namespace FirstFit.RegionD

theorem complementary_packet (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) :
    K.DLL A*g.m+K.DLtheta A*g.n 1=
      K.DLA A*g.n 0+K.DLHp A*g.n 2 := by
  have hp := RD.d_linear_packet hJ hc
  have hi := RD.intrinsic_linear_packet hJ hc
  have rem := RD.linear_remainder_parameters hJ hc
  have hC := rem.2.2.2.1
  have hQ : K.DLQ=K.DLf A*K.DLEpar A+K.DLtheta A := by
    simp only [DLtheta]
    ring
  have hT := K.chain.T_exact
  have hB : K.DLBpkt A=DLk A*K.Db+K.Dc := rfl
  rw [hQ, hC] at hi
  have hK : K.chain.alpha+K.DLf A*A.chi+K.DLw A+(D.b 2 : ℤ)=
      K.DLf A*A.chi+(K.chain.T+K.DLw A) := by rw [hT]; ring
  rw [hK] at hi
  rw [hB] at hp
  simp only [DLL, DLp, DLq, DLA, DLHp]
  linear_combination hi - K.DLf A*hp

theorem complementary_coefficients (RD : A.RegionD E hF)
    (hJ : K.J0<0) (hc : s.semigroup.Canonical F g.m) :
    0<K.DLL A ∧ 0<K.DLtheta A ∧ 0<K.DLA A ∧ 0<K.DLHp A := by
  have rem := RD.linear_remainder_parameters hJ hc
  have lin := RD.linear_parameters hJ hc
  have hr := K.euclidean.r_range.1
  have hs := K.chain.scalar_ranges
  have hT := K.chain.T_exact
  have hbk : (1:ℤ)≤D.b 2 := by exact_mod_cast D.b_pos 2
  simp only [DLL, DLp, DLq, DLA, DLHp, ChainCore.Db, ChainCore.Dc]
  constructor
  · nlinarith [mul_pos (show 0<K.DLf A by omega) (show 0<DLk A by omega)]
  constructor
  · exact rem.2.2.2.2.1
  constructor
  · nlinarith [mul_pos (show 0<K.DLf A*DLk A+1 by nlinarith)
        (show 0<K.r+K.chain.delta by omega),
      mul_pos (show 0<K.DLf A by omega) (show 0<K.r+K.chain.beta by omega)]
  · rw [hT]
    omega

theorem matrix_parameters (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) :
    1≤K.DLp A ∧ 1≤K.DLq A ∧ 1≤K.DLs A ∧ 1≤K.DLt A ∧
    K.DLp A*K.DLt A-K.DLq A*K.DLs A=1 ∧
    K.DLL A=1+K.DLf A*(DLk A+1) ∧
    K.DLM A=DLk A+1 ∧ K.DLM A<K.DLL A ∧
    K.DLA A=K.Db+K.DLf A*K.DLBpkt A ∧
    K.DLB A=K.DLBpkt A := by
  have hf := (RD.linear_remainder_parameters hJ hc).1
  have hk := (RD.linear_parameters hJ hc).1
  simp only [DLp, DLq, DLs, DLt, DLL, DLM, DLA, DLB, DLBpkt]
  constructor
  · nlinarith
  constructor
  · exact hf
  constructor
  · exact hk
  constructor
  · norm_num
  constructor
  · ring
  constructor
  · ring
  constructor
  · trivial
  constructor
  · nlinarith [mul_pos (show 0<K.DLf A-1+1 by omega)
        (show 0<DLk A+1 by omega)]
  constructor <;> ring

theorem packet_determinant_abstract (RD : A.RegionD E hF)
    (hJ : K.J0<0) (hc : s.semigroup.Canonical F g.m) :
    0<K.DLtheta A*A.chi-K.DLEpar A*K.DLHp A := by
  have hs := (RD.linear_remainder_parameters hJ hc).2.2.2.2.2.1
  simp only [DLHp]
  omega

theorem rho_linear_identities (RD : A.RegionD E hF)
    (hJ : K.J0<0) (hc : s.semigroup.Canonical F g.m) :
    (D.rho 1 : ℤ)=K.DLL A*K.DLEpar A+K.DLM A*K.DLtheta A-(D.a 1 : ℤ) ∧
    (D.rho 2 : ℤ)=K.DLL A*A.chi+K.DLM A*K.DLHp A-(D.b 2 : ℤ) := by
  rcases RD.linear_parameters hJ hc with
    ⟨hk, hu, ha, hS, hrj, hrk, hai, hbi, hd, hI, hJform, hB⟩
  have rem := RD.linear_remainder_parameters hJ hc
  have hC := rem.2.2.2.1
  have hQ : K.DLQ=K.DLf A*K.DLEpar A+K.DLtheta A := by
    simp only [DLtheta]
    ring
  have hE : K.DLEpar A=(D.a 1 : ℤ)+K.DLG A := by
    simp only [DLEpar, DLG, DLupsilon]
    rw [K.chain.R_exact]
    ring
  have hT := K.chain.T_exact
  constructor
  · rw [hrj, hQ, hE]
    simp only [DLL, DLM, DLp, DLq, DLs, DLt]
    ring
  · simp only [DLL, DLM, DLHp, DLp, DLq, DLs, DLt]
    rw [hrk, hC, hT]
    ring

end FirstFit.RegionD
end P21.Nonsymmetric.ChainCore
