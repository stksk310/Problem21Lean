import P21.Nonsymmetric.Chain.C9.MatrixEmbedding

namespace P21.Nonsymmetric

/-- The exact Section 10 input.  It deliberately contains no first-fit,
Region-D, root, or pseudo-Frobenius-row state. -/
structure EuclideanSeed {g : Generators} (s : g.Setting) (F : ℤ)
    (D : HerzogCriticalData g) where
  frobenius : s.semigroup.IsFrobenius F
  canonical : s.semigroup.Canonical F g.m
  delta : ℤ
  beta : ℤ
  gap : ℤ
  alpha : ℤ
  P : ℤ
  R : ℤ
  T : ℤ
  delta_pos : 1≤delta
  beta_pos : 1≤beta
  gap_pos : 1≤gap
  alpha_pos : 1≤alpha
  P_pos : 1≤P
  R_pos : 1≤R
  T_pos : 1≤T
  ai_source : (D.a 0 : ℤ)=P-beta
  bi_source : (D.b 0 : ℤ)=P-delta
  R_source : R=(D.a 1 : ℤ)+gap
  T_source : T=(D.b 2 : ℤ)+alpha
  W_face : W F g.m=(P-1)*g.n 0+(R-1)*g.n 1+(T-1)*g.n 2
  p : ℤ
  q : ℤ
  v : ℤ
  t : ℤ
  p_pos : 1≤p
  q_pos : 1≤q
  v_pos : 1≤v
  t_pos : 1≤t
  det_one : p*t-q*v=1
  L : ℤ
  M : ℤ
  L_eq : L=p+q
  M_eq : M=v+t
  L_gt_M : M<L
  r : ℤ
  r_nonneg : 0≤r
  Acoef : ℤ
  Bcoef : ℤ
  A_source : Acoef=p*(r+delta)+q*(r+beta)
  B_source : Bcoef=v*(r+delta)+t*(r+beta)
  u : ℤ
  Epar : ℤ
  u_pos : 1≤u
  E_source : Epar=R+u
  w : ℤ
  Hp : ℤ
  w_nonneg : 0≤w
  Hp_source : Hp=T+w
  theta : ℤ
  chi : ℤ
  theta_pos : 1≤theta
  theta_le : theta≤u
  chi_pos : 1≤chi
  packet_det_pos : 0<theta*chi-Epar*Hp
  DP : Bcoef*g.n 0+Epar*g.n 1=M*g.m+chi*g.n 2
  PP : Acoef*g.n 0+Hp*g.n 2=L*g.m+theta*g.n 1
  rhoj : (D.rho 1 : ℤ)=L*Epar+M*theta-(D.a 1 : ℤ)
  rhok : (D.rho 2 : ℤ)=L*chi+M*Hp-(D.b 2 : ℤ)

namespace ChainCore.FirstFit.RegionD

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns}
variable {hF : s.semigroup.IsFrobenius F}

noncomputable def toEuclideanSeed (RD : A.RegionD E hF) (hJ : K.J0<0)
    (hc : s.semigroup.Canonical F g.m) : EuclideanSeed s F D := by
  have mat := RD.matrix_parameters hJ hc
  rcases mat with ⟨hp_pos, hq_pos, hv_pos, ht_pos, hdet, hL, hM, hML, hA, hB⟩
  have lin := RD.linear_parameters hJ hc
  have rem := RD.linear_remainder_parameters hJ hc
  have theta := RD.theta_range hJ hc
  have comp := RD.complementary_coefficients hJ hc
  have rhos := RD.rho_linear_identities hJ hc
  have hs := K.chain.scalar_ranges
  have hP := K.chain.P_exact'
  have hR := K.chain.R_exact
  have hT := K.chain.T_exact
  have hlambda := K.d_range
  have haj : (1:ℤ)≤D.a 1 := by exact_mod_cast D.a_pos 1
  have hbk : (1:ℤ)≤D.b 2 := by exact_mod_cast D.b_pos 2
  refine {
    frobenius := hF
    canonical := hc
    delta := K.chain.delta
    beta := K.chain.beta
    gap := K.chain.gapJ
    alpha := K.chain.alpha
    P := K.chain.P
    R := K.chain.R
    T := K.chain.T
    delta_pos := hs.1
    beta_pos := hs.2.1
    gap_pos := hs.2.2.1
    alpha_pos := hs.2.2.2
    P_pos := by omega
    R_pos := by rw [hR]; omega
    T_pos := by rw [hT]; omega
    ai_source := by rw [K.chain.P_eq_a_beta]; ring
    bi_source := by rw [K.chain.P_eq_b_delta]; ring
    R_source := hR
    T_source := hT
    W_face := K.chain.W_exact
    p := K.DLp A
    q := K.DLq A
    v := K.DLs A
    t := K.DLt A
    p_pos := hp_pos
    q_pos := hq_pos
    v_pos := hv_pos
    t_pos := ht_pos
    det_one := hdet
    L := K.DLL A
    M := K.DLM A
    L_eq := rfl
    M_eq := rfl
    L_gt_M := hML
    r := K.r
    r_nonneg := K.euclidean.r_range.1
    Acoef := K.DLA A
    Bcoef := K.DLB A
    A_source := rfl
    B_source := rfl
    u := K.DLupsilon A
    Epar := K.DLEpar A
    u_pos := le_trans theta.1 theta.2
    E_source := rfl
    w := K.DLw A
    Hp := K.DLHp A
    w_nonneg := rem.2.1
    Hp_source := rfl
    theta := K.DLtheta A
    chi := A.chi
    theta_pos := theta.1
    theta_le := theta.2
    chi_pos := RD.chi_pos
    packet_det_pos := RD.packet_determinant_abstract hJ hc
    DP := by
      have hp := RD.d_linear_packet hJ hc
      rw [hB, hM]
      exact hp
    PP := by simpa [add_comm, add_left_comm, add_assoc] using
      (RD.complementary_packet hJ hc).symm
    rhoj := rhos.1
    rhok := rhos.2 }

end ChainCore.FirstFit.RegionD
end P21.Nonsymmetric
