import P21.Nonsymmetric.MixedColor
import P21.Nonsymmetric.Saturation
import P21.Nonsymmetric.MatchedPair
import P21.Nonsymmetric.Relabel

namespace P21.Nonsymmetric

/-- Exact PATH input on the same semigroup and the same four actual rows.
The ladder names A/B are positions, not Herzog colors. -/
structure PathInput {g : Generators} (s : g.Setting) (F : ℤ) (D : HerzogCriticalData g) where
  lambda : ℤ
  nu : ℤ
  R : ℤ
  qL : ℤ
  qA : ℤ
  qB : ℤ
  qR : ℤ
  actual : ∀ t : Fin 4, ![qL,qA,qB,qR] t ∈ s.semigroup.Q F
  distinct : Function.Injective (![qL,qA,qB,qR] : Fin 4 → ℤ)
  left_singleton : IsSingleton g qL 0
  right_singleton : IsSingleton g qR 2
  A_eq : qA = D.fA-nu*g.n 2
  B_eq : qB = D.fB-lambda*g.n 0
  A_missing : (2:Fin 3) ∉ g.SH qA
  B_missing : (0:Fin 3) ∉ g.SH qB
  lambda_range : 1 ≤ lambda ∧ lambda < D.b 0
  nu_range : 1 ≤ nu ∧ nu < D.a 2
  R_range : 1 ≤ R ∧ R < D.rho 1
  cL : complement F g.m qL = (D.rho 0-lambda)*g.n 0
  cA : complement F g.m qA = (D.b 0-lambda)*g.n 0+R*g.n 1
  cB : complement F g.m qB = R*g.n 1+(D.a 2-nu)*g.n 2
  cR : complement F g.m qR = (D.rho 2-nu)*g.n 2
  boxW : W F g.m = (D.rho 0-lambda-1)*g.n 0+(R-1)*g.n 1+(D.rho 2-nu-1)*g.n 2
  ladder_left : qL+(D.a 0:ℤ)*g.n 0 = qA+R*g.n 1
  ladder_middle : qA+(D.b 0-lambda)*g.n 0 = qB+(D.a 2-nu)*g.n 2
  ladder_right : qR+(D.b 2:ℤ)*g.n 2 = qB+R*g.n 1

/-- Exact TYPE II scalar input, with the singleton saturation included. -/
structure TypeIIInput {g : Generators} (s : g.Setting) (F : ℤ) (D : HerzogCriticalData g) where
  lambda : ℤ
  mu : ℤ
  nu : ℤ
  qS : ℤ
  actual : ∀ t : Fin 4,
    ![qS,D.fA-lambda*g.n 0,D.fB-mu*g.n 1,D.fA-nu*g.n 2] t ∈ s.semigroup.Q F
  distinct : Function.Injective
    (![qS,D.fA-lambda*g.n 0,D.fB-mu*g.n 1,D.fA-nu*g.n 2] : Fin 4 → ℤ)
  singleton : IsSingleton g qS 0
  Ai_missing : (0:Fin 3) ∉ g.SH (D.fA-lambda*g.n 0)
  Bj_missing : (1:Fin 3) ∉ g.SH (D.fB-mu*g.n 1)
  Ak_missing : (2:Fin 3) ∉ g.SH (D.fA-nu*g.n 2)
  lambda_range : 1 ≤ lambda ∧ lambda < D.a 0 ∧ lambda ≤ D.b 0
  mu_range : 1 ≤ mu ∧ mu < D.b 1
  nu_range : 1 ≤ nu ∧ nu < D.a 2
  cS : complement F g.m qS = (D.rho 0-lambda)*g.n 0
  cAi : complement F g.m (D.fA-lambda*g.n 0) =
    (D.b 1-mu)*g.n 1+(D.rho 2-nu)*g.n 2
  cBj : complement F g.m (D.fB-mu*g.n 1) =
    (D.a 0-lambda)*g.n 0+(D.rho 2-nu)*g.n 2
  cAk : complement F g.m (D.fA-nu*g.n 2) =
    (D.b 0-lambda)*g.n 0+(D.rho 1-mu)*g.n 1
  boxW : W F g.m = (D.rho 0-lambda-1)*g.n 0+
    (D.rho 1-mu-1)*g.n 1+(D.rho 2-nu-1)*g.n 2
  singleton_row : qS = -g.n 0+(D.rho 1-mu-1)*g.n 1+(D.rho 2-nu-1)*g.n 2

/-- Exact positive CHAIN box, without assuming any later branch exclusion. -/
structure ChainInput {g : Generators} (s : g.Setting) (F : ℤ) (D : HerzogCriticalData g) where
  lambda : ℤ
  mu : ℤ
  nu : ℤ
  actual : ∀ t : Fin 4,
    ![D.fB-mu*g.n 1,D.fA-lambda*g.n 0,D.fB-lambda*g.n 0,D.fA-nu*g.n 2] t ∈ s.semigroup.Q F
  distinct : Function.Injective
    (![D.fB-mu*g.n 1,D.fA-lambda*g.n 0,D.fB-lambda*g.n 0,D.fA-nu*g.n 2] : Fin 4 → ℤ)
  Bj_missing : (1:Fin 3) ∉ g.SH (D.fB-mu*g.n 1)
  Ai_missing : (0:Fin 3) ∉ g.SH (D.fA-lambda*g.n 0)
  Bi_missing : (0:Fin 3) ∉ g.SH (D.fB-lambda*g.n 0)
  Ak_missing : (2:Fin 3) ∉ g.SH (D.fA-nu*g.n 2)
  lambda_range : 1 ≤ lambda ∧ lambda < D.a 0 ∧ lambda < D.b 0
  mu_range : 1 ≤ mu ∧ mu < D.b 1
  nu_range : 1 ≤ nu ∧ nu < D.a 2
  cBj : complement F g.m (D.fB-mu*g.n 1) =
    (D.a 0-lambda)*g.n 0+(D.rho 2-nu)*g.n 2
  cAi : complement F g.m (D.fA-lambda*g.n 0) =
    (D.b 1-mu)*g.n 1+(D.rho 2-nu)*g.n 2
  cBi : complement F g.m (D.fB-lambda*g.n 0) =
    (D.rho 1-mu)*g.n 1+(D.a 2-nu)*g.n 2
  cAk : complement F g.m (D.fA-nu*g.n 2) =
    (D.b 0-lambda)*g.n 0+(D.rho 1-mu)*g.n 1
  boxW : W F g.m = (D.rho 0-lambda-1)*g.n 0+
    (D.rho 1-mu-1)*g.n 1+(D.rho 2-nu-1)*g.n 2

variable {g : Generators}

/-- Pure gap translation gives the required missing direction directly. -/
theorem herzog_arm_missing {f : ℤ} (hf : f ∉ g.H) (i : Fin 3)
    (l : ℤ) (hl : 1 ≤ l) : i ∉ g.SH (f-l*g.n i) := by
  intro hh
  have hm := g.H.nsmul_mem (generator_mem g.n i) (l-1).toNat
  have hc : ((l-1).toNat:ℤ) = l-1 := Int.toNat_of_nonneg (by omega)
  have ht := g.H.add_mem hh hm
  simp only [nsmul_eq_mul,hc] at ht
  apply hf
  convert ht using 1; ring

/-- Actual PATH arms determine the common coefficient, which is strictly
positive because an endpoint singleton forbids pure-ray comparability. -/
theorem path_pair_data (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (l n : ℤ)
    (hl : 1 ≤ l) (hlb : l < D.b 0) (hn : 1 ≤ n) (hna : n < D.a 2)
    (hqB : D.fB-l*g.n 0 ∈ s.semigroup.Q F)
    (hqA : D.fA-n*g.n 2 ∈ s.semigroup.Q F)
    {qL : ℤ} (hqL : qL ∈ s.semigroup.Q F) (hsL : IsSingleton g qL 0)
    (hne : D.fA-n*g.n 2 ≠ qL) :
    ∃ R : ℤ, 1 ≤ R ∧ R < D.rho 1 ∧
      complement F g.m (D.fB-l*g.n 0) = R*g.n 1+(D.a 2-n)*g.n 2 ∧
      complement F g.m (D.fA-n*g.n 2) = (D.b 0-l)*g.n 0+R*g.n 1 ∧
      W F g.m = (D.rho 0-l-1)*g.n 0+(R-1)*g.n 1+(D.rho 2-n-1)*g.n 2 := by
  have hp : ∀ i, 0 < g.n i := fun i => lt_trans s.m_pos (s.n_gt i)
  obtain ⟨y,z,hy,hz,hci⟩ := arm_complement_pair s hF hc D hqB
    (herzog_arm_missing (D.fB_gap hp) 0 l hl)
  obtain ⟨x,y',hx,hy',hck⟩ := arm_complement_pair s hF hc D hqA
    (herzog_arm_missing (D.fA_gap hp) 2 n hn)
  change y < D.rho 1 at hy
  change z < D.rho 2 at hz
  change x < D.rho 0 at hx
  change y' < D.rho 1 at hy'
  change complement F g.m (D.fB-l*g.n 0) = (y:ℤ)*g.n 1+(z:ℤ)*g.n 2 at hci
  change complement F g.m (D.fA-n*g.n 2) = (x:ℤ)*g.n 0+(y':ℤ)*g.n 1 at hck
  obtain ⟨ez,ex,ey⟩ := mixed_right_complement_geometry D hp F l n hl hlb hn hna x y z y' hx hy hz hy' hci hck
  have hyp : 0 < y := by
    by_contra hh
    have hy0 : y = 0 := by omega
    obtain ⟨k,_,hsk⟩ := singleton_pure_complement s hF hc hqL hsL
    exact distinct_complements_not_one_ray hqA hqL hne 0 x k
      (by simpa [ey,hy0] using hck) hsk
  refine ⟨y,by omega,by exact_mod_cast hy,?_,?_,?_⟩
  · simpa [ez] using hci
  · simpa [ex,ey] using hck
  · have er2 : (D.rho 2:ℤ) = D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
    rw [ez] at hci
    simp only [complement,HerzogCriticalData.fB] at hci
    linear_combination hci-g.n 2*er2

end P21.Nonsymmetric

namespace P21.Nonsymmetric
variable {g : Generators}

/-- TYPE II extraction starts from four actual rows and arm ranges, and
constructs all scalar/complement data, including singleton saturation. -/
theorem typeII_exact_input (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (l m n qS : ℤ)
    (hl : 1 ≤ l) (hla : l < D.a 0) (hm : 1 ≤ m) (hmb : m < D.b 1)
    (hn : 1 ≤ n) (hna : n < D.a 2)
    (hactual : ∀ t : Fin 4, ![qS,D.fA-l*g.n 0,D.fB-m*g.n 1,D.fA-n*g.n 2] t ∈ s.semigroup.Q F)
    (hdistinct : Function.Injective (![qS,D.fA-l*g.n 0,D.fB-m*g.n 1,D.fA-n*g.n 2] : Fin 4 → ℤ))
    (hs : IsSingleton g qS 0) : Nonempty (TypeIIInput s F D) := by
  have hp : ∀ i, 0 < g.n i := fun i => lt_trans s.m_pos (s.n_gt i)
  have hqS : qS ∈ s.semigroup.Q F := hactual 0
  have hqi : D.fA-l*g.n 0 ∈ s.semigroup.Q F := hactual 1
  have hqj : D.fB-m*g.n 1 ∈ s.semigroup.Q F := hactual 2
  have hqk : D.fA-n*g.n 2 ∈ s.semigroup.Q F := hactual 3
  obtain ⟨y,z,hy,hz,hci⟩ := arm_complement_pair s hF hc D hqi
    (herzog_arm_missing (D.fA_gap hp) 0 l hl)
  obtain ⟨z',x',hz',hx',hcj⟩ := arm_complement_pair s hF hc D hqj
    (herzog_arm_missing (D.fB_gap hp) 1 m hm)
  obtain ⟨x,y',hx,hy',hck⟩ := arm_complement_pair s hF hc D hqk
    (herzog_arm_missing (D.fA_gap hp) 2 n hn)
  change y < D.rho 1 at hy
  change z < D.rho 2 at hz
  change z' < D.rho 2 at hz'
  change x' < D.rho 0 at hx'
  change x < D.rho 0 at hx
  change y' < D.rho 1 at hy'
  change complement F g.m (D.fA-l*g.n 0) = (y:ℤ)*g.n 1+(z:ℤ)*g.n 2 at hci
  change complement F g.m (D.fB-m*g.n 1) = (z':ℤ)*g.n 2+(x':ℤ)*g.n 0 at hcj
  change complement F g.m (D.fA-n*g.n 2) = (x:ℤ)*g.n 0+(y':ℤ)*g.n 1 at hck
  have ⟨ex',ey,ez'⟩ := mixed_right_next_complement_geometry D hp F l m hl hla hm hmb
    x' y z z' hx' hy hz hz' hci (by linarith [hcj])
  have hcase := same_color_complement_cases D hp F l n hl hla hn hna
    x y z y' hx hy hz hy' hci hck
  have he : (z:ℤ) = D.rho 2-n ∧ (x:ℤ) = D.b 0-l ∧ (y':ℤ) = y+D.a 1 := by
    rcases hcase with hcase | ⟨_,_,hybad⟩
    · exact hcase
    · omega
  obtain ⟨ez,ex,ey'⟩ := he
  have er0 : (D.rho 0:ℤ) = D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
  have er1 : (D.rho 1:ℤ) = D.a 1+D.b 1 := by exact_mod_cast D.rho_eq 1
  have er2 : (D.rho 2:ℤ) = D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
  have hw : W F g.m = (D.rho 0-l-1)*g.n 0+(D.rho 1-m-1)*g.n 1+(D.rho 2-n-1)*g.n 2 := by
    have hh := hci
    rw [ez,ey] at hh
    simp only [complement,HerzogCriticalData.fA] at hh
    linear_combination hh-g.n 1*er1
  obtain ⟨k,hkp,hsk⟩ := singleton_pure_complement s hF hc hqS hs
  have ek := singleton_saturation s hF hc D hqS hs hkp hsk
    (by have := D.b_pos 0; omega) (by have := D.a_pos 1; omega)
    (by have := D.b_pos 2; omega) (by omega) (by omega) (by omega) hw
  refine ⟨{
    lambda := l
    mu := m
    nu := n
    qS := qS
    actual := hactual
    distinct := hdistinct
    singleton := hs
    Ai_missing := herzog_arm_missing (D.fA_gap hp) 0 l hl
    Bj_missing := herzog_arm_missing (D.fB_gap hp) 1 m hm
    Ak_missing := herzog_arm_missing (D.fA_gap hp) 2 n hn
    lambda_range := ⟨hl,hla,by omega⟩
    mu_range := ⟨hm,hmb⟩
    nu_range := ⟨hn,hna⟩
    cS := by simpa [ek] using hsk
    cAi := by simpa [ey,ez] using hci
    cBj := ?_
    cAk := ?_
    boxW := hw
    singleton_row := ?_ }⟩
  · rw [ez',ex',ez] at hcj
    linarith [hcj]
  · rw [ex,ey',ey] at hck
    linear_combination hck-g.n 1*er1
  · rw [ek] at hsk
    simp only [complement] at hsk
    linear_combination hw-hsk

end P21.Nonsymmetric


namespace P21.Nonsymmetric
variable {g : Generators}

/-- CHAIN extraction proves strict positivity of all four slack parameters
from the arm ranges, after comparing the same actual matched complements. -/
theorem chain_exact_input (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (l m n : ℤ)
    (hl : 1 ≤ l) (hla : l < D.a 0) (hlb : l < D.b 0)
    (hm : 1 ≤ m) (hmb : m < D.b 1) (hn : 1 ≤ n) (hna : n < D.a 2)
    (hactual : ∀ t : Fin 4,
      ![D.fB-m*g.n 1,D.fA-l*g.n 0,D.fB-l*g.n 0,D.fA-n*g.n 2] t ∈ s.semigroup.Q F)
    (hdistinct : Function.Injective
      (![D.fB-m*g.n 1,D.fA-l*g.n 0,D.fB-l*g.n 0,D.fA-n*g.n 2] : Fin 4 → ℤ)) :
    Nonempty (ChainInput s F D) := by
  have hp : ∀ i, 0 < g.n i := fun i => lt_trans s.m_pos (s.n_gt i)
  have hqj : D.fB-m*g.n 1 ∈ s.semigroup.Q F := hactual 0
  have hqi : D.fA-l*g.n 0 ∈ s.semigroup.Q F := hactual 1
  have hqbi : D.fB-l*g.n 0 ∈ s.semigroup.Q F := hactual 2
  have hqk : D.fA-n*g.n 2 ∈ s.semigroup.Q F := hactual 3
  obtain ⟨y,z,hy,hz,hci⟩ := arm_complement_pair s hF hc D hqi
    (herzog_arm_missing (D.fA_gap hp) 0 l hl)
  obtain ⟨Y,Z,hY,hZ,hcbi⟩ := arm_complement_pair s hF hc D hqbi
    (herzog_arm_missing (D.fB_gap hp) 0 l hl)
  obtain ⟨z',x',hz',hx',hcj⟩ := arm_complement_pair s hF hc D hqj
    (herzog_arm_missing (D.fB_gap hp) 1 m hm)
  obtain ⟨x,y',hx,hy',hck⟩ := arm_complement_pair s hF hc D hqk
    (herzog_arm_missing (D.fA_gap hp) 2 n hn)
  change y < D.rho 1 at hy
  change z < D.rho 2 at hz
  change Y < D.rho 1 at hY
  change Z < D.rho 2 at hZ
  change z' < D.rho 2 at hz'
  change x' < D.rho 0 at hx'
  change x < D.rho 0 at hx
  change y' < D.rho 1 at hy'
  change complement F g.m (D.fA-l*g.n 0) = (y:ℤ)*g.n 1+(z:ℤ)*g.n 2 at hci
  change complement F g.m (D.fB-l*g.n 0) = (Y:ℤ)*g.n 1+(Z:ℤ)*g.n 2 at hcbi
  change complement F g.m (D.fB-m*g.n 1) = (z':ℤ)*g.n 2+(x':ℤ)*g.n 0 at hcj
  change complement F g.m (D.fA-n*g.n 2) = (x:ℤ)*g.n 0+(y':ℤ)*g.n 1 at hck
  have ⟨ex',ey,ez'⟩ := mixed_right_next_complement_geometry D hp F l m hl hla hm hmb
    x' y z z' hx' hy hz hz' hci (by linarith [hcj])
  have ⟨eZ,ex,ey'⟩ := mixed_right_complement_geometry D hp F l n hl hlb hn hna
    x Y Z y' hx hY hZ hy' hcbi hck
  have hln : (l.toNat:ℤ) = l := Int.toNat_of_nonneg (by omega)
  have ⟨_,eY,ez⟩ := matched_pair_sync hp D (lam:=l.toNat) (mu:=l.toNat)
    (by omega) (by omega) (by omega) (by omega)
    (by rw [hln]) (by rw [hln]) hci hcbi hy hz hY hZ
  have er1 : (D.rho 1:ℤ) = D.a 1+D.b 1 := by exact_mod_cast D.rho_eq 1
  have er2 : (D.rho 2:ℤ) = D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
  have eY' : (Y:ℤ) = D.rho 1-m := by
    have hcast : (Y:ℤ) = y+D.a 1 := by exact_mod_cast eY
    omega
  have ez'' : (z:ℤ) = D.rho 2-n := by
    have hcast : (z:ℤ) = Z+D.b 2 := by exact_mod_cast ez
    omega
  refine ⟨{
    lambda := l
    mu := m
    nu := n
    actual := hactual
    distinct := hdistinct
    Bj_missing := herzog_arm_missing (D.fB_gap hp) 1 m hm
    Ai_missing := herzog_arm_missing (D.fA_gap hp) 0 l hl
    Bi_missing := herzog_arm_missing (D.fB_gap hp) 0 l hl
    Ak_missing := herzog_arm_missing (D.fA_gap hp) 2 n hn
    lambda_range := ⟨hl,hla,hlb⟩
    mu_range := ⟨hm,hmb⟩
    nu_range := ⟨hn,hna⟩
    cBj := ?_
    cAi := by simpa [ey,ez''] using hci
    cBi := by simpa [eY',eZ] using hcbi
    cAk := by simpa [ex,ey',eY'] using hck
    boxW := ?_ }⟩
  · rw [ez',ex',ez''] at hcj
    linarith [hcj]
  · rw [ey,ez''] at hci
    simp only [complement,HerzogCriticalData.fA] at hci
    linear_combination hci-g.n 1*er1

end P21.Nonsymmetric


namespace P21.Nonsymmetric
variable {g : Generators}

/-- Cyclic BOX-W saturation in the last coordinate, preserving the same W. -/
theorem singleton_saturation_last (s : g.Setting) {F q P R T : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (hq : q ∈ s.semigroup.Q F)
    (hs : IsSingleton g q 2) {k : ℕ} (hk : 0 < k)
    (he : complement F g.m q = (k:ℤ)*g.n 2)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hT : 1 ≤ T)
    (hPr : P ≤ D.rho 0) (hRr : R ≤ D.rho 1) (hTr : T ≤ D.rho 2)
    (hW : W F g.m = (P-1)*g.n 0+(R-1)*g.n 1+(T-1)*g.n 2) : (k:ℤ) = T := by
  apply singleton_saturation (relabelSetting s (rotatePerm 2))
    (F:=F) (q:=q) (k:=k) (P:=T) (R:=P) (T:=R) (by rw [relabel_semigroup]; exact hF) (by rw [relabel_semigroup]; exact hc)
    (rotateHerzog D 2) (by rw [relabel_semigroup]; exact hq) ?_ hk ?_ hT hP hR ?_ ?_ ?_ ?_
  · apply (relabel_singleton_iff g (rotatePerm 2) q 0).mpr
    simpa using hs
  · simpa [relabel] using he
  · simpa [rotateHerzog] using hTr
  · simpa [rotateHerzog,next] using hPr
  · simpa [rotateHerzog,prev] using hRr
  · change W F g.m = (T-1)*g.n 2+(P-1)*g.n 0+(R-1)*g.n 1
    linarith [hW]

/-- PATH extraction constructs both saturated endpoint rays and the actual
publication ladder from the selected four rows. -/
theorem path_exact_input (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (l n qL qR : ℤ)
    (hl : 1 ≤ l) (hlb : l < D.b 0) (hn : 1 ≤ n) (hna : n < D.a 2)
    (hactual : ∀ t : Fin 4,
      ![qL,D.fA-n*g.n 2,D.fB-l*g.n 0,qR] t ∈ s.semigroup.Q F)
    (hdistinct : Function.Injective
      (![qL,D.fA-n*g.n 2,D.fB-l*g.n 0,qR] : Fin 4 → ℤ))
    (hsL : IsSingleton g qL 0) (hsR : IsSingleton g qR 2) : Nonempty (PathInput s F D) := by
  have hqL : qL ∈ s.semigroup.Q F := hactual 0
  have hqA : D.fA-n*g.n 2 ∈ s.semigroup.Q F := hactual 1
  have hqB : D.fB-l*g.n 0 ∈ s.semigroup.Q F := hactual 2
  have hqR : qR ∈ s.semigroup.Q F := hactual 3
  have hne : D.fA-n*g.n 2 ≠ qL := by
    intro he
    have hh := hdistinct (show (![qL,D.fA-n*g.n 2,D.fB-l*g.n 0,qR] : Fin 4 → ℤ) 1 =
      (![qL,D.fA-n*g.n 2,D.fB-l*g.n 0,qR] : Fin 4 → ℤ) 0 from he)
    exact (by decide : (1:Fin 4) ≠ 0) hh
  obtain ⟨R,hR,hRr,hcB,hcA,hw⟩ := path_pair_data s hF hc D l n hl hlb hn hna
    hqB hqA hqL hsL hne
  obtain ⟨kL,hkL,hcL⟩ := singleton_pure_complement s hF hc hqL hsL
  obtain ⟨kR,hkR,hcR⟩ := singleton_pure_complement s hF hc hqR hsR
  have er0 : (D.rho 0:ℤ) = D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
  have er2 : (D.rho 2:ℤ) = D.a 2+D.b 2 := by exact_mod_cast D.rho_eq 2
  have hP : 1 ≤ (D.rho 0:ℤ)-l := by have := D.a_pos 0; omega
  have hT : 1 ≤ (D.rho 2:ℤ)-n := by have := D.b_pos 2; omega
  have eL := singleton_saturation s hF hc D hqL hsL hkL hcL hP hR hT
    (by omega) hRr.le (by omega) hw
  have eR := singleton_saturation_last s hF hc D hqR hsR hkR hcR hP hR hT
    (by omega) hRr.le (by omega) hw
  rw [eL] at hcL
  rw [eR] at hcR
  refine ⟨{
    lambda := l
    nu := n
    R := R
    qL := qL
    qA := D.fA-n*g.n 2
    qB := D.fB-l*g.n 0
    qR := qR
    actual := hactual
    distinct := hdistinct
    left_singleton := hsL
    right_singleton := hsR
    A_eq := rfl
    B_eq := rfl
    A_missing := herzog_arm_missing (D.fA_gap (fun i => lt_trans s.m_pos (s.n_gt i))) 2 n hn
    B_missing := herzog_arm_missing (D.fB_gap (fun i => lt_trans s.m_pos (s.n_gt i))) 0 l hl
    lambda_range := ⟨hl,hlb⟩
    nu_range := ⟨hn,hna⟩
    R_range := ⟨hR,hRr⟩
    cL := hcL
    cA := hcA
    cB := hcB
    cR := hcR
    boxW := hw
    ladder_left := ?_
    ladder_middle := ?_
    ladder_right := ?_ }⟩
  · simp only [complement] at hcA hcL
    linear_combination hcA-hcL-g.n 0*er0
  · simp only [complement] at hcA hcB
    linear_combination hcB-hcA
  · simp only [complement] at hcB hcR
    linear_combination hcB-hcR-g.n 2*er2

namespace ChainInput
variable {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g} (C : ChainInput s F D)

def delta : ℤ := D.a 0-C.lambda
def beta : ℤ := D.b 0-C.lambda
def gapJ : ℤ := D.b 1-C.mu
def alpha : ℤ := D.a 2-C.nu

theorem all_slacks_positive : 1 ≤ C.delta ∧ 1 ≤ C.beta ∧ 1 ≤ C.gapJ ∧ 1 ≤ C.alpha := by
  have := C.lambda_range
  have := C.mu_range
  have := C.nu_range
  simp only [delta,beta,gapJ,alpha]
  omega

theorem P_exact : (D.rho 0:ℤ)-C.lambda = C.lambda+C.delta+C.beta := by
  have he : (D.rho 0:ℤ) = D.a 0+D.b 0 := by exact_mod_cast D.rho_eq 0
  simp only [delta,beta]
  omega
end ChainInput
end P21.Nonsymmetric




namespace P21.Nonsymmetric
variable {g : Generators}

/-- Actual matched arms synchronize their initially independent integer depths. -/
theorem actual_matched_depths_equal (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (l r : ℤ)
    (hl : 1 ≤ l) (hla : l < D.a 0) (hr : 1 ≤ r) (hrb : r < D.b 0)
    (hqA : D.fA-l*g.n 0 ∈ s.semigroup.Q F)
    (hqB : D.fB-r*g.n 0 ∈ s.semigroup.Q F) : l = r := by
  have hp : ∀ i, 0 < g.n i := fun i => lt_trans s.m_pos (s.n_gt i)
  obtain ⟨y,z,hy,hz,hcA⟩ := arm_complement_pair s hF hc D hqA
    (herzog_arm_missing (D.fA_gap hp) 0 l hl)
  obtain ⟨y',z',hy',hz',hcB⟩ := arm_complement_pair s hF hc D hqB
    (herzog_arm_missing (D.fB_gap hp) 0 r hr)
  change y < D.rho 1 at hy
  change z < D.rho 2 at hz
  change y' < D.rho 1 at hy'
  change z' < D.rho 2 at hz'
  change complement F g.m (D.fA-l*g.n 0) = (y:ℤ)*g.n 1+(z:ℤ)*g.n 2 at hcA
  change complement F g.m (D.fB-r*g.n 0) = (y':ℤ)*g.n 1+(z':ℤ)*g.n 2 at hcB
  have hln : (l.toNat:ℤ) = l := Int.toNat_of_nonneg (by omega)
  have hrn : (r.toNat:ℤ) = r := Int.toNat_of_nonneg (by omega)
  have hh := matched_pair_sync hp D (lam:=l.toNat) (mu:=r.toNat)
    (by omega) (by omega) (by omega) (by omega)
    (by rw [hln]) (by rw [hrn]) hcA hcB hy hz hy' hz'
  omega

/-- CHAIN extraction does not presume that the two selected matched-arm
depths have already been identified. -/
theorem chain_exact_input_independent (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (l r m n : ℤ)
    (hl : 1 ≤ l) (hla : l < D.a 0) (hr : 1 ≤ r) (hrb : r < D.b 0)
    (hm : 1 ≤ m) (hmb : m < D.b 1) (hn : 1 ≤ n) (hna : n < D.a 2)
    (hactual : ∀ t : Fin 4,
      ![D.fB-m*g.n 1,D.fA-l*g.n 0,D.fB-r*g.n 0,D.fA-n*g.n 2] t ∈ s.semigroup.Q F)
    (hdistinct : Function.Injective
      (![D.fB-m*g.n 1,D.fA-l*g.n 0,D.fB-r*g.n 0,D.fA-n*g.n 2] : Fin 4 → ℤ)) :
    Nonempty (ChainInput s F D) := by
  have he := actual_matched_depths_equal s hF hc D l r hl hla hr hrb (hactual 1) (hactual 2)
  subst r
  exact chain_exact_input s hF hc D l m n hl hla hrb hm hmb hn hna hactual hdistinct

end P21.Nonsymmetric
