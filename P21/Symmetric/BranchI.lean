import P21.Symmetric.TwoGenerator

namespace P21.Symmetric

/-- The integral parameters of Appendix A, S3.6--S3.7. -/
structure BranchIData where
  base : TwoGeneratorData
  d : ℤ
  s : ℤ
  κ : ℤ
  a : ℤ
  b : ℤ
  α : ℤ
  β : ℤ
  p₀ : ℤ
  q₀ : ℤ
  d_ge_two : 2 ≤ d
  s_pos : 0 < s
  s_lt : s < d
  κ_pos : 0 < κ
  κ_le : κ ≤ d - 1 - s
  a_pos : 0 < a
  b_pos : 0 < b
  α_pos : 0 < α
  β_pos : 0 < β
  aα_lt : a + α < base.v
  bβ_lt : b + β < base.u
  p₀_nonneg : 0 ≤ p₀
  q₀_nonneg : 0 ≤ q₀

namespace BranchIData
variable (B : BranchIData)
def w : ℤ := B.α * B.base.u + B.β * B.base.v
def L : ℤ := (B.p₀ + 1) * B.base.u + (B.q₀ + 1) * B.base.v
def ρ : ℤ := B.base.u * B.base.v - B.w - B.a * B.base.u - B.b * B.base.v
/-- Negative floor is exactly the source's ceiling. -/
def c (n : ℤ) : ℤ := -((B.s - n * B.κ) / B.d)
def j (n : ℤ) : ℤ := B.s - n * B.κ + B.d * B.c n
def τ (n : ℤ) : ℤ := B.ρ + n * B.L - B.c n * B.w
def Ux (t : ℤ) : Prop := ∃ p : ℤ, 0 ≤ p ∧ p < B.base.v - B.a - B.α ∧ t = p * B.base.u
def Uy (t : ℤ) : Prop := ∃ q : ℤ, 0 ≤ q ∧ q < B.base.u - B.b - B.β ∧ t = q * B.base.v
def Zx (t : ℤ) : Prop := ∃ p q : ℤ, 0 ≤ p ∧ p < B.base.v - B.a ∧ 0 ≤ q ∧ q < B.β ∧ t = p * B.base.u + q * B.base.v
def Zy (t : ℤ) : Prop := ∃ p q : ℤ, 0 ≤ p ∧ p < B.α ∧ 0 ≤ q ∧ q < B.base.u - B.b ∧ t = p * B.base.u + q * B.base.v

def Stable : Prop := ∀ n : ℤ, 1 ≤ n → B.τ n ∈ B.base.T
/-- The four source hits, with the two rectangular hits restricted to returns. -/
structure FourHits : Prop where
  ux : ∃ n : ℤ, 1 ≤ n ∧ B.Ux (B.τ n)
  uy : ∃ n : ℤ, 1 ≤ n ∧ B.Uy (B.τ n)
  zx : ∃ n : ℤ, 1 ≤ n ∧ B.j n = 0 ∧ B.Zx (B.τ n)
  zy : ∃ n : ℤ, 1 ≤ n ∧ B.j n = 0 ∧ B.Zy (B.τ n)

theorem j_eq_emod (n : ℤ) : B.j n = (B.s - n * B.κ) % B.d := by
  have h := Int.ediv_mul_add_emod (B.s - n * B.κ) B.d
  dsimp [j,c]
  nlinarith

theorem j_bounds (n : ℤ) : 0 ≤ B.j n ∧ B.j n < B.d := by
  rw [B.j_eq_emod]
  exact ⟨Int.emod_nonneg _ (by have := B.d_ge_two; omega), Int.emod_lt_of_pos _ (by have := B.d_ge_two; omega)⟩

theorem step (n : ℤ) : B.c n = B.c (n-1) ∨ B.c n = B.c (n-1)+1 := by
  have h := B.j_bounds n
  have h' := B.j_bounds (n-1)
  have hd := B.d_ge_two
  have hk := B.κ_pos
  have hkd : B.κ < B.d := by have := B.κ_le; have := B.s_pos; omega
  have he : B.j n - B.j (n-1) = -B.κ + B.d * (B.c n - B.c (n-1)) := by unfold j; ring
  have hlo : 0 ≤ B.c n - B.c (n-1) := by
    by_contra hh
    have hh' : B.c n - B.c (n-1) ≤ -1 := by omega
    nlinarith
  have hhi : B.c n - B.c (n-1) ≤ 1 := by
    by_contra hh
    have hh' : 2 ≤ B.c n - B.c (n-1) := by omega
    nlinarith
  omega

theorem return_previous (n : ℤ) (hr : B.j n = 0) : B.c (n-1) = B.c n := by
  have h := B.j_bounds (n-1)
  have he : B.j (n-1) = B.κ + B.d * (B.c (n-1) - B.c n) := by unfold j at *; nlinarith [hr]
  rcases B.step n with hstep | hstep
  · omega
  · have := B.κ_le; have := B.s_pos; nlinarith

theorem return_next (n : ℤ) (hr : B.j n = 0) : B.c (n+1) = B.c n + 1 := by
  have h := B.j_bounds (n+1)
  have he : B.j (n+1) = -B.κ + B.d * (B.c (n+1) - B.c n) := by unfold j at *; nlinarith [hr]
  have hs := B.step (n+1)
  simp only [add_sub_cancel_right] at hs
  rcases hs with hs | hs
  · have := B.κ_pos; nlinarith
  · exact hs

theorem c_zero : B.c 0 = 0 := by
  have hd : 0 < B.d := by have := B.d_ge_two; omega
  simp [c, Int.ediv_eq_zero_of_lt B.s_pos.le B.s_lt]

theorem c_one : B.c 1 = 0 ∨ B.c 1 = 1 := by
  simpa [B.c_zero] using B.step 1

theorem first_return (hr : B.j 1 = 0) : B.κ = B.s ∧ B.c 1 = 0 := by
  have hc := B.return_previous 1 hr
  simp only [sub_self, B.c_zero] at hc
  have : B.s - B.κ + B.d * B.c 1 = 0 := by simpa [j] using hr
  rw [← hc] at this
  constructor <;> omega

/-- LOWER is intentionally available only for N>1. -/
theorem later_return_lower (hs : B.Stable) {n p q : ℤ}
    (hn : 1 < n) (hr : B.j n = 0)
    (hp : p < B.base.v) (hq : q < B.base.u)
    (he : B.τ n = p * B.base.u + q * B.base.v) :
    B.p₀ + 1 ≤ p ∧ B.q₀ + 1 ≤ q := by
  have hprev := hs (n-1) (by omega)
  have hc := B.return_previous n hr
  have he' : B.τ (n-1) = (p-B.p₀-1)*B.base.u + (q-B.q₀-1)*B.base.v := by
    dsimp [τ,L] at *
    rw [hc]
    nlinarith [he]
  rw [he'] at hprev
  have h := B.base.subcritical_nonneg (by have := B.p₀_nonneg; omega : p-B.p₀-1 < B.base.v)
    (by have := B.q₀_nonneg; omega : q-B.q₀-1 < B.base.u) hprev
  omega






theorem not_both_late (hs : B.Stable)
    (hx : ∃ n : ℤ, 1 < n ∧ B.j n = 0 ∧ B.Zx (B.τ n))
    (hy : ∃ n : ℤ, 1 < n ∧ B.j n = 0 ∧ B.Zy (B.τ n)) : False := by
  obtain ⟨nx,hnx,hrx,p,q,hp,hpv,hq,hqβ,he⟩ := hx
  obtain ⟨ny,hny,hry,r,t,hr,hrα,ht,htu,he'⟩ := hy
  have hlx := B.later_return_lower hs hnx hrx (by have := B.a_pos; omega)
    (by have := B.bβ_lt; have := B.b_pos; omega) he
  have hly := B.later_return_lower hs hny hry (by have := B.aα_lt; have := B.a_pos; omega)
    (by have := B.b_pos; omega) he'
  have hc : 0 ≤ B.c 1 := by rcases B.c_one with h | h <;> omega
  have hP : 0 < B.a+B.α-B.p₀-1+B.c 1*B.α := by
    have := B.a_pos
    have := mul_nonneg hc B.α_pos.le
    omega
  have hQ : 0 < B.b+B.β-B.q₀-1+B.c 1*B.β := by
    have := B.b_pos
    have := mul_nonneg hc B.β_pos.le
    omega
  apply B.base.interior_gap hP hQ
  convert hs 1 (by omega) using 1
  dsimp [τ,ρ,L,w]
  ring

/-- Later Ux hits necessarily occur through a carry; the base index is excluded. -/
theorem ux_carry (hs : B.Stable) {n p : ℤ} (hn : 1 < n)
    (hp : p < B.base.v-B.a-B.α) (he : B.τ n = p*B.base.u) :
    B.c n = B.c (n-1)+1 := by
  rcases B.step n with hc | hc
  · have hprev := hs (n-1) (by omega)
    have he' : B.τ (n-1) = (p-B.p₀-1)*B.base.u + (-B.q₀-1)*B.base.v := by
      dsimp [τ,L] at *
      rw [hc] at he
      nlinarith [he]
    rw [he'] at hprev
    have h := B.base.subcritical_nonneg (by have := B.p₀_nonneg; have := B.a_pos; have := B.α_pos; omega : p-B.p₀-1 < B.base.v)
      (by have := B.q₀_nonneg; have := B.base.u_ge_two; omega : -B.q₀-1 < B.base.u) hprev
    have := B.q₀_nonneg
    omega
  · exact hc

/-- X-only exclusion. Only the later Zy return and the first return are needed. -/
theorem x_only (hs : B.Stable) (hr : B.j 1 = 0)
    (hy : ∃ n : ℤ, 1 < n ∧ B.j n = 0 ∧ B.Zy (B.τ n))
    (hx : ∃ n : ℤ, 1 ≤ n ∧ B.Ux (B.τ n)) : False := by
  obtain ⟨ny,hny,hry,p,q,hp,hpα,hq,hqu,he⟩ := hy
  have hl := B.later_return_lower hs hny hry (by have := B.a_pos; have := B.aα_lt; omega)
    (by have := B.b_pos; omega) he
  have hc := (B.first_return hr).2
  let R := B.α-B.p₀-1
  let S := B.q₀+1-B.β
  have hR : 0 < R := by dsimp [R]; omega
  have hRα : R ≤ B.α-1 := by dsimp [R]; have := B.p₀_nonneg; omega
  have hSu : S < B.base.u := by dsimp [S]; have := B.b_pos; have := B.β_pos; omega
  have ht1 : B.τ 1 = (B.base.v-B.a-R)*B.base.u + (S-B.b)*B.base.v := by
    dsimp [τ,ρ,L,w,R,S]
    rw [hc]
    ring
  have hnonneg := B.base.subcritical_nonneg
    (by have := B.a_pos; omega : B.base.v-B.a-R < B.base.v)
    (by have := B.b_pos; omega : S-B.b < B.base.u)
    (by rw [← ht1]; exact hs 1 (by omega))
  have hS : 0 < S := by have := B.b_pos; omega
  obtain ⟨nx,hnx,j,hj,hjD,hej⟩ := hx
  by_cases hn : nx = 1
  · subst nx
    have heq : (B.base.v-B.a-R)*B.base.u + (S-B.b)*B.base.v = j*B.base.u + 0*B.base.v := by
      rw [← ht1,hej]; ring
    have huniq := B.base.normal_form_unique hnonneg.2 (by have := B.b_pos; omega)
      (by omega : (0:ℤ) ≤ 0) B.base.u_pos heq
    omega
  · have hn' : 1 < nx := by omega
    have hcarry := B.ux_carry hs hn' hjD hej
    have hprev : B.τ (nx-1) = (j+R)*B.base.u + (-S)*B.base.v := by
      dsimp [τ,L,w,R,S] at *
      rw [hcarry] at hej
      nlinarith [hej]
    have hmem := hs (nx-1) (by omega)
    rw [hprev] at hmem
    have hnonneg := B.base.subcritical_nonneg
      (by have := B.a_pos; omega : j+R < B.base.v)
      (by have := B.base.u_pos; omega : -S < B.base.u) hmem
    omega

/-- Swapping u and v is used only to reuse the symmetric arithmetic proof. -/
def swap : BranchIData where
  base := ⟨B.base.v, B.base.u, B.base.v_ge_two, B.base.u_ge_two,
    by simpa [Int.gcd_comm] using B.base.coprime⟩
  d := B.d
  s := B.s
  κ := B.κ
  a := B.b
  b := B.a
  α := B.β
  β := B.α
  p₀ := B.q₀
  q₀ := B.p₀
  d_ge_two := B.d_ge_two
  s_pos := B.s_pos
  s_lt := B.s_lt
  κ_pos := B.κ_pos
  κ_le := B.κ_le
  a_pos := B.b_pos
  b_pos := B.a_pos
  α_pos := B.β_pos
  β_pos := B.α_pos
  aα_lt := B.bβ_lt
  bβ_lt := B.aα_lt
  p₀_nonneg := B.q₀_nonneg
  q₀_nonneg := B.p₀_nonneg

@[simp] theorem swap_c (n : ℤ) : B.swap.c n = B.c n := rfl
@[simp] theorem swap_j (n : ℤ) : B.swap.j n = B.j n := rfl
@[simp] theorem swap_τ (n : ℤ) : B.swap.τ n = B.τ n := by dsimp [τ,ρ,L,w,swap,c]; ring
@[simp] theorem swap_mem (t : ℤ) : t ∈ B.swap.base.T ↔ t ∈ B.base.T := by
  constructor
  · rintro ⟨a,b,ha,hb,he⟩
    exact ⟨b,a,hb,ha,by simpa [swap,add_comm] using he⟩
  · rintro ⟨a,b,ha,hb,he⟩
    exact ⟨b,a,hb,ha,by simpa [swap,add_comm] using he⟩
@[simp] theorem swap_Ux (t : ℤ) : B.swap.Ux t ↔ B.Uy t := Iff.rfl
@[simp] theorem swap_Zy (t : ℤ) : B.swap.Zy t ↔ B.Zx t := by
  constructor
  · rintro ⟨p,q,hp,hp',hq,hq',he⟩
    exact ⟨q,p,hq,hq',hp,hp',by simpa [swap,add_comm] using he⟩
  · rintro ⟨p,q,hp,hp',hq,hq',he⟩
    exact ⟨q,p,hq,hq',hp,hp',by simpa [swap,add_comm] using he⟩

theorem stable_swap (hs : B.Stable) : B.swap.Stable := by
  intro n hn
  simpa using hs n hn

theorem y_only (hs : B.Stable) (hr : B.j 1 = 0)
    (hx : ∃ n : ℤ, 1 < n ∧ B.j n = 0 ∧ B.Zx (B.τ n))
    (hy : ∃ n : ℤ, 1 ≤ n ∧ B.Uy (B.τ n)) : False := by
  apply B.swap.x_only (B.stable_swap hs) (by simpa using hr)
  · simpa using hx
  · simpa using hy



/-- In the XY case an Ux hit bounds the doubled u-coordinate. -/
theorem xy_upper_x (hs : B.Stable) (hr : B.j 1 = 0)
    {p q : ℤ} (_hp : 0 ≤ p) (hpα : p < B.α) (hq : 0 ≤ q) (hqβ : q < B.β)
    (he : B.τ 1 = p*B.base.u + q*B.base.v)
    (hx : ∃ n : ℤ, 1 ≤ n ∧ B.Ux (B.τ n)) : 2*p+B.a < B.base.v := by
  have hc := (B.first_return hr).2
  obtain ⟨n,hn,j,hj,hjD,hej⟩ := hx
  by_cases hn1 : n = 1
  · subst n
    have heq : p*B.base.u + q*B.base.v = j*B.base.u + 0*B.base.v := by
      rw [← he,hej]; ring
    have huniq := B.base.normal_form_unique hq (by have := B.b_pos; have := B.bβ_lt; omega)
      (by omega : (0:ℤ) ≤ 0) B.base.u_pos heq
    omega
  · have hn' : 1 < n := by omega
    have hcarry := B.ux_carry hs hn' hjD hej
    have hprev : B.τ (n-1) = B.base.u*B.base.v - (B.a+p-j)*B.base.u - (B.b+q)*B.base.v := by
      dsimp [τ,ρ] at he hej ⊢
      rw [hc] at he
      rw [hcarry] at hej
      nlinarith [he,hej]
    have hmem := hs (n-1) (by omega)
    rw [hprev] at hmem
    have hP : B.a+p ≤ j := by
      by_contra hh
      exact B.base.interior_gap (by omega : 0 < B.a+p-j)
        (by have := B.b_pos; omega : 0 < B.b+q) hmem
    have := B.a_pos
    omega

theorem xy (hs : B.Stable) (hr : B.j 1 = 0)
    (hzx : B.Zx (B.τ 1)) (hzy : B.Zy (B.τ 1))
    (hx : ∃ n : ℤ, 1 ≤ n ∧ B.Ux (B.τ n))
    (hy : ∃ n : ℤ, 1 ≤ n ∧ B.Uy (B.τ n)) : False := by
  obtain ⟨p,q,hp,hp',hq,hqβ,he⟩ := hzx
  obtain ⟨r,t,hr',hrα,ht,ht',he'⟩ := hzy
  have huniq := B.base.normal_form_unique hq
    (by have := B.bβ_lt; have := B.b_pos; omega)
    ht (by have := B.b_pos; omega) (he.symm.trans he')
  obtain ⟨rfl,rfl⟩ := huniq
  have hu := B.xy_upper_x hs hr hp hrα hq hqβ he hx
  have hhe : B.swap.τ 1 = q*B.swap.base.u + p*B.swap.base.v := by
    rw [B.swap_τ,he]
    dsimp [swap]
    ring
  have hv := B.swap.xy_upper_x (B.stable_swap hs) (by simpa using hr)
    hq hqβ hp hrα hhe (by simpa using hy)
  change 2*q+B.b < B.base.u at hv
  have hc1 := (B.first_return hr).2
  have hc2 : B.c 2 = 1 := by simpa [hc1] using B.return_next 1 hr
  have ht2 : B.τ 2 = (2*p+B.a)*B.base.u + (2*q+B.b)*B.base.v - B.base.u*B.base.v := by
    dsimp [τ,ρ] at he ⊢
    rw [hc1] at he
    rw [hc2]
    nlinarith [he]
  apply B.base.subcritical_gap (by have := B.a_pos; omega : 0 ≤ 2*p+B.a) hu
    (by have := B.b_pos; omega : 0 ≤ 2*q+B.b) hv
  rw [← ht2]
  exact hs 2 (by omega)

/-- Source S3.7: all four quantified hits on this one stable walk are incompatible. -/
theorem four_hits_impossible (hs : B.Stable) (hh : B.FourHits) : False := by
  obtain ⟨nx,hnx,hrx,hzx⟩ := hh.zx
  obtain ⟨ny,hny,hry,hzy⟩ := hh.zy
  by_cases hx1 : nx = 1
  · subst nx
    by_cases hy1 : ny = 1
    · subst ny
      exact B.xy hs hrx hzx hzy hh.ux hh.uy
    · exact B.x_only hs hrx ⟨ny,by omega,hry,hzy⟩ hh.ux
  · by_cases hy1 : ny = 1
    · subst ny
      exact B.y_only hs hry ⟨nx,by omega,hrx,hzx⟩ hh.uy
    · exact B.not_both_late hs ⟨nx,by omega,hrx,hzx⟩ ⟨ny,by omega,hry,hzy⟩




/-- The source translation criterion for a rectangular return hit. -/
theorem rectangle_translation (D : TwoGeneratorData) {A Q t : ℤ}
    (hA : 0 < A) (_hAv : A < D.v) (_hQ : 0 < Q) (hQu : Q < D.u)
    (ht : t ∈ D.T) :
    t + A*D.u - Q*D.v ∉ D.T ↔
      ∃ p q : ℤ, 0 ≤ p ∧ p < D.v-A ∧ 0 ≤ q ∧ q < Q ∧ t = p*D.u+q*D.v := by
  obtain ⟨p,q,hq,hqu,he⟩ := D.normal_form_exists t
  have hp : 0 ≤ p := (D.normal_form_mem_iff hq hqu).mp (by rw [← he]; exact ht)
  constructor
  · intro hgap
    have hqQ : q < Q := by
      by_contra h
      apply hgap
      exact ⟨p+A,q-Q,by omega,by omega,by rw [he]; ring⟩
    have hrep : t + A*D.u - Q*D.v = (p+A-D.v)*D.u+(q-Q+D.u)*D.v := by rw [he]; ring
    rw [hrep,D.normal_form_mem_iff (by omega) (by omega)] at hgap
    exact ⟨p,q,hp,by omega,hq,hqQ,he⟩
  · rintro ⟨r,s,hr,hrv,hs,hsQ,he'⟩
    have hu := D.normal_form_unique hq hqu hs (by omega) (he.symm.trans he')
    obtain ⟨rfl,rfl⟩ := hu
    have hrep : t + A*D.u - Q*D.v = (p+A-D.v)*D.u+(q-Q+D.u)*D.v := by rw [he]; ring
    rw [hrep,D.normal_form_mem_iff (by omega) (by omega)]
    omega

theorem ux_translation {t : ℤ} (ht : t ∈ B.base.T) :
    t + (B.a+B.α)*B.base.u - B.base.v ∉ B.base.T ↔ B.Ux t := by
  have h := rectangle_translation B.base (by have := B.a_pos; have := B.α_pos; omega : 0 < B.a+B.α)
    B.aα_lt (by omega : (0:ℤ) < 1) (by have := B.base.u_ge_two; omega) ht
  simp only [one_mul] at h
  rw [h]
  constructor
  · rintro ⟨p,q,hp,hp',hq,hq',he⟩
    have : q = 0 := by omega
    exact ⟨p,hp,by omega,by simpa [this] using he⟩
  · rintro ⟨p,hp,hp',he⟩
    exact ⟨p,0,hp,by omega,by omega,by omega,by simpa using he⟩

theorem zx_translation {t : ℤ} (ht : t ∈ B.base.T) :
    t + B.a*B.base.u - B.β*B.base.v ∉ B.base.T ↔ B.Zx t := by
  exact rectangle_translation B.base B.a_pos (by have := B.aα_lt; have := B.α_pos; omega)
    B.β_pos (by have := B.bβ_lt; have := B.b_pos; omega) ht

theorem uy_translation {t : ℤ} (ht : t ∈ B.base.T) :
    t + (B.b+B.β)*B.base.v - B.base.u ∉ B.base.T ↔ B.Uy t := by
  have h := B.swap.ux_translation (by simpa using ht)
  rw [B.swap_mem,B.swap_Ux] at h
  exact h

theorem zy_translation {t : ℤ} (ht : t ∈ B.base.T) :
    t + B.b*B.base.v - B.α*B.base.u ∉ B.base.T ↔ B.Zy t := by
  have h := B.swap.zx_translation (by simpa using ht)
  have hzy : B.swap.Zx t ↔ B.Zy t := by
    constructor
    · rintro ⟨p,q,hp,hp',hq,hq',he⟩
      exact ⟨q,p,hq,hq',hp,hp',by simpa [swap,add_comm] using he⟩
    · rintro ⟨p,q,hp,hp',hq,hq',he⟩
      exact ⟨q,p,hq,hq',hp,hp',by simpa [swap,add_comm] using he⟩
  rw [hzy,B.swap_mem] at h
  exact h

/-- Compile-time guard: a first return need not have a stable predecessor. -/
def firstReturnExample : BranchIData where
  base := ⟨7,5,by norm_num,by norm_num,by decide⟩
  d := 3
  s := 1
  κ := 1
  a := 1
  b := 1
  α := 3
  β := 1
  p₀ := 0
  q₀ := 1
  d_ge_two := by norm_num
  s_pos := by norm_num
  s_lt := by norm_num
  κ_pos := by norm_num
  κ_le := by norm_num
  a_pos := by norm_num
  b_pos := by norm_num
  α_pos := by norm_num
  β_pos := by norm_num
  aα_lt := by norm_num
  bβ_lt := by norm_num
  p₀_nonneg := by norm_num
  q₀_nonneg := by norm_num

theorem first_return_exception :
    firstReturnExample.j 1 = 0 ∧ firstReturnExample.τ 1 = 2*7+0*5 ∧
    firstReturnExample.Zx (firstReturnExample.τ 1) ∧
    ¬ firstReturnExample.q₀ + 1 ≤ (0:ℤ) ∧
    firstReturnExample.τ 0 ∉ firstReturnExample.base.T := by
  refine ⟨by norm_num [firstReturnExample,j,c], by norm_num [firstReturnExample,τ,ρ,w,L,c], ?_, by norm_num [firstReturnExample], ?_⟩
  · exact ⟨2,0,by norm_num,by norm_num [firstReturnExample],by norm_num,
      by norm_num [firstReturnExample],by norm_num [firstReturnExample,τ,ρ,w,L,c]⟩
  · intro h
    have := firstReturnExample.base.nonneg h
    norm_num [firstReturnExample,τ,ρ,w,L,c] at this




theorem firstReturnExample_periodic (n : ℤ) :
    firstReturnExample.τ (n+3) = firstReturnExample.τ n + 25 := by
  norm_num [firstReturnExample,τ,ρ,w,L,c]
  omega

theorem firstReturnExample_stable : firstReturnExample.Stable := by
  have hall : ∀ n : ℕ, 1 ≤ n → firstReturnExample.τ n ∈ firstReturnExample.base.T := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hsmall : n < 4
      · have hn_cases : n = 1 ∨ n = 2 ∨ n = 3 := by omega
        rcases hn_cases with rfl | rfl | rfl
        · exact ⟨2,0,by norm_num,by norm_num,by norm_num [firstReturnExample,τ,ρ,w,L,c]⟩
        · exact ⟨0,1,by norm_num,by norm_num,by norm_num [firstReturnExample,τ,ρ,w,L,c]⟩
        · exact ⟨1,3,by norm_num,by norm_num,by norm_num [firstReturnExample,τ,ρ,w,L,c]⟩
      · have hprev := ih (n-3) (by omega) (by omega)
        have h25 : (25:ℤ) ∈ firstReturnExample.base.T :=
          ⟨0,5,by norm_num,by norm_num,by norm_num [firstReturnExample]⟩
        have he : (n:ℤ) = ((n-3:ℕ):ℤ)+3 := by omega
        rw [he,firstReturnExample_periodic]
        exact firstReturnExample.base.T.add_mem hprev h25
  intro n hn
  have h := hall n.toNat (by omega)
  simpa [Int.toNat_of_nonneg (show 0 ≤ n by omega)] using h

end BranchIData
end P21.Symmetric

