import P21.Symmetric.BranchI
import P21.Symmetric.RawRows
import P21.Symmetric.GlueNormalForm

namespace P21.Symmetric

/-- Equalities identifying the arithmetic walk with the actual glued tail. -/
structure BranchIRealization {g : Generators} (B : BranchIData)
    (G : SymmetricGlueData g) (F f : ℤ) : Prop where
  two_eq : G.two = B.base
  d_eq : G.d = B.d
  w_eq : G.w = B.w
  m_eq : g.m = B.d*B.L-B.κ*B.w
  r_eq : f-F-g.m = B.s*B.w+B.d*B.ρ

namespace BranchIRealization
variable {g : Generators} {B : BranchIData} {G : SymmetricGlueData g} {F f : ℤ}
variable (R : BranchIRealization B G F f)
include R

theorem normal_mem {j t : ℤ} (hj : 0 ≤ j) (hjd : j < B.d) :
    j*B.w+B.d*t ∈ g.H ↔ t ∈ B.base.T := by
  have h := G.normal_form_mem_iff (t := t) hj (by simpa [R.d_eq] using hjd)
  simpa only [R.two_eq,R.d_eq,R.w_eq] using h

theorem represented_mem {j t : ℤ} (hj : 0 ≤ j) (ht : t ∈ B.base.T) :
    j*B.w+B.d*t ∈ g.H := by
  apply G.mem_tail_iff.mpr
  exact ⟨j.toNat,t,by simpa [R.two_eq] using ht,by rw [R.w_eq,R.d_eq,Int.toNat_of_nonneg hj]⟩

theorem x_eq : g.n (G.perm 0) = B.d*B.base.u := by simpa only [R.two_eq,R.d_eq] using G.x_eq
theorem y_eq : g.n (G.perm 1) = B.d*B.base.v := by simpa only [R.two_eq,R.d_eq] using G.y_eq
theorem z_eq : g.n (G.perm 2) = B.w := G.z_eq.trans R.w_eq

theorem walk_identity (n : ℤ) : f-F-g.m+n*g.m = B.j n*B.w+B.d*B.τ n := by
  rw [R.r_eq,R.m_eq]
  dsimp [BranchIData.j,BranchIData.τ]
  ring

/-- FS is exactly T-membership for the same residue-normalized walk. -/
theorem stable_iff : B.Stable ↔ ∀ n : ℤ, 1 ≤ n → f-F-g.m+n*g.m ∈ g.H := by
  constructor <;> intro hs n hn
  · rw [R.walk_identity]
    exact (R.normal_mem (B.j_bounds n).1 (B.j_bounds n).2).mpr (hs n hn)
  · apply (R.normal_mem (B.j_bounds n).1 (B.j_bounds n).2).mp
    rw [← R.walk_identity]
    exact hs n hn

theorem stable (s : g.Setting) (hF : s.semigroup.IsFrobenius F)
    (hsym : SymmetricAt g.H f) : B.Stable := by
  apply R.stable_iff.mpr
  intro n hn
  have h := stable_walk s hF hsym n.toNat (by omega)
  simpa [Int.toNat_of_nonneg (show 0 ≤ n by omega)] using h

theorem ux_hit (s : g.Setting) (hF : s.semigroup.IsFrobenius F)
    (hcan : s.semigroup.Canonical F g.m) (hsym : SymmetricAt g.H f)
    (hx : ActualRawRow s F f ((B.a+B.α)*B.d*B.base.u)) :
    ∃ n : ℤ, 1 ≤ n ∧ B.Ux (B.τ n) := by
  have hb : (B.a+B.α)*B.d*B.base.u + (f-F-g.m) - g.n (G.perm 1) ∈ g.H := by
    have ht : (B.base.u-B.b-B.β-1)*B.base.v ∈ B.base.T :=
      ⟨0,B.base.u-B.b-B.β-1,by omega,by have := B.bβ_lt; omega,by ring⟩
    have hh := R.represented_mem B.s_pos.le ht
    convert hh using 1
    rw [R.r_eq,R.y_eq]
    dsimp [BranchIData.ρ,BranchIData.w]
    ring
  obtain ⟨n,hn,hgap⟩ := hx.positive_hit_required hF hcan hsym (G.perm 1) hb
  refine ⟨n,by exact_mod_cast hn,(B.ux_translation (R.stable s hF hsym n (by exact_mod_cast hn))).mp ?_⟩
  intro ht
  apply hgap
  have hmem := (R.normal_mem (B.j_bounds n).1 (B.j_bounds n).2).mpr ht
  convert hmem using 1
  rw [R.y_eq,R.r_eq,R.m_eq]
  dsimp [BranchIData.j,BranchIData.τ]
  ring

theorem uy_hit (s : g.Setting) (hF : s.semigroup.IsFrobenius F)
    (hcan : s.semigroup.Canonical F g.m) (hsym : SymmetricAt g.H f)
    (hy : ActualRawRow s F f ((B.b+B.β)*B.d*B.base.v)) :
    ∃ n : ℤ, 1 ≤ n ∧ B.Uy (B.τ n) := by
  have hb : (B.b+B.β)*B.d*B.base.v + (f-F-g.m) - g.n (G.perm 0) ∈ g.H := by
    have ht : (B.base.v-B.a-B.α-1)*B.base.u ∈ B.base.T :=
      ⟨B.base.v-B.a-B.α-1,0,by have := B.aα_lt; omega,by omega,by ring⟩
    have hh := R.represented_mem B.s_pos.le ht
    convert hh using 1
    rw [R.r_eq,R.x_eq]
    dsimp [BranchIData.ρ,BranchIData.w]
    ring
  obtain ⟨n,hn,hgap⟩ := hy.positive_hit_required hF hcan hsym (G.perm 0) hb
  refine ⟨n,by exact_mod_cast hn,(B.uy_translation (R.stable s hF hsym n (by exact_mod_cast hn))).mp ?_⟩
  intro ht
  apply hgap
  have hmem := (R.normal_mem (B.j_bounds n).1 (B.j_bounds n).2).mpr ht
  convert hmem using 1
  rw [R.x_eq,R.r_eq,R.m_eq]
  dsimp [BranchIData.j,BranchIData.τ]
  ring



theorem zx_hit (s : g.Setting) (hF : s.semigroup.IsFrobenius F)
    (hcan : s.semigroup.Canonical F g.m) (hsym : SymmetricAt g.H f)
    (hx : ActualRawRow s F f ((B.a+B.α)*B.d*B.base.u)) :
    ∃ n : ℤ, 1 ≤ n ∧ B.j n = 0 ∧ B.Zx (B.τ n) := by
  have hb : (B.a+B.α)*B.d*B.base.u + (f-F-g.m) - g.n (G.perm 2) ∈ g.H := by
    have ht : (B.base.u-B.b-B.β)*B.base.v ∈ B.base.T :=
      ⟨0,B.base.u-B.b-B.β,by omega,by have := B.bβ_lt; omega,by ring⟩
    have hh := R.represented_mem (by have := B.s_pos; omega : 0 ≤ B.s-1) ht
    convert hh using 1
    rw [R.r_eq,R.z_eq]
    dsimp [BranchIData.ρ,BranchIData.w]
    ring
  obtain ⟨n,hn,hgap⟩ := hx.positive_hit_required hF hcan hsym (G.perm 2) hb
  have hτ := R.stable s hF hsym n (by exact_mod_cast hn)
  have hj : B.j n = 0 := by
    by_contra hh
    have ht : B.τ n+(B.a+B.α)*B.base.u ∈ B.base.T :=
      B.base.T.add_mem hτ ⟨B.a+B.α,0,by have := B.a_pos; have := B.α_pos; omega,by omega,by ring⟩
    have hmem := R.represented_mem (by have := (B.j_bounds n).1; omega : 0 ≤ B.j n-1) ht
    apply hgap
    convert hmem using 1
    rw [R.z_eq,R.r_eq,R.m_eq]
    dsimp [BranchIData.j,BranchIData.τ]
    ring
  refine ⟨n,by exact_mod_cast hn,hj,(B.zx_translation hτ).mp ?_⟩
  intro ht
  apply hgap
  have hmem := (R.normal_mem (by have := B.d_ge_two; omega : 0 ≤ B.d-1) (by omega : B.d-1 < B.d)).mpr ht
  have he : (B.a+B.α)*B.d*B.base.u+(f-F-g.m)-g.n (G.perm 2)+(n:ℤ)*g.m =
      (B.j n-1)*B.w+B.d*(B.τ n+(B.a+B.α)*B.base.u) := by
    rw [R.z_eq,R.r_eq,R.m_eq]
    dsimp [BranchIData.j,BranchIData.τ]
    ring
  rw [he,hj]
  convert hmem using 1
  dsimp [BranchIData.w]
  ring

theorem zy_hit (s : g.Setting) (hF : s.semigroup.IsFrobenius F)
    (hcan : s.semigroup.Canonical F g.m) (hsym : SymmetricAt g.H f)
    (hy : ActualRawRow s F f ((B.b+B.β)*B.d*B.base.v)) :
    ∃ n : ℤ, 1 ≤ n ∧ B.j n = 0 ∧ B.Zy (B.τ n) := by
  have hb : (B.b+B.β)*B.d*B.base.v + (f-F-g.m) - g.n (G.perm 2) ∈ g.H := by
    have ht : (B.base.v-B.a-B.α)*B.base.u ∈ B.base.T :=
      ⟨B.base.v-B.a-B.α,0,by have := B.aα_lt; omega,by omega,by ring⟩
    have hh := R.represented_mem (by have := B.s_pos; omega : 0 ≤ B.s-1) ht
    convert hh using 1
    rw [R.r_eq,R.z_eq]
    dsimp [BranchIData.ρ,BranchIData.w]
    ring
  obtain ⟨n,hn,hgap⟩ := hy.positive_hit_required hF hcan hsym (G.perm 2) hb
  have hτ := R.stable s hF hsym n (by exact_mod_cast hn)
  have hj : B.j n = 0 := by
    by_contra hh
    have ht : B.τ n+(B.b+B.β)*B.base.v ∈ B.base.T :=
      B.base.T.add_mem hτ ⟨0,B.b+B.β,by omega,by have := B.b_pos; have := B.β_pos; omega,by ring⟩
    have hmem := R.represented_mem (by have := (B.j_bounds n).1; omega : 0 ≤ B.j n-1) ht
    apply hgap
    convert hmem using 1
    rw [R.z_eq,R.r_eq,R.m_eq]
    dsimp [BranchIData.j,BranchIData.τ]
    ring
  refine ⟨n,by exact_mod_cast hn,hj,(B.zy_translation hτ).mp ?_⟩
  intro ht
  apply hgap
  have hmem := (R.normal_mem (by have := B.d_ge_two; omega : 0 ≤ B.d-1) (by omega : B.d-1 < B.d)).mpr ht
  have he : (B.b+B.β)*B.d*B.base.v+(f-F-g.m)-g.n (G.perm 2)+(n:ℤ)*g.m =
      (B.j n-1)*B.w+B.d*(B.τ n+(B.b+B.β)*B.base.v) := by
    rw [R.z_eq,R.r_eq,R.m_eq]
    dsimp [BranchIData.j,BranchIData.τ]
    ring
  rw [he,hj]
  convert hmem using 1
  dsimp [BranchIData.w]
  ring

/-- Four-hit necessity is obtained from the same two actual PF rows and walk. -/
theorem four_hits (s : g.Setting) (hF : s.semigroup.IsFrobenius F)
    (hcan : s.semigroup.Canonical F g.m) (hsym : SymmetricAt g.H f)
    (hx : ActualRawRow s F f ((B.a+B.α)*B.d*B.base.u))
    (hy : ActualRawRow s F f ((B.b+B.β)*B.d*B.base.v)) : B.FourHits :=
  ⟨R.ux_hit s hF hcan hsym hx,R.uy_hit s hF hcan hsym hy,
   R.zx_hit s hF hcan hsym hx,R.zy_hit s hF hcan hsym hy⟩

/-- Branch I is impossible for these actual surviving rows. -/
theorem impossible (s : g.Setting) (hF : s.semigroup.IsFrobenius F)
    (hcan : s.semigroup.Canonical F g.m) (hsym : SymmetricAt g.H f)
    (hx : ActualRawRow s F f ((B.a+B.α)*B.d*B.base.u))
    (hy : ActualRawRow s F f ((B.b+B.β)*B.d*B.base.v)) : False :=
  B.four_hits_impossible (R.stable s hF hsym) (R.four_hits s hF hcan hsym hx hy)

end BranchIRealization
end P21.Symmetric


