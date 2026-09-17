import P21.Symmetric.Classification.SymmetricRigidity
import P21.Symmetric.Classification.AperyCardinality
import P21.Symmetric.Classification.GcdDecomposition

namespace P21.Symmetric.Classification

variable {g : Generators}

theorem tail_apery_pair_rep {w : ℤ} (hw : TailApery g 0 w) :
    ∃ a b : ℤ, 0 ≤ a ∧ 0 ≤ b ∧ w = a*g.n 1+b*g.n 2 := by
  obtain ⟨c,hc⟩ := hw.1
  have hz := apery_actual_zero hw (⟨c,hc⟩ : g.ActualFactorization3 w)
  change c 0 = 0 at hz
  refine ⟨c 1,c 2,Int.natCast_nonneg _,Int.natCast_nonneg _,?_⟩
  simpa [value, Fin.sum_univ_succ, hz] using hc.symm

theorem tail_apery_reduction (s : g.Setting) (hsym : SymmetricTail g)
    (i : Fin 3) {w : ℤ} (hw : w ∈ g.H) :
    ∃ q a : ℤ, 0 ≤ q ∧ TailApery g i a ∧ w=q*g.n i+a := by
  exact tail_apery_reduce s hsym i hw

theorem unique_top_rectangle (s : g.Setting) {f A B : ℤ}
    (hs : SymmetricAt g.H f) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ht : f+g.n 0=A*g.n 1+B*g.n 2)
    (hu : ∀ a b : ℤ, 0 ≤ a → 0 ≤ b →
      f+g.n 0=a*g.n 1+b*g.n 2 → a=A ∧ b=B)
    {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    TailApery g 0 (a*g.n 1+b*g.n 2) ↔ a≤A ∧ b≤B := by
  exact unique_top_apery_rectangle g.H (generator_mem g.n 1) (generator_mem g.n 2)
    hA hB ht (symmetry_apery_top s hs 0).2
    (fun _ hm hg => tail_apery_pair_rep ⟨hm,hg⟩)
    (fun _ hm hg => symmetry_apery_complement hs 0 ⟨hm,hg⟩) hu ha hb

theorem unique_top_boundary_relations (s : g.Setting) {f A B : ℤ}
    (hs : SymmetricAt g.H f) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ht : f+g.n 0=A*g.n 1+B*g.n 2)
    (hu : ∀ a b : ℤ, 0 ≤ a → 0 ≤ b →
      f+g.n 0=a*g.n 1+b*g.n 2 → a=A ∧ b=B) :
    ∃ q r a b : ℤ, 0<q ∧ 0<r ∧ 0≤a ∧ a≤A ∧ 0≤b ∧ b≤B ∧
      (A+1)*g.n 1=q*g.n 0+b*g.n 2 ∧
      (B+1)*g.n 2=r*g.n 0+a*g.n 1 := by
  have hr := @unique_top_rectangle g s f A B hs hA hB ht hu
  have hred : ∀ w ∈ g.H, ∃ q a b : ℤ, 0≤q ∧ 0≤a ∧ a≤A ∧
      0≤b ∧ b≤B ∧ w=q*g.n 0+a*g.n 1+b*g.n 2 := by
    intro w hw
    obtain ⟨q,t,hq,htap,he⟩ := tail_apery_reduction s ⟨f,hs⟩ 0 hw
    obtain ⟨a,b,ha,hb,ht'⟩ := tail_apery_pair_rep htap
    have hbds := (hr ha hb).1 (by rwa [ht'] at htap)
    exact ⟨q,a,b,hq,ha,hbds.1,hb,hbds.2,by linear_combination he+ht'⟩
  obtain ⟨q,b,hq,hb,hbB,hqy⟩ := rectangular_boundary_relation g.H
    (generator_mem g.n 0) (generator_mem g.n 1) (generator_mem g.n 2)
    hA hB (fun a b ha hb => hr ha hb) hred
  have hred' : ∀ w ∈ g.H, ∃ q b a : ℤ, 0≤q ∧ 0≤b ∧ b≤B ∧
      0≤a ∧ a≤A ∧ w=q*g.n 0+b*g.n 2+a*g.n 1 := by
    intro w hw
    obtain ⟨q,a,b,hq,ha,haA,hb,hbB,he⟩ := hred w hw
    exact ⟨q,b,a,hq,hb,hbB,ha,haA,by linear_combination he⟩
  have hr' : ∀ b a : ℤ, 0≤b → 0≤a →
      ((b*g.n 2+a*g.n 1∈g.H ∧ b*g.n 2+a*g.n 1-g.n 0∉g.H) ↔ b≤B ∧ a≤A) := by
    intro b a hb ha
    simpa only [TailApery, add_comm, and_comm] using hr ha hb
  obtain ⟨r,a,hr0,ha,haA,hrz⟩ := rectangular_boundary_relation g.H
    (generator_mem g.n 0) (generator_mem g.n 2) (generator_mem g.n 1)
    hB hA hr' hred'
  exact ⟨q,r,a,b,hq,hr0,ha,haA,hb,hbB,hqy,hrz⟩

theorem unique_top_glue_data (g : Generators) (s : g.Setting) {f A B : ℤ}
    (hs : SymmetricAt g.H f) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ht : f+g.n 0=A*g.n 1+B*g.n 2)
    (hu : ∀ a b : ℤ, 0 ≤ a → 0 ≤ b →
      f+g.n 0=a*g.n 1+b*g.n 2 → a=A ∧ b=B) :
    Nonempty (SymmetricGlueData g) := by
  have hr := @unique_top_rectangle g s f A B hs hA hB ht hu
  have hcard : g.n 0=(A+1)*(B+1) := by
    apply tail_apery_rectangle_card s ⟨f,hs⟩ 0 (g.n 1) (g.n 2) A B hA hB
      (fun _ hw => tail_apery_pair_rep hw) (fun a b ha hb => hr ha hb)
    intro a b c d ha _ hb _ hc hcA hd hdB he
    exact unique_top_rectangle_injective ht hu ha hb hc hcA hd hdB he
  obtain ⟨q,r,a,b,hq,hr0,ha,haA,hb,hbB,hy,hz⟩ :=
    unique_top_boundary_relations s hs hA hB ht hu
  have hbez : ∃ α β γ : ℤ, α*g.n 0+β*g.n 1+γ*g.n 2=1 :=
    tail_bezout s ⟨f,hs⟩ (Equiv.refl _)
  have hzero := rectangular_boundary_zero (by omega : 0<A+1) (by omega : 0<B+1)
    ha (by omega : a<A+1) hb (by omega : b<B+1) hcard hbez hy hz
  have hcommon : ∀ d : ℤ, (∀ i, d ∣ g.n i) → d ∣ 1 :=
    fun _ hd => tail_common_divisor_dvd_one s ⟨f,hs⟩ hd
  rcases hzero with ha0 | hb0
  · have hz' : (B+1)*g.n 2=r*g.n 0 := by simpa [ha0] using hz
    obtain ⟨hez,hey⟩ := rectangular_zero_boundary_decomposition
      (by omega : 0<A+1) (by omega : 0<B+1) hcard hy hz'
    exact rectangle_glue_data g s hcommon (Equiv.refl _) (A+1) (B+1) r q b
      (by omega) hq.le hb hcard hez hey
  · have hy' : (A+1)*g.n 1=q*g.n 0 := by simpa [hb0] using hy
    have hcard' : g.n 0=(B+1)*(A+1) := by nlinarith [hcard]
    obtain ⟨hey,hez⟩ := rectangular_zero_boundary_decomposition
      (by omega : 0<B+1) (by omega : 0<A+1) hcard' hz hy'
    apply rectangle_glue_data g s hcommon (Equiv.swap 1 2) (B+1) (A+1) q r a
      (by omega) hr0.le ha
    · simpa [Equiv.swap_apply_def] using hcard'
    · simpa using hey
    · simpa using hez

end P21.Symmetric.Classification
