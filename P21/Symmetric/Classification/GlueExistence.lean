import P21.Symmetric.Classification.TopFactorization
import P21.Symmetric.Classification.UniqueTop

namespace P21.Symmetric.Classification

/-- Frobenius symmetry forces gluing: its top Apéry element has either a unique
pair factorization (the rectangle branch) or two distinct pair factorizations. -/
theorem glue_exists_of_symmetric (g : Generators) (s : g.Setting)
    (hsym : SymmetricTail g) : Nonempty (SymmetricGlueData g) := by
  classical
  obtain ⟨f, hs⟩ := hsym
  have htop := symmetry_apery_top s hs 0
  obtain ⟨A, hA⟩ := htop.1
  have hzero : A 0 = 0 := apery_actual_zero htop ⟨A, hA⟩
  have ht : f + g.n 0 = (A 1 : ℤ) * g.n 1 + (A 2 : ℤ) * g.n 2 := by
    simpa [value, Fin.sum_univ_succ, hzero] using hA.symm
  by_cases hunique : ∀ a b : ℤ, 0 ≤ a → 0 ≤ b →
      f + g.n 0 = a * g.n 1 + b * g.n 2 → a = A 1 ∧ b = A 2
  · exact unique_top_glue_data g s hs (Int.natCast_nonneg _) (Int.natCast_nonneg _) ht hunique
  · push Not at hunique
    obtain ⟨a,b,ha,hb,he,hne⟩ := hunique
    let p : Equiv.Perm (Fin 3) := (Equiv.swap 0 1).trans (Equiv.swap 0 2)
    have hp0 : p 0 = 1 := by simp [p, Equiv.trans_apply, Equiv.swap_apply_def]
    have hp1 : p 1 = 2 := by simp [p, Equiv.trans_apply]
    have hp2 : p 2 = 0 := by simp [p, Equiv.trans_apply, Equiv.swap_apply_def]
    have hf : f ∉ g.H := (hs f).2 (by simp)
    apply two_top_representations_glue_data g s
      (fun d hd => tail_common_divisor_dvd_one s ⟨f,hs⟩ hd) p hf
      (Int.natCast_nonneg (A 1)) (Int.natCast_nonneg (A 2)) ha hb
    · simpa only [hp0,hp1,hp2] using ht
    · simpa only [hp0,hp1,hp2] using he
    · omega

end P21.Symmetric.Classification

