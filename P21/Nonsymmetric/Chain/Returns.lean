import P21.Nonsymmetric.Chain.Core
import P21.Nonsymmetric.Path.Returns

namespace P21.Nonsymmetric

namespace ChainCore

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

/-- The four genuine Section 7 returns.  Each field retains the complete
actual factorization from which all named coefficients are read. -/
structure Returns (K : ChainCore s F D) where
  EA : PathInput.ActualReturn g K.chain.qA 0
  EB : PathInput.ActualReturn g K.chain.qB 0
  Qj : PathInput.ActualReturn g K.chain.qJ 1
  Qk : PathInput.ActualReturn g K.chain.qK 2

noncomputable def returns (K : ChainCore s F D) : K.Returns where
  EA := Classical.choice <|
    PathInput.actual_return_exists 0 K.chain.qA_actual K.chain.Ai_missing
  EB := Classical.choice <|
    PathInput.actual_return_exists 0 K.chain.qB_actual K.chain.Bi_missing
  Qj := Classical.choice <|
    PathInput.actual_return_exists 1 K.chain.qJ_actual K.chain.Bj_missing
  Qk := Classical.choice <|
    PathInput.actual_return_exists 2 K.chain.qK_actual K.chain.Ak_missing

namespace Returns

variable {K : ChainCore s F D}

def Li (E : K.Returns) : ℤ := E.EA.factorization.coeff 0
def Uj (E : K.Returns) : ℤ := E.EA.factorization.coeff 2
def Uk (E : K.Returns) : ℤ := E.EA.factorization.coeff 3

def Lb (E : K.Returns) : ℤ := E.EB.factorization.coeff 0
def Vj (E : K.Returns) : ℤ := E.EB.factorization.coeff 2
def Vk (E : K.Returns) : ℤ := E.EB.factorization.coeff 3

def Lj (E : K.Returns) : ℤ := E.Qj.factorization.coeff 0
def Aj (E : K.Returns) : ℤ := E.Qj.factorization.coeff 1
def Cj (E : K.Returns) : ℤ := E.Qj.factorization.coeff 3

def Lk (E : K.Returns) : ℤ := E.Qk.factorization.coeff 0
def Ak (E : K.Returns) : ℤ := E.Qk.factorization.coeff 1
def Bk (E : K.Returns) : ℤ := E.Qk.factorization.coeff 2

theorem coeff_nonneg (E : K.Returns) :
    0 ≤ E.Uj ∧ 0 ≤ E.Uk ∧ 0 ≤ E.Vj ∧ 0 ≤ E.Vk ∧
    0 ≤ E.Aj ∧ 0 ≤ E.Cj ∧ 0 ≤ E.Ak ∧ 0 ≤ E.Bk := by
  simp [Uj, Uk, Vj, Vk, Aj, Cj, Ak, Bk]

theorem levels_pos (E : K.Returns) :
    1 ≤ E.Li ∧ 1 ≤ E.Lb ∧ 1 ≤ E.Lj ∧ 1 ≤ E.Lk := by
  simp only [Li, Lb, Lj, Lk]
  exact ⟨by exact_mod_cast E.EA.level_pos,
    by exact_mod_cast E.EB.level_pos,
    by exact_mod_cast E.Qj.level_pos,
    by exact_mod_cast E.Qk.level_pos⟩

theorem EA_eq (E : K.Returns) :
    K.chain.qA + g.n 0 = E.Li * g.m + E.Uj * g.n 1 + E.Uk * g.n 2 := by
  have he := E.EA.factorization.equation
  have hz := E.EA.direction_zero
  have hz' : E.EA.factorization.coeff 1 = 0 := by simpa using hz
  simp [value, Generators.all, Fin.sum_univ_succ] at he
  rw [hz'] at he
  simpa [Li, Uj, Uk, add_assoc] using he.symm

theorem EB_eq (E : K.Returns) :
    K.chain.qB + g.n 0 = E.Lb * g.m + E.Vj * g.n 1 + E.Vk * g.n 2 := by
  have he := E.EB.factorization.equation
  have hz := E.EB.direction_zero
  have hz' : E.EB.factorization.coeff 1 = 0 := by simpa using hz
  simp [value, Generators.all, Fin.sum_univ_succ] at he
  rw [hz'] at he
  simpa [Lb, Vj, Vk, add_assoc] using he.symm

theorem Qj_eq (E : K.Returns) :
    K.chain.qJ + g.n 1 = E.Lj * g.m + E.Aj * g.n 0 + E.Cj * g.n 2 := by
  have he := E.Qj.factorization.equation
  have hz := E.Qj.direction_zero
  have hz' : E.Qj.factorization.coeff 2 = 0 := by simpa using hz
  simp [value, Generators.all, Fin.sum_univ_succ] at he
  rw [hz'] at he
  dsimp [Lj, Aj, Cj]
  calc
    K.chain.qJ + g.n 1 =
        (E.Qj.factorization.coeff 0 : ℤ) * g.m +
        ((E.Qj.factorization.coeff 1 : ℤ) * g.n 0 +
        ((0 : ℤ) * g.n 1 + (E.Qj.factorization.coeff 3 : ℤ) * g.n 2)) := he.symm
    _ = _ := by ring

theorem Qk_eq (E : K.Returns) :
    K.chain.qK + g.n 2 = E.Lk * g.m + E.Ak * g.n 0 + E.Bk * g.n 1 := by
  have he := E.Qk.factorization.equation
  have hz := E.Qk.direction_zero
  have hz' : E.Qk.factorization.coeff 3 = 0 := by simpa using hz
  simp [value, Generators.all, Fin.sum_univ_succ] at he
  rw [hz'] at he
  dsimp [Lk, Ak, Bk]
  calc
    K.chain.qK + g.n 2 =
        (E.Qk.factorization.coeff 0 : ℤ) * g.m +
        ((E.Qk.factorization.coeff 1 : ℤ) * g.n 0 +
        ((E.Qk.factorization.coeff 2 : ℤ) * g.n 1 + (0 : ℤ) * g.n 2)) := he.symm
    _ = _ := by ring

end Returns
end ChainCore
end P21.Nonsymmetric
