import P21.Nonsymmetric.Chain.C8.KernelOne

namespace P21.Nonsymmetric
namespace ChainCore
namespace FirstFit

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} (A : K.FirstFit) (E : K.Returns)

/-- The exact EA-ONE / QJ-ONE equations, with the kernel coefficients retained. -/
structure OneData where
  anchor : A.zhat=A.zhat
  x : ℤ
  z : ℤ
  x_pos : 1 ≤ x
  z_pos : 1 ≤ z
  ea_d : E.Li*K.d = x*(D.a 0 : ℤ)-K.chain.delta
  ea_S : E.Li*K.S = x*(D.rho 1 : ℤ)-(E.Uj+1)
  ea_k : (D.rho 2 : ℤ)-E.Uk-1 = E.Li*K.Croot+x*(D.b 2 : ℤ)
  qj_d : E.Lj*K.d = z*(D.a 0 : ℤ)+(E.Aj+1)
  qj_S : E.Lj*K.S = z*(D.rho 1 : ℤ)+K.chain.gapJ
  qj_k : (D.rho 2 : ℤ) = E.Lj*K.Croot+E.Cj+1+z*(D.b 2 : ℤ)

noncomputable def oneData (hF : s.semigroup.IsFrobenius F)
    (hw : A.chi ≤ K.chain.T) : A.OneData E := by
  let R := A.oneRelations E hF hw
  refine {
    anchor := rfl
    x := R.ea.x
    z := R.qj.z
    x_pos := R.ea.x_pos
    z_pos := R.qj.z_pos
    ea_d := ?_
    ea_S := ?_
    ea_k := ?_
    qj_d := ?_
    qj_S := ?_
    qj_k := ?_ }
  · have h := R.ea.d_eq
    rw [R.ea_y_one] at h
    simpa using h
  · have h := R.ea.S_eq
    rw [R.ea_y_one] at h
    simpa using h
  · have h := R.ea.epsilon_eq
    rw [R.ea_y_one] at h
    simpa using h
  · have h := R.qj.d_eq
    rw [R.qj_v_one] at h
    simpa using h
  · have h := R.qj.S_eq
    rw [R.qj_v_one] at h
    simpa using h
  · have h := R.qj.rho_eq
    rw [R.qj_v_one] at h
    simpa using h

namespace OneData
variable {A E} (O : A.OneData E)

def det : ℤ := O.x*E.Lj-O.z*E.Li

def a (E : K.Returns) : ℤ := E.Aj+1

def Q (E : K.Returns) : ℤ := E.Uj+1

 theorem a_pos : 1 ≤ a E := by
  have hn := E.coeff_nonneg.2.2.2.2.1
  simp [a]
  omega

 theorem Q_pos : 1 ≤ Q E := by
  have hn := E.coeff_nonneg.1
  simp [Q]
  omega

/-- The exact determinant identity preceding the lattice-index argument. -/
theorem det_mul_d : O.det*K.d = O.x*(a E)+O.z*K.chain.delta := by
  simp [det, a]
  linear_combination O.x*O.qj_d - O.z*O.ea_d

theorem det_pos : 1 ≤ O.det := by
  have hd := K.d_range.1
  have ha := a_pos (K:=K) (E:=E)
  have hx := O.x_pos
  have hz := O.z_pos
  have hdelta := K.chain.scalar_ranges.1
  have hrhs : 0 < O.x*(a E)+O.z*K.chain.delta := by
    nlinarith [mul_pos (show 0 < O.x by omega) (show 0 < a E by omega),
      mul_pos (show 0 < O.z by omega) (show 0 < K.chain.delta by omega)]
  by_contra h
  have hprod : O.det*K.d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
  rw [O.det_mul_d] at hprod
  omega

/-- Closed-triangle lattice coordinates expressed without division. -/
def InTriangle (p q : ℤ) : Prop :=
  0 ≤ E.Lj*p-O.z*q ∧ 0 ≤ -E.Li*p+O.x*q ∧
  (E.Lj*p-O.z*q)+(-E.Li*p+O.x*q) ≤ O.det

def IsVertex (p q : ℤ) : Prop :=
  (p=0 ∧ q=0) ∨ (p=O.x ∧ q=E.Li) ∨ (p=O.z ∧ q=E.Lj)

/-- Exact load-bearing statement still required for the empty-triangle gate. -/
def EmptyTriangleStatement : Prop :=
  ∀ p q : ℤ, O.InTriangle p q → O.IsVertex p q

/-- Exact DET1 target; it is intentionally a proposition rather than a field. -/
def DetOneStatement : Prop := O.det=1

end OneData
end FirstFit
end ChainCore
end P21.Nonsymmetric
