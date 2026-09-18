import P21.Nonsymmetric.Chain.C8.CrossProductScale

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} (O : A.OneData E)

def Dj (O : A.OneData E) : ℤ := K.d*(D.a 1 : ℤ)+K.S*(D.b 0 : ℤ)

def P0 (O : A.OneData E) : ℤ := O.V+(D.a 0 : ℤ)

def CA (O : A.OneData E) : ℤ :=
  O.Kcal-(E.Lj+E.Li-1)*O.P0

def CB (O : A.OneData E) : ℤ :=
  O.Dj-(D.b 0 : ℤ)-(O.z+O.x-1)*O.P0

theorem P0_pos (P : O.ParamData) : 0 < O.P0 := by
  have hai : (0:ℤ) < D.a 0 := by exact_mod_cast D.a_pos 0
  simp only [P0]
  nlinarith [P.V_pos]

/-- Exact boundary multiplicity identity (BOUND-MULT). -/
theorem bound_mult (hb : K.Croot=K.chain.alpha) (hdet : O.DetOneStatement)
    (C : O.CeilingData) (P : O.ParamData) :
    O.mhat-O.Jcal =
      O.H0*O.P0+K.chain.alpha*O.CA+(D.b 2 : ℤ)*O.CB := by
  have hrhok := O.boundary_k_ceiling C hb
  simp only [mhat, Ical, Jcal, Kcal, Dj, P0, CA, CB, V]
  rw [P.d_eq, P.S_eq, P.ai_eq, P.rhoj_eq, P.bi_eq, hrhok, hb]
  change O.x*E.Lj-O.z*E.Li=1 at hdet
  linear_combination
    ((a E*Q E-K.chain.delta*K.chain.gapJ) *
      (O.H0-(O.x+O.z-1)*(D.b 2 : ℤ)-
        (E.Li+E.Lj-1)*K.chain.alpha)) * hdet

end P21.Nonsymmetric.ChainCore.FirstFit.OneData
