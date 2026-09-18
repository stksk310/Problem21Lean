import P21.Nonsymmetric.Chain.C8.BoundaryClosed

set_option maxHeartbeats 1200000

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} (O : A.OneData E)

def gamma (O : A.OneData E) : ℤ := K.Croot-K.chain.alpha

def Ea (O : A.OneData E) : ℤ :=
  ((E.Li-1)*(E.Lj-1)-1)*(Q E-2)+E.Li^2*(K.chain.gapJ-1)+
    E.Li*((D.a 1 : ℤ)-1)+(E.Li-2)*E.Lj-E.Li

def Edelta (O : A.OneData E) : ℤ :=
  E.Lj*(E.Lj-1)*(Q E-2)+(E.Li*E.Lj+E.Lj)*(K.chain.gapJ-1)+
    E.Lj*((D.a 1 : ℤ)-1)+E.Lj^2

def Aprime (O : A.OneData E) : ℤ :=
  O.Kcal-(E.Lj+E.Li)*O.V

def Bprime (O : A.OneData E) : ℤ :=
  O.Dj-(O.z+O.x-1)*O.V

def Dbase (O : A.OneData E) : ℤ :=
  2*O.Aprime+O.Bprime+O.V-O.Kcal

def Ecoeff (O : A.OneData E) : ℤ :=
  (E.Li-2)*E.Lj+(E.Li-1)*O.z-2*E.Li-O.x+2

theorem strict_regular (hdet : O.DetOneStatement) (P : O.ParamData)
    (hLi : 2≤E.Li) :
    E.Li≥O.x+1 ∧ E.Lj>O.z ∧ O.x≥1 ∧ O.z≥1 := by
  rcases O.level_split hdet P with hreg | hunit
  · omega
  · omega

/-- General K-CEILING multiplicity identity, with no boundary synchronization. -/
theorem strict_j (hdet : O.DetOneStatement) (C : O.CeilingData)
    (P : O.ParamData) :
    O.mhat-O.Jcal = O.H0*O.P0+K.chain.alpha*O.CA+
      O.gamma*(O.CA-O.P0)+(D.b 2 : ℤ)*O.CB := by
  have hrhok := C.k_ceiling
  simp only [mhat, Ical, Jcal, Kcal, Dj, P0, CA, CB, V, gamma]
  rw [P.d_eq, P.S_eq, P.ai_eq, P.rhoj_eq, P.bi_eq, hrhok]
  change O.x*E.Lj-O.z*E.Li=1 at hdet
  linear_combination
    ((a E*Q E-K.chain.delta*K.chain.gapJ) *
      (O.H0+K.chain.alpha-(E.Li+E.Lj)*K.Croot-
        (O.x+O.z-1)*(D.b 2 : ℤ))) * hdet

theorem CA_sub_P0_decomposition (P : O.ParamData) :
    O.CA-O.P0 = a E*O.Ea+K.chain.delta*O.Edelta+
      K.chain.beta*(D.rho 1 : ℤ) := by
  rw [O.CA_decomposition P]
  simp only [P0, V, Aa, Adelta, Ea, Edelta]
  rw [P.ai_eq]
  ring

theorem Aprime_decomposition (P : O.ParamData) :
    O.Aprime =
      a E*(E.Li^2*K.chain.gapJ+((E.Li-1)*E.Lj-E.Li)*Q E+
        E.Li*(D.a 1 : ℤ))+
      K.chain.delta*((E.Lj-1)*(D.rho 1 : ℤ)+E.Lj*(D.a 1 : ℤ)+
        (E.Lj+E.Li)*K.chain.gapJ)+
      K.chain.beta*(D.rho 1 : ℤ) := by
  simp only [Aprime, Kcal, V]
  rw [P.ai_eq, P.rhoj_eq, P.bi_eq]
  ring

theorem Bprime_decomposition (P : O.ParamData) :
    O.Bprime =
      a E*(O.x*(D.a 1 : ℤ)+E.Li*O.x*K.chain.gapJ+
        (O.z*(E.Li-1)-O.x+1)*Q E)+
      K.chain.delta*(O.z*(D.a 1 : ℤ)+(E.Lj-1)*K.S+
        (O.z+O.x-1)*K.chain.gapJ)+
      K.chain.beta*K.S := by
  simp only [Bprime, Dj, V]
  rw [P.d_eq, P.S_eq, P.bi_eq]
  ring

/-- The `n_k` comparison identity used for `Q=1` and the three exceptions. -/
theorem strict_k (hdet : O.DetOneStatement) (C : O.CeilingData)
    (P : O.ParamData) :
    O.mhat-O.Kcal = O.H0*O.V+
      (K.chain.alpha-1)*(O.V+O.Aprime)+
      (O.gamma-1)*O.Aprime+((D.b 2 : ℤ)-1)*O.Bprime+O.Dbase := by
  have hrhok := C.k_ceiling
  simp only [mhat, Ical, Jcal, Kcal, Dj, V, Aprime, Bprime, Dbase, gamma]
  rw [P.d_eq, P.S_eq, P.ai_eq, P.rhoj_eq, P.bi_eq, hrhok]
  change O.x*E.Lj-O.z*E.Li=1 at hdet
  linear_combination
    ((a E*Q E-K.chain.delta*K.chain.gapJ) *
      (O.H0+K.chain.alpha-(E.Li+E.Lj)*K.Croot-
        (O.x+O.z-1)*(D.b 2 : ℤ))) * hdet

theorem Dbase_decomposition (P : O.ParamData) :
    O.Dbase =
      a E*((E.Li+O.x)*(D.a 1 : ℤ)+
        E.Li*(E.Li+O.x)*K.chain.gapJ+O.Ecoeff*Q E)+
      K.chain.delta*((E.Lj-1)*(D.rho 1 : ℤ)+
        (E.Lj+O.z)*(D.a 1 : ℤ)+(E.Lj-1)*K.S+
        (2*(E.Lj+E.Li)+O.z+O.x-2)*K.chain.gapJ)+
      K.chain.beta*((D.rho 1 : ℤ)+K.S) := by
  simp only [Dbase, Aprime, Bprime, Kcal, Dj, V, Ecoeff]
  rw [P.d_eq, P.S_eq, P.ai_eq, P.rhoj_eq, P.bi_eq]
  ring

end P21.Nonsymmetric.ChainCore.FirstFit.OneData
