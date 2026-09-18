import P21.Nonsymmetric.Chain.C8.BoundaryTriangle

namespace P21.Nonsymmetric.ChainCore.FirstFit.OneData

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
variable {K : ChainCore s F D} {A : K.FirstFit} {E : K.Returns} (O : A.OneData E)

/-- Full publication SYNC.  The EB determinant is proved internally from its boundary triangle. -/
theorem boundary_sync (hF : s.semigroup.IsFrobenius F) (hb : K.Croot=K.chain.alpha)
    (hdet : O.DetOneStatement) (P : O.ParamData) :
    ∃ B : A.EBKernel E, O.BoundarySyncData B := by
  let B := A.ebKernel E
  have hy : B.y=1 := B.y_eq_one hF hb
  let T : A.EBOneData E := A.ebOneData B hy O
  have hemptyB : T.EBEmptyTriangleStatement := T.empty_triangleB hF hb
  have hdetB : T.EBDetOneStatement := T.det_oneB hemptyB
  change T.detB=1 at hdetB
  have hcross : O.x*E.Lj-O.z*E.Li=1 := hdet
  have hcrossB : B.x*E.Lj-O.z*E.Lb=1 := by
    simpa [T, EBOneData.detB, FirstFit.ebOneData] using hdetB
  have hBd := B.d_eq
  have hBS := B.S_eq
  have hBk := B.k_eq
  rw [hy] at hBd hBS hBk
  simp at hBd hBS hBk
  have hdetDiff : (B.x-O.x)*E.Lj=O.z*(E.Lb-E.Li) := by
    nlinarith
  have hdDiff : (E.Lb-E.Li)*K.d=(B.x-O.x)*(D.a 0 : ℤ) := by
    have hEA := O.ea_d
    nlinarith
  have hprod : (B.x-O.x)*(E.Lj*K.d-O.z*(D.a 0 : ℤ))=0 := by
    calc
      (B.x-O.x)*(E.Lj*K.d-O.z*(D.a 0 : ℤ)) =
          ((B.x-O.x)*E.Lj)*K.d-O.z*((B.x-O.x)*(D.a 0 : ℤ)) := by ring
      _ = O.z*(E.Lb-E.Li)*K.d-O.z*((E.Lb-E.Li)*K.d) := by
        rw [hdetDiff, hdDiff]
      _ = 0 := by ring
  have haeq : E.Lj*K.d-O.z*(D.a 0 : ℤ)=a E := by
    have h := O.qj_d
    simp [a]
    nlinarith
  rw [haeq] at hprod
  have hx : B.x=O.x := by
    have ha := a_pos (K:=K) (E:=E)
    have hz : B.x-O.x=0 := (mul_eq_zero.mp hprod).resolve_right (by omega)
    omega
  have hL : E.Lb=E.Li := by
    rw [hx] at hdDiff
    have hd := K.d_range.1
    have hz : E.Lb-E.Li=0 := by
      have hp : (E.Lb-E.Li)*K.d=0 := by simpa using hdDiff
      exact (mul_eq_zero.mp hp).resolve_right (by omega)
    omega
  have hU : E.Uj=E.Vj+(D.a 1 : ℤ) := by
    rw [hx, hL] at hBS
    have hEA := O.ea_S
    nlinarith
  have hVk : E.Vk=E.Uk+(D.b 2 : ℤ) := by
    rw [hx, hL] at hBk
    have hEA := O.ea_k
    nlinarith
  have hQ2 : 2≤Q E := by
    have hV := E.coeff_nonneg.2.2.1
    have ha1 : (1:ℤ)≤D.a 1 := by exact_mod_cast D.a_pos 1
    simp [Q, hU]
    omega
  exact ⟨B,hy,hL,hx,hU,hVk,hQ2⟩

end P21.Nonsymmetric.ChainCore.FirstFit.OneData
