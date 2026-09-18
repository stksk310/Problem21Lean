import P21.Nonsymmetric.Path.RootWalls

namespace P21.Nonsymmetric
namespace PathInput

variable {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}

/-- A weak root after the audited finite k-packet descent. -/
structure NormalizedRoot (P : PathInput s F D) extends WeakRoot P where
  K : ℤ
  e_eq : e = K + P.alpha
  S_lt : S < P.R
  K_lower : (D.b 2 : ℤ) ≤ K
  K_upper : K < D.rho 2

namespace WeakRoot

private theorem tail_of_coordinates (g : Generators) (x a b c : ℤ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (he : x = a * g.n 0 + b * g.n 1 + c * g.n 2) : x ∈ g.H := by
  have h0 := g.H.nsmul_mem (generator_mem g.n 0) a.toNat
  have h1 := g.H.nsmul_mem (generator_mem g.n 1) b.toNat
  have h2 := g.H.nsmul_mem (generator_mem g.n 2) c.toNat
  have hsum := g.H.add_mem h0 (g.H.add_mem h1 h2)
  have hac : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha
  have hbc : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb
  have hcc : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hc
  simp only [nsmul_eq_mul] at hsum
  rw [hac, hbc, hcc] at hsum
  rw [he]
  simpa [add_assoc] using hsum

/-- One exact HCR k-packet step in the signed root relation. -/
def step (P : PathInput s F D) (w : WeakRoot P)
    (hK : (D.rho 2 : ℤ) ≤ w.e - P.alpha)
    (hd : 1 ≤ w.d - D.b 0) : WeakRoot P where
  d := w.d - D.b 0
  S := w.S + D.a 1
  e := w.e - D.rho 2
  d_pos := hd
  d_le := by have := D.b_pos 0; have := w.d_le; omega
  S_pos := by have := D.a_pos 1; have := w.S_pos; omega
  e_ge := by omega
  equation := by
    have hw := w.equation
    linear_combination hw + D.relation_two

theorem step_measure (P : PathInput s F D) (w : WeakRoot P)
    (hK : (D.rho 2 : ℤ) ≤ w.e - P.alpha)
    (hd : 1 ≤ w.d - D.b 0) :
    (w.step P hK hd).e - P.alpha =
      (w.e - P.alpha) - D.rho 2 := by
  simp [step]
  ring

private theorem normalize_aux (P : PathInput s F D)
    (hF : s.semigroup.IsFrobenius F) (LK : ActualReturn g P.qL 2)
    (Knat : ℕ) (w : WeakRoot P)
    (hmeasure : (Knat : ℤ) = w.e - P.alpha) :
    Nonempty (NormalizedRoot P) := by
  induction Knat using Nat.strong_induction_on generalizing w with
  | h Knat ih =>
      have hwalls := w.walls P hF LK
      by_cases hsub : w.e - P.alpha < D.rho 2
      · exact ⟨{
          toWeakRoot := w
          K := w.e - P.alpha
          e_eq := by ring
          S_lt := hwalls.1
          K_lower := hwalls.2.2
          K_upper := hsub }⟩
      · have hpacket : (D.rho 2 : ℤ) ≤ w.e - P.alpha := by omega
        let d' : ℤ := w.d - D.b 0
        have hdpos : 1 ≤ d' := by
          by_contra hn
          have he' : g.m = (-d') * g.n 0 +
              (w.S + D.a 1) * g.n 1 + (w.e - D.rho 2) * g.n 2 := by
            dsimp [d']
            linear_combination w.equation + D.relation_two
          apply P21.Symmetric.m_not_mem_tail s
          apply tail_of_coordinates g g.m (-d') (w.S + D.a 1)
            (w.e - D.rho 2)
          · omega
          · have := w.S_pos; have := D.a_pos 1; omega
          · have := w.e_ge; have := P.alpha_pos; omega
          · exact he'
        let w' := w.step P hpacket (by simpa [d'] using hdpos)
        let K' : ℕ := (w'.e - P.alpha).toNat
        have hK'nonneg : 0 ≤ w'.e - P.alpha := by
          have := w'.e_ge
          omega
        have hK'cast : (K' : ℤ) = w'.e - P.alpha := by
          exact Int.toNat_of_nonneg hK'nonneg
        have hdecrease : K' < Knat := by
          have hrho := D.rho_pos 2
          have hs : w'.e - P.alpha = (w.e - P.alpha) - D.rho 2 := by
            simpa [w'] using w.step_measure P hpacket (by simpa [d'] using hdpos)
          omega
        exact ih K' hdecrease w' hK'cast

/-- Publication P5.3.4: explicit well-founded descent to a subcritical root.
The actual LK witness is passed unchanged through every recursive call. -/
theorem normalize (P : PathInput s F D) (hF : s.semigroup.IsFrobenius F)
    (LK : ActualReturn g P.qL 2) (w : WeakRoot P) :
    Nonempty (NormalizedRoot P) := by
  let Knat : ℕ := (w.e - P.alpha).toNat
  have hwalls := w.walls P hF LK
  have hnonneg : 0 ≤ w.e - P.alpha := by omega
  have hcast : (Knat : ℤ) = w.e - P.alpha :=
    Int.toNat_of_nonneg hnonneg
  exact normalize_aux P hF LK Knat w hcast

end WeakRoot
end PathInput
end P21.Nonsymmetric
