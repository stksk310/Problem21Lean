import P21.Nonsymmetric.ColorCap.DPE.FirstThirdColor
import P21.Nonsymmetric.ColorCap.ThreeArms

namespace P21.Nonsymmetric.ColorCap

/-- Appendix B.20 in canonical orientation. -/
theorem canonical_trace_sink_impossible (D : BoxInput)
    {l : List (Fin 3)} {u : Point}
    (ht : FiringTrace D.upper D.rows D.x l u) (hne : l ≠ [])
    (hstart : D.x 0 < D.y 0)
    (hp : ProperNonzeroPredecessors l)
    (hsink : ¬ ∃ i, ∀ j, 1 ≤ fire D.rows i u j) : False := by
  by_cases h1 : l.count 1 = 0
  · by_cases h2 : l.count 2 = 0
    · exact one_color_trace_sink_impossible D ht hne h1 h2 hsink
    · have h2pos : 1 ≤ l.count 2 := by omega
      exact two_color13_trace_sink_impossible D ht hp h1 h2pos hstart hsink
  · have h1pos : 1 ≤ l.count 1 := by omega
    by_cases h2 : l.count 2 = 0
    · exact two_color12_trace_sink_impossible D ht hp h2 h1pos hstart hsink
    · have h2pos : 1 ≤ l.count 2 := by omega
      exact first_third_color_actual_impossible D ht hp h1pos h2pos hstart

/-- Appendix B.20: the exact previously frozen DPE statement. -/
theorem box_positive_exit_proved : BoxPositiveExitStatement := by
  intro D t u hpath hmax
  by_contra hsink
  obtain ⟨l, hlen, ht⟩ := hpath.exists_trace
  by_cases hnil : l = []
  · subst l
    simp at hlen
    subst t
    have hu : u = D.x := by simpa using ht.execute_eq.symm
    subst u
    exact hsink D.initial_positive_firing
  cases l with
  | nil => contradiction
  | cons first rest =>
      have hprefix : [first] <+: first :: rest := ⟨rest, by simp⟩
      obtain ⟨v, hv⟩ := ht.prefix_trace hprefix
      have hveq : v = fire D.rows first D.x := by
        rw [← hv.execute_eq]
        rfl
      have hfirstOld : InBox D.upper (fire D.rows first D.x) := by
        rw [← hveq]
        exact hv.endpoint_inBox
      let D' := D.rotate first
      let u' : Point := permutePoint (P21.Nonsymmetric.rotatePerm first) u
      have hpath' := hpath.rotate D first
      change BoxPath D'.upper D'.rows t D'.x u' at hpath'
      obtain ⟨l', hlen', ht'⟩ := hpath'.exists_trace
      have hne' : l' ≠ [] := by
        intro he
        subst l'
        simp at hlen'
        simp at hlen
        omega
      have hfirstRot : InBox D'.upper (fire D'.rows 0 D'.x) := by
        have hpbox := (inBox_permute_iff D first _).mpr hfirstOld
        rw [permutePoint_fire D first first] at hpbox
        fin_cases first <;> simpa [D', BoxInput.rotate, permutePoint, P21.Nonsymmetric.rotatePerm,
          P21.Nonsymmetric.cyclePerm, P21.Nonsymmetric.next, P21.Nonsymmetric.prev] using hpbox
      have hhead : ∃ b, l' = 0 :: b := ht'.head_zero D' hne' hfirstRot
      have hp' := ht'.properNonzeroPredecessors D'
        (D'.start_of_row0 hfirstRot).1 (Or.inr hhead)
      have hstart' := (D'.start_of_row0 hfirstRot).1
      have hsink' : ¬ ∃ k, ∀ j, 1 ≤ fire D'.rows k u' j := by
        rintro ⟨k, hk⟩
        apply hsink
        refine ⟨P21.Nonsymmetric.rotatePerm first k, ?_⟩
        intro j
        have hh := hk ((P21.Nonsymmetric.rotatePerm first).symm j)
        have hfire := congrFun (permutePoint_fire D first
          (P21.Nonsymmetric.rotatePerm first k) u)
          ((P21.Nonsymmetric.rotatePerm first).symm j)
        simp [D', u', permutePoint] at hh hfire
        rw [← hfire] at hh
        simpa [permutePoint] using hh
      exact canonical_trace_sink_impossible D' ht' hne' hstart' hp' hsink'

end P21.Nonsymmetric.ColorCap
