import P21.Nonsymmetric.ColorCap.PrefixArithmetic

namespace P21.Nonsymmetric.ColorCap

/-- Execute a chronological list of row firings. -/
def execute (C : Fin 3 → Point) : List (Fin 3) → Point → Point
  | [], u => u
  | i :: is, u => execute C is (fire C i u)

@[simp] theorem execute_nil (C : Fin 3 → Point) (u : Point) : execute C [] u = u := rfl

@[simp] theorem execute_cons (C : Fin 3 → Point) (i : Fin 3)
    (is : List (Fin 3)) (u : Point) :
    execute C (i :: is) u = execute C is (fire C i u) := rfl

theorem execute_append (C : Fin 3 → Point) (l r : List (Fin 3)) (u : Point) :
    execute C (l ++ r) u = execute C r (execute C l u) := by
  induction l generalizing u with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append, execute_cons, ih]

/-- A proposition-valued chronological trace. It carries precisely the same
accepted states as `BoxPath`, while exposing their row labels for finite counting. -/
inductive FiringTrace (upper : Point) (C : Fin 3 → Point) (start : Point) :
    List (Fin 3) → Point → Prop
  | nil : InBox upper start → FiringTrace upper C start [] start
  | snoc {l v} : FiringTrace upper C start l v → (i : Fin 3) →
      InBox upper (fire C i v) → FiringTrace upper C start (l ++ [i]) (fire C i v)

/-- A trace is obtained existentially from the actual path proof; it is not an input. -/
theorem BoxPath.exists_trace {upper : Point} {C : Fin 3 → Point}
    {t : ℕ} {u v : Point} (h : BoxPath upper C t u v) :
    ∃ l, l.length = t ∧ FiringTrace upper C u l v := by
  induction h with
  | nil hb => exact ⟨[], rfl, FiringTrace.nil hb⟩
  | @snoc t u v h i hi ih =>
      obtain ⟨l, hlen, hl⟩ := ih
      exact ⟨l ++ [i], by simp [hlen], FiringTrace.snoc hl i hi⟩

theorem FiringTrace.execute_eq {upper : Point} {C : Fin 3 → Point}
    {l : List (Fin 3)} {u v : Point} (h : FiringTrace upper C u l v) :
    execute C l u = v := by
  induction h with
  | nil _ => rfl
  | snoc h i hi ih => simp [execute_append, ih]

theorem FiringTrace.toBoxPath {upper : Point} {C : Fin 3 → Point}
    {l : List (Fin 3)} {u v : Point} (h : FiringTrace upper C u l v) :
    BoxPath upper C l.length u v := by
  induction h with
  | nil hb => exact BoxPath.nil hb
  | snoc h i hi ih => simpa using BoxPath.snoc ih i hi

/-- Prefix closure at the trace-relation level. -/
theorem FiringTrace.prefix_trace {upper : Point} {C : Fin 3 → Point}
    {full : List (Fin 3)} {u v : Point} (h : FiringTrace upper C u full v)
    {l : List (Fin 3)} (hl : l <+: full) :
    ∃ w, FiringTrace upper C u l w := by
  induction h with
  | nil hb =>
      have : l = [] := List.prefix_nil.mp hl
      subst l
      exact ⟨u, FiringTrace.nil hb⟩
  | @snoc full v h i hi ih =>
      have hp : full <+: full ++ [i] := List.prefix_append _ _
      rcases List.prefix_or_prefix_of_prefix hl hp with hprev | hprev
      · exact ih hprev
      · have hle := hl.length_le
        have hge := hprev.length_le
        by_cases heq : l.length = full.length
        · have hel : full = l := hprev.eq_of_length heq.symm
          subst l
          exact ih (by rfl)
        · have hle' : l.length ≤ full.length + 1 := by simpa using hle
          have hlen : l.length = (full ++ [i]).length := by simp; omega
          have hall : l = full ++ [i] := hl.eq_of_length hlen
          subst l
          exact ⟨_, FiringTrace.snoc h i hi⟩

/-- Every list prefix of the extracted trace is backed by an actual `BoxPath`. -/
theorem FiringTrace.prefix_path {upper : Point} {C : Fin 3 → Point}
    {full : List (Fin 3)} {u v : Point} (h : FiringTrace upper C u full v)
    {l : List (Fin 3)} (hl : l <+: full) :
    ∃ w, BoxPath upper C l.length u w ∧ execute C l u = w := by
  obtain ⟨w,hw⟩ := h.prefix_trace hl
  exact ⟨w,hw.toBoxPath,hw.execute_eq⟩

/-- The endpoint depends only on the genuine row counts in the trace. -/
theorem FiringTrace.endpoint_eq_sub_sum {upper : Point} {C : Fin 3 → Point}
    {l : List (Fin 3)} {u v : Point} (h : FiringTrace upper C u l v) (j : Fin 3) :
    v j = u j - ∑ i, (l.count i : ℤ) * C i j := by
  induction h with
  | nil hb => simp
  | @snoc l v h i hi ih =>
      rw [show fire C i v j = v j - C i j by rfl, ih]
      fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_succ] <;> ring

end P21.Nonsymmetric.ColorCap
