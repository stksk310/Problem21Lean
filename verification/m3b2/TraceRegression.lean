import P21.Nonsymmetric.ColorCap.DPE.Trace

open P21.Nonsymmetric.ColorCap

-- A chronological trace is existentially extracted from the actual BoxPath proof.
example {upper : Point} {C : Fin 3 → Point} {t : ℕ} {u v : Point}
    (h : BoxPath upper C t u v) :
    ∃ l, l.length = t ∧ FiringTrace upper C u l v := h.exists_trace

-- Executing precisely those recorded firings reconstructs the actual endpoint.
example {upper : Point} {C : Fin 3 → Point} {l : List (Fin 3)} {u v : Point}
    (h : FiringTrace upper C u l v) : execute C l u = v := h.execute_eq

-- Every recorded chronological prefix is an actual in-box path state.
example {upper : Point} {C : Fin 3 → Point} {full : List (Fin 3)} {u v : Point}
    (h : FiringTrace upper C u full v) {l : List (Fin 3)} (hl : l <+: full) :
    ∃ w, BoxPath upper C l.length u w ∧ execute C l u = w :=
  h.prefix_path hl
