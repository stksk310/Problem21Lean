import P21.Nonsymmetric.Extraction

namespace P21.Nonsymmetric.ExtractionRegression
variable {g : Generators}

/-- PATH regression: the selected four rows, not an exact-cardinality premise,
produce the complete endpoint/ladder input. -/
example (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (l n qL qR : ℤ)
    (hl : 1 ≤ l) (hlb : l < D.b 0) (hn : 1 ≤ n) (hna : n < D.a 2)
    (ha : ∀ t : Fin 4, ![qL,D.fA-n*g.n 2,D.fB-l*g.n 0,qR] t ∈ s.semigroup.Q F)
    (hd : Function.Injective (![qL,D.fA-n*g.n 2,D.fB-l*g.n 0,qR] : Fin 4 → ℤ))
    (hsL : IsSingleton g qL 0) (hsR : IsSingleton g qR 2) :
    Nonempty (PathInput s F D) :=
  path_exact_input s hF hc D l n qL qR hl hlb hn hna ha hd hsL hsR

/-- TYPE II regression includes the derived lambda ≤ b_i and exact singleton
saturation; neither is an additional premise. -/
example (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (l m n qS : ℤ)
    (hl : 1 ≤ l) (hla : l < D.a 0) (hm : 1 ≤ m) (hmb : m < D.b 1)
    (hn : 1 ≤ n) (hna : n < D.a 2)
    (ha : ∀ t : Fin 4, ![qS,D.fA-l*g.n 0,D.fB-m*g.n 1,D.fA-n*g.n 2] t ∈ s.semigroup.Q F)
    (hd : Function.Injective (![qS,D.fA-l*g.n 0,D.fB-m*g.n 1,D.fA-n*g.n 2] : Fin 4 → ℤ))
    (hs : IsSingleton g qS 0) : Nonempty (TypeIIInput s F D) :=
  typeII_exact_input s hF hc D l m n qS hl hla hm hmb hn hna ha hd hs

/-- CHAIN regression supplies only synchronized arm positions; all four
complement identities are extracted inside the theorem. -/
example (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (l m n : ℤ)
    (hl : 1 ≤ l) (hla : l < D.a 0) (hlb : l < D.b 0)
    (hm : 1 ≤ m) (hmb : m < D.b 1) (hn : 1 ≤ n) (hna : n < D.a 2)
    (ha : ∀ t : Fin 4,
      ![D.fB-m*g.n 1,D.fA-l*g.n 0,D.fB-l*g.n 0,D.fA-n*g.n 2] t ∈ s.semigroup.Q F)
    (hd : Function.Injective
      (![D.fB-m*g.n 1,D.fA-l*g.n 0,D.fB-l*g.n 0,D.fA-n*g.n 2] : Fin 4 → ℤ)) :
    Nonempty (ChainInput s F D) :=
  chain_exact_input s hF hc D l m n hl hla hlb hm hmb hn hna ha hd

/-- Strict CHAIN slacks are conclusions of the exact input, not assumptions
on the preceding matched-pair package. -/
example {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g} (C : ChainInput s F D) :
    1 ≤ C.delta ∧ 1 ≤ C.beta ∧ 1 ≤ C.gapJ ∧ 1 ≤ C.alpha := C.all_slacks_positive

/-- Boundary regression: completed BA-W remains actual at shared coefficient
zero. The naive signed expression is not used as an actual factorization. -/
example (D : HerzogCriticalData g) (F l n : ℤ)
    (hlb : l < D.b 0) (hna : n < D.a 2)
    (hcB : complement F g.m (D.fB-l*g.n 0) = (D.a 2-n)*g.n 2) :
    W F g.m ∈ g.H := by
  have ⟨he,h0,h1,h2⟩ := mixed_right_completed_W D F l n 0 hlb hna
    (by simpa using hcB)
  rw [he]
  exact herzog_three_mem _ _ _ h0 h1 h2

end P21.Nonsymmetric.ExtractionRegression

#print axioms P21.Nonsymmetric.path_exact_input
#print axioms P21.Nonsymmetric.typeII_exact_input
#print axioms P21.Nonsymmetric.chain_exact_input
#print axioms P21.Nonsymmetric.singleton_saturation_last
#print axioms P21.Nonsymmetric.ChainInput.all_slacks_positive
#print axioms P21.Nonsymmetric.same_color_no_two_endpoint_singletons
#print axioms P21.Nonsymmetric.mixed_left_no_first_singleton
#print axioms P21.Nonsymmetric.mixed_left_no_last_singleton

namespace P21.Nonsymmetric.ExtractionRegression
variable {g : Generators}

/-- Incoming CHAIN labels may have independent A/B depths: synchronization is
proved internally before exact scalar extraction. -/
example (s : g.Setting) {F : ℤ}
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (l r m n : ℤ)
    (hl : 1 ≤ l) (hla : l < D.a 0) (hr : 1 ≤ r) (hrb : r < D.b 0)
    (hm : 1 ≤ m) (hmb : m < D.b 1) (hn : 1 ≤ n) (hna : n < D.a 2)
    (ha : ∀ t : Fin 4,
      ![D.fB-m*g.n 1,D.fA-l*g.n 0,D.fB-r*g.n 0,D.fA-n*g.n 2] t ∈ s.semigroup.Q F)
    (hd : Function.Injective
      (![D.fB-m*g.n 1,D.fA-l*g.n 0,D.fB-r*g.n 0,D.fA-n*g.n 2] : Fin 4 → ℤ)) :
    Nonempty (ChainInput s F D) :=
  chain_exact_input_independent s hF hc D l r m n hl hla hr hrb hm hmb hn hna ha hd
end P21.Nonsymmetric.ExtractionRegression

#print axioms P21.Nonsymmetric.chain_exact_input_independent
#print axioms P21.Nonsymmetric.actual_matched_depths_equal
