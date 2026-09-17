import P21.Nonsymmetric.ReturnLevels
import P21.Nonsymmetric.Extraction

open P21 P21.Nonsymmetric

-- Only the frozen support inclusion is consumed; equality is not asserted.
example (g : Generators) (s : g.Setting) (F q : ℤ)
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (hq : q ∈ s.semigroup.Q F) : g.D (complement F g.m q) ⊆ g.SH q :=
  (s.key_support_inclusion hF hc hq).2

-- Replacements retain the same element and consume contained coefficients.
example {k : ℕ} (n : Fin k → ℤ) (x : ℤ) (a : ActualFactorization n x)
    (source target : Fin k → ℕ) (hc : ∀ i, source i ≤ a.coeff i)
    (he : value n source = value n target) : ActualFactorization n x :=
  replaceWithinActualFactorization a source target hc he

-- Independent minima are not assumed equal; neither gap is assumed positive.
example (g : Generators) (s : g.Setting) (F qA qB : ℤ)
    (hF : s.semigroup.IsFrobenius F) (D : HerzogCriticalData g)
    (M : MatchedPairData g F D qA qB)
    (A : MinimalReturn g (qA+g.n 0)) (B : MinimalReturn g (qB+g.n 0)) :
    A.L = B.L ∧ A.U = (D.a 1 : ℤ)+B.U ∧ B.V = A.V+D.b 2 :=
  equal_level_matching s hF M A B

-- The same statement remains applicable to either boundary gap zero.
example (g : Generators) (s : g.Setting) (F qA qB : ℤ)
    (hF : s.semigroup.IsFrobenius F) (D : HerzogCriticalData g)
    (M : MatchedPairData g F D qA qB) (_hz : M.gapJ = 0 ∨ M.gapK = 0)
    (A : MinimalReturn g (qA+g.n 0)) (B : MinimalReturn g (qB+g.n 0)) :
    A.L = B.L ∧ A.U = (D.a 1 : ℤ)+B.U ∧ B.V = A.V+D.b 2 :=
  equal_level_matching s hF M A B

-- Every singleton direction is excluded before any terminal argument.
example (g : Generators) (s : g.Setting) (F qA qB q : ℤ)
    (hF : s.semigroup.IsFrobenius F) (hc : s.semigroup.Canonical F g.m)
    (D : HerzogCriticalData g) (M : MatchedPairData g F D qA qB)
    (ha : qA ∈ s.semigroup.Q F) (hb : qB ∈ s.semigroup.Q F)
    (hq : q ∈ s.semigroup.Q F) (i : Fin 3) (hs : IsSingleton g q i) : False :=
  matched_pair_no_singleton s hF hc M ha hb hq i hs
