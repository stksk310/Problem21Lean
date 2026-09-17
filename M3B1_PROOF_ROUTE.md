# M3B1 proof route

1. Take the exact `MinimumOneStatement` inputs. If k is not one, positivity
   implies k >= 2. All old interfaces remain unchanged.
2. Tail cofiniteness supplies an integer vector of weight m through the frozen
   Bezout theorem. The saturated kernel and socle-row differences express k
   times that vector in the socle matrix, with integer coefficient sum one.
   Kernel saturation alone is never used to infer primitivity.
3. Reduce each multiplied row coefficient modulo k. The resulting integral
   representative has residues a_i in [0,k). If their sum S were between zero
   and k, the identity
   `k*(p+v) = (k-S)*p + sum_i a_i*R_i`
   makes every integer coordinate of p+v positive. Subtracting one in each
   coordinate gives an actual natural-coefficient factorization at level k-S,
   contradicting the original minimum. The class congruence excludes S=0,k.
4. Repeat for the negative class. Complementary residues imply every residue
   is nonzero and k<S<2k, hence AGE: S=k+j. This derives the arithmetic input
   directly, avoiding an unnecessary general convex/lattice bridge.
5. Prove the specialized White theorem internally. AGE forces three binary
   floor-jump sequences to partition the interior positions. If all three
   residues exceed one, sort them and complement the largest. The support of
   that complementary slope is the disjoint union of the other two supports.
   Their first jumps and an interleaving point force two minimum support gaps
   inside one smaller allowed gap, a contradiction. Integer divisions, strict
   endpoints, ties and all six orderings are handled in Lean.
6. A residue equal to one, together with AGE, yields the pair (r,k-r).
   Nonzero classes give gcd(r,k)=1; Bezout constructs positive q<k and ell with
   rq=1+ell*k. Reconstruct the integral source vector z; derive zq algebraically.
7. Cyclically relabel both coordinates and socle rows so the distinguished row
   is row zero. The semigroup, m, original element and actual minimum are
   preserved by the frozen relabeling API.
8. For each color, derive the twelve companion exclusions (z and zq) from the
   actual minimum, obtain the source BA/BB bounds and integral AP/BP slack
   parameters, and invoke the unchanged multiplicity contradiction certificate.
9. Conclude k=1 in `minimum_one_proved`. The DPE-only wrapper supplies this
   proof to the unchanged M3A three-arm theorem.

The source determinant, relative-coset and rational-barycentric empty-simplex
statements are also proved in separate new modules. They remain useful exact
source landmarks even where the streamlined AGE route does not need every lemma.
