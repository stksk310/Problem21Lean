# M3B1 geometry and cyclic AGE review

Reviewer: delegated `m3b1_colors` worker. This worker authored the separate
`ClassArithmetic`, `ColorA`, `ColorB`, and `RotationClosure` modules, but did not
author any of the five modules reviewed below. This is an internal proof review,
not a TRUE AUDIT determination.

Outcome: no blocking mathematical, type-level, or firewall issue found in the
reviewed source. No source edits or repeated compilation were performed for this
review. Unconditional MINBOX and the outstanding scalar White consequence are
outside this finding.

## Coverage and precise findings

1. `P21/Nonsymmetric/ColorCap/MinimumOne/Setup.lean`:
   the two explicit row matrices match the natural source orders and diagonal
   zero pattern. Row weights derive from the frozen cyclic socle identities.
   `socleMatrix_det` explicitly receives tail cofiniteness and calls
   `primitive_generator_formulas`; it does not infer primitive weights from a
   saturated kernel. `socleMatrix_det_level` substitutes the exact original
   factorization equality. No gap, PF, arm, determinant, or White conclusion is
   hidden in an input structure.

2. `P21/Nonsymmetric/ColorCap/MinimumOne/SocleSimplex.lean`:
   `socleMatrix_span_level` applies the frozen integer-kernel spanning theorem
   only after subtracting an actual specified-height row multiple and proving
   that the difference has weight zero. The two color coefficient formulas give
   the requested integer span and coefficient sum exactly. It legitimately
   requires no cofiniteness: it proves a conditional row-span fact, not that the
   weight map is primitive. `socleMatrix_row_lattice` expands divisibility into
   an integer level in the forward direction and computes the weight of the
   signed integer row combination in the reverse direction. It makes no
   semigroup-membership assertion from signed coefficients.

3. `P21/Nonsymmetric/ColorCap/MinimumOne/EmptyTetrahedron.lean`:
   `InSocleSimplex` explicitly uses rational barycentric coordinates. The
   positivity lemma correctly uses integral coordinates, positive apex, zero
   diagonal, and positive off-diagonal entries to show that every point other
   than a row vertex is coordinatewise at least one. The level proof treats
   `ell=k`, `ell=0`, and `0<ell<k` separately. Tail membership at the top face and
   smaller actual levels use the frozen positivity-to-natural-factorization
   lemmas. The final Herzog wrapper derives the gap using `fA_gap`/`fB_gap`;
   the generic helper's explicit gap input is therefore discharged. This is a
   rational-presentation emptiness theorem; a general real convex-hull API is
   not claimed. The cyclic AGE route reviewed here does not require such a
   bridge.

4. `P21/Nonsymmetric/White/RelativeIndex.lean`:
   surjectivity and existence of every residue explicitly derive from
   `tail_bezout_vector hcof`. Uniqueness of a residue does not need primitivity,
   and is correctly separated from existence. The relative quotient statements
   have the required `m != 0` or `m>0`, `k>0` cancellation/range hypotheses.
   The API expresses the index through exact residue representatives, equality
   of cosets, and existence/uniqueness, rather than asserting an unchecked
   abstract quotient cardinality. This is sufficient specialized content for
   the requested route.

5. `P21/Nonsymmetric/White/CyclicClasses.lean`:
   all residue representatives are integer vectors by construction. The exact
   equation is obtained from Euclidean division; no integrality flag is assumed.
   The input `sum t=1` normalizes integer row coordinates, and does not encode a
   White split or a distinguished residue. Its later existence obligation must
   still be discharged using a weight-`m` vector from cofiniteness and the
   integer span theorem applied to its `k` multiple.

   For residue mass `S` with `0<S<k`, the displayed class equation implies
   `k*(p+v)=(k-S)*p+sum a_i R_i`. Since the apex is positive and the rows and
   residues are nonnegative, the integral vector `p+v` is strictly positive.
   Its weight is `s-(k-S)*m`, so the frozen actual-companion lemma gives a
   smaller natural-coefficient factorization of the same `f`. This is the
   correct actuality and SAME-ELEMENT passage. The case `S=k` is excluded by
   `S % k=j` for `0<j<k`; no top-face gap hypothesis is missing.

   Applying the lower bound to both `j` and `k-j`, each zero coordinate would
   force their combined mass to be at most `2*k`, a contradiction. Hence all
   three residues are nonzero, their complementary masses sum to `3*k`, and
   `k<S<2*k`. Together with the exact residue congruence this yields `S=k+j`.
   Thus `cyclic_age_of_minimum` proves precisely the source AGE condition from
   actual minimality without invoking White. It does not yet prove a coordinate
   residue equals one; that separate scalar White step remains necessary.

## Existing verification evidence

The geometry author confirmed successful `verification/lake.ps1 env lean -o`
checks with tool sessions `94478` (Setup), `95484` (SocleSimplex), `35548`
(EmptyTetrahedron including the Herzog wrapper), and `92885` (RelativeIndex
including the final quotient representatives); all returned exit code zero.
These four checks have tool-output evidence rather than separate log files.
The root also reports the successful CyclicClasses check. Their corresponding `.olean` files exist in the
worktree build tree. `verification/m3b1/cyclic-progress.log` records the
`CyclicClasses.lean` check with only unused/deprecated-tactic warnings. The
reviewer also already compiled `RotationClosure.lean` against `Setup.lean` and
the arithmetic modules; that independent importing check succeeded. No tests
were rerun solely for this read-only review. These observations do not replace
the final fresh source build and axiom/regression gates.

`MinimumOne/CyclicInput.lean` was still being assembled and is intentionally
excluded from this review; the transient missing-`WidthOne.olean` message in its
progress log is not a finding against the five reviewed files.

## Reviewed source SHA-256 snapshots

| File | SHA-256 |
| --- | --- |
| `MinimumOne/Setup.lean` | `82757296F5637766E628A9D92D5C969A82BC861263694458C3E09A4C7EA1676F` |
| `MinimumOne/SocleSimplex.lean` | `2BF4215AE7C563988EA49AC4EE81DA753BF85B9D2AC08A92A87DA7D1EFB8C60D` |
| `MinimumOne/EmptyTetrahedron.lean` | `231FF301C64CD5785AA7AA3A2954158931824DB22A511E1C5E69DCFA6CA0F6EF` |
| `White/RelativeIndex.lean` | `7ED0D96134B1B30C588D011BF9E1D305659125889FDCC3DEFDCF512E5D803408` |
| `White/CyclicClasses.lean` | `2BD303E38E717968D61941C2632CF0E41604C9E189DE96AED288C3085C6E062E` |
