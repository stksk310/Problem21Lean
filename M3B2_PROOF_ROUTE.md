# M3B2 proof route

1. Convert the actual `BoxPath` to an endpoint-equal chronological
   `FiringTrace`. Rotate by its actual first firing and derive START.
2. Obtain chronological successful prefixes and the LR/ELR separator bounds.
3. For reciprocal rank, map every shifted residue to an actual original trace
   prefix. Treat `K_s < Q`, `K_s = Q`, and the initial-run `K_s = 1` case.
4. Exclude one-color terminals with the frozen B.16 theorem.
5. Exclude every B.17 `{1,2}` sink/last-firing case, including `X = 0` and
   the `X < 0, D < 0` predecessor/PREFIX branch.
6. Independently exclude every B.18 `{1,3}` case.
7. Split at the first actual occurrence of the third color and prove both
   `{1,2} -> 3` and `{1,3} -> 2` contradictions without a firing-order premise.
8. Exhaust trace colors and transport the canonical contradiction back through
   the cyclic permutation to prove `box_positive_exit_proved`.
9. Compose DPE with frozen `minimum_one_proved` and the frozen residual
   reductions in a new wrapper module.

Actual/nonnegative factorizations remain distinct from signed row identities.
Weighted certificates prove coefficientwise nonnegativity before use. The
existing `BoxPath` SAME-F route is unchanged.
