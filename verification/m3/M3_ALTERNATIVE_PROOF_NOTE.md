# Equivalent local proof choices in M3

The nonsymmetric standard input is proved directly through critical relations
and a two-rectangle Apéry domain. No arbitrary affine-semigroup presentation
theory is required. The complete proof route is recorded in
HERZOG_WORK_REPORT.md.

For publication Section 4.7's nonmembership of the two positive-m returns in H,
ReturnLevels uses the already-proved Herzog PF gap: the return is
f_epsilon-(depth-1)*n_i with depth >= 1. If it belonged to H, adding the removed
nonnegative generator copies would put f_epsilon in H. This is equivalent to
the required conclusion and uses no stronger hypothesis. Criticality was
already used to prove that f_epsilon is a gap in the exact Herzog package.

For Section 4.9, the Lean proof combines the signed intermediate W identity
with the completed relation algebraically before constructing a factorization.
It directly verifies nonnegativity of the final F coefficients, preserving
both zero-slack boundary cases. No signed intermediate expression is treated
as an actual factorization.

These choices do not replace, assume, or discharge the separate Appendix-B
White input or color-cap theorem.
