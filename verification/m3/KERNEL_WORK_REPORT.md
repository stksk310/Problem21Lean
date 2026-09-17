# Critical box and saturated integer kernel: work report

## Owned source and mathematical route

New files only:
- `P21/Nonsymmetric/CriticalBox.lean`
- `P21/Nonsymmetric/Kernel.lean`
- `verification/m3/KernelVerification.lean`

The source is publication Section 4.3 (`publication.txt`, lines 490–505), in
agreement with `section4-readable.md`, Critical-box uniqueness and integer basis.
The proof uses the existing immutable `CriticalRelation` definition, including
its actual least-positive-multiplier field `minimal`.

## Exact results

`critical_le_of_single_positive`: a signed integer relation with exactly one
positive coordinate has that coordinate at least the corresponding critical
multiplier. The proof converts every other coordinate into an actual
nonnegative off-direction factorization and applies `CriticalRelation.minimal`.

`critical_kernel_box_zero`: an integer kernel vector whose every coordinate
lies strictly between the negative and positive critical multipliers is zero.
It uses positivity of the three tail generators and a complete three-coordinate
sign division. It assumes neither nonsymmetry nor Herzog data.

`critical_box_unique`: two nonnegative factorization vectors with equal value
and every coordinate below its own critical multiplier are equal. Their
integer difference satisfies `critical_kernel_box_zero`. This is local box
uniqueness; no global factorization uniqueness is assumed.

`kernelRowJ`, `kernelRowK` are exactly `(a_0,-rho_1,b_2)` and
`(b_0,a_1,-rho_2)` in fixed publication order `(i,j,k)=(0,1,2)`.
`kernelRowJ_mem` and `kernelRowK_mem` prove they are actual integer relations.
`kernel_minor_pos` and `kernel_rows_independent` prove integer independence.

`kernel_span_rat` gives rational spanning using the explicitly positive minor
`rho_1*rho_2-a_1*b_2`. This replaces the source's real-span step with exact
rational elimination; it does not change any hypothesis or conclusion.

`integer_kernel_span` subtracts the integer floors of those rational
coefficients. The residual is an integer kernel vector, and its three
coordinates lie in the strict critical box. Hence it is zero. Thus this proof
establishes integer saturation; no saturation, connectivity, primitive minor,
pairwise coprimality, or lattice index hypothesis is supplied.

`integer_kernel_basis` says every integer kernel vector has a **unique pair of
integer coefficients** in the displayed rows. Together with row membership,
this is the exact algebraic integer-basis property, stronger than rational or
real spanning.

## Input scope

The kernel results take positivity of the actual tail generators and
`HerzogCriticalData g`. That structure has positive natural a/b coefficients,
rho=a+b, the exact critical equations, and actual minimal critical relations.
It does not carry or assume a kernel-basis field. Existence of Herzog data is
owned by the separate Herzog-classification module.

There is no remaining mathematical obligation within Section 4.3 once these
explicit critical-cycle inputs have been supplied. Other M3 obligations are
outside this worker's scope.

## Verification

Final compile and exact declaration/axiom checks are recorded in
`KERNEL_VERIFICATION_LOG.txt`. The check source prints both principal theorem
types and checks all thirteen new declarations. Integration and clean CI are
owned by the root worker.
