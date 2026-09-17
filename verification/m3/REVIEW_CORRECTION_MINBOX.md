# Correction to the independent MINBOX review

Date: 2026-09-17. Reviewer: m3_kernel. No Lean source changes made.

## Retraction and confirmed defect

The earlier COLORCAP_INDEPENDENT_REVIEW.md incorrectly reported no statement-level defect in the original `MinimumOneStatement`. That conclusion is withdrawn. Its original quantification omitted tail cofiniteness (equivalently, in this positive finitely generated setting, primitivity of the tail). `g.Setting` supplies cofiniteness of Gamma, not of H. True critical relations and even a saturated integer kernel basis do not supply primitivity of the vector n.

The parent's counterexample is valid at the arithmetic level:

* m=33, n=(70,65,40), a=(2,2,2), b=(1,2,3), rho=(3,4,5).
* Critical equalities are 3*70=2*65+2*40, 4*65=2*70+3*40, and 5*40=70+2*65. Checking all smaller positive multipliers gives no off-direction nonnegative representation. The check was independently enumerated with coefficient bounds exceeding every possible coefficient for these targets.
* fA=2*70+65-40=165=5*33. Taking p=(1,1,1) satisfies 1<=p_i<a_i.
* Any representation 165=33*k+70*x+65*y+40*z forces 5|k. Nonnegativity forces k<=5. At k=0 there is no representation: after division by 5, 33 is not in <14,13,8>. Exhaustive bounded enumeration gives only k=5,x=y=z=0. Thus k=5 is the actual minimum, contradicting the original asserted k=1.
* Gamma is cofinite since it contains <33,40>, and its four generators are irredundant; 33 is its multiplicity. Hence the Setting assumption does not exclude this example. H is contained in 5Z and is not cofinite.

These arithmetic checks support the defect independently; the parent owns the formal Lean regression/correction.

## Correct restriction and its source

Add a premise `(exists B : Z, forall x : Z, B <= x -> x in g.H)` to `MinimumOneStatement` and propagate it to the actual three-arm reduction. This restores an explicit assumption of Appendix B.1, which starts with a nonsymmetric three-generated numerical semigroup H. Appendix B.3 expressly uses primitive n for `[Z^3:L_d]=d`; the determinant/index and relative-volume-k assertions depend on that normalization. A scaled tail preserves the kernel while changing precisely this index computation.

At the actual canonical-Q integration point the restriction is already derivable: `s.tail_cofinite hF hc hQ`. Any selected actual row supplies hQ. It therefore need not become an additional final user assumption. It must nonetheless appear in the local residual statement, because that statement separately quantifies over arbitrary Settings without hF, hc, or Q.

## Reassessment of remaining MINBOX scope

After adding tail cofiniteness, no further missing source premise was identified in this review. Positivity and m<min(n) come from Setting. True least critical multipliers and positive a/b come from HerzogCriticalData. The concrete fA/fB gap and socle row identities are already consequences proved from that data. The local source argument after selection uses a positive least actual m-level and p in the strict a/b box, all supplied explicitly by the residual. Actual arms are used upstream to produce that input and its bounds; they are not needed as an additional premise of this local MINBOX consequence.

This is a scope comparison, not a proof that the corrected residual is true. The relative-lattice geometry, White-class construction, and remaining assembly are still open. In particular, kernel saturation must never again be conflated with gcd(n)=1.

## DPE does not need the same restriction

The current `BoxPositiveExitStatement` has the exact stand-alone scope of Appendix B.10: integral positive x,y,b; C*n=m*1; 0<m<min(n); initial point x; and an actual finite in-box path ending with no in-box firing. The source expressly says neither det(C)=m nor adj(C)*1=n is an additional requirement and that INPUT alone suffices. BoxInput contains precisely these arithmetic assumptions.

No tail cofiniteness, critical minimality, primitive generator formula, or actual arm hypothesis should be added to DPE merely to repair MINBOX. DPE's path begins at x, and the endpoint condition is maximality under in-box continuation, exactly as in the source. Positivity is >=1 for integer coordinates; the upper box bound is x_i+y_i-1, so the boundary conventions agree. No additional missing DPE premise was found. DPE itself remains unproved.

## Status

The first review's descriptions of actual-path factorization tracking, color reversal, and Extraction's selected-value transport are unaffected by this correction. Its claim that the original two residuals had correct mathematical scope is superseded here. The corrected two-input conditional reduction must be freshly rebuilt and its exact public types audited after propagation; no fresh-build claim is made by this document.
