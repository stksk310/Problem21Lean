# T6 TYPE II exclusion

This candidate formalizes publication Section 6. It proves the frozen
`TypeIIInput` configuration impossible and adds wrappers that preserve the same
selected four actual values while leaving CHAIN as the sole terminal frontier.

The protected mathematical base is commit
`707d9386037e8bcdec9c9bfb02f95731c9ce2597`. Every mathematical addition is a
new module under `P21/Nonsymmetric/TypeII/`; no pre-existing mathematical Lean
source is modified.

The principal theorem is `P21.Nonsymmetric.TypeIIInput.impossible`. It assumes
only the exact `TypeIIInput` and Frobenius gap hypothesis. It does not assume a
return of `B_j`, canonicality, nonsymmetry, PATH data, or return minimality.
