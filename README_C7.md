# C7 CHAIN core-root

This candidate formalizes publication Section 7 from the actual frozen
`ChainInput`.  It constructs PFIBER, the same-element MAX-I extremum, ROOT0 and
ROOT-BOX, proves strictness and an exact color reversal, and exposes the
oriented `ChainCore` interface.  Four returns retain their actual nonnegative
factorizations and positive levels.  The final API contains all caps, slopes,
intrinsic parameters, COMPACT, return-level bounds, SHIFT-NEW and strict-region
FK-STRONG.

The protected mathematical base is commit
`6a1e395736e442bcda33c0da282220c98a444c76`.  Existing Lean source is unchanged;
all mathematical additions are under `P21/Nonsymmetric/Chain/` plus its public
import module.  C7 does not prove CHAIN impossible.  The next frontier is C8.
