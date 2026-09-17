# Direct three-generator rigidity route

Let H = <x,y,z> be a positive, cofinite, irredundant three-generator
integer semigroup, symmetric about f. Put T=f+x. The proof is an elementary
Apéry-set argument. No complete-intersection theorem or external classification
is an assumption.

## Common foundation

Ap(H,x) consists of h in H with h-x outside H. Symmetry supplies T in Ap(H,x)
and T-h in Ap(H,x) for every h in Ap(H,x). Every representation of an Apéry
element has zero x-coordinate. Thus its representations use y,z only.
Residues modulo x give a bijection Ap(H,x) with the x integer residues.

## Multiple top representations

Write y=d*u,z=d*v where d=gcd(y,z) and gcd(u,v)=1. Irredundancy proves u,v>=2.
Two distinct nonnegative y,z representations of T differ by a nonzero multiple
of the primitive relation v*y=u*z. One representation therefore contains the
pure common multiple d*u*v. The Apéry downset property shows
d*u*v-x is outside H.

If x were outside <u,v>, the already proved two-generator symmetry theorem
would give uv-u-v-x=a*u+b*v for a,b>=0. Consequently

    d*u*v-x = a*(d*u)+b*(d*v)+(d*u)+(d*v)+(d-1)*x

would belong to H, contradiction. Thus x has an actual nonnegative expression
in u,v. The gcd decomposition module constructs the frozen gluing structure.

## Unique top representation

Suppose T=A*y+B*z has exactly one nonnegative y,z representation. Complementing
an arbitrary Apéry element against T shows that all its coefficients satisfy
0<=a<=A and 0<=b<=B. Conversely each such subexpression lies in Ap(H,x), since
otherwise adding its remaining top coefficients would put T-x in H.
Uniqueness of the top also proves injectivity of this rectangle of values.

Put L=A+1 and M=B+1. Counting residues yields x=L*M. Reducing L*y and M*z to
their Apéry representatives gives the boundary equations

    L*y=q*x+b*z,     M*z=r*x+a*y,

where q,r>0, 0<=a<L and 0<=b<M. The same-axis coefficients vanish: a positive
same-axis coefficient would put a rectangle point minus x in H.

The determinant D=L*M-a*b satisfies x|D*y and x|D*z. The explicitly constructed
three-generator Bezout witness gives x|D. Since 0<D<=L*M=x, we obtain D=x,
hence a*b=0.

If a=0, cancellation in the boundary equations gives

    x=L*M,    z=L*r,    y=q*M+b*r.

This is actual gluing data with d=L, primitive pair M,r and remaining
generator y. A common divisor of M,r divides all x,y,z, so gcd(M,r)=1.
All required lower bounds follow from positivity and irredundancy. If b=0,
exchange the rectangle axes and apply the same argument. The permutation is
constructed explicitly with Equiv.swap.

## Lean implementation

- SymmetricRigidity.lean proves nonnegative monoid multiplication, the pure
  common-multiple gap criterion, determinant divisibility and zero-boundary
  arithmetic, the rectangle characterization, and boundary reduction.
- UniqueTop.lean applies these to the actual tail and proves
  unique_top_glue_data with no supplied cardinality, gcd, or boundary assumptions.
- AperyCardinality.lean provides the explicit residue count.
- TopFactorization.lean supplies the multiple-representation alternative.
- GcdDecomposition.lean constructs every field of SymmetricGlueData.

The classical Herzog theorem motivated the target, but is not used in any
proof term. Online route audit found the research literature's three-generator
symmetry/complete-intersection characterization and rectangular Apéry
descriptions; the proof above is recorded independently so each mathematical
step can be checked against its Lean declaration.
