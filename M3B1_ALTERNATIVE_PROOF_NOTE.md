# Specialized arithmetic White route

The mathematical result being replaced is the width-one/2+2-split/class
normalization part of publication Appendix B.4. For MINBOX, the proof needs
exactly a unit coordinate in the cyclic class of height one, followed by the
integral vector Z and modular inverse. It does not need a reusable theorem
about every real-lattice tetrahedron.

`White.CyclicWhiteStatement` says, for every integer k>1 and triple with
0<a_i<k, that the identities
`sum_i ((j*a_i)%k)=k+j` for every 0<j<k imply some a_i=1.
`White.cyclic_white_proved` proves this proposition by the elementary
floor-jump support argument. It has no unproved White, functional, volume,
class, coprimality or simplex-emptiness input.

`exists_cyclic_age` derives those hypotheses from exactly the existing MINBOX
inputs. The primitive weight comes from hcof, integral row coordinates from
the frozen kernel, and the age identities from actual smaller-level exclusions.
`integral_class_of_unit_coordinate` then constructs the original Z formula;
the other residues sum to k, and coprimality/inverse construction are proved.
Thus the replacement reaches the same class data used in the publication.

The independent `socle_simplex_empty` theorem also formalizes the source
emptiness argument for rational barycentric coordinates. No unproved bridge
from that specialized statement to a general real convex-hull API is used.
No stronger hidden hypothesis enters the final `MinimumOneStatement` theorem.
