# M3B1 theorem map

All abbreviated names below are under `P21.Nonsymmetric`.

| Source requirement | New theorem | Scope |
|---|---|---|
| B.1/B.3 socle matrix | `ColorCap.MinimumOne.socleRows_weight`, `socleMatrix_det_level` | Both natural color matrices; det C = km from hcof and existing primitive formulas |
| Primitive weight and relative index | `White.weight_surjective`, `relative_coset_iff`, `relative_residue_unique`, `residue_realized` | Exact residue/coset characterization, with hcof supplying surjectivity |
| LAT row lattice | `ColorCap.MinimumOne.socleMatrix_span_level`, `socleMatrix_row_lattice` | Integer row coordinates with exact coefficient sum |
| LAT cyclic quotient | `White.relative_level_residue_unique`, `relative_level_residue_realized` | Exactly the k height residues |
| B.3 empty simplex | `ColorCap.MinimumOne.socle_simplex_empty` | Rational barycentric integer points in the affine relative lattice are vertices |
| B.4 AGE | `White.cyclic_age_of_minimum`, `ColorCap.MinimumOne.exists_cyclic_age` | Every nonzero cyclic class, derived from actual minimum |
| Specialized White gate | `White.cyclic_white_proved : White.CyclicWhiteStatement` | Symbolic all-k arithmetic theorem, no external assumption |
| Class/inverse construction | `White.gcd_eq_one_of_nonzero_classes`, `exists_positive_inverse`, `integral_class_of_unit_coordinate` | Derives r, q, ell and integral Z |
| Inverse class Zq | `ColorCap.MinimumOne.inverseClass_identity`, `inverseClass_weight` | Same source rows and original m |
| B.5-B.6 color A | `ColorCap.MinimumOne.colorA_integral_class_contradiction` | All companion failures from actual minimum; AP and frozen certificate |
| B.7 color B | `ColorCap.MinimumOne.colorB_integral_class_contradiction` | Explicit B inequalities/BP and frozen certificate |
| Row normalization | `ColorCap.MinimumOne.rotated_integral_class_contradiction` | Any distinguished row via genuine cyclic relabeling |
| Exact assembly | `ColorCap.MinimumOne.minimum_one_of_cyclic_white` | Intermediate reduction; its White input is discharged below |
| Final MINBOX | `ColorCap.minimum_one_proved : ColorCap.MinimumOneStatement` | Exact unchanged target, zero extra assumptions |
| Residual frontier | `ColorCap.three_arms_impossible_of_dpe` | Only DPE remains as an external mathematical input |

`verification/m3b1/DECLARATIONS.json` lists all new explicit declarations.
The generated kernel inventory and axiom summary also include generated helpers.
Unconditional COLOR-CAP and FULL G4 are not results of this milestone.
