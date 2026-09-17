# M3B1 integration review: cyclic White proof, reconstruction, both colors, and final MINBOX

Reviewer: delegated `m2_stable_core` worker, independently reviewing M3B1. The reviewer authored none of the M3B1 Lean proofs covered here. Prior work by this worker was confined to a different M2 worktree and is not part of this review.

Disposition: **no blocking statement-strength, mathematical-integration, or actuality-firewall defect found in the reviewed snapshot**. This is an internal source review, not a TRUE AUDIT determination. No Lean source was edited and no previously successful compilation or test was repeated.

The final reviewed endpoint is exactly:

```lean
ColorCap.minimum_one_proved : ColorCap.MinimumOneStatement
```

Its proof composes `minimum_one_of_cyclic_white` with the internally proved `White.cyclic_white_proved : White.CyclicWhiteStatement`. The former conditional reduction has no residual White premise at this final endpoint. The companion `three_arms_impossible_of_dpe` wrapper supplies MINBOX to the frozen residual theorem and retains `BoxPositiveExitStatement` as its only residual mathematical input. This does not prove DPE, unconditional COLOR-CAP, or FULL G4.

Review chronology: the initial pass correctly recorded the scalar White proposition as open. After the coordinating agent reported successful compilation of `WidthOneBeatty.lean`, the scope was extended to its complete proof, all supporting WidthOne arithmetic, and the final wrapper. The current report supersedes the initial conditional-only assessment. No unprovided `WidthOneClosure.lean` is being relied on; the completed proof is in `WidthOneBeatty.lean`.

## Coverage

Full source review:

- `White/CyclicClasses.lean`
- `White/ClassReconstruction.lean`
- `White/ClassData.lean`
- `ColorCap/MinimumOne/CyclicInput.lean`
- `ColorCap/MinimumOne/CyclicReduction.lean`
- `ColorCap/MinimumOne/ColorA.lean`
- `ColorCap/MinimumOne/ColorB.lean`
- `ColorCap/MinimumOne/RotationClosure.lean`
- `White/WidthOne.lean` and `White/WidthOneBeatty.lean`
- `ColorCap/MinimumOneProof.lean`
- `verification/m3b1/StatementRegression.lean` (statement and axiom-check coverage; not rerun)

Additional dependency-interface review, authorized by the coordinating agent: `MinimumOne/ClassArithmetic.lean` (natural row matrices, inverse-class definition, identity and weight). The full floor/Beatty helpers in WidthOne and their complete consumption in WidthOneBeatty were read during the extended review.

The earlier `GEOMETRY_REVIEW.md` was read as separate evidence concerning Setup, SocleSimplex, EmptyTetrahedron, RelativeIndex, and CyclicClasses. To check this integration directly, the reviewer also read the relevant signatures/proofs of `socleMatrix_span_level`, `weight_surjective`, the frozen actual-companion helpers, and the frozen `MinimumOneStatement` definition. The full geometry modules and frozen upstream theory were not re-reviewed wholesale.

Source comparison used `REQUEST.md`, the corrected-primitivity review, and Appendix B readable source sections A1.3--A1.8. This review did not independently re-extract the publication PDF or source ZIP; comparison is against the supplied readable source and frozen Lean interfaces.

## Exact statement and discharge of helper hypotheses

The conditional helper and the final unconditional theorem conclude the existing frozen `MinimumOneStatement` by name. It does not replace it with a weaker local definition. Its introduction order matches the frozen quantifiers, including tail cofiniteness, both colors, positive natural k, the strict box, the exact factorization equality, and actual minimality over natural coefficients.

| Additional helper premise | Derivation in the conditional endpoint |
| --- | --- |
| `k >= 2` | Original `0 < k` plus the contradiction assumption `k != 1`. |
| Positive tail weights and `m < n_i` | `Setting.m_pos` and `Setting.n_gt`. |
| A weight-m integral vector | `weight_surjective hcof g.m`, whose proof invokes `tail_bezout_vector hcof`. |
| Integral row coordinates summing to one | `socleMatrix_span_level` applied to k times that vector at level one, after the exact row-weight identity is proved. |
| AGE and positive, bounded residues in every nonzero class | `cyclic_age_of_minimum`, proved using the original actual minimum. |
| Initial residues `0 < a_i < k` and `sum a_i = k+1` | Class one in `exists_cyclic_age`, followed by `cyclicAge_sum`. |
| A distinguished coordinate equal to one | The conditional helper receives `hwhite`; the final wrapper supplies the internally proved `White.cyclic_white_proved`. |
| `1 <= r < k` | `r = a (next i)` and the already proved strict residue bounds. |
| `gcd(r,k)=1` | `cyclicAge_nonzero` for every nonzero class, followed by `gcd_eq_one_of_nonzero_classes`. |
| `1 <= q < k`, `r*q = 1 + ell*k`, and nonnegative ell | `exists_positive_inverse`, using integer Bezout and the positive residue representative. Nonnegative ell is proved even though the downstream closure does not need to assume it separately. |
| Integral z with the required class identity | `integral_class_of_unit_coordinate`, from the actual integral residue representative and sum identity. |
| Integral inverse class zq and weight q*m | The explicit integer-vector definition `inverseClass` and its identity/weight lemmas. |
| Strict positivity of the opposite Herzog parameters | `HerzogCriticalData.a_pos` and `.b_pos`; no new arm or PF premise. |
| Coarse bounds, six failures, refined BA/BB bounds, and AP/BP parameters | Derived by the corresponding color module, then passed to the frozen parameter-contradiction theorem. |
| Distinguished row numbered zero | A simultaneous cyclic relabeling of rows, coordinates, and actual factorizations, proved in RotationClosure. |

No determinant equation, primitive-weight conclusion, pairwise coprimality, simplex-emptiness certificate, actual-arm premise, PF premise, r/q existence, integrality flag, or companion-failure flag is supplied as an additional premise to `minimum_one_of_cyclic_white`.

## Actuality and same-element checks

1. `classRepresentative` is an integer vector explicitly formed using integer Euclidean quotients. Its exact k-multiple identity follows from Euclidean division. It is never declared to be a semigroup factorization merely because that signed identity holds.

2. In `small_mass_impossible`, nonnegative row/residue coordinates and positive apex coordinates establish positivity of the **integral** vector `p+v`. Its weight is computed from the same socle value. Only then does the proof invoke `positive_companion_failure` at level `k-sum a_i`. The frozen `lower_companion_impossible` explicitly proves `0 <= u_i-1`, converts these coefficients to natural numbers, and applies the same supplied `hmin` to the same `f`. Thus the natural-factorization firewall is preserved.

3. Mass equal to k is excluded using the class residue congruence and `0<j<k`; no missing top-face gap premise is silently substituted. The complementary-class argument proves nonvanishing of all three residues and the upper mass bound before obtaining exact AGE.

4. Both `boundsA_of_actual` and `boundsB_of_actual` call `six_companion_failures` with the original `f`, k and actual `hmin`. The inverse class is separately shown to have weight q*m before the same companion theorem is used at q. There is no requirement that q differ from one; k=2 and coincident classes remain included.

5. Rotation transports any new natural coefficient function `x'` back as `x'` composed with the inverse cyclic permutation. `value_relabel` and the unchanged rotated socle values supply the equality needed by the original `hmin`. Natural coefficients remain natural, the same element is retained, and k is unchanged. No signed minimum is substituted.

## Primitivity and cyclic normalization

`exists_cyclic_input` uses tail cofiniteness for the indispensable construction of a vector of weight m. The integer-kernel spanning theorem is used only subsequently, to express its k multiple in the exact row lattice with coefficient sum one. This keeps the two roles distinct and does not confuse a saturated kernel with primitive tail weights. The corrected scaled-tail counterexample cannot pass the required `hcof` premise.

The scalar White gate asks only for some residue coordinate equal to one. Given index i, reconstruction sets `r = a(next i)` and derives `a(prev i)=k-r`, then constructs `z = v-(R(prev i)-p)`. This yields exactly the source Z identity. It imposes no arbitrary ordering of the remaining two vertices. Since their orientation is free in this scalar formulation, choosing `next`/`prev` and performing an honest cyclic rotation suffices. The code therefore does not need an unsupported claim that every arbitrary row permutation preserves color. This is a legitimate specialization of the source's general row-order discussion, not a hidden ordering hypothesis.

## Source correspondence of the color closures

The natural matrices `rowsA` and `rowsB` agree with the source U matrices and the Setup socle rows; equality is explicitly proved in RotationClosure. Color B is treated directly, not discharged by an informal symmetry assertion.

For A, the three class identities give source X/Y/Z with `z=(-X,Y,Z)`. The six actual companion failures feed the frozen BA proof. For the inverse class, the bound on Yq uses the first-class inequality and `r*q=1+ell*k`; it is not assumed. The resulting inputs to `colorA_parameters` are precisely Xq>=p1, Y>=0, Zq>=a3. The actual row weights provide the three equations expected by the frozen A multiplicity certificate.

For B, the identities use `z=(X,-Y,Z)` in the source's natural ordering. The initial inverse coarse bounds intentionally do not assume positivity of Yq. The proof first uses failure of `p+zq` to derive Yq>=p2>0, and only then invokes the complete BB companion argument. The parameters are extracted from Xq>=0, Yq>=p2 and Z>=b3, agreeing with BP. The three corresponding row equations feed the frozen B certificate in their explicit B order.

## Full specialized White proof

`CyclicWhiteStatement` has exactly the general scalar domain required by the reduction: every integer k>1 and every triple with residues strictly between zero and k satisfying AGE for every nonzero class. `cyclic_white_proved` proves that definition by name. It does not introduce coprimality, parity, sortedness, a support-partition flag, a distinguished coordinate, or any bounded-search premise at the public theorem.

The arithmetic proof was checked at the following transitions:

1. The complementary remainder formula handles the divisible case explicitly. AGE for j and k-j then derives `NonzeroClasses` for every coordinate. These properties are not assumptions imported from a White certificate.

2. `floorJump_bounds` proves jumps are zero or one for 0<n<k. AGE is subtracted only at valid adjacent indices `0<j` and `j+1<k`. The proof never extends the jump-sum identity across the excluded endpoints.

3. Both directions of the correspondence between a jump and a rational Beatty support point are proved with strict endpoint bounds. `floorJump_support` uses nonvanishing at j+1 to exclude the upper boundary; `floorJump_of_support` uses nonvanishing at j to exclude the lower boundary. The latter also proves that the resulting support index satisfies `0<j` and `j+1<k` before it can be used in the partition.

4. The complement slope identity `J_(k-n)=1-J_n` requires and receives nonzero remainders at both adjacent indices. `NonzeroClasses` is transported to k-n by a genuine divisibility argument.

5. In `cyclicWhite_sorted_impossible`, sortedness is local to an arbitrary ordering of the original triple. The sum a+b+d=k+1 and nonzero classes are derived from AGE. Assuming every residue exceeds one, the j=1 jump identity rules out 2a<k, while the nonzero class at j=2 rules out 2a=k. Thus k<2a is derived. For e=k-a, the needed d<=b<e and 2e<k follow, including b<e from e=b+d-1 and d>1. These are not extra global hypotheses.

6. In the support partition, jump bounds and the exact partition equality prove disjointness and inclusion of the b and d supports in the e support. The first e point must lie in one component, forcing `floor(k/b)=floor(k/e)`. Coincident first b/d points contradict disjointness; consequently the first b point strictly precedes the first d point. The last-support formula uses nonzero classes to exclude k divisible by the slope; this is proved, not assumed.

7. The last-support identities place the first d point strictly before the last b point. An integer greatest-element theorem, applied to an explicitly nonempty bounded set of b-support indices, locates consecutive b points on either side of that d point. Equality with the right b point is excluded by disjointness. This is a symbolic all-parameter extremum argument, not finite enumeration.

8. Both endpoints and the intermediate d point are e-support points. Strict ordering of their support values gives strict ordering of their indices. Every e gap has size at least L=floor(k/e), whereas a neighboring b gap has size at most floor(k/b)+1=L+1. Since L>=2 is derived from 2e<k, the two e gaps cannot fit inside the b gap. The general partition lemma's displayed hypotheses are all discharged in the sorted caller.

9. The final theorem covers the six weak orders of the three coordinates using `le_total`, including ties. Each permutation preserves AGE by equality of the three-term residue sum. No permutation hypothesis is imposed on the input. If any residue already equals one the theorem is immediate by the contradiction setup; otherwise positivity and integrality give the strict lower bounds needed by the sorted contradiction.

This proves the specialized arithmetic White consequence actually needed by Appendix B's class normalization. It does not purport to formalize the full general geometric theorem for arbitrary real tetrahedra. The request explicitly permits this specialized internal route. A proof-route/alternative note should describe this exact scope, rather than claim an unprovided general width-one API.

## Final composition and verification limitations

`MinimumOneProof.lean` directly supplies `White.cyclic_white_proved` to the already reviewed exact conditional reduction. The public `minimum_one_proved` has no mathematical parameter and its type is the frozen `MinimumOneStatement`, including the corrected hcof premise inside that proposition. Thus no White-class, inverse, emptiness, sortedness, partition, arm or PF premise has escaped into the final target.

`three_arms_impossible_of_dpe` delegates to the unchanged frozen `three_arms_impossible_of_residuals`, supplying the new MINBOX theorem and retaining precisely the original DPE parameter, setting, tail cofiniteness and actual arms. The regression file has exact type examples for both `MinimumOneStatement` and `CyclicWhiteStatement`, the DPE-only wrapper, and explicit axiom-print commands for all three public theorems.

No requested Lean corrections were found. The coordinator reports successful kernel compilation of the integration modules and scalar White proof; the final wrapper's target build was in progress when review was requested. This reviewer did not repeat those builds, run the regression file, or independently execute an all-declaration axiom scan. No new `axiom`, `sorry`, opaque placeholder, or unsafe proof mechanism appears in the reviewed proof text. Final build/axiom results, frozen-source integrity, CI and packaging remain separate project gates and must not be inferred from this source-review finding.
## Source SHA-256 snapshots

Paths below are relative to the worktree root `C:/LeanProjects/Problem21Lean/m3b1-minbox-white`. A changed hash invalidates that file's snapshot coverage until its change is reviewed.

| File | SHA-256 |
| --- | --- |
| P21/Nonsymmetric/White/CyclicClasses.lean | 2BD303E38E717968D61941C2632CF0E41604C9E189DE96AED288C3085C6E062E |
| P21/Nonsymmetric/White/ClassReconstruction.lean | 463D1622E1546A453B3075289141C4B2E1A673F48DA484D5EC4F76C93083CDD3 |
| P21/Nonsymmetric/White/ClassData.lean | 7B938856E7E4874BD53D9756D71AB9D5EBC34B567461D72C64F4B9648B2992C1 |
| P21/Nonsymmetric/ColorCap/MinimumOne/CyclicInput.lean | 80EBB18E1A1A6EB40C6461F8C1E1C739FCDC3A2F08C10D8D7D3B0B76E9E9D25C |
| P21/Nonsymmetric/ColorCap/MinimumOne/CyclicReduction.lean | 4E3B9E0F48B706F3F4FB2DC0CDC19C6A57F1625EBB98E5A022AB4C4CE72E7B99 |
| P21/Nonsymmetric/ColorCap/MinimumOne/ColorA.lean | 8CF016B810D2668D9F2B83DAA2A0512066C9D6A2D4F8209EB13B3963283FD8AB |
| P21/Nonsymmetric/ColorCap/MinimumOne/ColorB.lean | 3176D5F17A7A6B42865080291A2E81085717D1281CA7E7BFB05E5BF7B41C7FAA |
| P21/Nonsymmetric/ColorCap/MinimumOne/RotationClosure.lean | 74DF2073B65DA84D0747D730139AB22B88C1353C637574E374F72029C27B0A3A |
| P21/Nonsymmetric/White/WidthOne.lean | 662AFF345B53949B94AE14B7D2571F4CDE2A932CC2A3FD2D984C8882E3189B27 |
| P21/Nonsymmetric/White/WidthOneBeatty.lean | 2C9BCDF14CC93521D1AFC40C24D52EDD891BD94C3320047DE81C46096A1AB218 |
| P21/Nonsymmetric/ColorCap/MinimumOneProof.lean | 1CDB75BE1E19A9B275F88A7F62F24FE72BC22147F1E08122BECC3EFCE3443038 |
| verification/m3b1/StatementRegression.lean | 7EE15E696E7660ED02691EDBFE130BDAF17174FEDDE87A67B4D08314A028FCE0 |
| P21/Nonsymmetric/ColorCap/MinimumOne/ClassArithmetic.lean | BC986CE7E4EDA95516A0B4261838B198CA4A8602B56B3862FE825CF84C1B9EC6 |
| P21/Nonsymmetric/ColorCap/MinimumOne/SocleSimplex.lean | 2BF4215AE7C563988EA49AC4EE81DA753BF85B9D2AC08A92A87DA7D1EFB8C60D |
| P21/Nonsymmetric/White/RelativeIndex.lean | 7ED0D96134B1B30C588D011BF9E1D305659125889FDCC3DEFDCF512E5D803408 |
| P21/Nonsymmetric/ColorCap/RelativeLattice.lean | AF9A84FA2173C592EB70F07EFE69315ED20263EC9D2A91B24AC14AAEC2AEAF99 |
| P21/Nonsymmetric/ColorCap/Residuals.lean | A74FF340F44A6D739AF3988559A5F13D3A3C9DE50C843FFCD2CE3EAD16953AB6 |
| verification/m3b1/REQUEST.md | 2AF11EC466398C58638A32832664EBAED275F9CA1537F4E61702183385510F2B |
| verification/m3b1/GEOMETRY_REVIEW.md | 04EEF15BA83C2DA9B7C55D6DEF9D87BD06A273B3FFAA6D22E7B397053C4DE897 |
| verification/m3/source/appendixB-readable.md | 0CEFDC031E113399D39DCF7EA3B5141C3C4151A8AB719E5E964139406B26E9D5 |
| verification/m3/REVIEW_CORRECTION_MINBOX.md | 2075C3D9386372828E8F255CD4C26B256C83D1F0B6CE67C118F698D4903D7977 |

