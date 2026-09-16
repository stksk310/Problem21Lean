# Pinned mathlib STD_SYM_GLUE search

Revision: de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11. Search covers all Mathlib/**/*.lean.


## Query
```text
numerical.?semigroup|NumericalSemigroup
```
Exit 1
```text

```


## Query
```text
symmetric.{0,35}semigroup|semigroup.{0,35}symmetric
```
Exit 1
```text

```


## Query
```text
complete.?intersection
```
Exit 0
```text
.lake\packages\mathlib\Mathlib\RingTheory\Extension\Presentation\Basic.lean:103:is a complete intersection.

```


## Query
```text
embedding.?dimension.{0,20}(three|3)|three.?generated
```
Exit 0
```text
.lake\packages\mathlib\Mathlib\Tactic\Translate\Core.lean:43:three generated declarations.

```


## Query
```text
gluing
```
Exit 0
```text
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\StructureSheaf.lean:715:formed by gluing the `openToLocalization` maps. -/
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Sites\SmallAffineZariski.lean:9:public import Mathlib.AlgebraicGeometry.RelativeGluing
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Sites\SmallAffineZariski.lean:250:Under this condition we can construct a family of gluing data (See `relativeGluingData`) and glue
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Sites\SmallAffineZariski.lean:251:`F` into a scheme over `X` via `(relativeGluingData _).glued`,
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Sites\SmallAffineZariski.lean:252:Also see the relative gluing API in `Mathlib/AlgebraicGeometry/RelativeGluing.lean`.
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Sites\SmallAffineZariski.lean:297:/-- The relative gluing data associated to a quasi-coherent `𝒪ₓ` algebra. -/
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Sites\SmallAffineZariski.lean:298:def relativeGluingData {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat}
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Sites\SmallAffineZariski.lean:301:    (AffineZariskiSite.directedCover X).RelativeGluingData where
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Sites\SmallAffineZariski.lean:311:  (relativeGluingData H).instIsLocallyDirectedI₀CompFunctorForgetOfIsThin
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Sites\SmallAffineZariski.lean:318:  exact fun U V ↦ (relativeGluingData H).instIsOpenImmersionMapI₀Functor
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Sites\SmallAffineZariski.lean:320:lemma opensRange_relativeGluingData_map (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Sites\SmallAffineZariski.lean:323:    ((relativeGluingData H).functor.map (homOfLE (U.basicOpen_le r))).opensRange =
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Sites\SmallAffineZariski.lean:332:alias PreservesLocalization.opensRange_map := opensRange_relativeGluingData_map
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Sites\SmallAffineZariski.lean:335:@[deprecated Cover.RelativeGluingData.toBase_preimage_eq_opensRange_ι (since := "2026-02-01")]
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Sites\SmallAffineZariski.lean:339:    (relativeGluingData H).toBase ⁻¹ᵁ U.1 = ((relativeGluingData H).cover.f U).opensRange := by
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Sites\SmallAffineZariski.lean:340:  simpa using! (relativeGluingData H).toBase_preimage_eq_opensRange_ι U
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Sites\SmallAffineZariski.lean:350:  letI D := relativeGluingData (X := X) (.of_isIso (𝟙 _))
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Sites\SmallAffineZariski.lean:355:    Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Sites\SmallAffineZariski.lean:367:        simp [D, relativeGluingData, restrictIsoSpec]
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Sites\Representability.lean:11:public import Mathlib.AlgebraicGeometry.GluingOneHypercover
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Sites\Representability.lean:66:/-- We get a family of gluing data by taking `U i = X i` and `V i j = (hf i).rep.pullback (f j)`. -/
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Sites\Representability.lean:101:  -- This section is obtained from gluing the section corresponding to `f i : Hom(-, X i) ⟶ F`.
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\RelativeGluing.lean:12:# Relative gluing
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\RelativeGluing.lean:14:In this file we show a relative gluing lemma (see https://stacks.math.columbia.edu/tag/01LH):
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\RelativeGluing.lean:60:A relative gluing datum over a locally directed cover `𝒰` of `S` is a scheme `Xᵢ` for every
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\RelativeGluing.lean:71:(see `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.glued`).
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\RelativeGluing.lean:74:structure RelativeGluingData where
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\RelativeGluing.lean:81:variable {𝒰} (d : RelativeGluingData 𝒰)
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\RelativeGluing.lean:83:namespace RelativeGluingData
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\RelativeGluing.lean:97:The glued scheme of a relative gluing datum is the colimit over the `Xᵢ`. For the
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\RelativeGluing.lean:98:structure map, see `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.toBase` and the isomorphisms
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\RelativeGluing.lean:99:with the preimages `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.isPullback_natTrans_ι_toBase`.
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\RelativeGluing.lean:195:end Scheme.Cover.RelativeGluingData
.lake\packages\mathlib\Mathlib\AlgebraicTopology\SimplicialSet\HornColimits.lean:134:/-- The multicoequalizer diagram which expresses `Λ[n, i]` as a gluing
.lake\packages\mathlib\Mathlib\AlgebraicTopology\SimplicialSet\HornColimits.lean:308:/-- The morphism `Λ[3, 1] ⟶ X` which is obtained by gluing three
.lake\packages\mathlib\Mathlib\AlgebraicTopology\SimplicialSet\HornColimits.lean:396:/-- The morphism `Λ[3, 2] ⟶ X` which is obtained by gluing three
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:9:public import Mathlib.AlgebraicGeometry.Gluing
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:17:In this file we construct the fibred product of schemes via gluing.
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:95:`((Xⱼ ×[Z] Y) ×[X] Xₖ) ×[Xⱼ ×[Z] Y] ((Xⱼ ×[Z] Y) ×[X] Xᵢ)` needed for gluing -/
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:199:def gluing : Scheme.GlueData.{u} where
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:219:lemma gluing_ι (j : 𝒰.I₀) :
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:220:    (gluing 𝒰 f g).ι j = Multicoequalizer.π (gluing 𝒰 f g).diagram j := rfl
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:225:def p1 : (gluing 𝒰 f g).glued ⟶ X := by
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:226:  apply Multicoequalizer.desc (gluing 𝒰 f g).diagram _ fun i ↦ pullback.fst _ _ ≫ 𝒰.f i
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:232:def p2 : (gluing 𝒰 f g).glued ⟶ Y := by
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:250:      (gluing 𝒰 f g).V ⟨i, j⟩ := by
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:276:/-- The lifted map `s.X ⟶ (gluing 𝒰 f g).glued` in order to show that `(gluing 𝒰 f g).glued` is
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:286:def gluedLift : s.pt ⟶ (gluing 𝒰 f g).glued := by
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:289:      pullback.map _ _ _ _ (𝟙 _) s.snd f (Category.id_comp _).symm s.condition ≫ (gluing 𝒰 f g).ι i
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:291:  rw [← gluedLiftPullbackMap_fst_assoc, ← gluing_f, ← (gluing 𝒰 f g).glue_condition i j,
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:292:    gluing_t, gluing_f]
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:330:    pullback (pullback.fst (p1 𝒰 f g) (𝒰.f i)) ((gluing 𝒰 f g).ι j) ⟶
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:357:        (gluing 𝒰 f g).ι i =
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:359:  apply Cover.hom_ext ((gluing 𝒰 f g).openCover.pullback₁ (pullback.fst _ _))
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:363:  trans pullbackFstιToV 𝒰 f g i j ≫ fV 𝒰 f g j i ≫ (gluing 𝒰 f g).ι _
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:364:  · rw [← show _ = fV 𝒰 f g j i ≫ _ from (gluing 𝒰 f g).glue_condition j i]
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:367:    rw [gluing_f, gluing_t]
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:384:  · exact pullback.lift ((gluing 𝒰 f g).ι i) (pullback.fst _ _)
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:385:      (by rw [gluing_ι, p1, Multicoequalizer.π_desc])
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:406:    (pullbackP1Iso 𝒰 f g i).inv ≫ pullback.fst _ _ = (gluing 𝒰 f g).ι i := by
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:418:    (pullbackP1Iso 𝒰 f g i).hom ≫ Multicoequalizer.π (gluing 𝒰 f g).diagram i =
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:420:  rw [← gluing_ι, ← pullbackP1Iso_inv_fst, Iso.hom_inv_id_assoc]
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:424:/-- The glued scheme (`(gluing 𝒰 f g).glued`) is indeed the pullback of `f` and `g`. -/
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:435:    PreZeroHypercover.pullback₁_X, PullbackCone.mk_pt, PreZeroHypercover.pullback₁_f, gluing_ι]
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:516:    · let 𝒱 := ((gluing 𝒰.ulift f g).openCover.pushforwardIso
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Pullbacks.lean:522:          GlueData.openCover_I₀, gluing_J]
.lake\packages\mathlib\Mathlib\Combinatorics\SimpleGraph\Regularity\Increment.lean:15:to increase the energy. This file defines the partition obtained by gluing the parts partitions
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ProjectiveSpectrum\StructureSheaf.lean:259:formed by gluing the `openToLocalization` maps. -/
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ProjectiveSpectrum\Basic.lean:10:public import Mathlib.AlgebraicGeometry.Gluing
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Normalization.lean:120:def normalizationGlueData := relativeGluingData f.coequifibered_normalizationDiagramMap
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Normalization.lean:123:  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Normalization.lean:154:  dsimp [normalizationGlueData, relativeGluingData]
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Normalization.lean:354:    dsimp [normalizationOpenCover, normalizationGlueData, relativeGluingData]
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Normalization.lean:390:    dsimp [normalizationGlueData, relativeGluingData]
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Normalization.lean:424:  dsimp [normalizationGlueData, relativeGluingData, restrictIsoSpec]
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Modules\Tilde.lean:744:    have := TopCat.Sheaf.existsUnique_gluing' ⟨_, M.isSheaf⟩ (fun i ↦ basicOpen (g i)) V
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\IdealSheaf\Subscheme.lean:190:/-- (Implementation) The intersections `Spec Γ(𝒪ₓ/I, U) ∩ V` useful for gluing. -/
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\GluingOneHypercover.lean:8:public import Mathlib.AlgebraicGeometry.Gluing
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Gluing.lean:11:public import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Gluing.lean:14:# Gluing Schemes
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Gluing.lean:16:Given a family of gluing data of schemes, we may glue them together.
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Gluing.lean:17:Also see the section about "locally directed" gluing,
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Gluing.lean:22:* `AlgebraicGeometry.Scheme.GlueData`: A structure containing the family of gluing data.
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Gluing.lean:28:  of the glued scheme and the gluing of the underlying topological spaces.
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Gluing.lean:50:All the hard work is done in `Mathlib/Geometry/RingedSpace/PresheafedSpace/Gluing.lean` where we
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Gluing.lean:72:/-- A family of gluing data consists of
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Gluing.lean:166:/-- The gluing as sheafed spaces is isomorphic to the gluing as presheafed spaces. -/
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Gluing.lean:210:/-- The underlying topological space of the glued scheme is isomorphic to the gluing of the
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Gluing.lean:353:/-- The canonical morphism from the gluing of an open cover of `X` into `X`.
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Gluing.lean:446:If `X` is exactly (defeq to) the gluing of `U i`, then using `Multicoequalizer.desc` suffices.
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Gluing.lean:507:## Locally directed gluing
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Gluing.lean:513:For such a diagram, we can glue them directly since the gluing conditions are always satisfied.
.lake\packages\mathlib\Mathlib\AlgebraicTopology\ModelCategory\PathObject.lean:82:/-- The gluing of two pre-path objects. -/
.lake\packages\mathlib\Mathlib\AlgebraicTopology\ModelCategory\PathObject.lean:274:/-- The gluing of two good path objects. -/
.lake\packages\mathlib\Mathlib\Algebra\Colimit\Ring.lean:20:Generalizes the notion of "union", or "gluing", of incomparable rings or fields.
.lake\packages\mathlib\Mathlib\Algebra\Colimit\Ring.lean:52:/-- The direct limit of a directed system is the ring obtained by gluing the components along the
.lake\packages\mathlib\Mathlib\Algebra\Colimit\Module.lean:19:Generalizes the notion of "union", or "gluing", of incomparable modules over the same ring,
.lake\packages\mathlib\Mathlib\AlgebraicTopology\ModelCategory\Cylinder.lean:78:/-- The gluing of two precylinders. -/
.lake\packages\mathlib\Mathlib\AlgebraicTopology\ModelCategory\Cylinder.lean:271:/-- The gluing of two good cylinders. -/
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Cover\Directed.lean:10:public import Mathlib.AlgebraicGeometry.Gluing
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\Cover\Directed.lean:19:Gluing along directed covers is easier, because the intersections `𝒰ᵢ ×[X] 𝒰ⱼ` can
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:8:public import Mathlib.AlgebraicGeometry.RelativeGluing
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:43:/-- The data required for gluing the colimits of the `Dᵢ : J ⥤ P.Over ⊤ (𝒰.X i)`. -/
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:44:structure ColimitGluingData (D : J ⥤ P.Over ⊤ S) (𝒰 : S.OpenCover)
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:52:namespace ColimitGluingData
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:54:variable {D} {𝒰} (d : ColimitGluingData D 𝒰)
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:57:`AlgebraicGeometry.Scheme.Cover.ColimitGluingData.functor`. -/
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:66:`AlgebraicGeometry.Scheme.Cover.ColimitGluingData.functor`. -/
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:74:`AlgebraicGeometry.Scheme.Cover.ColimitGluingData.functor`. -/
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:111:/-- (Implementation): Underlying functor of associated relative gluing datum. -/
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:151:/-- The relative gluing datum associated to the family of the `colim Dᵢ`. -/
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:154:def relativeGluingData : 𝒰.RelativeGluingData where
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:162:/-- The result of gluing the `colim Dᵢ`. -/
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:164:  Over.mk _ d.relativeGluingData.toBase <| by
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:168:      ← (d.relativeGluingData.isPullback_natTrans_ι_toBase i).flip.isoPullback_inv_snd,
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:177:  Over.isoMk (d.relativeGluingData.isPullback_natTrans_ι_toBase i).flip.isoPullback.symm
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:183:    colimit.ι d.relativeGluingData.functor i := by
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:202:      exact ((d.cocone i).ι.app a).left ≫ colimit.ι d.relativeGluingData.functor i
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:204:      conv_rhs => rw [← colimit.w d.relativeGluingData.functor hij]
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:226:      ((d.cocone i).ι.app a).left ≫ colimit.ι d.relativeGluingData.functor i := by
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:237:  letI 𝒱 : d.glued.left.OpenCover := d.relativeGluingData.cover
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:290:end ColimitGluingData
.lake\packages\mathlib\Mathlib\AlgebraicGeometry\ColimitsOver.lean:298:  let d : ColimitGluingData D 𝒰 :=
.lake\packages\mathlib\Mathlib\CategoryTheory\Sites\Precoverage\Subsheaf.lean:43:/-- Closure of a family of elements of a presheaf under restriction and gluing of
.lake\packages\mathlib\Mathlib\CategoryTheory\Sites\Precoverage\Subsheaf.lean:53:  /-- Gluing of sections in the closure. -/
.lake\packages\mathlib\Mathlib\MeasureTheory\MeasurableSpace\Embedding.lean:137:section gluing
.lake\packages\mathlib\Mathlib\MeasureTheory\MeasurableSpace\Embedding.lean:168:end gluing
.lake\packages\mathlib\Mathlib\Topology\Sheaves\Stalks.lean:9:public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
.lake\packages\mathlib\Mathlib\Topology\Sheaves\Stalks.lean:34:is the case for most algebraic structures), we have access to the unique gluing API and can prove
.lake\packages\mathlib\Mathlib\Topology\Sheaves\Stalks.lean:610:    obtain ⟨s, s_spec, -⟩ := F.existsUnique_gluing' V U iVU V_cover sf this
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafOfFunctions.lean:9:public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafOfFunctions.lean:52:  isSheaf_of_isSheafUniqueGluing_types _ fun ι U sf hsf => by
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafOfFunctions.lean:53:  -- We use the sheaf condition in terms of unique gluing
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafOfFunctions.lean:72:      -- So we suppose we had some other gluing `t` of our sections
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:12:# The sheaf condition in terms of unique gluings
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:14:We provide an alternative formulation of the sheaf condition in terms of unique gluings.
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:22:compatible family of sections `sf : Π i : ι, F.obj (op (U i))`, there exists a unique gluing
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:26:and `sf j` to `U i ⊓ U j` agree. A section `s : F.obj (op (iSup U))` is a gluing for the
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:29:We show that the sheaf condition in terms of unique gluings is equivalent to the definition
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:63:/-- A section `s` is a gluing for a family of sections `sf` if it restricts to `sf i` on `U i`,
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:66:def IsGluing (sf : ∀ i : ι, ToType (F.obj (op (U i)))) (s : ToType (F.obj (op (iSup U)))) : Prop :=
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:70:The sheaf condition in terms of unique gluings. A presheaf `F : Presheaf C X` satisfies this sheaf
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:72:there exists a unique gluing `s : F.obj (op (iSup U))`.
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:75:`TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing`
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:77:def IsSheafUniqueGluing : Prop :=
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:79:    IsCompatible F U sf → ∃! s : ToType (F.obj (op (iSup U))), IsGluing F U sf s
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:106:theorem isGluing_iff_pairwise {sf s} : IsGluing F U sf s ↔
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:114:theorem IsSheaf.isSheafUniqueGluing_types (h : F.IsSheaf) (sf : ∀ i : ι, F.obj (op (U i)))
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:115:    (cpt : IsCompatible F U sf) : ∃! s : F.obj (op (iSup U)), IsGluing F U sf s := by
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:116:  simp_rw [isGluing_iff_pairwise]
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:122:/-- For type-valued presheaves, the sheaf condition in terms of unique gluings is equivalent to the
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:125:theorem isSheaf_iff_isSheafUniqueGluing_types : F.IsSheaf ↔ F.IsSheafUniqueGluing := by
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:127:    Types.isLimit_iff, IsSheafUniqueGluing, isGluing_iff_pairwise]
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:137:in terms of unique gluings.
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:139:theorem isSheaf_of_isSheafUniqueGluing_types (Fsh : F.IsSheafUniqueGluing) : F.IsSheaf :=
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:140:  (isSheaf_iff_isSheafUniqueGluing_types F).mpr Fsh
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:150:theorem IsSheaf.isSheafUniqueGluing (h : F.IsSheaf) {ι : Type*} (U : ι → Opens X)
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:152:    (cpt : IsCompatible F U sf) : ∃! s : ToType (F.obj (op (iSup U))), IsGluing F U sf s :=
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:153:  ((isSheaf_iff_isSheaf_comp' (forget C) F).mp h).isSheafUniqueGluing_types sf cpt
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:158:preserves limits, the sheaf condition in terms of unique gluings is equivalent to the usual one.
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:160:theorem isSheaf_iff_isSheafUniqueGluing : F.IsSheaf ↔ F.IsSheafUniqueGluing :=
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:162:    (isSheaf_iff_isSheafUniqueGluing_types (F ⋙ forget C))
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:178:/-- A more convenient way of obtaining a unique gluing of sections for a sheaf.
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:180:theorem existsUnique_gluing (sf : ∀ i : ι, ToType (F.1.obj (op (U i))))
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:182:    ∃! s : ToType (F.1.obj (op (iSup U))), IsGluing F.1 U sf s :=
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:183:  IsSheaf.isSheafUniqueGluing F.property U sf h
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:188:theorem existsUnique_gluing' (V : Opens X) (iUV : ∀ i : ι, U i ⟶ V) (hcover : V ≤ iSup U)
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:192:  obtain ⟨gl, gl_spec, gl_uniq⟩ := F.existsUnique_gluing U sf h
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:211:  obtain ⟨gl, -, gl_uniq⟩ := F.existsUnique_gluing U sf sf_compatible
.lake\packages\mathlib\Mathlib\Topology\Sheaves\SheafCondition\UniqueGluing.lean:254:    {sf : ∀ i : ι, ToType (F.1.obj (op (U i)))} (h : IsGluing F.1 U sf s) (hV : ∀ i : ι, U i ≤ V)
.lake\packages\mathlib\Mathlib\CategoryTheory\Sites\Descent\Precoverage.lean:245:that is deduced from `φ` by gluing. -/
.lake\packages\mathlib\Mathlib\CategoryTheory\Sites\DenseSubsite\Basic.lean:227:/-- (Implementation). The morphism `ℱ(X) ⟶ ℱ'(X)` given by gluing the `pushforwardFamily`. -/
.lake\packages\mathlib\Mathlib\Topology\Sheaves\Sheaf.lean:20:gluing `A ⟶ F(U)` compatible with the restriction.
.lake\packages\mathlib\Mathlib\Topology\Sheaves\Sheaf.lean:55:  `A : X`, there exists a unique gluing `A ⟶ F(U)` compatible with the restriction.
.lake\packages\mathlib\Mathlib\Topology\Sheaves\Sheaf.lean:75:5. `TopCat.Presheaf.IsSheafUniqueGluing`:
.lake\packages\mathlib\Mathlib\Topology\Sheaves\Sheaf.lean:78:  a unique gluing `x : F(U)` that restricts to the given elements.
.lake\packages\mathlib\Mathlib\Topology\Sheaves\Sheaf.lean:79:  See `TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing`.
.lake\packages\mathlib\Mathlib\CategoryTheory\Sites\ConcreteSheafification.lean:347:  -- provide the gluing of the given local sections.
.lake\packages\mathlib\Mathlib\CategoryTheory\Sites\ConcreteSheafification.lean:354:  -- The associated gluing will be the candidate section.
.lake\packages\mathlib\Mathlib\CategoryTheory\Sites\ConcreteSheafification.lean:359:  -- Use the separatedness of `P⁺` to prove that this is indeed a gluing of our
.lake\packages\mathlib\Mathlib\Topology\Sheaves\LocalPredicate.lean:10:public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
.lake\packages\mathlib\Mathlib\Topology\Sheaves\LocalPredicate.lean:246:  Presheaf.isSheaf_of_isSheafUniqueGluing_types _ fun ι U sf sf_comp ↦ by
.lake\packages\mathlib\Mathlib\Topology\Sheaves\LocalPredicate.lean:247:    -- We show the sheaf condition in terms of unique gluing.
.lake\packages\mathlib\Mathlib\Topology\Sheaves\LocalPredicate.lean:254:    -- So, we can obtain a unique gluing
.lake\packages\mathlib\Mathlib\Topology\Sheaves\LocalPredicate.lean:255:    obtain ⟨gl, gl_spec, gl_uniq⟩ := (sheafToTypes X T).existsUnique_gluing U sf'
.lake\packages\mathlib\Mathlib\Topology\Sheaves\LocalPredicate.lean:259:    · -- Our first goal is to show that this chosen gluing satisfies the
.lake\packages\mathlib\Mathlib\Topology\Sheaves\LocalPredicate.lean:270:    -- It remains to show that the chosen lift is really a gluing for the subsheaf and
.lake\packages\mathlib\Mathlib\Topology\Sheaves\Flasque.lean:91:  obtain ⟨t, ht, _⟩ : ∃! s_1, IsGluing F.obj f (fun x => x.val.right.2) s_1 := by
.lake\packages\mathlib\Mathlib\Topology\Sheaves\Flasque.lean:92:    refine Sheaf.existsUnique_gluing F _ _ (fun i j ↦ ?_)
.lake\packages\mathlib\Mathlib\Topology\Sheaves\Flasque.lean:151:    obtain ⟨t₅, ht₅, _⟩ : ∃! t₅, IsGluing S.X₂.obj f sf t₅ := by
.lake\packages\mathlib\Mathlib\Topology\Sheaves\Flasque.lean:152:      apply Sheaf.existsUnique_gluing
.lake\packages\mathlib\Mathlib\Topology\Sheaves\CommRingCat.lean:288:noncomputable section Gluing
.lake\packages\mathlib\Mathlib\Topology\Sheaves\CommRingCat.lean:371:end Gluing
.lake\packages\mathlib\Mathlib\Tactic\Module.lean:255:in the obvious way: by forgetting the natural numbers and gluing together the `Expr`s. -/
.lake\packages\mathlib\Mathlib\Data\Set\UnionLift.lean:39:directed union, directed supremum, glue, gluing
.lake\packages\mathlib\Mathlib\Tactic\FieldSimp.lean:53:in the obvious way: by forgetting the natural numbers and gluing together the integers and `Expr`s.
.lake\packages\mathlib\Mathlib\Topology\Metrizable\CompletelyMetrizable.lean:8:public import Mathlib.Topology.MetricSpace.Gluing
.lake\packages\mathlib\Mathlib\Topology\CWComplex\Classical\Basic.lean:19:A CW complex is a topological space that is made by gluing closed disks of different dimensions
.lake\packages\mathlib\Mathlib\Topology\MetricSpace\GromovHausdorffRealized.lean:10:public import Mathlib.Topology.MetricSpace.Gluing
.lake\packages\mathlib\Mathlib\Topology\MetricSpace\GromovHausdorff.lean:532:coupling between the two spaces, by gluing them (approximately) along the two matching subsets. -/
.lake\packages\mathlib\Mathlib\Topology\MetricSpace\GromovHausdorff.lean:900:`Y 1` (with an embedding of `X 1`). Then, consider an optimal gluing of `X 1` and `X 2`, and
.lake\packages\mathlib\Mathlib\Topology\MetricSpace\GromovHausdorff.lean:912:structure AuxGluingStruct (A : Type) [MetricSpace A] : Type 1 where
.lake\packages\mathlib\Mathlib\Topology\MetricSpace\GromovHausdorff.lean:918:attribute [local instance] AuxGluingStruct.metric
.lake\packages\mathlib\Mathlib\Topology\MetricSpace\GromovHausdorff.lean:920:instance (A : Type) [MetricSpace A] : Inhabited (AuxGluingStruct A) :=
.lake\packages\mathlib\Mathlib\Topology\MetricSpace\GromovHausdorff.lean:929:def auxGluing (n : ℕ) : AuxGluingStruct (X n) :=
.lake\packages\mathlib\Mathlib\Topology\MetricSpace\GromovHausdorff.lean:947:  let Y := auxGluing X
.lake\packages\mathlib\Mathlib\Topology\MetricSpace\GromovHausdorff.lean:952:    fun n => by dsimp only [Y, auxGluing]
.lake\packages\mathlib\Mathlib\Topology\MetricSpace\GromovHausdorff.lean:954:  have ic : ∀ n, Isometry (c n) := fun n x y => by dsimp only [Y, auxGluing]; exact rfl
.lake\packages\mathlib\Mathlib\Topology\MetricSpace\Gluing.lean:12:# Metric space gluing
.lake\packages\mathlib\Mathlib\Topology\MetricSpace\Gluing.lean:14:Gluing two metric spaces along a common subset. Formally, we are given
.lake\packages\mathlib\Mathlib\Topology\MetricSpace\Gluing.lean:62:section ApproxGluing
.lake\packages\mathlib\Mathlib\Topology\MetricSpace\Gluing.lean:197:end ApproxGluing
.lake\packages\mathlib\Mathlib\Topology\MetricSpace\Gluing.lean:207:the gluing distance defined above to take advantage of the lemmas we have already proved.
.lake\packages\mathlib\Mathlib\Topology\MetricSpace\Gluing.lean:460:section Gluing
.lake\packages\mathlib\Mathlib\Topology\MetricSpace\Gluing.lean:462:-- Exact gluing of two metric spaces along isometric subsets.
.lake\packages\mathlib\Mathlib\Topology\MetricSpace\Gluing.lean:487:/-- The canonical map from `X` to the space obtained by gluing isometric subsets in `X` and `Y`. -/
.lake\packages\mathlib\Mathlib\Topology\MetricSpace\Gluing.lean:491:/-- The canonical map from `Y` to the space obtained by gluing isometric subsets in `X` and `Y`. -/
.lake\packages\mathlib\Mathlib\Topology\MetricSpace\Gluing.lean:518:end Gluing --section
.lake\packages\mathlib\Mathlib\Topology\ContinuousMap\Basic.lean:355:section Gluing
.lake\packages\mathlib\Mathlib\Topology\ContinuousMap\Basic.lean:410:end Gluing
.lake\packages\mathlib\Mathlib\Analysis\Calculus\ContDiff\Defs.lean:52:numbers, but they are designed to circumvent the lack of gluing properties and partitions of unity
.lake\packages\mathlib\Mathlib\CategoryTheory\LocallyDirected.lean:11:## Locally directed gluing
.lake\packages\mathlib\Mathlib\CategoryTheory\LocallyDirected.lean:18:gluing of the open sets. See `Mathlib/AlgebraicGeometry/Gluing.lean` for an actual application.
.lake\packages\mathlib\Mathlib\Topology\Gluing.lean:16:# Gluing Topological spaces
.lake\packages\mathlib\Mathlib\Topology\Gluing.lean:18:Given a family of gluing data (see `Mathlib/CategoryTheory/GlueData.lean`), we can then glue them
.lake\packages\mathlib\Mathlib\Topology\Gluing.lean:26:* `TopCat.GlueData`: A structure containing the family of gluing data.
.lake\packages\mathlib\Mathlib\Topology\Gluing.lean:67:/-- A family of gluing data consists of
.lake\packages\mathlib\Mathlib\Topology\Gluing.lean:270:/-- A family of gluing data consists of
.lake\packages\mathlib\Mathlib\Topology\Gluing.lean:429:/-- The gluing of an open cover is homeomorphic to the original space. -/
.lake\packages\mathlib\Mathlib\Topology\FiberBundle\Basic.lean:37:of the bundle and its topology by a suitable gluing construction. The main content of this file is
.lake\packages\mathlib\Mathlib\Topology\FiberBundle\Basic.lean:120:The fiber above `x` is the disjoint union of `F` over all trivializations, modulo the gluing
.lake\packages\mathlib\Mathlib\Topology\FiberBundle\Basic.lean:128:gluing and quotienting construction above, and to declare above each `x` that the fiber is `F`,
.lake\packages\mathlib\Mathlib\CategoryTheory\GlueData.lean:15:# Gluing data
.lake\packages\mathlib\Mathlib\CategoryTheory\GlueData.lean:36:/-- A gluing datum consists of
.lake\packages\mathlib\Mathlib\CategoryTheory\GlueData.lean:52:  /-- The index type `J` of a gluing datum -/
.lake\packages\mathlib\Mathlib\CategoryTheory\GlueData.lean:163:/-- The glued object given a family of gluing data. -/
.lake\packages\mathlib\Mathlib\CategoryTheory\GlueData.lean:296:/-- If `F` preserves the gluing, we obtain an iso between the glued objects. -/
.lake\packages\mathlib\Mathlib\CategoryTheory\GlueData.lean:312:/-- If `F` preserves the gluing, and reflects the pullback of `U i ⟶ glued` and `U j ⟶ glued`,
.lake\packages\mathlib\Mathlib\Probability\Kernel\IonescuTulcea\Maps.lean:26:/-- Gluing `Ioc a b` and `Ioc b c` into `Ioc a c`. -/
.lake\packages\mathlib\Mathlib\Probability\Kernel\IonescuTulcea\Maps.lean:42:/-- Gluing `Iic a` and `Ioc a b` into `Iic b`. If `b < a`, this is just a projection on the first
.lake\packages\mathlib\Mathlib\Probability\Kernel\IonescuTulcea\Maps.lean:93:/-- Gluing `Iic a` and `Ioc a b` into `Iic b`. This version requires `a ≤ b` to get a measurable
.lake\packages\mathlib\Mathlib\Probability\Kernel\IonescuTulcea\Maps.lean:120:/-- Gluing `Iic a` and `Ioi a` into `ℕ`, version as a measurable equivalence
.lake\packages\mathlib\Mathlib\Geometry\RingedSpace\PresheafedSpace\Gluing.lean:8:public import Mathlib.Topology.Gluing
.lake\packages\mathlib\Mathlib\Geometry\RingedSpace\PresheafedSpace\Gluing.lean:13:# Gluing structured spaces
.lake\packages\mathlib\Mathlib\Geometry\RingedSpace\PresheafedSpace\Gluing.lean:15:Given a family of gluing data of structured spaces (presheafed spaces, sheafed spaces, or locally
.lake\packages\mathlib\Mathlib\Geometry\RingedSpace\PresheafedSpace\Gluing.lean:23:* `AlgebraicGeometry.PresheafedSpace.GlueData`: A structure containing the family of gluing data.
.lake\packages\mathlib\Mathlib\Geometry\RingedSpace\PresheafedSpace\Gluing.lean:43:this is an open embedding of topological spaces follows from `Mathlib/Topology/Gluing.lean`, and it
.lake\packages\mathlib\Mathlib\Geometry\RingedSpace\PresheafedSpace\Gluing.lean:46:sheaves of the spaces in the gluing diagram, we need to construct a map
.lake\packages\mathlib\Mathlib\Geometry\RingedSpace\PresheafedSpace\Gluing.lean:47:`ιInvApp_π_app : Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_V, U_V)` for each `V` in the gluing diagram.
.lake\packages\mathlib\Mathlib\Geometry\RingedSpace\PresheafedSpace\Gluing.lean:79:/-- A family of gluing data consists of
.lake\packages\mathlib\Mathlib\Geometry\RingedSpace\PresheafedSpace\Gluing.lean:322:/-- (Implementation) We construct the map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_V, U_V)` for each `V` in the gluing
.lake\packages\mathlib\Mathlib\Geometry\RingedSpace\PresheafedSpace\Gluing.lean:543:/-- A family of gluing data consists of
.lake\packages\mathlib\Mathlib\Geometry\RingedSpace\PresheafedSpace\Gluing.lean:581:/-- The gluing as sheafed spaces is isomorphic to the gluing as presheafed spaces. -/
.lake\packages\mathlib\Mathlib\Geometry\RingedSpace\PresheafedSpace\Gluing.lean:619:/-- A family of gluing data consists of
.lake\packages\mathlib\Mathlib\Geometry\RingedSpace\PresheafedSpace\Gluing.lean:654:/-- The gluing as locally ringed spaces is isomorphic to the gluing as ringed spaces. -/
.lake\packages\mathlib\Mathlib\Geometry\RingedSpace\Basic.lean:121:    X.sheaf.existsUnique_gluing' V U iVU hcover g ic
.lake\packages\mathlib\Mathlib\Geometry\Manifold\VectorBundle\FiberwiseLinear.lean:155:gluing together the various bi-`C^n` fiberwise linear open partial homeomorphism which exist
.lake\packages\mathlib\Mathlib\Geometry\Manifold\Sheaf\Basic.lean:22:invariant" property is preserved under restriction and gluing.
.lake\packages\mathlib\Mathlib\Geometry\Manifold\Riemannian\PathELength.lean:262:which is convenient for gluing purposes. -/

```


## Query
```text
frobenius.{0,30}symmetr|symmetr.{0,30}frobenius
```
Exit 1
```text

```


## Assessment
No matching formal theorem supplying the symmetric, minimally three-generated numerical-semigroup gluing normal form was located. General gluing results in topology/category theory and ring presentations do not supply the numerical-semigroup classification. This is a searched-source finding, not a theorem that no alternate encoding exists.

`Mathlib/NumberTheory/FrobeniusNumber.lean` supplies `frobeniusNumber_pair`, `Nat.exists_mem_closure_of_ge`, `Nat.addSubmonoid_fg`, and `exists_frobeniusNumber_iff`. These address nonnegative additive closures/Frobenius existence and the two-generator formula, not STD_SYM_GLUE. Integer normal forms, symmetry and the exact 2GI interface are implemented locally.

Gate 0 remains OPEN unless a local classification proof is subsequently completed. No assumption of gluing may be hidden in the meaning of symmetric, and no gluing axiom may be introduced.
