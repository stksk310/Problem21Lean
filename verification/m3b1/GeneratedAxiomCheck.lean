import P21.Nonsymmetric.ActualClassification
import P21.Nonsymmetric.ActualLabels
import P21.Nonsymmetric.ActualMixed
import P21.Nonsymmetric.Arms
import P21.Nonsymmetric.ColorCap.ActualMinimum
import P21.Nonsymmetric.ColorCap.BoxInput
import P21.Nonsymmetric.ColorCap.BoxPaths
import P21.Nonsymmetric.ColorCap.CompanionBounds
import P21.Nonsymmetric.ColorCap.DPEOneColor
import P21.Nonsymmetric.ColorCap.PositiveMinors
import P21.Nonsymmetric.ColorCap.PrefixArithmetic
import P21.Nonsymmetric.ColorCap.RelativeLattice
import P21.Nonsymmetric.ColorCap.Residuals
import P21.Nonsymmetric.ColorCap.ThreeArms
import P21.Nonsymmetric.ColorCap.WhiteCertificates
import P21.Nonsymmetric.ComplementGeometry
import P21.Nonsymmetric.Corners
import P21.Nonsymmetric.CriticalBox
import P21.Nonsymmetric.Extraction
import P21.Nonsymmetric.FourRowCombinatorics
import P21.Nonsymmetric.Herzog.PseudoFrobenius
import P21.Nonsymmetric.HerzogClassification
import P21.Nonsymmetric.HerzogCoordinates
import P21.Nonsymmetric.HerzogData
import P21.Nonsymmetric.Kernel
import P21.Nonsymmetric.MatchedPair
import P21.Nonsymmetric.MixedColor
import P21.Nonsymmetric.PrimitiveGenerators
import P21.Nonsymmetric.Relabel
import P21.Nonsymmetric.ReturnLevels
import P21.Nonsymmetric.RowAtlas
import P21.Nonsymmetric.Rows
import P21.Nonsymmetric.SameColor
import P21.Nonsymmetric.Saturation
import P21.Nonsymmetric.SelectedExtraction
import P21.Nonsymmetric.Singletons
import P21.Nonsymmetric.ColorCap.MinimumOne.ClassArithmetic
import P21.Nonsymmetric.ColorCap.MinimumOne.ColorA
import P21.Nonsymmetric.ColorCap.MinimumOne.ColorB
import P21.Nonsymmetric.ColorCap.MinimumOne.CyclicInput
import P21.Nonsymmetric.ColorCap.MinimumOne.CyclicReduction
import P21.Nonsymmetric.ColorCap.MinimumOne.EmptyTetrahedron
import P21.Nonsymmetric.ColorCap.MinimumOne.RotationClosure
import P21.Nonsymmetric.ColorCap.MinimumOne.Setup
import P21.Nonsymmetric.ColorCap.MinimumOne.SocleSimplex
import P21.Nonsymmetric.ColorCap.MinimumOneProof
import P21.Nonsymmetric.White.ClassData
import P21.Nonsymmetric.White.ClassReconstruction
import P21.Nonsymmetric.White.CyclicClasses
import P21.Nonsymmetric.White.RelativeIndex
import P21.Nonsymmetric.White.WidthOne
import P21.Nonsymmetric.White.WidthOneBeatty

set_option linter.auxLemma false
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.InSocleSimplex
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.barycentric_weight
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsA_of_actual
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsA_of_actual._proof_1_10
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsA_of_actual._proof_1_11
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsA_of_actual._proof_1_12
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsA_of_actual._proof_1_13
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsA_of_actual._proof_1_14
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsA_of_actual._proof_1_15
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsA_of_actual._proof_1_16
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsA_of_actual._proof_1_17
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsA_of_actual._proof_1_18
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsA_of_actual._proof_1_19
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsA_of_actual._proof_1_2
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsA_of_actual._proof_1_3
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsA_of_actual._proof_1_4
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsA_of_actual._proof_1_5
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsA_of_actual._proof_1_6
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsA_of_actual._proof_1_7
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsA_of_actual._proof_1_8
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsA_of_actual._proof_1_9
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsB_of_actual
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsB_of_actual._proof_1_10
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsB_of_actual._proof_1_11
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsB_of_actual._proof_1_12
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsB_of_actual._proof_1_13
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsB_of_actual._proof_1_14
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsB_of_actual._proof_1_15
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsB_of_actual._proof_1_16
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsB_of_actual._proof_1_17
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsB_of_actual._proof_1_18
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsB_of_actual._proof_1_19
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsB_of_actual._proof_1_2
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsB_of_actual._proof_1_3
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsB_of_actual._proof_1_4
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsB_of_actual._proof_1_5
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsB_of_actual._proof_1_6
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsB_of_actual._proof_1_7
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsB_of_actual._proof_1_8
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.boundsB_of_actual._proof_1_9
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.class_boundsB
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.class_boundsB._proof_1_1
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.class_boundsB._proof_1_10
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.class_boundsB._proof_1_11
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.class_boundsB._proof_1_12
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.class_boundsB._proof_1_2
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.class_boundsB._proof_1_3
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.class_boundsB._proof_1_4
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.class_boundsB._proof_1_5
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.class_boundsB._proof_1_6
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.class_boundsB._proof_1_7
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.class_boundsB._proof_1_8
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.class_boundsB._proof_1_9
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.class_weight
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.colorA_integral_class_contradiction
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.colorA_integral_class_contradiction._proof_1_1
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.colorA_integral_class_contradiction._proof_1_3
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.colorA_integral_class_contradiction._proof_1_4
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.colorA_integral_class_contradiction._proof_1_5
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.colorA_integral_class_contradiction._proof_1_6
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.colorA_integral_class_contradiction._proof_1_7
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.colorB_integral_class_contradiction
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.colorB_integral_class_contradiction._proof_1_1
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.colorB_integral_class_contradiction._proof_1_10
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.colorB_integral_class_contradiction._proof_1_3
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.colorB_integral_class_contradiction._proof_1_4
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.colorB_integral_class_contradiction._proof_1_5
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.colorB_integral_class_contradiction._proof_1_6
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.colorB_integral_class_contradiction._proof_1_7
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.colorB_integral_class_contradiction._proof_1_8
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.colorB_integral_class_contradiction._proof_1_9
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.exists_cyclic_age
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.exists_cyclic_age._proof_1_1
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.exists_cyclic_age._proof_1_2
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.exists_cyclic_age._proof_1_3
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.exists_cyclic_input
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.exists_cyclic_input._proof_1_1
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.exists_cyclic_input._proof_1_2
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.integral_class_contradiction
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.integral_class_contradiction._proof_1_1
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.integral_class_contradiction._proof_1_2
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.integral_class_contradiction._proof_1_3
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverseClass
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverseClass_identity
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverseClass_weight
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsA
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsA._proof_1_1
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsA._proof_1_10
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsA._proof_1_11
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsA._proof_1_12
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsA._proof_1_13
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsA._proof_1_14
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsA._proof_1_15
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsA._proof_1_16
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsA._proof_1_17
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsA._proof_1_2
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsA._proof_1_3
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsA._proof_1_4
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsA._proof_1_5
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsA._proof_1_6
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsA._proof_1_7
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsA._proof_1_8
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsA._proof_1_9
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsB
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsB._proof_1_1
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsB._proof_1_10
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsB._proof_1_11
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsB._proof_1_12
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsB._proof_1_2
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsB._proof_1_3
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsB._proof_1_4
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsB._proof_1_5
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsB._proof_1_6
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsB._proof_1_7
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsB._proof_1_8
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.inverse_boundsB._proof_1_9
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.minimum_one_of_cyclic_white
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.minimum_one_of_cyclic_white._proof_1_1
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.minimum_one_of_cyclic_white._proof_1_2
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.minimum_one_of_cyclic_white._proof_1_3
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.minimum_one_of_cyclic_white._proof_1_4
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.minimum_one_of_cyclic_white._proof_1_5
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.minimum_one_of_cyclic_white._proof_1_6
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.minimum_one_of_cyclic_white._proof_1_7
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.minimum_simplex_empty
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.minimum_simplex_empty._proof_1_1
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.minimum_simplex_empty._proof_1_2
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.rotated_integral_class_contradiction
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.rowsA
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.rowsA._proof_1
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.rowsA.eq_1
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.rowsA_eq_socleRows
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.rowsB
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.rowsB.eq_1
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.rowsB_eq_socleRows
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.simplex_positive_or_row
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.simplex_positive_or_row._proof_1_1
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socle
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socle.eq_1
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socleMatrix
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socleMatrix.eq_1
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socleMatrix_det
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socleMatrix_det_level
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socleMatrix_kernelJ
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socleMatrix_kernelK
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socleMatrix_row_lattice
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socleMatrix_row_lattice._simp_1_1
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socleMatrix_span_level
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socleMatrix_span_level._simp_1_1
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socleMatrix_weight
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socleRows
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socleRows._proof_1
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socleRows.eq_1
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socleRows_diagonal
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socleRows_nonneg
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socleRows_off_diagonal
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socleRows_rotate
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socleRows_weight
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socle_minimum_weight
#print axioms P21.Nonsymmetric.ColorCap.MinimumOne.socle_simplex_empty
#print axioms P21.Nonsymmetric.ColorCap.minimum_one_proved
#print axioms P21.Nonsymmetric.ColorCap.three_arms_impossible_of_dpe
#print axioms P21.Nonsymmetric.White.CyclicAge
#print axioms P21.Nonsymmetric.White.CyclicWhiteStatement
#print axioms P21.Nonsymmetric.White.NonzeroClasses
#print axioms P21.Nonsymmetric.White.beatty_adjacent_gap
#print axioms P21.Nonsymmetric.White.beatty_adjacent_gap._proof_1_1
#print axioms P21.Nonsymmetric.White.beatty_adjacent_gap._proof_1_2
#print axioms P21.Nonsymmetric.White.beatty_div_antitone
#print axioms P21.Nonsymmetric.White.beatty_div_antitone._proof_1_1
#print axioms P21.Nonsymmetric.White.beatty_div_antitone._proof_1_2
#print axioms P21.Nonsymmetric.White.beatty_gap
#print axioms P21.Nonsymmetric.White.beatty_gap._proof_1_1
#print axioms P21.Nonsymmetric.White.beatty_gap._proof_1_2
#print axioms P21.Nonsymmetric.White.beatty_index_lt
#print axioms P21.Nonsymmetric.White.beatty_index_lt._proof_1_1
#print axioms P21.Nonsymmetric.White.beatty_index_lt._proof_1_2
#print axioms P21.Nonsymmetric.White.beatty_interleaving_impossible
#print axioms P21.Nonsymmetric.White.beatty_interleaving_impossible._proof_1_1
#print axioms P21.Nonsymmetric.White.beatty_last
#print axioms P21.Nonsymmetric.White.beatty_last._proof_1_1
#print axioms P21.Nonsymmetric.White.beatty_last._proof_1_2
#print axioms P21.Nonsymmetric.White.beatty_last._proof_1_3
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_1
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_10
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_11
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_12
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_13
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_14
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_15
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_16
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_17
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_18
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_19
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_2
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_20
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_21
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_22
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_23
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_24
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_25
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_26
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_27
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_28
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_29
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_3
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_30
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_31
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_32
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_33
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_34
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_35
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_4
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_5
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_6
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_7
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_8
#print axioms P21.Nonsymmetric.White.beatty_partition_impossible._proof_1_9
#print axioms P21.Nonsymmetric.White.classRepresentative
#print axioms P21.Nonsymmetric.White.classRepresentative.eq_1
#print axioms P21.Nonsymmetric.White.classRepresentative_equation
#print axioms P21.Nonsymmetric.White.classResidues
#print axioms P21.Nonsymmetric.White.classResidues.eq_1
#print axioms P21.Nonsymmetric.White.classResidues_complement
#print axioms P21.Nonsymmetric.White.classResidues_complement._proof_1_2
#print axioms P21.Nonsymmetric.White.classResidues_complement._proof_1_3
#print axioms P21.Nonsymmetric.White.classResidues_complement._simp_1_1
#print axioms P21.Nonsymmetric.White.classResidues_lower
#print axioms P21.Nonsymmetric.White.classResidues_lower._proof_1_1
#print axioms P21.Nonsymmetric.White.classResidues_lower._proof_1_2
#print axioms P21.Nonsymmetric.White.classResidues_lower._proof_1_3
#print axioms P21.Nonsymmetric.White.classResidues_lower._proof_1_4
#print axioms P21.Nonsymmetric.White.classResidues_sum
#print axioms P21.Nonsymmetric.White.classResidues_sum_mod
#print axioms P21.Nonsymmetric.White.combination
#print axioms P21.Nonsymmetric.White.combination.eq_1
#print axioms P21.Nonsymmetric.White.complementary_remainder
#print axioms P21.Nonsymmetric.White.complementary_remainder._proof_1_1
#print axioms P21.Nonsymmetric.White.cyclicAge_jump_sum
#print axioms P21.Nonsymmetric.White.cyclicAge_jump_sum._proof_1_1
#print axioms P21.Nonsymmetric.White.cyclicAge_jump_sum._proof_1_2
#print axioms P21.Nonsymmetric.White.cyclicAge_jump_sum._proof_1_3
#print axioms P21.Nonsymmetric.White.cyclicAge_jump_sum._proof_1_4
#print axioms P21.Nonsymmetric.White.cyclicAge_nonzero
#print axioms P21.Nonsymmetric.White.cyclicAge_nonzero._proof_1_1
#print axioms P21.Nonsymmetric.White.cyclicAge_nonzero._proof_1_2
#print axioms P21.Nonsymmetric.White.cyclicAge_nonzero._proof_1_3
#print axioms P21.Nonsymmetric.White.cyclicAge_nonzero._proof_1_4
#print axioms P21.Nonsymmetric.White.cyclicAge_nonzero._proof_1_5
#print axioms P21.Nonsymmetric.White.cyclicAge_nonzero._proof_1_6
#print axioms P21.Nonsymmetric.White.cyclicAge_nonzero._proof_1_7
#print axioms P21.Nonsymmetric.White.cyclicAge_nonzero._proof_1_8
#print axioms P21.Nonsymmetric.White.cyclicAge_sum
#print axioms P21.Nonsymmetric.White.cyclicAge_sum._proof_1_1
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_1
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_10
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_11
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_12
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_13
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_14
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_15
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_16
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_17
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_18
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_19
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_2
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_20
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_21
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_22
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_23
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_3
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_4
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_5
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_6
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_7
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_8
#print axioms P21.Nonsymmetric.White.cyclicWhite_sorted_impossible._proof_1_9
#print axioms P21.Nonsymmetric.White.cyclic_age_of_minimum
#print axioms P21.Nonsymmetric.White.cyclic_age_of_minimum._proof_1_1
#print axioms P21.Nonsymmetric.White.cyclic_age_of_minimum._proof_1_10
#print axioms P21.Nonsymmetric.White.cyclic_age_of_minimum._proof_1_11
#print axioms P21.Nonsymmetric.White.cyclic_age_of_minimum._proof_1_12
#print axioms P21.Nonsymmetric.White.cyclic_age_of_minimum._proof_1_13
#print axioms P21.Nonsymmetric.White.cyclic_age_of_minimum._proof_1_2
#print axioms P21.Nonsymmetric.White.cyclic_age_of_minimum._proof_1_3
#print axioms P21.Nonsymmetric.White.cyclic_age_of_minimum._proof_1_4
#print axioms P21.Nonsymmetric.White.cyclic_age_of_minimum._proof_1_5
#print axioms P21.Nonsymmetric.White.cyclic_age_of_minimum._proof_1_6
#print axioms P21.Nonsymmetric.White.cyclic_age_of_minimum._proof_1_7
#print axioms P21.Nonsymmetric.White.cyclic_age_of_minimum._proof_1_8
#print axioms P21.Nonsymmetric.White.cyclic_age_of_minimum._proof_1_9
#print axioms P21.Nonsymmetric.White.cyclic_white_proved
#print axioms P21.Nonsymmetric.White.cyclic_white_proved._proof_1_1
#print axioms P21.Nonsymmetric.White.exists_positive_inverse
#print axioms P21.Nonsymmetric.White.exists_positive_inverse._proof_1_1
#print axioms P21.Nonsymmetric.White.exists_positive_inverse._proof_1_2
#print axioms P21.Nonsymmetric.White.exists_positive_inverse._proof_1_3
#print axioms P21.Nonsymmetric.White.exists_positive_inverse._proof_1_4
#print axioms P21.Nonsymmetric.White.exists_positive_inverse._proof_1_5
#print axioms P21.Nonsymmetric.White.floorJump
#print axioms P21.Nonsymmetric.White.floorJump.eq_1
#print axioms P21.Nonsymmetric.White.floorJump_bounds
#print axioms P21.Nonsymmetric.White.floorJump_bounds._proof_1_1
#print axioms P21.Nonsymmetric.White.floorJump_bounds._proof_1_2
#print axioms P21.Nonsymmetric.White.floorJump_complement
#print axioms P21.Nonsymmetric.White.floorJump_complement._proof_1_1
#print axioms P21.Nonsymmetric.White.floorJump_complement._proof_1_2
#print axioms P21.Nonsymmetric.White.floorJump_complement._proof_1_3
#print axioms P21.Nonsymmetric.White.floorJump_complement._proof_1_4
#print axioms P21.Nonsymmetric.White.floorJump_of_support
#print axioms P21.Nonsymmetric.White.floorJump_of_support._proof_1_1
#print axioms P21.Nonsymmetric.White.floorJump_of_support._proof_1_2
#print axioms P21.Nonsymmetric.White.floorJump_of_support._proof_1_3
#print axioms P21.Nonsymmetric.White.floorJump_support
#print axioms P21.Nonsymmetric.White.floorJump_support._proof_1_1
#print axioms P21.Nonsymmetric.White.floorJump_support._proof_1_2
#print axioms P21.Nonsymmetric.White.gcd_eq_one_of_nonzero_classes
#print axioms P21.Nonsymmetric.White.gcd_eq_one_of_nonzero_classes._proof_1_1
#print axioms P21.Nonsymmetric.White.gcd_eq_one_of_nonzero_classes._proof_1_2
#print axioms P21.Nonsymmetric.White.integral_class_of_unit_coordinate
#print axioms P21.Nonsymmetric.White.integral_class_of_unit_coordinate._proof_1_1
#print axioms P21.Nonsymmetric.White.integral_class_of_unit_coordinate._proof_1_2
#print axioms P21.Nonsymmetric.White.integral_class_of_unit_coordinate._proof_1_3
#print axioms P21.Nonsymmetric.White.nonzeroClasses_complement
#print axioms P21.Nonsymmetric.White.relative_coset_iff
#print axioms P21.Nonsymmetric.White.relative_cyclic_representatives
#print axioms P21.Nonsymmetric.White.relative_cyclic_representatives._simp_1_1
#print axioms P21.Nonsymmetric.White.relative_level_coset_iff
#print axioms P21.Nonsymmetric.White.relative_level_residue_realized
#print axioms P21.Nonsymmetric.White.relative_level_residue_unique
#print axioms P21.Nonsymmetric.White.relative_residue_unique
#print axioms P21.Nonsymmetric.White.residue_realized
#print axioms P21.Nonsymmetric.White.small_mass_impossible
#print axioms P21.Nonsymmetric.White.small_mass_impossible._proof_1_1
#print axioms P21.Nonsymmetric.White.small_mass_impossible._proof_1_2
#print axioms P21.Nonsymmetric.White.small_mass_impossible._proof_1_3
#print axioms P21.Nonsymmetric.White.weight_combination
#print axioms P21.Nonsymmetric.White.weight_scale
#print axioms P21.Nonsymmetric.White.weight_surjective
#print axioms P21.Nonsymmetric.White.weight_surjective._simp_1_1
