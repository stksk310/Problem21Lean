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

-- Read-only environment inventory; this command constructs no proof or declaration.
run_cmd do
  for (n, _) in (← Lean.getEnv).constants do
    if n.toString.startsWith "P21.Nonsymmetric." then
      Lean.logInfo (Lean.MessageData.ofName n)
