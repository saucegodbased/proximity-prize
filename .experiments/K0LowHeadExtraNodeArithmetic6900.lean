import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LowerGeometry

/-!
# Low-epsilon-head capacity at lower 6900

This file keeps the target k=0 source cutoff at the original multiplicity
`m=47`, but counts only the local contact head `epsilon < m-3`, whose order is
44.  It proves the exact closed local rank and the resulting capacity for an
extra local node block.  This is necessary arithmetic for an `(n+1)`-node
CRT argument; it does not prove that the extra evaluation map is surjective.

Only kernel-checked reduction is used in this file.
-/

namespace ProximityPrize.SubmissionLower.K0LowHeadExtraNodeArithmetic6900

set_option autoImplicit false
set_option Elab.async false

open ProximityPrize.SubmissionLower

def sourceColumns : Nat := 65_061_789_117_960
def fullLocalRank : Nat := 248_191_020
def lowHeadLocalRank : Nat := 213_740_910

/-- Exact closed local rank after retaining epsilon orders `0,...,43`. -/
theorem lowHeadLocalRank_eq_closed :
    SecondJetRelaxedCounts.rankBound 44 3757 16 8 64 =
      lowHeadLocalRank := by
  decide

/-- Removing the last three epsilon orders saves this rank at each node. -/
theorem omittedThreeLayerRank :
    fullLocalRank - lowHeadLocalRank = 34_450_110 := by
  norm_num [fullLocalRank, lowHeadLocalRank]

/-- Exact all-node low-head margin with the unchanged `47*g` source. -/
theorem targetLowHeadMargin :
    sourceColumns - 262144 * lowHeadLocalRank = 9_030_892_006_920 := by
  norm_num [sourceColumns, lowHeadLocalRank]

/-- The low-head margin pays for one whole additional low local block. -/
theorem targetExtraLowNodeBlock :
    sourceColumns - 262144 * lowHeadLocalRank - lowHeadLocalRank =
      9_030_678_266_010 ∧
    lowHeadLocalRank ≤ sourceColumns - 262144 * lowHeadLocalRank := by
  norm_num [sourceColumns, lowHeadLocalRank]

/-- It even pays for a full order-47 local block at the extra point. -/
theorem targetExtraFullNodeBlock :
    sourceColumns - 262144 * lowHeadLocalRank - fullLocalRank =
      9_030_643_815_900 ∧
    fullLocalRank ≤ sourceColumns - 262144 * lowHeadLocalRank := by
  norm_num [sourceColumns, lowHeadLocalRank, fullLocalRank]

/-- Four scalar boundary rows are negligible in the low-head ledger. -/
theorem targetFourBoundaryRows :
    sourceColumns - 262144 * lowHeadLocalRank - 4 =
      9_030_892_006_916 ∧
    4 ≤ sourceColumns - 262144 * lowHeadLocalRank := by
  norm_num [sourceColumns, lowHeadLocalRank]

/-- The exact margin contains 42,251 complete low local blocks plus residue. -/
theorem targetLowBlockQuotient :
    9_030_892_006_920 = 42_251 * lowHeadLocalRank + 124_818_510 := by
  norm_num [lowHeadLocalRank]

#print axioms lowHeadLocalRank_eq_closed
#print axioms targetLowHeadMargin
#print axioms targetExtraLowNodeBlock
#print axioms targetExtraFullNodeBlock
#print axioms targetFourBoundaryRows

end ProximityPrize.SubmissionLower.K0LowHeadExtraNodeArithmetic6900
