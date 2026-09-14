import CompPoly.Bivariate.GuruswamiSudan.Implementations

/-!
Executable/formal interface probe for the Full187 pure `R=S=Z=0` face.

This file only records the exact Lee--O'Sullivan parameters already exposed
by patched CompPoly.  It does not assert that the prescribed `Y`-linear
boundary is attained.
-/

namespace ProximityPrize.Experiments.Full187PureFaceLeeOSullivan6900

open CompPoly CompPoly.GuruswamiSudan

def params : GSInterpParams where
  messageDegree := 131072
  multiplicity := 60
  weightedDegreeBound := 10824779

theorem koalaBear_fieldSize : KoalaBear.fieldSize = 2130706433 := by
  norm_num [KoalaBear.fieldSize]

theorem params_yWeight : yWeight params = 131071 := by
  norm_num [params, yWeight]

theorem params_yCap : interpolationYCap params = 82 := by
  norm_num [params, interpolationYCap, yWeight]

theorem params_leeWidth : leeOSullivanWidth params = 83 := by
  norm_num [leeOSullivanWidth, params_yCap]

theorem params_multiplicity : params.multiplicity = 60 := rfl

theorem params_strictBound : params.weightedDegreeBound + 1 = 10824780 := rfl

/-- The already-certified native-word backend has exactly the target field. -/
def exactFastLeeContext : GSInterpContext KoalaBear.Fast.Field :=
  fastKoalaBearLeeSubproductInterpContext

#check leeOSullivanBasisRowsWithRG
#check LeeOSullivan.leeOSullivanInterpolate_complete
#check PolynomialMatrix.muldersStorjohannReduceFast_eq

end ProximityPrize.Experiments.Full187PureFaceLeeOSullivan6900
