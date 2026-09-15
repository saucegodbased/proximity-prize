import Mathlib.Tactic.NormNum

/-!
# First exact delta from the accepted 6811 moving-fiber certificate to 6900

This is an arithmetic discriminator, not a retargeted certificate.  It records
the accepted maximum and budget and checks the first unavoidable changes in
the interpolation identity ratio when the error count rises from 80860 to
81731.
-/

namespace ProximityPrize.SubmissionLower.Accepted6811To6900FirstDelta

set_option autoImplicit false

def acceptedErrors : Nat := 80860
def targetErrors : Nat := 81731
def acceptedAgreements : Nat := 262144 - acceptedErrors
def targetAgreements : Nat := 262144 - targetErrors
def sectionDegree : Nat := 131071
def acceptedGap : Nat := acceptedAgreements - sectionDegree
def targetGap : Nat := targetAgreements - sectionDegree

def acceptedBudget : Nat := 274980720549750805
def acceptedLedgerMax : Nat := 274693043573515013
def targetBudget : Nat := 254684620614660120

theorem exact_error_agreement_delta :
    targetErrors - acceptedErrors = 871 /\
    acceptedAgreements = 181284 /\ targetAgreements = 180413 /\
    acceptedGap = 50213 /\ targetGap = 49342 /\
    acceptedGap - targetGap = 871 := by
  norm_num [acceptedErrors, targetErrors, acceptedAgreements,
    targetAgreements, sectionDegree, acceptedGap, targetGap]

/-- The accepted certificate used almost all of its 6811 allowance. -/
theorem accepted_ledger_margin :
    acceptedBudget - acceptedLedgerMax = 287676976235792 := by
  norm_num [acceptedBudget, acceptedLedgerMax]

/-- Even unrealistically keeping every 6811 table entry unchanged would put
the accepted maximum more than twenty quadrillion above the 6900 budget. -/
theorem unchanged_ledger_already_fails_target :
    targetBudget < acceptedLedgerMax /\
    acceptedLedgerMax - targetBudget = 20008422958854893 := by
  norm_num [targetBudget, acceptedLedgerMax]

theorem budget_loss_exceeds_entire_accepted_margin :
    acceptedBudget - targetBudget = 20296099935090685 /\
    acceptedBudget - acceptedLedgerMax < acceptedBudget - targetBudget := by
  norm_num [acceptedBudget, acceptedLedgerMax, targetBudget]

/-- The moving-fiber identity term contains `131073*(errors+1)`, while the
proper-section denominator is `agreements-131071`.  Both changes are adverse.
The cross multiplication proves the target ratio is strictly larger without
using floating point. -/
theorem target_identity_ratio_strictly_worse :
    80861 * targetGap < 81732 * acceptedGap /\
    81732 * acceptedGap - 80861 * targetGap = 114165454 /\
    131073 * 80861 = 10598693853 /\
    131073 * 81732 = 10712858436 /\
    131073 * 81732 - 131073 * 80861 = 114164583 := by
  norm_num [acceptedGap, targetGap, acceptedAgreements, targetAgreements,
    acceptedErrors, targetErrors, sectionDegree]

#print axioms exact_error_agreement_delta
#print axioms unchanged_ledger_already_fails_target
#print axioms target_identity_ratio_strictly_worse

end ProximityPrize.SubmissionLower.Accepted6811To6900FirstDelta
