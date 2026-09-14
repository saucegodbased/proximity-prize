import O2ABR4LiteralAdjacentDepthRed6900
import K0CriticalAdjacentCellCommutator6900

/-!
# The literal three-cell quotient relation

The old adjacent-depth RED example discarded the same-grade `u1 * Z^2`
summand in the literal contact of `Y * Z`.  Here we retain all three cells.
The resulting dual equation and its quotient-pairing form are exact, and the
old `Rat[X]/(X^3)` counterexample then cancels identically.

This is a local quotient bridge.  It does not construct the common global
numerators, nor does it prove that the target taper is stable under the
three-cell recurrence.
-/

namespace ProximityPrize.SubmissionLower.K0LiteralThreeCellQuotient6900

open Polynomial
open Order2SourceRank Order2PassiveSeedSource
open HrsQuotientTopPairing6900 HrsU0PCInteriorOrdering6900
open O2ABR4LiteralAdjacentDepthRed6900
open K0CriticalAdjacentCellCommutator6900
open K0RawRSConnectionTranspose6900
open K0CriticalRawSTwoSeedStaircase6900

noncomputable section

set_option autoImplicit false
set_option Elab.async false

/-! ## Literal `Y*Z` equation -/

/-- Applying a dual functional to the complete literal `Y*Z` source column
gives a three-cell equation.  In particular the same-grade `u1*Z^2` cell is
present, rather than being silently discharged by an induction hypothesis. -/
theorem literal_YZ_three_cell_after_source
    (x u0 u1 : Rat) (ell : SeedPoly Rat →ₗ[Rat] Rat)
    (hsource : ell (localSeedSubstitution Rat x u0 u1
      (passiveGlobalSourceMonomial Rat 0 1 0 0 1)) = 0) :
    ell (passiveColumnTerm Rat x u0 u1 0 1 0 0 1 1 0) +
        ell (passiveColumnTerm Rat x u0 u1 0 1 0 0 1 0 0) +
        ell (passiveColumnTerm Rat x u0 u1 0 1 0 0 1 0 1) = 0 := by
  rw [literal_YZ_expansion_is_three_term] at hsource
  simpa only [map_add] using hsource

/-! ## Quotient-pairing transport -/

/-- The quotient top pairing is additive in its numerator, including the
two subtractions in the critical adjacent-cell commutator. -/
theorem quotientTopPairing_sub_sub
    {K : Type*} [Field K] (A nY n0 nZ p : K[X]) (M : Nat) :
    quotientTopPairing A (nY - n0 - nZ) p M =
      quotientTopPairing A nY p M -
        quotientTopPairing A n0 p M -
        quotientTopPairing A nZ p M := by
  simp only [quotientTopPairing, sub_mul, Polynomial.sub_modByMonic,
    Polynomial.coeff_sub]

/-- Exact quotient form of the literal three-cell source equation.  The
three representation hypotheses are the common-denominator interface: no
term is deleted, and no dimension/maximal-rank assertion is used. -/
theorem literal_YZ_three_cell_quotient_relation
    (x u0 u1 : Rat) (ell : SeedPoly Rat →ₗ[Rat] Rat)
    (A nDiag nBase nLeak p : Rat[X]) (M : Nat)
    (hsource : ell (localSeedSubstitution Rat x u0 u1
      (passiveGlobalSourceMonomial Rat 0 1 0 0 1)) = 0)
    (hdiag : ell (passiveColumnTerm Rat x u0 u1
        0 1 0 0 1 1 0) = quotientTopPairing A nDiag p M)
    (hbase : ell (passiveColumnTerm Rat x u0 u1
        0 1 0 0 1 0 0) = quotientTopPairing A nBase p M)
    (hleak : ell (passiveColumnTerm Rat x u0 u1
        0 1 0 0 1 0 1) = quotientTopPairing A nLeak p M) :
    quotientTopPairing A (nDiag + nBase + nLeak) p M = 0 := by
  have hthree := literal_YZ_three_cell_after_source x u0 u1 ell hsource
  rw [hdiag, hbase, hleak] at hthree
  simpa only [quotientTopPairing, add_mul, Polynomial.add_modByMonic,
    Polynomial.coeff_add] using hthree

/-! ## Critical packet form -/

/-- Any functional killing order-`m+1` contact sees the complete critical
adjacent commutator as zero.  This packages the base, next-Y, and next-Z
cells without dropping the `u1`-weighted seed shift. -/
theorem critical_three_cell_after_contact
    {K : Type*} [Field K] (x u0 u1 : K) (a m : Nat)
    (ell : FlatContact K →ₗ[K] K)
    (hkill : ∀ q : FlatContact K,
      ell (eps (K := K) ^ (m + 1) * q) = 0) :
    ell (criticalNextYPacket x u0 u1 a m -
        MvPolynomial.C u0 * criticalPacket x u0 u1 a m -
        MvPolynomial.C u1 * criticalSeedPacket x u0 u1 a m) = 0 := by
  rcases eps_pow_succ_dvd_critical_adjacent_YZ_commutator
      x u0 u1 a m with ⟨q, hq⟩
  rw [hq]
  exact hkill q

/-- Once the three weighted critical cells have quotient numerators, their
literal commutator numerator pairs to zero.  This is the corrected
three-cell version of the invalid pair-only quotient step. -/
theorem critical_three_cell_quotient_relation
    {K : Type*} [Field K] (x u0 u1 : K) (a m : Nat)
    (ell : FlatContact K →ₗ[K] K)
    (A nY n0 nZ p : K[X]) (M : Nat)
    (hkill : ∀ q : FlatContact K,
      ell (eps (K := K) ^ (m + 1) * q) = 0)
    (hY : ell (criticalNextYPacket x u0 u1 a m) =
      quotientTopPairing A nY p M)
    (h0 : ell (MvPolynomial.C u0 * criticalPacket x u0 u1 a m) =
      quotientTopPairing A n0 p M)
    (hZ : ell (MvPolynomial.C u1 * criticalSeedPacket x u0 u1 a m) =
      quotientTopPairing A nZ p M) :
    quotientTopPairing A (nY - n0 - nZ) p M = 0 := by
  have hthree := critical_three_cell_after_contact
    x u0 u1 a m ell hkill
  simp only [map_sub] at hthree
  rw [hY, h0, hZ] at hthree
  rw [quotientTopPairing_sub_sub]
  exact hthree

/-! ## Target support check -/

/-- The complete corrected three-cell head and the mixed `S*Y^46*R`
connector all lie in the reduced m47/B16/s6 profile at their exact strict
X widths.  This is only source legality; it deliberately does not assert
that a common tapered numerator realizes all four bands. -/
theorem m47_three_cell_and_SYR_connector_legal
    (aCritical aNextY aConnector : Nat)
    (hCritical : aCritical < 2188005)
    (hNextY : aNextY < 2056934)
    (hConnector : aConnector < 2188006) :
    rawShapeLegal (47 * 180413) 131071 5107 16 6 64
        aCritical 1 47 0 0 ∧
      rawShapeLegal (47 * 180413) 131071 5107 16 6 64
        aCritical 1 47 0 1 ∧
      rawShapeLegal (47 * 180413) 131071 5107 16 6 64
        aNextY 1 48 0 0 ∧
      rawShapeLegal (47 * 180413) 131071 5107 16 6 64
        aConnector 1 46 1 0 := by
  constructor
  · exact (m47_reduced_profile_two_seed_packet_legal
      aCritical 0 0 0 hCritical (by norm_num) (by norm_num) (by norm_num)).1
  constructor
  · exact (m47_reduced_profile_two_seed_packet_legal
      aCritical 0 0 1 hCritical (by norm_num) (by norm_num) (by norm_num)).1
  constructor
  · exact (m47_reduced_profile_next_Y_packet_legal
      aNextY 0 0 hNextY (by norm_num) (by norm_num)).1
  · exact m47_reduced_profile_critical_SYR_connector_legal
      aConnector 0 hConnector (by norm_num)

/-! ## Exact regression of the old RED witness -/

/-- In the old `Rat[X]/(X^3)` witness, the pair-only numerator is nonzero,
but the omitted third-cell leakage cancels it exactly.  Consequently the
complete numerator has zero remainder and zero quotient pairing against
every test polynomial. -/
theorem old_pair_only_counterexample_closes_with_third_cell :
    (-(Polynomial.X ^ 2 : Rat[X])) %ₘ
        (Polynomial.X ^ 3 : Rat[X]) ≠ 0 ∧
      (-(Polynomial.X ^ 2 : Rat[X]) +
          (Polynomial.X ^ 2 : Rat[X]) * 1) = 0 ∧
      (-(Polynomial.X ^ 2 : Rat[X]) +
          (Polynomial.X ^ 2 : Rat[X]) * 1) %ₘ
          (Polynomial.X ^ 3 : Rat[X]) = 0 ∧
      ∀ p : Rat[X], quotientTopPairing
        (Polynomial.X ^ 3 : Rat[X])
        (-(Polynomial.X ^ 2 : Rat[X]) +
          (Polynomial.X ^ 2 : Rat[X]) * 1) p 3 = 0 := by
  refine ⟨literal_profile_has_pair_only_counterexample.2.2.2.1, ?_⟩
  constructor
  · ring
  constructor
  · simp
  · intro p
    simp [quotientTopPairing]

#print axioms literal_YZ_three_cell_after_source
#print axioms quotientTopPairing_sub_sub
#print axioms literal_YZ_three_cell_quotient_relation
#print axioms critical_three_cell_after_contact
#print axioms critical_three_cell_quotient_relation
#print axioms m47_three_cell_and_SYR_connector_legal
#print axioms old_pair_only_counterexample_closes_with_third_cell

end

end ProximityPrize.SubmissionLower.K0LiteralThreeCellQuotient6900
