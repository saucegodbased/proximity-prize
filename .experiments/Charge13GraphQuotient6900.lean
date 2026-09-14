import Mathlib.Algebra.Exact.Basic

/-! A reusable split exact sequence attached to three endomorphisms.

If `TA` is an automorphism with specified two-sided inverse `U`, the graph of
`(TA, TB, TC)` is exactly the kernel of the map which subtracts the `TB` and
`TC` values reconstructed from the first coordinate.  The statements work for
modules over an arbitrary (not necessarily commutative) ring.
-/

namespace Charge13GraphQuotient6900

set_option autoImplicit false

variable {R S : Type*} [Ring R] [AddCommGroup S] [Module R S]

/-- The simultaneous graph of three endomorphisms. -/
def graphMap (TA TB TC : S →ₗ[R] S) : S →ₗ[R] S × S × S :=
  TA.prod (TB.prod TC)

@[simp]
theorem graphMap_apply (TA TB TC : S →ₗ[R] S) (x : S) :
    graphMap TA TB TC x = (TA x, TB x, TC x) :=
  rfl

/-- The two compatibility defects of a putative graph point. -/
def compatibilityMap (TB TC U : S →ₗ[R] S) : (S × S × S) →ₗ[R] S × S := by
  let first : (S × S × S) →ₗ[R] S := LinearMap.fst R S (S × S)
  let tail : (S × S × S) →ₗ[R] S × S := LinearMap.snd R S (S × S)
  let second : (S × S × S) →ₗ[R] S := (LinearMap.fst R S S).comp tail
  let third : (S × S × S) →ₗ[R] S := (LinearMap.snd R S S).comp tail
  exact (second - TB.comp (U.comp first)).prod
    (third - TC.comp (U.comp first))

@[simp]
theorem compatibilityMap_apply (TB TC U : S →ₗ[R] S) (p : S × S × S) :
    compatibilityMap TB TC U p =
      (p.2.1 - TB (U p.1), p.2.2 - TC (U p.1)) :=
  rfl

private theorem leftInverse_apply
    (TA U : S →ₗ[R] S) (hUT : U.comp TA = LinearMap.id) (x : S) :
    U (TA x) = x := by
  simpa using DFunLike.congr_fun hUT x

private theorem rightInverse_apply
    (TA U : S →ₗ[R] S) (hTU : TA.comp U = LinearMap.id) (x : S) :
    TA (U x) = x := by
  simpa using DFunLike.congr_fun hTU x

/-- The graph map is injective as soon as `U` is a left inverse to `TA`. -/
theorem graphMap_injective
    (TA TB TC U : S →ₗ[R] S) (hUT : U.comp TA = LinearMap.id) :
    Function.Injective (graphMap TA TB TC) := by
  intro x y hxy
  have hTA : TA x = TA y := congrArg Prod.fst hxy
  calc
    x = U (TA x) := (leftInverse_apply TA U hUT x).symm
    _ = U (TA y) := congrArg (fun z ↦ U z) hTA
    _ = y := leftInverse_apply TA U hUT y

/-- Compatibility is split surjective, by inserting zero in the first slot. -/
theorem compatibilityMap_surjective (TB TC U : S →ₗ[R] S) :
    Function.Surjective (compatibilityMap TB TC U) := by
  intro q
  refine ⟨(0, q.1, q.2), ?_⟩
  simp

/-- Every graph point has zero compatibility defect. -/
theorem compatibilityMap_comp_graphMap
    (TA TB TC U : S →ₗ[R] S) (hUT : U.comp TA = LinearMap.id) :
    (compatibilityMap TB TC U).comp (graphMap TA TB TC) = 0 := by
  apply LinearMap.ext
  intro x
  have hx : U (TA x) = x := leftInverse_apply TA U hUT x
  change (TB x - TB (U (TA x)), TC x - TC (U (TA x))) = (0, 0)
  simp [hx]

/-- Pointwise exactness, in an explicit witness form. -/
theorem compatibilityMap_eq_zero_iff_exists_graphMap
    (TA TB TC U : S →ₗ[R] S)
    (hUT : U.comp TA = LinearMap.id) (hTU : TA.comp U = LinearMap.id)
    (p : S × S × S) :
    compatibilityMap TB TC U p = 0 ↔ ∃ x, graphMap TA TB TC x = p := by
  constructor
  · intro hp
    have hb0 : p.2.1 - TB (U p.1) = 0 := by
      simpa using congrArg Prod.fst hp
    have hc0 : p.2.2 - TC (U p.1) = 0 := by
      simpa using congrArg Prod.snd hp
    have hb : p.2.1 = TB (U p.1) := sub_eq_zero.mp hb0
    have hc : p.2.2 = TC (U p.1) := sub_eq_zero.mp hc0
    refine ⟨U p.1, ?_⟩
    apply Prod.ext
    · exact rightInverse_apply TA U hTU p.1
    · exact Prod.ext hb.symm hc.symm
  · rintro ⟨x, rfl⟩
    have hx : U (TA x) = x := leftInverse_apply TA U hUT x
    simp [hx]

/-- The graph and compatibility maps form an exact pair. -/
theorem graphMap_exact_compatibilityMap
    (TA TB TC U : S →ₗ[R] S)
    (hUT : U.comp TA = LinearMap.id) (hTU : TA.comp U = LinearMap.id) :
    Function.Exact (graphMap TA TB TC) (compatibilityMap TB TC U) := by
  intro p
  exact compatibilityMap_eq_zero_iff_exists_graphMap TA TB TC U hUT hTU p

/-- Membership in the compatibility kernel is membership in the graph range. -/
theorem mem_ker_compatibilityMap_iff_mem_range_graphMap
    (TA TB TC U : S →ₗ[R] S)
    (hUT : U.comp TA = LinearMap.id) (hTU : TA.comp U = LinearMap.id)
    (p : S × S × S) :
    p ∈ LinearMap.ker (compatibilityMap TB TC U) ↔
      p ∈ LinearMap.range (graphMap TA TB TC) := by
  rw [(graphMap_exact_compatibilityMap TA TB TC U hUT hTU).linearMap_ker_eq]

/-- The compatibility kernel is precisely the range of the graph map. -/
theorem ker_compatibilityMap_eq_range_graphMap
    (TA TB TC U : S →ₗ[R] S)
    (hUT : U.comp TA = LinearMap.id) (hTU : TA.comp U = LinearMap.id) :
    LinearMap.ker (compatibilityMap TB TC U) =
      LinearMap.range (graphMap TA TB TC) :=
  (graphMap_exact_compatibilityMap TA TB TC U hUT hTU).linearMap_ker_eq

end Charge13GraphQuotient6900

#print axioms Charge13GraphQuotient6900.graphMap_exact_compatibilityMap
#print axioms Charge13GraphQuotient6900.ker_compatibilityMap_eq_range_graphMap
