import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Heterogeneous linear interpolation source at the sharp 6900 window

For seed width `r` (hence seed degree `< r`), cutoff `T`, selected degree
`w`, and scalar degree `W`,
use three coefficient families

* `A_j(X)` of degree `< T`,
* `B_j(X)` of degree `< T-w`, and
* `C_j(X)` of degree `< T-W`,

for `0 <= j < r`.  Coefficientwise imposition of

`A(X,g) + B(X,g) * (u0 + g*u1) + C(X,g) * centre = 0`

at every node costs only `r+2` scalar constraints per node.  This file keeps
the construction as a finite linear map; it never materializes its matrix.
-/

namespace ProximityPrize.SubmissionLower.HeterogeneousLinearInterpolationSource6900

open Polynomial Module

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 4000

variable (K : Type*) [Field K]

abbrev CoefficientFamily (r L : Nat) :=
  Fin r → Polynomial.degreeLT K L

abbrev SourceSpace (T w W r : Nat) :=
  CoefficientFamily K r T ×
    (CoefficientFamily K r (T - w) × CoefficientFamily K r (T - W))

abbrev ConstraintSpace (I : Type*) (r : Nat) :=
  I → Fin (r + 1) → K

def currentCoefficient
    {V : Type*} [Zero V] {r : Nat}
    (v : Fin r → V) (k : Fin (r + 1)) : V :=
  if hk : k.val < r then v ⟨k.val, hk⟩ else 0

def previousCoefficient
    {V : Type*} [Zero V] {r : Nat}
    (v : Fin r → V) (k : Fin (r + 1)) : V :=
  if hk : 0 < k.val then v ⟨k.val - 1, by omega⟩ else 0

@[simp] theorem currentCoefficient_castSucc
    {V : Type*} [Zero V] {r : Nat}
    (v : Fin r → V) (j : Fin r) :
    currentCoefficient v j.castSucc = v j := by
  unfold currentCoefficient
  split
  · apply congrArg v
    apply Fin.ext
    rfl
  · rename_i h
    exact (h j.isLt).elim

@[simp] theorem previousCoefficient_succ
    {V : Type*} [Zero V] {r : Nat}
    (v : Fin r → V) (j : Fin r) :
    previousCoefficient v j.succ = v j := by
  unfold previousCoefficient
  split
  · apply congrArg v
    apply Fin.ext
    simp
  · rename_i h
    exact (h (by simp)).elim

@[simp] theorem currentCoefficient_add
    {V : Type*} [AddMonoid V] {r : Nat}
    (v z : Fin r → V) (k : Fin (r + 1)) :
    currentCoefficient (v + z) k =
      currentCoefficient v k + currentCoefficient z k := by
  by_cases hk : k.val < r <;> simp [currentCoefficient, hk]

@[simp] theorem previousCoefficient_add
    {V : Type*} [AddMonoid V] {r : Nat}
    (v z : Fin r → V) (k : Fin (r + 1)) :
    previousCoefficient (v + z) k =
      previousCoefficient v k + previousCoefficient z k := by
  by_cases hk : 0 < k.val <;> simp [previousCoefficient, hk]

@[simp] theorem currentCoefficient_smul
    {V : Type*} [AddCommMonoid V] [Module K V] {r : Nat}
    (c : K) (v : Fin r → V) (k : Fin (r + 1)) :
    currentCoefficient (c • v) k = c • currentCoefficient v k := by
  by_cases hk : k.val < r <;> simp [currentCoefficient, hk]

@[simp] theorem previousCoefficient_smul
    {V : Type*} [AddCommMonoid V] [Module K V] {r : Nat}
    (c : K) (v : Fin r → V) (k : Fin (r + 1)) :
    previousCoefficient (c • v) k = c • previousCoefficient v k := by
  by_cases hk : 0 < k.val <;> simp [previousCoefficient, hk]

/-- Literal coefficient map at arbitrary nodes. -/
def nodalConstraintMap
    {I : Type*} [Fintype I]
    (node u0 u1 centre : I → K) (T w W r : Nat) :
    SourceSpace K T w W r →ₗ[K] ConstraintSpace K I r where
  toFun source i k :=
    (currentCoefficient source.1 k).val.eval (node i) +
      (currentCoefficient source.2.1 k).val.eval (node i) * u0 i +
      (currentCoefficient source.2.2 k).val.eval (node i) * centre i +
      (previousCoefficient source.2.1 k).val.eval (node i) * u1 i
  map_add' := by
    intro x y
    funext i k
    simp only [Prod.fst_add, Prod.snd_add, currentCoefficient_add,
      previousCoefficient_add, Submodule.coe_add, Polynomial.eval_add,
      Pi.add_apply]
    ring
  map_smul' := by
    intro c x
    funext i k
    simp only [Prod.smul_fst, Prod.smul_snd, currentCoefficient_smul,
      previousCoefficient_smul, Pi.smul_apply, Submodule.coe_smul_of_tower,
      Polynomial.eval_smul, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem nodalConstraintMap_apply
    {I : Type*} [Fintype I]
    (node u0 u1 centre : I → K) (T w W r : Nat)
    (source : SourceSpace K T w W r) (i : I) (k : Fin (r + 1)) :
    nodalConstraintMap K node u0 u1 centre T w W r source i k =
      (currentCoefficient source.1 k).val.eval (node i) +
        (currentCoefficient source.2.1 k).val.eval (node i) * u0 i +
        (currentCoefficient source.2.2 k).val.eval (node i) * centre i +
        (previousCoefficient source.2.1 k).val.eval (node i) * u1 i := rfl

/-- Specialize the seed variable while retaining the `X`-degree bound. -/
def specializeFamily
    {r L : Nat} (family : CoefficientFamily K r L) (gamma : K) :
    Polynomial.degreeLT K L :=
  ∑ j : Fin r, gamma ^ j.val • family j

@[simp] theorem currentCoefficient_eval
    {r L : Nat} (family : CoefficientFamily K r L)
    (k : Fin (r + 1)) (x : K) :
    (currentCoefficient family k).val.eval x =
      currentCoefficient (fun j ↦ (family j).val.eval x) k := by
  by_cases hk : k.val < r <;> simp [currentCoefficient, hk]

@[simp] theorem previousCoefficient_eval
    {r L : Nat} (family : CoefficientFamily K r L)
    (k : Fin (r + 1)) (x : K) :
    (previousCoefficient family k).val.eval x =
      previousCoefficient (fun j ↦ (family j).val.eval x) k := by
  by_cases hk : 0 < k.val <;> simp [previousCoefficient, hk]

theorem sum_currentCoefficient
    {r : Nat} (v : Fin r → K) (gamma : K) :
    (∑ k : Fin (r + 1), gamma ^ k.val * currentCoefficient v k) =
      ∑ j : Fin r, gamma ^ j.val * v j := by
  rw [Fin.sum_univ_castSucc]
  simp [currentCoefficient]

theorem sum_previousCoefficient
    {r : Nat} (v : Fin r → K) (gamma : K) :
    (∑ k : Fin (r + 1), gamma ^ k.val * previousCoefficient v k) =
      gamma * ∑ j : Fin r, gamma ^ j.val * v j := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero]
  rw [show previousCoefficient v (0 : Fin (r + 1)) = 0 by
    simp [previousCoefficient], mul_zero, zero_add]
  simp_rw [previousCoefficient_succ, Fin.val_succ, pow_succ]
  rw [Finset.mul_sum]
  ring

theorem eval_specializeFamily
    {r L : Nat} (family : CoefficientFamily K r L)
    (gamma x : K) :
    (specializeFamily K family gamma).val.eval x =
      ∑ j : Fin r, gamma ^ j.val * (family j).val.eval x := by
  simp only [specializeFamily, Submodule.coe_sum,
    Submodule.coe_smul_of_tower, Polynomial.eval_finsetSum,
    Polynomial.eval_smul, smul_eq_mul]

theorem specializeFamily_natDegree_lt
    {r L : Nat} (family : CoefficientFamily K r L)
    (gamma : K) (hL : 0 < L) :
    (specializeFamily K family gamma).val.natDegree < L := by
  by_cases hz : (specializeFamily K family gamma).val = 0
  · simp only [hz, Polynomial.natDegree_zero]
    exact hL
  · exact (Polynomial.natDegree_lt_iff_degree_lt hz).2
      (Polynomial.mem_degreeLT.mp (specializeFamily K family gamma).property)

/-- Kernel membership is the intended all-node identity for every seed
specialization, not merely a formal dimension statement. -/
theorem kernel_all_seed_node_identity
    {I : Type*} [Fintype I]
    (node u0 u1 centre : I → K) (T w W r : Nat)
    (source : SourceSpace K T w W r)
    (hsource : nodalConstraintMap K node u0 u1 centre T w W r source = 0) :
    ∀ (i : I) (gamma : K),
      (specializeFamily K source.1 gamma).val.eval (node i) +
        (specializeFamily K source.2.1 gamma).val.eval (node i) *
          (u0 i + gamma * u1 i) +
        (specializeFamily K source.2.2 gamma).val.eval (node i) * centre i = 0 := by
  intro i gamma
  have hcoeff : ∀ k : Fin (r + 1),
      nodalConstraintMap K node u0 u1 centre T w W r source i k = 0 := by
    intro k
    have h := congrFun (congrFun hsource i) k
    simpa only [Pi.zero_apply] using h
  have hweighted :
      (∑ k : Fin (r + 1), gamma ^ k.val *
        nodalConstraintMap K node u0 u1 centre T w W r source i k) = 0 := by
    simp only [hcoeff, mul_zero, Finset.sum_const_zero]
  rw [eval_specializeFamily, eval_specializeFamily, eval_specializeFamily]
  rw [← sum_currentCoefficient K
      (fun j ↦ (source.1 j).val.eval (node i)) gamma,
    ← sum_currentCoefficient K
      (fun j ↦ (source.2.1 j).val.eval (node i)) gamma,
    ← sum_currentCoefficient K
      (fun j ↦ (source.2.2 j).val.eval (node i)) gamma]
  rw [← hweighted]
  simp only [nodalConstraintMap_apply, currentCoefficient_eval,
    previousCoefficient_eval]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  simp_rw [← mul_assoc]
  repeat rw [← Finset.sum_mul]
  rw [sum_previousCoefficient K
    (fun j ↦ (source.2.1 j).val.eval (node i)) gamma]
  rw [sum_currentCoefficient K
      (fun j ↦ (source.1 j).val.eval (node i)) gamma,
    sum_currentCoefficient K
      (fun j ↦ (source.2.1 j).val.eval (node i)) gamma,
    sum_currentCoefficient K
      (fun j ↦ (source.2.2 j).val.eval (node i)) gamma]
  ring

/-- An all-node kernel row becomes a genuine polynomial syzygy for any
candidate and scalar polynomial agreeing with the two prescribed values on
at least `T` distinct nodes.  This is the semantic bridge needed by the sharp
leaf; it does not use a matrix or an unproved rank assertion. -/
theorem kernel_global_syzygy
    {I : Type*} [Fintype I]
    (node u0 u1 centre : I → K) (T w W r : Nat)
    (source : SourceSpace K T w W r)
    (hsource : nodalConstraintMap K node u0 u1 centre T w W r source = 0)
    (gamma : K) (P S : K[X]) (active : Finset I)
    (hinj : Function.Injective node)
    (hT : 0 < T) (hw : w < T) (hW : W < T)
    (hPdegree : P.natDegree ≤ w) (hSdegree : S.natDegree ≤ W)
    (hcard : T ≤ active.card)
    (hPagrees : ∀ i ∈ active,
      P.eval (node i) = u0 i + gamma * u1 i)
    (hSagrees : ∀ i ∈ active, S.eval (node i) = centre i) :
    (specializeFamily K source.1 gamma).val +
        (specializeFamily K source.2.1 gamma).val * P +
        (specializeFamily K source.2.2 gamma).val * S = 0 := by
  classical
  let relation : K[X] :=
    (specializeFamily K source.1 gamma).val +
      (specializeFamily K source.2.1 gamma).val * P +
      (specializeFamily K source.2.2 gamma).val * S
  have hTw : 0 < T - w := Nat.sub_pos_of_lt hw
  have hTW : 0 < T - W := Nat.sub_pos_of_lt hW
  have hAdeg :
      (specializeFamily K source.1 gamma).val.natDegree < T :=
    specializeFamily_natDegree_lt K source.1 gamma hT
  have hBdeg :
      (specializeFamily K source.2.1 gamma).val.natDegree < T - w :=
    specializeFamily_natDegree_lt K source.2.1 gamma hTw
  have hCdeg :
      (specializeFamily K source.2.2 gamma).val.natDegree < T - W :=
    specializeFamily_natDegree_lt K source.2.2 gamma hTW
  have hBPdeg :
      ((specializeFamily K source.2.1 gamma).val * P).natDegree < T := by
    calc
      ((specializeFamily K source.2.1 gamma).val * P).natDegree ≤
          (specializeFamily K source.2.1 gamma).val.natDegree + P.natDegree :=
        Polynomial.natDegree_mul_le
      _ < T := by omega
  have hCSdeg :
      ((specializeFamily K source.2.2 gamma).val * S).natDegree < T := by
    calc
      ((specializeFamily K source.2.2 gamma).val * S).natDegree ≤
          (specializeFamily K source.2.2 gamma).val.natDegree + S.natDegree :=
        Polynomial.natDegree_mul_le
      _ < T := by omega
  have hrelationDegree : relation.natDegree < T := by
    dsimp only [relation]
    refine (Polynomial.natDegree_add_le _ _).trans_lt (max_lt ?_ hCSdeg)
    exact (Polynomial.natDegree_add_le _ _).trans_lt (max_lt hAdeg hBPdeg)
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    relation (active.image node)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hnode := kernel_all_seed_node_identity K node u0 u1 centre
      T w W r source hsource i gamma
    dsimp only [relation]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, hPagrees i hi,
      hSagrees i hi]
    exact hnode
  · rw [Finset.card_image_of_injective _ hinj]
    exact hrelationDegree.trans_le hcard

theorem coefficientFamily_finrank (r L : Nat) :
    Module.finrank K (CoefficientFamily K r L) = r * L := by
  rw [Module.finrank_pi_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis K L),
    Fintype.card_fin]
  simp only [Nat.cast_id]

theorem sourceSpace_finrank (T w W r : Nat) :
    Module.finrank K (SourceSpace K T w W r) =
      r * (T + (T - w) + (T - W)) := by
  rw [Module.finrank_prod, Module.finrank_prod,
    coefficientFamily_finrank, coefficientFamily_finrank,
    coefficientFamily_finrank]
  ring

theorem constraintSpace_finrank
    {I : Type*} [Fintype I] (r : Nat) :
    Module.finrank K (ConstraintSpace K I r) =
      Fintype.card I * (r + 1) := by
  have hinner : Module.finrank K (Fin (r + 1) → K) = r + 1 := by
    rw [Module.finrank_pi_fintype]
    simp only [finrank_self, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_id]
  rw [Module.finrank_pi_fintype]
  simp only [hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.cast_id]

/-- Pure dimension theorem for the literal nodal constraint map. -/
theorem exists_nonzero_nodal_kernel_of_gap
    {I : Type*} [Fintype I]
    (node u0 u1 centre : I → K) (T w W r : Nat)
    (hgap : Fintype.card I * (r + 1) <
      r * (T + (T - w) + (T - W))) :
    ∃ source : SourceSpace K T w W r,
      source ≠ 0 ∧ nodalConstraintMap K node u0 u1 centre T w W r source = 0 := by
  let f := nodalConstraintMap K node u0 u1 centre T w W r
  have hdim : Module.finrank K (ConstraintSpace K I r) <
      Module.finrank K (SourceSpace K T w W r) := by
    rw [constraintSpace_finrank, sourceSpace_finrank]
    exact hgap
  have hker : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨source, hsource, hsource_ne⟩ := (LinearMap.ker f).ne_bot_iff.mp hker
  exact ⟨source, hsource_ne, LinearMap.mem_ker.mp hsource⟩

theorem target_raw_dimensions :
    18 *
        (180413 + (180413 - 131071) + (180413 - 133225)) =
      4984974 ∧
    262144 * 19 = 4980736 ∧
    4984974 - 4980736 = 4238 := by
  norm_num

theorem target_raw_gap :
    262144 * 19 <
      18 *
        (180413 + (180413 - 131071) + (180413 - 133225)) := by
  norm_num

/-- The raw gap survives only in the first 236 values of the sharp scalar
window.  In particular, replacing the scalar degree by its proved uniform
upper bound is not a harmless weakening. -/
theorem target_gap_iff_scalar_cap_le_133460
    (W : Nat) (hlo : 133225 ≤ W) (hhi : W ≤ 149485) :
    262144 * 19 <
        18 * (180413 + (180413 - 131071) + (180413 - W)) ↔
      W ≤ 133460 := by
  omega

theorem target_last_positive_gap_dimensions :
    18 *
        (180413 + (180413 - 131071) + (180413 - 133460)) =
      4980744 ∧
    4980744 - 4980736 = 8 := by
  norm_num

theorem target_first_negative_gap_dimensions :
    18 *
        (180413 + (180413 - 131071) + (180413 - 133461)) =
      4980726 ∧
    4980736 - 4980726 = 10 := by
  norm_num

theorem target_safe_uniform_cap_deficit :
    18 *
        (180413 + (180413 - 131071) + (180413 - 149485)) =
      4692294 ∧
    4980736 - 4692294 = 288442 := by
  norm_num

/-- Increasing seed width rescues every scalar cap through `148023`.  At the
last such cap the minimal convenient width is `262145`, and the gap is
exactly one; this is still a symbolic finite-dimensional argument and does
not materialize the enormous matrix. -/
theorem target_adaptive_last_positive_dimensions :
    262145 *
        (180413 + (180413 - 131071) + (180413 - 148023)) =
      68720001025 ∧
    262144 * 262146 = 68720001024 ∧
    68720001025 - 68720001024 = 1 := by
  norm_num

theorem target_adaptive_last_positive_gap :
    262144 * (262145 + 1) <
      262145 *
        (180413 + (180413 - 131071) + (180413 - 148023)) := by
  norm_num

/-- At `W=148024`, adding more seed coefficients can never create a raw
dimension gap: each extra source layer and target layer both cost 262144,
while the target retains its initial 262144 equations. -/
theorem target_adaptive_first_impossible_gap (r : Nat) :
    ¬ 262144 * (r + 1) <
      r * (180413 + (180413 - 131071) + (180413 - 148024)) := by
  omega

/-- Numerical quotient threshold.  If the scalar cap is in the adaptive
range and `W ≤ 131071 + e`, then 32390 nonidentity nodes consume strictly
more than the worst fixed-relation multiplier width. -/
theorem target_mask_width_lt_adaptive_slope
    (W e t : Nat) (hW : W ≤ 148023)
    (hWe : W ≤ 131071 + e) (ht : 32390 ≤ t) :
    49342 - e - t < 148024 - W := by
  omega

/-- With the smallest uniform adaptive width, the raw kernel lower bound
then strictly exceeds the conservative masked-multiple upper bound. -/
theorem target_adaptive_kernel_beats_masked_bound
    (W e t : Nat) (hW : W ≤ 148023)
    (hWe : W ≤ 131071 + e) (ht : 32390 ≤ t) :
    262145 * (49342 - e - t) <
      262145 * (148024 - W) - 262144 := by
  have hslope := target_mask_width_lt_adaptive_slope W e t hW hWe ht
  omega

/-- In the opposite 292-exception branch, even the smallest possible
multiplier window leaves over half a million width-18 tautological
directions, far beyond the 4,238 raw surplus. -/
theorem target_large_identity_mask_capacity :
    17 * (49342 - 18414 - 292) = 520812 ∧
      4238 < 520812 := by
  norm_num

/-- Literal target-sized kernel source.  Width `18` means seed degree at most
`17`; the target contains `4,238` more source coefficients than equations. -/
theorem target_exists_nonzero_nodal_kernel
    {I : Type*} [Fintype I]
    (node u0 u1 centre : I → K)
    (hcard : Fintype.card I = 262144) :
    ∃ source : SourceSpace K 180413 131071 133225 18,
      source ≠ 0 ∧
      nodalConstraintMap K node u0 u1 centre
        180413 131071 133225 18 source = 0 := by
  apply exists_nonzero_nodal_kernel_of_gap K
  rw [hcard]
  exact target_raw_gap

/-- The one-dimensional adaptive kernel at the last potentially reachable
scalar cap.  Its seed degree is at most `262144`. -/
theorem target_exists_nonzero_adaptive_nodal_kernel
    {I : Type*} [Fintype I]
    (node u0 u1 centre : I → K)
    (hcard : Fintype.card I = 262144) :
    ∃ source : SourceSpace K 180413 131071 148023 262145,
      source ≠ 0 ∧
      nodalConstraintMap K node u0 u1 centre
        180413 131071 148023 262145 source = 0 := by
  apply exists_nonzero_nodal_kernel_of_gap K
  rw [hcard]
  exact target_adaptive_last_positive_gap

#print axioms coefficientFamily_finrank
#print axioms sourceSpace_finrank
#print axioms constraintSpace_finrank
#print axioms exists_nonzero_nodal_kernel_of_gap
#print axioms target_raw_dimensions
#print axioms target_raw_gap
#print axioms target_gap_iff_scalar_cap_le_133460
#print axioms target_last_positive_gap_dimensions
#print axioms target_first_negative_gap_dimensions
#print axioms target_safe_uniform_cap_deficit
#print axioms target_adaptive_last_positive_dimensions
#print axioms target_adaptive_last_positive_gap
#print axioms target_adaptive_first_impossible_gap
#print axioms target_mask_width_lt_adaptive_slope
#print axioms target_adaptive_kernel_beats_masked_bound
#print axioms target_large_identity_mask_capacity
#print axioms specializeFamily_natDegree_lt
#print axioms kernel_all_seed_node_identity
#print axioms kernel_global_syzygy
#print axioms target_exists_nonzero_nodal_kernel
#print axioms target_exists_nonzero_adaptive_nodal_kernel

end
end ProximityPrize.SubmissionLower.HeterogeneousLinearInterpolationSource6900
