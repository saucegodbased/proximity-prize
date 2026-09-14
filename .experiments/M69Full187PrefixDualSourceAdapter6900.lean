import ProximityPrize.Benchmark.TargetLower
import CompPoly.Univariate.NTT.Kernel
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Conditional single-covector prefix-dual adapter for m69

This file treats the conditional single-output model consisting of
independently choosable channels

`W(i)^t * P_t(node i)`,  with `degree P_t < f_t`.

This file derives, rather than assumes, the standard dual encoding of an
annihilator of those channels.  On a full multiplicative NTT domain, the
barycentric weight is `node/N`.  Therefore the annihilator of a prefix of
length `f_t` has a unique representative `H_t` of degree `< N-f_t` with

`lambda(i) * W(i)^t = node(i) * H_t(node(i))`.

Combining adjacent channels with `E(i)W(i)=N(i)` gives
`N H_t = E H_(t+1)` at every node, with no extra power of `X`.  Whenever the
two sides are below the domain size this is an honest polynomial identity;
coprimality then gives the high/low common-kernel normal form, and the next
adjacent relation gives `N^2 K_j = E^2 K_(j+1)` on the nodes.

**Scope guard.**  The literal fixed-shape Full187 source has several output
contacts.  Its transpose sends an output-covector tuple `lambda_y` to

`mu_k = sum_{y <= k} choose k y * W^(k-y) * lambda_y`,

not to one fixed `lambda * W^k`.  Therefore the adjacent recurrence proved
below is conditional and is not, by itself, a physical Full187 source
adapter.  `M69FixedShapePascalAdjointCountergate6900` formalizes the literal
Pascal transpose and the resulting countergate.
-/

namespace ProximityPrize.SubmissionLower.M69Full187PrefixDualSourceAdapter6900

open Polynomial
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 10000

namespace NTT

open CompPoly.CPolynomial.NTT

variable {K : Type*} [Field K]

/-- The NTT nodes are pairwise distinct. -/
theorem node_injective (D : Domain K) : Function.Injective D.node := by
  intro i j hij
  apply Fin.ext
  exact D.primitive.pow_inj i.isLt j.isLt hij

/-- Every NTT node is nonzero. -/
theorem node_ne_zero (D : Domain K) (i : D.Idx) : D.node i ≠ 0 := by
  exact pow_ne_zero _ (D.primitive.ne_zero D.n_ne_zero)

/-- The nodal polynomial of the complete NTT domain is exactly `X^N-1`. -/
theorem nodal_eq_X_pow_sub_one (D : Domain K) :
    Lagrange.nodal Finset.univ D.node =
      (Polynomial.X : K[X]) ^ D.n - 1 := by
  have hdegree : degree (1 : K[X]) <
      degree ((Polynomial.X : K[X]) ^ D.n) := by
    simp
  apply Polynomial.eq_of_degree_le_of_eval_index_eq
      (v := D.node) (s := (Finset.univ : Finset D.Idx))
  · exact (node_injective D).injOn
  · simp
  · rw [degree_sub_eq_left_of_degree_lt hdegree,
      Lagrange.degree_nodal, Finset.card_univ, Fintype.card_fin,
      degree_pow, degree_X, nsmul_eq_mul, mul_one]
  · rw [Lagrange.nodal_monic,
      leadingCoeff_sub_of_degree_lt hdegree, monic_X_pow]
  · intro i _hi
    rw [Lagrange.eval_nodal_at_node (Finset.mem_univ i)]
    simp only [eval_sub, eval_pow, eval_X, eval_one]
    symm
    exact sub_eq_zero.mpr (by
      simp only [CompPoly.CPolynomial.NTT.Domain.node]
      rw [← pow_mul]
      rw [Nat.mul_comm, pow_mul]
      have homega : D.omega ^ D.n = 1 := by
        simpa only [CompPoly.CPolynomial.NTT.Domain.n] using
          D.primitive.pow_eq_one
      rw [homega, one_pow])

/-- The exact barycentric weight on the complete multiplicative NTT domain.
The scalar `nInv` is independent of the node. -/
theorem nodalWeight_eq_nInv_mul_node (D : Domain K) (i : D.Idx) :
    Lagrange.nodalWeight Finset.univ D.node i = D.nInv * D.node i := by
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ i),
    nodal_eq_X_pow_sub_one D]
  simp only [derivative_sub, derivative_pow, derivative_X, mul_one,
    derivative_one, sub_zero, eval_mul, eval_C, eval_pow, eval_X]
  have hn : (D.n : K) ≠ 0 := D.natCast_ne_zero
  have hx : D.node i ≠ 0 := node_ne_zero D i
  have hxpow : D.node i ^ D.n = 1 := by
    change (D.omega ^ (i : Nat)) ^ D.n = 1
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    have homega : D.omega ^ D.n = 1 := by
      simpa only [CompPoly.CPolynomial.NTT.Domain.n] using
        D.primitive.pow_eq_one
    rw [homega, one_pow]
  have hpos : 0 < D.n := D.n_pos
  have hsplit : D.node i ^ D.n = D.node i ^ (D.n - 1) * D.node i := by
    nth_rewrite 1 [show D.n = (D.n - 1) + 1 by omega]
    rw [pow_succ]
  rw [hsplit] at hxpow
  rw [Domain.nInv]
  apply inv_eq_of_mul_eq_one_right
  calc
    ((D.n : K) * D.node i ^ (D.n - 1)) *
        ((D.n : K)⁻¹ * D.node i) =
        ((D.n : K) * (D.n : K)⁻¹) *
          (D.node i ^ (D.n - 1) * D.node i) := by ring
    _ = 1 := by rw [mul_inv_cancel₀ hn, hxpow, one_mul]

end NTT

/-- Orthogonality to one literal prefix channel of the Full187 source. -/
def PrefixChannelOrthogonal
    {I K : Type*} [Fintype I] [Field K]
    (nodes : I -> K) (W lambda : I -> K) (t f : Nat) : Prop :=
  ∀ P : K[X], P.natDegree < f →
    (∑ i, lambda i * (W i ^ t * P.eval (nodes i))) = 0

/-- The complete source condition: every independently choosable power/prefix
channel is killed by the same output covector. -/
def PrefixPowerSourceOrthogonal
    {I K T : Type*} [Fintype I] [Field K]
    (nodes : I -> K) (W lambda : I -> K)
    (power cap : T -> Nat) : Prop :=
  ∀ a, PrefixChannelOrthogonal nodes W lambda (power a) (cap a)

/-- Generic Lagrange form of prefix duality.  It is useful separately from
the NTT specialization: every prefix annihilator is a nodal-weight-scaled
short polynomial. -/
theorem exists_nodalWeight_prefix_dual
    {I K : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Field K]
    (nodes : I -> K) (hnodes : Function.Injective nodes)
    (mu : I -> K) (f : Nat) (hf : f < Fintype.card I)
    (hmoments : ∀ j < f, (∑ i, mu i * nodes i ^ j) = 0) :
    ∃ H : K[X],
      H.natDegree < Fintype.card I - f ∧
      ∀ i, mu i =
        Lagrange.nodalWeight Finset.univ nodes i * H.eval (nodes i) := by
  let weights : I -> K := Lagrange.nodalWeight Finset.univ nodes
  let H : K[X] := Lagrange.interpolate Finset.univ nodes
    (fun i => mu i / weights i)
  have hw : ∀ i, weights i ≠ 0 := fun i =>
    Lagrange.nodalWeight_ne_zero hnodes.injOn (Finset.mem_univ i)
  have hHeval : ∀ i, H.eval (nodes i) = mu i / weights i := fun i =>
    Lagrange.eval_interpolate_at_node _ hnodes.injOn (Finset.mem_univ i)
  have hdegree : H.degree < (Fintype.card I : WithBot Nat) := by
    simpa only [Finset.card_univ] using
      (Lagrange.degree_interpolate_lt
        (s := (Finset.univ : Finset I)) (v := nodes)
        (r := fun i => mu i / weights i) hnodes.injOn)
  have hnat : H.natDegree ≤ Fintype.card I - f - 1 := by
    by_cases hH : H = 0
    · simp only [hH, natDegree_zero]
      omega
    · have hnatlt : H.natDegree < Fintype.card I :=
        (natDegree_lt_iff_degree_lt hH).mpr hdegree
      by_contra hfail
      have hlow : Fintype.card I - f <= H.natDegree := by omega
      let j := Fintype.card I - 1 - H.natDegree
      have hj : j < f := by
        dsimp only [j]
        omega
      have hprodDegree :
          (H * Polynomial.X ^ j).degree <
            (Fintype.card I : WithBot Nat) := by
        have hX : ((Polynomial.X : K[X]) ^ j) ≠ 0 :=
          pow_ne_zero _ Polynomial.X_ne_zero
        rw [degree_mul, degree_X_pow]
        rw [degree_eq_natDegree hH]
        norm_cast
        dsimp only [j]
        omega
      have hcoeff0 := Lagrange.coeff_eq_sum
        (s := (Finset.univ : Finset I)) (v := nodes)
        hnodes.injOn hprodDegree
      have hcoeff :
          (H * Polynomial.X ^ j).coeff (Fintype.card I - 1) =
            ∑ i, (H * Polynomial.X ^ j).eval (nodes i) /
              ∏ x ∈ (Finset.univ : Finset I).erase i,
                (nodes i - nodes x) := by
        simpa only [Finset.card_univ] using hcoeff0
      have hweightSum :
          (∑ i, weights i * H.eval (nodes i) * nodes i ^ j) = 0 := by
        calc
          (∑ i, weights i * H.eval (nodes i) * nodes i ^ j) =
              ∑ i, mu i * nodes i ^ j := by
                apply Finset.sum_congr rfl
                intro i _hi
                rw [hHeval i]
                field_simp [hw i]
          _ = 0 := hmoments j hj
      have htop : (H * Polynomial.X ^ j).coeff
          (Fintype.card I - 1) = 0 := by
        calc
          (H * Polynomial.X ^ j).coeff (Fintype.card I - 1) =
              ∑ i, (H * Polynomial.X ^ j).eval (nodes i) /
                ∏ x ∈ (Finset.univ : Finset I).erase i,
                  (nodes i - nodes x) := hcoeff
          _ = ∑ i, weights i * H.eval (nodes i) * nodes i ^ j := by
            apply Finset.sum_congr rfl
            intro i _hi
            simp only [eval_mul, eval_pow, eval_X, div_eq_mul_inv,
              weights, Lagrange.nodalWeight, Finset.prod_inv_distrib]
            ring
          _ = 0 := hweightSum
      have hindex : Fintype.card I - 1 = H.natDegree + j := by
        dsimp only [j]
        omega
      rw [hindex, coeff_mul_X_pow] at htop
      have hc : H.coeff H.natDegree ≠ 0 := by
        rw [coeff_natDegree]
        exact leadingCoeff_ne_zero.mpr hH
      exact hc htop
  refine ⟨H, by omega, ?_⟩
  intro i
  change mu i = weights i * H.eval (nodes i)
  rw [hHeval i]
  field_simp [hw i]

/-- Exact NTT specialization.  The invertible constant `nInv` is absorbed
into `H`, producing the advertised common `node i` factor. -/
theorem exists_ntt_prefix_dual
    {K : Type*} [Field K]
    (D : CompPoly.CPolynomial.NTT.Domain K)
    (mu : D.Idx -> K) (f : Nat) (hf : f < D.n)
    (hmoments : ∀ j < f, (∑ i, mu i * D.node i ^ j) = 0) :
    ∃ H : K[X], H.natDegree < D.n - f ∧
      ∀ i, mu i = D.node i * H.eval (D.node i) := by
  have hnonempty : Nonempty D.Idx := Fin.pos_iff_nonempty.mp D.n_pos
  letI : Nonempty D.Idx := hnonempty
  obtain ⟨H, hHdegree, hH⟩ :=
    exists_nodalWeight_prefix_dual D.node (NTT.node_injective D) mu f
      (by simpa only [Fintype.card_fin] using hf)
      (by simpa only [Fintype.card_fin] using hmoments)
  refine ⟨Polynomial.C D.nInv * H, ?_, ?_⟩
  · by_cases hH0 : H = 0
    · simp only [hH0, mul_zero, natDegree_zero]
      exact Nat.sub_pos_of_lt hf
    · have hn : D.nInv ≠ 0 := inv_ne_zero D.natCast_ne_zero
      rw [natDegree_mul (Polynomial.C_ne_zero.mpr hn) hH0, natDegree_C]
      simpa only [zero_add, Fintype.card_fin] using hHdegree
  · intro i
    rw [hH i]
    calc
      Lagrange.nodalWeight Finset.univ D.node i * H.eval (D.node i) =
          (D.nInv * D.node i) * H.eval (D.node i) := by
            rw [NTT.nodalWeight_eq_nInv_mul_node D i]
      _ = D.node i *
          (Polynomial.C D.nInv * H).eval (D.node i) := by
            simp only [eval_mul, eval_C]
            ring

/-- The short NTT prefix-dual polynomial is unique.  This rules out a hidden
normalization choice when adjacent channels are compared. -/
theorem ntt_prefix_dual_unique
    {K : Type*} [Field K]
    (D : CompPoly.CPolynomial.NTT.Domain K)
    (mu : D.Idx -> K) (f : Nat) (_hf : f < D.n)
    (H G : K[X])
    (hHdegree : H.natDegree < D.n - f)
    (hGdegree : G.natDegree < D.n - f)
    (hH : ∀ i, mu i = D.node i * H.eval (D.node i))
    (hG : ∀ i, mu i = D.node i * G.eval (D.node i)) :
    H = G := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
    (s := (Finset.univ : Finset D.Idx)) (v := D.node)
  · exact (NTT.node_injective D).injOn
  · by_cases hz : H = 0
    · simp only [hz, degree_zero, Finset.card_univ, Fintype.card_fin]
      exact WithBot.bot_lt_coe D.n
    · apply (natDegree_lt_iff_degree_lt hz).mp
      simpa only [Finset.card_univ, Fintype.card_fin] using
        hHdegree.trans_le (Nat.sub_le D.n f)
  · by_cases hz : G = 0
    · simp only [hz, degree_zero, Finset.card_univ, Fintype.card_fin]
      exact WithBot.bot_lt_coe D.n
    · apply (natDegree_lt_iff_degree_lt hz).mp
      simpa only [Finset.card_univ, Fintype.card_fin] using
        hGdegree.trans_le (Nat.sub_le D.n f)
  · intro i _hi
    apply mul_left_cancel₀ (NTT.node_ne_zero D i)
    rw [← hH i, ← hG i]

/-- One conditional fixed-covector power channel yields its unique short dual
polynomial on the complete NTT domain. -/
theorem exists_prefix_channel_dual
    {K : Type*} [Field K]
    (D : CompPoly.CPolynomial.NTT.Domain K)
    (W lambda : D.Idx -> K) (t f : Nat) (hf : f < D.n)
    (horth : PrefixChannelOrthogonal D.node W lambda t f) :
    ∃ H : K[X], H.natDegree < D.n - f ∧
      ∀ i, lambda i * W i ^ t = D.node i * H.eval (D.node i) := by
  apply exists_ntt_prefix_dual D (fun i => lambda i * W i ^ t) f hf
  intro j hj
  have h := horth ((Polynomial.X : K[X]) ^ j)
    (by simpa only [natDegree_X_pow] using hj)
  simpa only [eval_pow, eval_X, mul_assoc] using h

/-- Simultaneously extract all prefix-dual polynomials from an annihilator of
the conditional direct sum of fixed-covector power channels. -/
theorem exists_prefix_power_source_duals
    {K T : Type*} [Field K]
    (D : CompPoly.CPolynomial.NTT.Domain K)
    (W lambda : D.Idx -> K) (power cap : T -> Nat)
    (hcap : ∀ a, cap a < D.n)
    (hsource : PrefixPowerSourceOrthogonal D.node W lambda power cap) :
    ∃ H : T -> K[X], ∀ a,
      (H a).natDegree < D.n - cap a ∧
      ∀ i, lambda i * W i ^ power a =
        D.node i * (H a).eval (D.node i) := by
  choose H hH using fun a =>
    exists_prefix_channel_dual D W lambda (power a) (cap a)
      (hcap a) (hsource a)
  exact Exists.intro H hH

namespace Actual

open ProximityPrize.Benchmark
open CompPoly.CPolynomial.NTT

abbrev Field := IRSProfile.Field
abbrev Index := IRSProfile.Index

/-- The benchmark's base-field NTT domain, embedded into the exact sextic
field used by the lower challenge. -/
abbrev domain : Domain Field where
  logN := 18
  omega := CompPoly.Extension.Ext.ofBase IRSProfile.baseNttDomain.omega
  primitive := by
    simpa only [CompPoly.Extension.Ext.ofBaseRingHom_apply,
      IRSProfile.baseNttDomain,
      CompPoly.CPolynomial.NTT.KoalaBear.domainOfLogN] using
      IRSProfile.baseNttDomain.primitive.map_of_injective
        (CompPoly.Extension.Ext.ofBaseRingHom _).injective

theorem domain_n : domain.n = 262144 := by
  norm_num [domain, Domain.n, IRSProfile.baseNttDomain,
    CompPoly.CPolynomial.NTT.KoalaBear.domainOfLogN]

theorem domain_node (i : Index) : domain.node i = IRSProfile.domain i := by
  change
    (CompPoly.Extension.Ext.ofBase IRSProfile.baseNttDomain.omega : Field) ^
        (i : Nat) =
      CompPoly.Extension.Ext.ofBase (IRSProfile.baseNttDomain.node i)
  change
    (CompPoly.Extension.Ext.ofBase IRSProfile.baseNttDomain.omega : Field) ^
        (i : Nat) =
      CompPoly.Extension.Ext.ofBase
        (IRSProfile.baseNttDomain.omega ^ (i : Nat))
  rw [← CompPoly.Extension.Ext.ofBaseRingHom_apply,
    ← CompPoly.Extension.Ext.ofBaseRingHom_apply, map_pow]

/-- Conditional fixed-covector source condition on `IRSProfile.domain`, with
no abstract-node hypothesis left to instantiate.  This is not the literal
multi-output Pascal adjoint. -/
def Full187PrefixChannelOrthogonal
    (W lambda : Index -> Field) (t f : Nat) : Prop :=
  PrefixChannelOrthogonal IRSProfile.domain W lambda t f

def Full187PrefixPowerSourceOrthogonal
    {T : Type*} (W lambda : Index -> Field)
    (power cap : T -> Nat) : Prop :=
  PrefixPowerSourceOrthogonal IRSProfile.domain W lambda power cap

/-- Concrete prefix-dual extraction on the benchmark domain. -/
theorem exists_full187_prefix_channel_dual
    (W lambda : Index -> Field) (t f : Nat) (hf : f < 262144)
    (horth : Full187PrefixChannelOrthogonal W lambda t f) :
    ∃ H : Field[X], H.natDegree < 262144 - f ∧
      ∀ i, lambda i * W i ^ t =
        IRSProfile.domain i * H.eval (IRSProfile.domain i) := by
  have hnodes : domain.node = IRSProfile.domain := funext domain_node
  have hf' : f < domain.n := by simpa only [domain_n] using hf
  obtain ⟨H, hdegree, hH⟩ :=
    exists_prefix_channel_dual domain W lambda t f hf' (by
      rw [hnodes]
      exact horth)
  refine ⟨H, ?_, ?_⟩
  · simpa only [domain_n] using hdegree
  · intro i
    calc
      lambda i * W i ^ t =
          domain.node (show domain.Idx from i) *
            H.eval (domain.node (show domain.Idx from i)) :=
        hH (show domain.Idx from i)
      _ = IRSProfile.domain i * H.eval (IRSProfile.domain i) := by
        rw [domain_node i]

/-- Concrete simultaneous extraction for every independently choosable
Full187 power/prefix channel. -/
theorem exists_full187_prefix_power_source_duals
    {T : Type*} (W lambda : Index -> Field)
    (power cap : T -> Nat) (hcap : ∀ a, cap a < 262144)
    (hsource : Full187PrefixPowerSourceOrthogonal W lambda power cap) :
    ∃ H : T -> Field[X], ∀ a,
      (H a).natDegree < 262144 - cap a ∧
      ∀ i, lambda i * W i ^ power a =
        IRSProfile.domain i * (H a).eval (IRSProfile.domain i) := by
  choose H hH using fun a =>
    exists_full187_prefix_channel_dual W lambda (power a) (cap a)
      (hcap a) (hsource a)
  exact ⟨H, hH⟩

/-- Concrete uniqueness on `IRSProfile.domain`. -/
theorem full187_prefix_dual_unique
    (mu : Index -> Field) (f : Nat) (hf : f < 262144)
    (H G : Field[X])
    (hHdegree : H.natDegree < 262144 - f)
    (hGdegree : G.natDegree < 262144 - f)
    (hH : ∀ i, mu i = IRSProfile.domain i * H.eval (IRSProfile.domain i))
    (hG : ∀ i, mu i = IRSProfile.domain i * G.eval (IRSProfile.domain i)) :
    H = G := by
  have hnodes : domain.node = IRSProfile.domain := funext domain_node
  apply ntt_prefix_dual_unique domain mu f
    (by simpa only [domain_n] using hf) H G
  · simpa only [domain_n] using hHdegree
  · simpa only [domain_n] using hGdegree
  · intro i
    rw [hnodes]
    exact hH i
  · intro i
    rw [hnodes]
    exact hG i

end Actual

/-- Adjacent extracted source duals satisfy the exact rational relation.
No `X` factor survives. -/
theorem adjacent_relation_of_extracted_duals
    {K : Type*} [Field K]
    (D : CompPoly.CPolynomial.NTT.Domain K)
    (E N : K[X]) (W lambda : D.Idx -> K)
    (t : Nat) (H Hnext : K[X])
    (hW : ∀ i, E.eval (D.node i) * W i = N.eval (D.node i))
    (hH : ∀ i, lambda i * W i ^ t =
      D.node i * H.eval (D.node i))
    (hHnext : ∀ i, lambda i * W i ^ (t + 1) =
      D.node i * Hnext.eval (D.node i)) :
    ∀ i, (N * H).eval (D.node i) =
      (E * Hnext).eval (D.node i) := by
  intro i
  simp only [eval_mul]
  apply mul_left_cancel₀ (NTT.node_ne_zero D i)
  calc
    D.node i * (N.eval (D.node i) * H.eval (D.node i)) =
        N.eval (D.node i) * (D.node i * H.eval (D.node i)) := by ring
    _ = N.eval (D.node i) * (lambda i * W i ^ t) := by rw [← hH i]
    _ = (lambda i * W i ^ t) *
        (E.eval (D.node i) * W i) := by rw [hW i]; ring
    _ = E.eval (D.node i) *
        (lambda i * W i ^ (t + 1)) := by rw [pow_succ]; ring
    _ = E.eval (D.node i) *
        (D.node i * Hnext.eval (D.node i)) := by rw [hHnext i]
    _ = D.node i *
        (E.eval (D.node i) * Hnext.eval (D.node i)) := by ring

/-- No-wrap turns an adjacent nodal relation into a polynomial identity. -/
theorem adjacent_polynomial_identity_of_no_wrap
    {K : Type*} [Field K]
    (D : CompPoly.CPolynomial.NTT.Domain K)
    (E N H Hnext : K[X])
    (hleft : (N * H).natDegree < D.n)
    (hright : (E * Hnext).natDegree < D.n)
    (hnodal : ∀ i, (N * H).eval (D.node i) =
      (E * Hnext).eval (D.node i)) :
    N * H = E * Hnext := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
    (s := (Finset.univ : Finset D.Idx)) (v := D.node)
  · exact (NTT.node_injective D).injOn
  · by_cases hz : N * H = 0
    · simp only [hz, degree_zero, Finset.card_univ, Fintype.card_fin]
      exact WithBot.bot_lt_coe D.n
    · apply (natDegree_lt_iff_degree_lt hz).mp
      simpa only [Finset.card_univ, Fintype.card_fin] using hleft
  · by_cases hz : E * Hnext = 0
    · simp only [hz, degree_zero, Finset.card_univ, Fintype.card_fin]
      exact WithBot.bot_lt_coe D.n
    · apply (natDegree_lt_iff_degree_lt hz).mp
      simpa only [Finset.card_univ, Fintype.card_fin] using hright
  · intro i _hi
    exact hnodal i

/-- Coprimality converts one no-wrap adjacent pair into a single kernel. -/
theorem coprime_high_low_normal_form
    {K : Type*} [Field K] (E N Hhigh Hlow : K[X])
    (hE : E ≠ 0) (hcop : IsCoprime E N)
    (hrelation : N * Hhigh = E * Hlow) :
    ∃ T, Hhigh = E * T ∧ Hlow = N * T := by
  have hdiv : E ∣ N * Hhigh := Exists.intro Hlow hrelation
  have hEH : E ∣ Hhigh := hcop.dvd_of_dvd_mul_left hdiv
  obtain ⟨T, hT⟩ := hEH
  refine ⟨T, hT, ?_⟩
  apply mul_left_cancel₀ hE
  calc
    E * Hlow = N * Hhigh := hrelation.symm
    _ = N * (E * T) := by rw [hT]
    _ = E * (N * T) := by ring

/-- Substituting two consecutive high/low normal forms into the intervening
low/high relation yields the oriented square recurrence, with no `X^2`. -/
theorem paired_recurrence_of_source_duals
    {K : Type*} [Field K]
    (D : CompPoly.CPolynomial.NTT.Domain K)
    (E N Hlow Hnext Kprev Knext : K[X])
    (hlow : Hlow = N * Kprev) (hnext : Hnext = E * Knext)
    (hmiddle : ∀ i, (N * Hlow).eval (D.node i) =
      (E * Hnext).eval (D.node i)) :
    ∀ i, (N ^ 2 * Kprev).eval (D.node i) =
      (E ^ 2 * Knext).eval (D.node i) := by
  intro i
  have h := hmiddle i
  rw [hlow, hnext] at h
  simpa only [eval_mul, eval_pow, pow_two, mul_assoc] using h

/-- Exact target-size no-wrap arithmetic consumed by the m69 all-shape
ledger. -/
theorem target_m69_no_wrap_arithmetic :
    149776 + 3342 - 1 = 153117 ∧ 153117 < 262144 ∧
    18414 + 134413 - 1 = 152826 ∧ 152826 < 262144 := by
  norm_num

#print axioms NTT.nodal_eq_X_pow_sub_one
#print axioms NTT.nodalWeight_eq_nInv_mul_node
#print axioms exists_nodalWeight_prefix_dual
#print axioms exists_ntt_prefix_dual
#print axioms ntt_prefix_dual_unique
#print axioms exists_prefix_channel_dual
#print axioms exists_prefix_power_source_duals
#print axioms Actual.domain_n
#print axioms Actual.domain_node
#print axioms Actual.exists_full187_prefix_channel_dual
#print axioms Actual.exists_full187_prefix_power_source_duals
#print axioms Actual.full187_prefix_dual_unique
#print axioms adjacent_relation_of_extracted_duals
#print axioms adjacent_polynomial_identity_of_no_wrap
#print axioms coprime_high_low_normal_form
#print axioms paired_recurrence_of_source_duals
#print axioms target_m69_no_wrap_arithmetic

end
end ProximityPrize.SubmissionLower.M69Full187PrefixDualSourceAdapter6900
