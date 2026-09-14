import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Root migration and backward recurrence for the m69 dual chain

This file proves the algebraic engine behind the conditional many-numerator-
zero route.  The recurrence is an explicit premise:

`N^2*K_j = E^2*K_(j+1)` at every evaluation node.

At a zero of `N`, nonvanishing of the node and `E` forces `K_(j+1)` to
vanish.  If the last kernel is shorter than the numerator zero set, it is
zero.  The same recurrence then propagates zero backwards on the complement
of that zero set.  These theorems do not derive the recurrence from the
physical Full187 source map.
-/

namespace ProximityPrize.SubmissionLower.M69ManyZeroDualBackwardRecurrence6900

open Polynomial

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000

local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- A polynomial shorter than a finite set of distinct evaluation nodes and
zero at all of them is the zero polynomial. -/
theorem eq_zero_of_eval_zero_on_finset
    {I K : Type*} [Fintype I] [Field K]
    (nodes : I ↪ K) (S : Finset I) (P : K[X])
    (hdegree : P.natDegree < S.card)
    (heval : ∀ i ∈ S, P.eval (nodes i) = 0) :
    P = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    P (S.image nodes)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact heval i hi
  · rw [Finset.card_image_of_injOn nodes.injective.injOn]
    exact hdegree

/-- Two polynomials of degree below the number of injective nodes are equal
if their evaluations agree at every node. -/
theorem eq_of_nodal_eq_of_natDegree_lt_card
    {I K : Type*} [Fintype I] [Field K]
    (nodes : I ↪ K) (P Q : K[X])
    (hP : P.natDegree < Fintype.card I)
    (hQ : Q.natDegree < Fintype.card I)
    (heval : ∀ i, P.eval (nodes i) = Q.eval (nodes i)) :
    P = Q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval_zero_on_finset nodes Finset.univ (P - Q)
  · simpa only [Finset.card_univ] using
      (natDegree_sub_le P Q).trans_lt (max_lt hP hQ)
  · intro i _hi
    simp only [eval_sub, heval i, sub_self]

/-- The exact oriented recurrence used below.  There is no `X^2` factor for
the literal source `sum_t W^t * F_<f_t>` with `W=N/E`: the common nodal
factor in the standard prefix-dual encoding cancels in adjacent powers. -/
def NodalSquareRecurrence
    {I K : Type*} [Field K] (nodes : I → K)
    (E N Kprev Knext : K[X]) : Prop :=
  ∀ i,
    (N ^ 2 * Kprev).eval (nodes i) =
      (E ^ 2 * Knext).eval (nodes i)

/-- Pointwise form of the standard prefix-dual encoding.  The same nodal
factor `nodes i` occurs for every prefix length; this is why it cancels from
adjacent rational-power channels. -/
def NodalPrefixDualEncoding
    {I K : Type*} [Field K] (nodes : I → K)
    (W lambda : I → K) (t : Nat) (H : K[X]) : Prop :=
  ∀ i, lambda i * W i ^ t = nodes i * H.eval (nodes i)

/-- Exact adjacent-channel calculation for the literal multiplier `W=N/E`.
It produces `N*H_t = E*H_(t+1)` at the nodes and no power of `X`.

This theorem catches the off-by-`X` normalization which had appeared in an
earlier exploratory square gate. -/
theorem adjacent_relation_of_prefix_dual_encodings
    {I K : Type*} [Field K] (nodes : I → K)
    (E N : K[X]) (W lambda : I → K) (t : Nat) (H Hnext : K[X])
    (hnodes : ∀ i, nodes i ≠ 0)
    (hW : ∀ i, E.eval (nodes i) * W i = N.eval (nodes i))
    (hdual : NodalPrefixDualEncoding nodes W lambda t H)
    (hdualNext : NodalPrefixDualEncoding nodes W lambda (t + 1) Hnext) :
    ∀ i, (N * H).eval (nodes i) = (E * Hnext).eval (nodes i) := by
  intro i
  simp only [eval_mul]
  apply mul_left_cancel₀ (hnodes i)
  calc
    nodes i * (N.eval (nodes i) * H.eval (nodes i)) =
        N.eval (nodes i) * (nodes i * H.eval (nodes i)) := by ring
    _ = N.eval (nodes i) * (lambda i * W i ^ t) := by
      rw [← hdual i]
    _ = (lambda i * W i ^ t) * N.eval (nodes i) := by ring
    _ = (lambda i * W i ^ t) * (E.eval (nodes i) * W i) := by
      rw [hW i]
    _ = E.eval (nodes i) * (lambda i * W i ^ (t + 1)) := by
      rw [pow_succ]
      ring
    _ = E.eval (nodes i) *
        (nodes i * Hnext.eval (nodes i)) := by rw [hdualNext i]
    _ = nodes i *
        (E.eval (nodes i) * Hnext.eval (nodes i)) := by ring

/-- Substituting two adjacent coprime normal forms into the intervening
adjacent relation gives the paired recurrence, again with no `X^2` factor. -/
theorem paired_recurrence_has_no_X_factor
    {I K : Type*} [Field K] (nodes : I → K)
    (E N Hlow Hnext Kprev Knext : K[X])
    (hlow : Hlow = N * Kprev)
    (hnext : Hnext = E * Knext)
    (hmiddle : ∀ i,
      (N * Hlow).eval (nodes i) = (E * Hnext).eval (nodes i)) :
    NodalSquareRecurrence nodes E N Kprev Knext := by
  intro i
  have h := hmiddle i
  rw [hlow, hnext] at h
  simpa only [eval_mul, eval_pow, pow_two, mul_assoc] using h

/-- At numerator roots, the oriented square recurrence forces the *next*
kernel to vanish.  A degree bound then kills that kernel globally. -/
theorem next_eq_zero_of_nodal_square_recurrence_on_numerator_roots
    {I K : Type*} [Fintype I] [Field K]
    (nodes : I ↪ K) (Z : Finset I) (E N Kprev Knext : K[X])
    (hEroot : ∀ i ∈ Z, E.eval (nodes i) ≠ 0)
    (hNroot : ∀ i ∈ Z, N.eval (nodes i) = 0)
    (hrec : NodalSquareRecurrence nodes E N Kprev Knext)
    (hdegree : Knext.natDegree < Z.card) :
    Knext = 0 := by
  apply eq_zero_of_eval_zero_on_finset nodes Z Knext hdegree
  intro i hi
  have hzero :
      E.eval (nodes i) ^ 2 * Knext.eval (nodes i) = 0 := by
    calc
      E.eval (nodes i) ^ 2 * Knext.eval (nodes i) =
          (E ^ 2 * Knext).eval (nodes i) := by
            simp only [eval_mul, eval_pow]
      _ = (N ^ 2 * Kprev).eval (nodes i) := (hrec i).symm
      _ = 0 := by simp [eval_mul, eval_pow, hNroot i hi]
  have hcoefficient : E.eval (nodes i) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (hEroot i hi)
  exact (mul_eq_zero.mp hzero).resolve_left hcoefficient

/-- Once the next kernel is zero, the recurrence forces the previous kernel
to vanish on every node where `N` is nonzero.  Enough such nodes kill it
globally. -/
theorem prev_eq_zero_of_next_eq_zero_on_numerator_complement
    {I K : Type*} [Fintype I] [Field K]
    (nodes : I ↪ K) (C : Finset I) (E N Kprev Knext : K[X])
    (hNnonroot : ∀ i ∈ C, N.eval (nodes i) ≠ 0)
    (hrec : NodalSquareRecurrence nodes E N Kprev Knext)
    (hnext : Knext = 0)
    (hdegree : Kprev.natDegree < C.card) :
    Kprev = 0 := by
  apply eq_zero_of_eval_zero_on_finset nodes C Kprev hdegree
  intro i hi
  have h := hrec i
  simp only [hnext, eval_mul, eval_pow, eval_zero, mul_zero] at h
  have hcoefficient : N.eval (nodes i) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (hNnonroot i hi)
  exact (mul_eq_zero.mp h).resolve_left hcoefficient

/-- A finite oriented recurrence chain is killed from its last member and
then backwards.  The last member is killed on `Z`; every previous member is
killed on the supplied complement `C`.

The theorem intentionally asks for the root/nonroot facts separately rather
than silently assuming that `C` is literally `univ \ Z`.  This makes the
precise hypotheses visible at the future source adapter. -/
theorem nodal_square_recurrence_chain_forces_zero
    {I K : Type*} [Fintype I] [Field K]
    (nodes : I ↪ K) (Z C : Finset I) (E N : K[X])
    (kernels : Nat → K[X]) (m : Nat) (hm : 1 ≤ m)
    (hEroot : ∀ i ∈ Z, E.eval (nodes i) ≠ 0)
    (hNroot : ∀ i ∈ Z, N.eval (nodes i) = 0)
    (hNnonroot : ∀ i ∈ C, N.eval (nodes i) ≠ 0)
    (hrec : ∀ j, j < m →
      NodalSquareRecurrence nodes E N (kernels j) (kernels (j + 1)))
    (hlastDegree : (kernels m).natDegree < Z.card)
    (hprevDegree : ∀ j, j < m → (kernels j).natDegree < C.card) :
    ∀ j, j ≤ m → kernels j = 0 := by
  have hmpos : 0 < m := by omega
  have hlastRec :
      NodalSquareRecurrence nodes E N (kernels (m - 1)) (kernels m) := by
    have h := hrec (m - 1) (by omega)
    simpa only [Nat.sub_add_cancel hm] using h
  have hlast : kernels m = 0 :=
    next_eq_zero_of_nodal_square_recurrence_on_numerator_roots
      nodes Z E N (kernels (m - 1)) (kernels m)
      hEroot hNroot hlastRec hlastDegree
  have hreverse : ∀ d, d ≤ m → kernels (m - d) = 0 := by
    intro d
    induction d with
    | zero =>
        intro _hd
        simpa only [Nat.sub_zero] using hlast
    | succ d ih =>
        intro hdm
        have hdlt : m - (d + 1) < m := by omega
        have hnext : kernels (m - d) = 0 := ih (by omega)
        have hstep := hrec (m - (d + 1)) hdlt
        have hindex : m - (d + 1) + 1 = m - d := by omega
        rw [hindex] at hstep
        exact prev_eq_zero_of_next_eq_zero_on_numerator_complement
          nodes C E N (kernels (m - (d + 1))) (kernels (m - d))
          hNnonroot hstep hnext (hprevDegree _ hdlt)
  intro j hj
  have h := hreverse (m - j) (Nat.sub_le m j)
  simpa only [Nat.sub_sub_self hj] using h

/-- Coprimality converts one honest polynomial high/low relation into a
single kernel.  This is the algebraic normal form used for each adjacent
high-prefix/low-prefix pair after a separate no-wrap proof. -/
theorem coprime_high_low_normal_form
    {K : Type*} [Field K] (E N Hhigh Hlow : K[X])
    (hE : E ≠ 0) (hcop : IsCoprime E N)
    (hrelation : N * Hhigh = E * Hlow) :
    ∃ T, Hhigh = E * T ∧ Hlow = N * T := by
  have hdiv : E ∣ N * Hhigh := ⟨Hlow, hrelation⟩
  have hEH : E ∣ Hhigh := hcop.dvd_of_dvd_mul_left hdiv
  obtain ⟨T, hT⟩ := hEH
  refine ⟨T, hT, ?_⟩
  apply mul_left_cancel₀ hE
  calc
    E * Hlow = N * Hhigh := hrelation.symm
    _ = N * (E * T) := by rw [hT]
    _ = E * (N * T) := by ring

/-- Complete generic adjacent-pair adapter: a bounded nodal relation is first
upgraded to an honest polynomial equality, then coprimality produces its
single kernel.  The all-shape executable checks the required degree bounds
for every m69 high/low pair. -/
theorem coprime_high_low_normal_form_of_nodal_no_wrap
    {I K : Type*} [Fintype I] [Field K]
    (nodes : I ↪ K) (E N Hhigh Hlow : K[X])
    (hE : E ≠ 0) (hcop : IsCoprime E N)
    (hhighDegree : (N * Hhigh).natDegree < Fintype.card I)
    (hlowDegree : (E * Hlow).natDegree < Fintype.card I)
    (hrelation : ∀ i,
      (N * Hhigh).eval (nodes i) = (E * Hlow).eval (nodes i)) :
    ∃ T, Hhigh = E * T ∧ Hlow = N * T := by
  apply coprime_high_low_normal_form E N Hhigh Hlow hE hcop
  exact eq_of_nodal_eq_of_natDegree_lt_card nodes
    (N * Hhigh) (E * Hlow) hhighDegree hlowDegree hrelation

/-- The endpoint inequality `cap ≤ e + |Z|` turns the short high dual factor
`H=E*K` into the strict root-count bound `deg K < |Z|`. -/
theorem factored_kernel_degree_lt_root_card
    {I K : Type*} [Fintype I] [Field K]
    (Z : Finset I) (E H T : K[X]) (e cap : Nat)
    (hZ : 0 < Z.card) (hE : E ≠ 0)
    (hfactor : H = E * T)
    (hEdegree : e ≤ E.natDegree)
    (hHdegree : H.natDegree < cap)
    (hcap : cap ≤ e + Z.card) :
    T.natDegree < Z.card := by
  by_cases hT : T = 0
  · simp only [hT, natDegree_zero]
    exact hZ
  · have hdegree : H.natDegree = E.natDegree + T.natDegree := by
      rw [hfactor, natDegree_mul hE hT]
    omega

/-- Exact target arithmetic for all 6930 deficient m69 shapes.  The
executable receipt proves that every last paired high cap is at most `3276`.
At `deg E ≥2151` and `|Z|≥1125`, the last kernel is therefore shorter than
`Z`.  The degree-`149776` numerator bound leaves at least `112368` nonroots,
far more than the largest earlier kernel cap `1191`. -/
theorem target_m69_many_zero_recurrence_arithmetic :
    3276 ≤ 2151 + 1125 ∧
    262144 - 149776 = 112368 ∧
    3342 - 2151 = 1191 ∧
    1191 ≤ 112368 ∧
    3218 ≤ 2151 + 1067 := by
  norm_num

#print axioms eq_zero_of_eval_zero_on_finset
#print axioms eq_of_nodal_eq_of_natDegree_lt_card
#print axioms adjacent_relation_of_prefix_dual_encodings
#print axioms paired_recurrence_has_no_X_factor
#print axioms next_eq_zero_of_nodal_square_recurrence_on_numerator_roots
#print axioms prev_eq_zero_of_next_eq_zero_on_numerator_complement
#print axioms nodal_square_recurrence_chain_forces_zero
#print axioms coprime_high_low_normal_form
#print axioms coprime_high_low_normal_form_of_nodal_no_wrap
#print axioms factored_kernel_degree_lt_root_card
#print axioms target_m69_many_zero_recurrence_arithmetic

end
end ProximityPrize.SubmissionLower.M69ManyZeroDualBackwardRecurrence6900
