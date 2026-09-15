import ProximityPrize.SubmissionLower.LowerGeometry

/-!
# Homogeneity of the weighted second-jet kernel face

The weighted contact-zero vectors used by `SecondJetRelaxedRank` are not only
supported below the passive cap: every monomial in one vector has exactly the
same passive degree. Consequently the exact new passive face contains the
corresponding exact-degree slice of the independent kernel family. The
companion arithmetic receipt counts that slice and obtains the candidate
coupled associated cap `91368 - 24948 = 66420` per node. The statements in
this file are the production local-kernel ingredients; packaging them as a
rank theorem for the actual global associated-face map is a separate explicit
assembly step.

This is only the normalized local associated cap.  Independent local
lower-grade corrections at the nodes need not arise from a single global old
source vector.  No attached-rank, filtered-strictness, liftability, or boundary
claim is made here.
-/

namespace ProximityPrize.SubmissionLower.K0FullFaceCoupledCap6900

open scoped BigOperators
open MvPolynomial SecondJetSupport SecondJetBasis SecondJetLocal
open SecondJetWeightedBasis SecondJetWeightedSupport

noncomputable section
set_option autoImplicit false

variable {K : Type*} [Field K]

/-- Every support monomial of a weighted kernel vector has exact passive total
degree `h+a+b+i+j+z`. This is the filtration fact missing from a bare
difference of two unrelated rank upper bounds. -/
theorem weightedVector_passiveDegree
    (r h a b i j z l : Nat) (hla : l ≤ a) (hlj : l ≤ j)
    (e : Fin 5 →₀ Nat)
    (he : e ∈ (weightedVector (K := K) r h a b i j z l).support) :
    e 1 + e 2 + e 3 + e 4 = h + a + b + i + j + z := by
  have hup := weightedVector_bound (K := K) ![0, 1, 1, 1, 1]
    r h a b i j z l e he
  have hlo := weightedVector_bound (K := K) ![0, -1, -1, -1, -1]
    r h a b i j z l e he
  norm_num [weight, Fin.sum_univ_five, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four] at hup hlo
  omega

/-- In the exact `weightedTerm` specialization used by the relaxed-rank
family, the homogeneous raw vector maps to the formal flat term and its
complete local contact vanishes to the requested order. -/
theorem weightedVector_flat_contact_zero
    (m r h a b : Nat) (e : Fin 3 →₀ Nat)
    (horder : m ≤ r + 2 * a + b) :
    Polynomial.X ^ m ∣ SecondJetLocal.contact (K := K)
      (SecondJetSupport.flatEquiv (K := K)
        (weightedVector (K := K) r h a b (e 0) (e 1) (e 2)
          (min a (e 1)))) := by
  rw [SecondJetWeightedLocal.flatEquiv_weightedVector]
  exact SecondJetWeightedLocal.weightedTerm_vanishes m r h a b e horder

/-! ## The exact-degree independent kernel slice -/

/-- The part of one relaxed-rank block lying on passive degree exactly `L`. -/
def KernelFaceBlock (m L B s U : Nat) (caps : Nat → Nat) (r h : Nat) :=
  {e : SecondJetRelaxedRank.Block m L B s U caps r h //
    h + SecondJetRelaxedRank.q m s r h +
      SecondJetRelaxedRank.exponent e 0 +
      SecondJetRelaxedRank.exponent e 1 +
      SecondJetRelaxedRank.exponent e 2 = L}

instance (m L B s U : Nat) (caps : Nat → Nat) (r h : Nat) :
    Fintype (KernelFaceBlock m L B s U caps r h) := by
  unfold KernelFaceBlock
  infer_instance

def kernelFaceExponent {m L B s U : Nat} {caps : Nat → Nat} {r h : Nat}
    (e : KernelFaceBlock m L B s U caps r h) : Fin 3 →₀ Nat :=
  SecondJetRelaxedRank.exponent e.val

theorem kernelFaceExponent_injective
    (m L B s U : Nat) (caps : Nat → Nat) (r h : Nat) :
    Function.Injective
      (kernelFaceExponent (m := m) (L := L) (B := B) (s := s)
        (U := U) (caps := caps) (r := r) (h := h)) :=
  (SecondJetRelaxedRank.exponent_injective m L B s U caps r h).comp
    Subtype.val_injective

abbrev KernelFaceParameters (K : Type*) [Field K]
    (m L B s U : Nat) (caps : Nat → Nat) :=
  ∀ r : Fin m, ∀ h : Fin (s + 1),
    KernelFaceBlock m L B s U caps r.val h.val → K

/-- The production weighted construction restricted to exact passive degree. -/
def kernelFaceMake (m L B s U : Nat) (caps : Nat → Nat) :
    KernelFaceParameters K m L B s U caps →ₗ[K]
      SecondJetBasis.Jet (SecondJetLocal.Base (K := K)) :=
  (SecondJetBasis.truncateOuter (K := K) m).comp
    (SecondJetWeightedBasis.weightedMake
      (fun r h ↦ SecondJetRelaxedRank.a m s r.val h.val)
      (fun r h ↦ SecondJetRelaxedRank.b m s r.val h.val)
      (fun _ _ e ↦ kernelFaceExponent e))

/-- No loss of dimension occurs in the exact-face family. -/
theorem kernelFaceMake_injective (m L B s U : Nat) (caps : Nat → Nat) :
    Function.Injective (kernelFaceMake (K := K) m L B s U caps) := by
  exact SecondJetWeightedBasis.truncateOuter_weightedMake_injective
    (fun r h ↦ SecondJetRelaxedRank.a m s r.val h.val)
    (fun r h ↦ SecondJetRelaxedRank.b m s r.val h.val)
    (fun _ _ e ↦ kernelFaceExponent e)
    (fun r h ↦ kernelFaceExponent_injective m L B s U caps r.val h.val)

/-- Each basis vector selected by `KernelFaceBlock` is genuinely on the top
passive face; it has no monomial in a lower passive grade. -/
theorem kernelFaceVector_passiveDegree
    (m L B s U r h : Nat) (caps : Nat → Nat)
    (hr : r ≤ m) (hh : h ≤ s)
    (e : KernelFaceBlock m L B s U caps r h)
    (d : Fin 5 →₀ Nat)
    (hd : d ∈ (weightedVector (K := K) r h
      (SecondJetRelaxedRank.a m s r h)
      (SecondJetRelaxedRank.b m s r h)
      (kernelFaceExponent e 0) (kernelFaceExponent e 1)
      (kernelFaceExponent e 2)
      (min (SecondJetRelaxedRank.a m s r h)
        (kernelFaceExponent e 1))).support) :
    d 1 + d 2 + d 3 + d 4 = L := by
  have hdegree := weightedVector_passiveDegree (K := K) r h
    (SecondJetRelaxedRank.a m s r h)
    (SecondJetRelaxedRank.b m s r h)
    (kernelFaceExponent e 0) (kernelFaceExponent e 1)
    (kernelFaceExponent e 2)
    (min (SecondJetRelaxedRank.a m s r h) (kernelFaceExponent e 1))
    (min_le_left _ _) (min_le_right _ _) d hd
  have hbudget := SecondJetRelaxedRank.budgets m s r h hr hh
  have hface := e.property
  simp only [kernelFaceExponent, SecondJetRelaxedRank.exponent_apply] at hdegree hface
  omega

/-- The exact-face family lies in the complete local contact kernel, hence in
particular in the associated top-symbol kernel. -/
theorem kernelFaceMake_zero
    (m L B s U : Nat) (caps : Nat → Nat)
    (p : KernelFaceParameters K m L B s U caps) :
    SecondJetRank.contactMap (K := K) m
      (kernelFaceMake (K := K) m L B s U caps p) = 0 := by
  change SecondJetLocal.contact (K := K)
      (kernelFaceMake (K := K) m L B s U caps p) %ₘ Polynomial.X ^ m = 0
  apply (Polynomial.modByMonic_eq_zero_iff_dvd
    (Polynomial.monic_X_pow m)).mpr
  change Polynomial.X ^ m ∣ SecondJetLocal.contact (K := K)
    (SecondJetBasis.truncateOuter (K := K) m _)
  apply SecondJetBasis.truncateOuter_contact
    (K := K) (SecondJetLocal.contact (K := K)).toRingHom Polynomial.X m _
    SecondJetLocal.contact_X
  change Polynomial.X ^ m ∣ SecondJetLocal.contact (K := K) _
  rw [SecondJetWeightedBasis.weightedMake_apply, map_sum]
  apply Finset.dvd_sum
  intro r _
  rw [map_sum]
  apply Finset.dvd_sum
  intro h _
  rw [map_sum]
  apply Finset.dvd_sum
  intro e _
  rw [map_smul, Algebra.smul_def]
  apply dvd_mul_of_dvd_right
  apply SecondJetWeightedLocal.weightedTerm_vanishes
  exact le_of_eq (SecondJetRelaxedRank.budgets m s r.val h.val
    (Nat.le_of_lt r.isLt) (Nat.le_of_lt_succ h.isLt)).2.2.symm

/-! ## A closed exact count for the face kernel -/

def kernelFaceCell (m B s U r h : Nat) : Nat :=
  if SecondJetRelaxedRank.q m s r h ≤ r ∧ m - r + 2 * h ≤ B then
    ∑ i : Fin (r - SecondJetRelaxedRank.q m s r h + 1),
      ∑ j : Fin (B - 2 * h - SecondJetRelaxedRank.q m s r h + 1),
        if h + SecondJetRelaxedRank.q m s r h + i.val + j.val ≤ U then 1 else 0
  else 0

def kernelFaceCount (m B s U : Nat) : Nat :=
  ∑ r : Fin m, ∑ h : Fin (s + 1), kernelFaceCell m B s U r.val h.val

abbrev KernelFaceCellIndex (m B s U r h : Nat) :=
  Σ i : Fin (r - SecondJetRelaxedRank.q m s r h + 1),
    Σ j : Fin (B - 2 * h - SecondJetRelaxedRank.q m s r h + 1),
      Fin (if h + SecondJetRelaxedRank.q m s r h + i.val + j.val ≤ U then 1 else 0)

/-- On a legal block the terminal `Z` exponent is uniquely determined by the
face equation, leaving exactly the two clipped rectangle coordinates counted
by `kernelFaceCell`. -/
def kernelFaceBlockEquiv
    (m L B s U : Nat) (caps : Nat → Nat) (r h : Nat)
    (hrm : r ≤ m) (hhs : h ≤ s)
    (hq : SecondJetRelaxedRank.q m s r h ≤ r)
    (hB : m - r + 2 * h ≤ B)
    (hUL : U ≤ L) (hcaps : ∀ t, t ≤ s → U ≤ caps t) :
    KernelFaceBlock m L B s U caps r h ≃
      KernelFaceCellIndex m B s U r h where
  toFun d := by
    let i : Fin (r - SecondJetRelaxedRank.q m s r h + 1) :=
      ⟨SecondJetRelaxedRank.exponent d.val 0,
        by have hd := d.val.property; simp only [SecondJetRelaxedRank.exponent_apply]; omega⟩
    let j : Fin (B - 2 * h - SecondJetRelaxedRank.q m s r h + 1) :=
      ⟨SecondJetRelaxedRank.exponent d.val 1,
        by have hd := d.val.property; simp only [SecondJetRelaxedRank.exponent_apply]; omega⟩
    have hU : h + SecondJetRelaxedRank.q m s r h + i.val + j.val ≤ U := by
      have hd := d.val.property
      dsimp only [i, j]
      simp only [SecondJetRelaxedRank.exponent_apply] at hd ⊢
      omega
    exact ⟨i, j, ⟨0, by simp [hU]⟩⟩
  invFun u := by
    rcases u with ⟨i, j, k⟩
    have hU : h + SecondJetRelaxedRank.q m s r h + i.val + j.val ≤ U := by
      by_contra hn
      have hk := k.isLt
      simp only [if_neg hn] at hk
      omega
    have hbaseL : h + SecondJetRelaxedRank.q m s r h + i.val + j.val ≤ L :=
      hU.trans hUL
    let iv : Fin (L + 1) := ⟨i.val, by omega⟩
    let jv : Fin (L + 1) := ⟨j.val, by omega⟩
    let zv : Fin (L + 1) :=
      ⟨L - (h + SecondJetRelaxedRank.q m s r h + i.val + j.val), by omega⟩
    have hbudgets := SecondJetRelaxedRank.budgets m s r h hrm hhs
    refine ⟨⟨![iv, jv, zv], ?_⟩, ?_⟩
    · refine ⟨?_, ?_, hB, ?_, ?_, ?_⟩
      · change i.val + SecondJetRelaxedRank.q m s r h ≤ r
        have hi := i.isLt
        omega
      · change j.val + SecondJetRelaxedRank.q m s r h + 2 * h ≤ B
        have hj := j.isLt
        omega
      · change i.val + j.val + h + SecondJetRelaxedRank.q m s r h ≤ U
        omega
      · change i.val + j.val + h + SecondJetRelaxedRank.q m s r h +
          (L - (h + SecondJetRelaxedRank.q m s r h + i.val + j.val)) ≤ L
        omega
      · intro t
        have ht := t.isLt
        have hts : h + t.val ≤ s := by omega
        exact (by omega : i.val + j.val + h +
          SecondJetRelaxedRank.q m s r h ≤ U).trans (hcaps _ hts)
    · change h + SecondJetRelaxedRank.q m s r h + i.val + j.val +
        (L - (h + SecondJetRelaxedRank.q m s r h + i.val + j.val)) = L
      omega
  left_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    funext k
    apply Fin.ext
    fin_cases k
    · rfl
    · rfl
    · dsimp
      have hface := d.property
      simp only [SecondJetRelaxedRank.exponent_apply] at hface ⊢
      omega
  right_inv u := by
    rcases u with ⟨i, j, k⟩
    apply Sigma.ext
    · apply Fin.ext
      rfl
    · apply heq_of_eq
      apply Sigma.ext
      · apply Fin.ext
        rfl
      · apply heq_of_eq
        apply Fin.ext
        have hcond : h + SecondJetRelaxedRank.q m s r h +
            i.val + j.val ≤ U := by
          by_contra hn
          have hk := k.isLt
          simp only [if_neg hn] at hk
          omega
        have hk := k.isLt
        simp only [if_pos hcond] at hk
        change 0 = k.val
        omega

theorem card_kernelFaceBlock_of_le
    (m L B s U : Nat) (caps : Nat → Nat) (r h : Nat)
    (hrm : r ≤ m) (hhs : h ≤ s)
    (hq : SecondJetRelaxedRank.q m s r h ≤ r)
    (hB : m - r + 2 * h ≤ B)
    (hUL : U ≤ L) (hcaps : ∀ t, t ≤ s → U ≤ caps t) :
    Fintype.card (KernelFaceBlock m L B s U caps r h) =
      ∑ i : Fin (r - SecondJetRelaxedRank.q m s r h + 1),
        ∑ j : Fin (B - 2 * h - SecondJetRelaxedRank.q m s r h + 1),
          if h + SecondJetRelaxedRank.q m s r h + i.val + j.val ≤ U then 1 else 0 := by
  rw [Fintype.card_congr
    (kernelFaceBlockEquiv m L B s U caps r h hrm hhs hq hB hUL hcaps)]
  simp [KernelFaceCellIndex]

theorem card_kernelFaceBlock_of_not_le
    (m L B s U : Nat) (caps : Nat → Nat) (r h : Nat)
    (hq : ¬ (SecondJetRelaxedRank.q m s r h ≤ r ∧ m - r + 2 * h ≤ B)) :
    Fintype.card (KernelFaceBlock m L B s U caps r h) = 0 := by
  letI : IsEmpty (KernelFaceBlock m L B s U caps r h) :=
    ⟨fun d ↦ by have hd := d.val.property; omega⟩
  simp

theorem card_kernelFaceBlock_closed
    (m L B s U : Nat) (caps : Nat → Nat) (r h : Nat)
    (hrm : r ≤ m) (hhs : h ≤ s)
    (hUL : U ≤ L) (hcaps : ∀ t, t ≤ s → U ≤ caps t) :
    Fintype.card (KernelFaceBlock m L B s U caps r h) =
      kernelFaceCell m B s U r h := by
  unfold kernelFaceCell
  split_ifs with hlegal
  · exact card_kernelFaceBlock_of_le m L B s U caps r h hrm hhs
      hlegal.1 hlegal.2 hUL hcaps
  · exact card_kernelFaceBlock_of_not_le m L B s U caps r h hlegal

theorem card_kernelFace_sum
    (m L B s U : Nat) (caps : Nat → Nat)
    (hUL : U ≤ L) (hcaps : ∀ t, t ≤ s → U ≤ caps t) :
    (∑ r : Fin m, ∑ h : Fin (s + 1),
      Fintype.card (KernelFaceBlock m L B s U caps r.val h.val)) =
        kernelFaceCount m B s U := by
  unfold kernelFaceCount
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro h _
  exact card_kernelFaceBlock_closed m L B s U caps r.val h.val
    (by omega) (by omega) hUL hcaps

/-- At the target the active cutoff inside every legal kernel-face cell is
vacuous.  Reducing it first keeps the numerical receipt independent of the
ambient passive cap and small enough for the verifier memory budget. -/
theorem target_kernelFaceCell_closed (r : Fin 47) (h : Fin 9) :
    kernelFaceCell 47 16 8 64 r.val h.val =
      if SecondJetRelaxedRank.q 47 8 r.val h.val ≤ r.val ∧
          47 - r.val + 2 * h.val ≤ 16 then
        (r.val - SecondJetRelaxedRank.q 47 8 r.val h.val + 1) *
          (16 - 2 * h.val - SecondJetRelaxedRank.q 47 8 r.val h.val + 1)
      else 0 := by
  unfold kernelFaceCell
  split_ifs with hlegal
  · have hcut
        (i : Fin (r.val - SecondJetRelaxedRank.q 47 8 r.val h.val + 1))
        (j : Fin
          (16 - 2 * h.val - SecondJetRelaxedRank.q 47 8 r.val h.val + 1)) :
        h.val + SecondJetRelaxedRank.q 47 8 r.val h.val + i.val + j.val ≤ 64 := by
      have hr := r.isLt
      have hh := h.isLt
      have hi := i.isLt
      have hj := j.isLt
      omega
    simp only [if_pos (hcut _ _)]
    simp
  · rfl

/-- The closed face count is only 47·9 compact cells, not an enumeration of
the ambient `Fin 3758` cube. -/
theorem target_kernelFaceCount : kernelFaceCount 47 16 8 64 = 24948 := by
  unfold kernelFaceCount
  simp_rw [target_kernelFaceCell_closed]
  decide

/-- Therefore the production exact-face independent family has exactly 24,948
parameters, for every target cap function satisfying the already-used local
middle-degree bound. -/
theorem target_kernelFace_card (caps : Nat → Nat)
    (hcaps : ∀ t, t ≤ 8 → 64 ≤ caps t) :
    (∑ r : Fin 47, ∑ h : Fin 9,
      Fintype.card (KernelFaceBlock 47 3757 16 8 64 caps r.val h.val)) =
        24948 := by
  rw [card_kernelFace_sum 47 3757 16 8 64 caps (by norm_num) hcaps,
    target_kernelFaceCount]

/-! ## The matching exact-degree local source slice -/

def LocalSourceFace (m L B s U : Nat) (caps : Nat → Nat) :=
  {d : SecondJetRelaxedSpace.Index m L B s U caps //
    SecondJetRelaxedSpace.exponent d 1 +
      SecondJetRelaxedSpace.exponent d 2 +
      SecondJetRelaxedSpace.exponent d 3 +
      SecondJetRelaxedSpace.exponent d 4 = L}

instance (m L B s U : Nat) (caps : Nat → Nat) :
    Fintype (LocalSourceFace m L B s U caps) := by
  unfold LocalSourceFace
  infer_instance

abbrev LocalSourceFaceClosedIndex (m B s U : Nat) :=
  Σ outer : Fin m, Σ h : Fin (s + 1), Σ y : Fin (outer.val + 1),
    Σ r : Fin (B - 2 * h.val + 1),
      Fin (if h.val + y.val + r.val ≤ U then 1 else 0)

def localSourceFaceEquiv
    (m L B s U : Nat) (caps : Nat → Nat)
    (hsB : 2 * s ≤ B) (hUL : U ≤ L)
    (hcaps : ∀ t, t ≤ s → U ≤ caps t) :
    LocalSourceFace m L B s U caps ≃ LocalSourceFaceClosedIndex m B s U where
  toFun d := by
    let coordinates := Subtype.val (Subtype.val (Subtype.val d))
    let outer : Fin m := coordinates 0
    let h : Fin (s + 1) := coordinates 1
    let y : Fin (outer.val + 1) :=
      ⟨(coordinates 2).val, by
        have hd := d.val.val.property.1
        change (coordinates 2).val ≤ (coordinates 0).val at hd
        dsimp only [outer]
        omega⟩
    let r : Fin (B - 2 * h.val + 1) :=
      ⟨(coordinates 3).val, by
        have hd := d.val.property.1
        change 2 * (coordinates 1).val + (coordinates 3).val ≤ B at hd
        dsimp only [h]
        omega⟩
    have hU : h.val + y.val + r.val ≤ U := by
      have hd := d.val.property.2.1
      change (coordinates 1).val + (coordinates 2).val +
        (coordinates 3).val ≤ U at hd
      dsimp only [h, y, r]
      exact hd
    exact ⟨outer, h, y, r, ⟨0, by simp [hU]⟩⟩
  invFun u := by
    rcases u with ⟨outer, h, y, r, k⟩
    have hU : h.val + y.val + r.val ≤ U := by
      by_contra hn
      have hk := k.isLt
      simp only [if_neg hn] at hk
      omega
    have hbaseL : h.val + y.val + r.val ≤ L := hU.trans hUL
    let yf : Fin m := ⟨y.val, by have ho := outer.isLt; have hy := y.isLt; omega⟩
    let rf : Fin (B + 1) := ⟨r.val, by have hr := r.isLt; omega⟩
    let zf : Fin (L + 1) :=
      ⟨L - (h.val + y.val + r.val), by omega⟩
    let coordinates : ∀ j, Fin (SecondJetSpace.bound m L B s j) :=
      Fin.cases outer (Fin.cases h (Fin.cases yf
        (Fin.cases rf (Fin.cases zf (fun j ↦ Fin.elim0 j)))))
    refine ⟨⟨⟨coordinates, ?_⟩, ?_⟩, ?_⟩
    · constructor
      · change y.val ≤ outer.val
        exact Nat.le_of_lt_succ y.isLt
      · change h.val + y.val + r.val +
          (L - (h.val + y.val + r.val)) ≤ L
        omega
    · refine ⟨?_, ?_, ?_⟩
      · change 2 * h.val + r.val ≤ B
        have hr := r.isLt
        omega
      · exact hU
      · exact hU.trans (hcaps h.val (by omega))
    · change h.val + y.val + r.val +
        (L - (h.val + y.val + r.val)) = L
      omega
  left_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext k
    apply Fin.ext
    fin_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · dsimp
      have hface := d.property
      change L - (SecondJetRelaxedSpace.exponent d.val 1 +
        SecondJetRelaxedSpace.exponent d.val 2 +
        SecondJetRelaxedSpace.exponent d.val 3) =
          SecondJetRelaxedSpace.exponent d.val 4
      omega
  right_inv u := by
    rcases u with ⟨outer, h, y, r, k⟩
    apply Sigma.ext
    · apply Fin.ext
      rfl
    · apply heq_of_eq
      apply Sigma.ext
      · apply Fin.ext
        rfl
      · apply heq_of_eq
        apply Sigma.ext
        · apply Fin.ext
          rfl
        · apply heq_of_eq
          apply Sigma.ext
          · apply Fin.ext
            rfl
          · apply heq_of_eq
            apply Fin.ext
            have hcond : h.val + y.val + r.val ≤ U := by
              by_contra hn
              have hk := k.isLt
              simp only [if_neg hn] at hk
              omega
            have hk := k.isLt
            simp only [if_pos hcond] at hk
            change 0 = k.val
            omega

def localSourceFaceCount (m B s U : Nat) : Nat :=
  ∑ outer : Fin m, ∑ h : Fin (s + 1), ∑ y : Fin (outer.val + 1),
    ∑ r : Fin (B - 2 * h.val + 1),
      if h.val + y.val + r.val ≤ U then 1 else 0

theorem card_localSourceFace
    (m L B s U : Nat) (caps : Nat → Nat)
    (hsB : 2 * s ≤ B) (hUL : U ≤ L)
    (hcaps : ∀ t, t ≤ s → U ≤ caps t) :
    Fintype.card (LocalSourceFace m L B s U caps) =
      localSourceFaceCount m B s U := by
  rw [Fintype.card_congr (localSourceFaceEquiv m L B s U caps hsB hUL hcaps)]
  simp [LocalSourceFaceClosedIndex, localSourceFaceCount]

theorem target_localSourceFaceCount : localSourceFaceCount 47 16 8 64 = 91368 := by
  have hcond (outer : Fin 47) (h : Fin 9) (y : Fin (outer.val + 1))
      (r : Fin (16 - 2 * h.val + 1)) : h.val + y.val + r.val ≤ 64 := by
    have ho := outer.isLt
    have hh := h.isLt
    have hy := y.isLt
    have hr := r.isLt
    omega
  simp only [localSourceFaceCount, if_pos (hcond _ _ _ _)]
  norm_num [Fin.sum_univ_succ]

theorem target_localSourceFace_card (caps : Nat → Nat)
    (hcaps : ∀ t, t ≤ 8 → 64 ≤ caps t) :
    Fintype.card (LocalSourceFace 47 3757 16 8 64 caps) = 91368 := by
  rw [card_localSourceFace 47 3757 16 8 64 caps (by norm_num) (by norm_num) hcaps,
    target_localSourceFaceCount]

/-- The 66,420 cap is now the difference of the cardinalities of the actual
production exact-degree source slice and its explicit injective contact-kernel
slice. -/
theorem target_exact_face_cap_from_actual_cards (caps : Nat → Nat)
    (hcaps : ∀ t, t ≤ 8 → 64 ≤ caps t) :
    Fintype.card (LocalSourceFace 47 3757 16 8 64 caps) -
      (∑ r : Fin 47, ∑ h : Fin 9,
        Fintype.card (KernelFaceBlock 47 3757 16 8 64 caps r.val h.val)) =
      66420 := by
  rw [target_localSourceFace_card caps hcaps, target_kernelFace_card caps hcaps]

/-! Exact target arithmetic, kept kernel-checkable and evaluation-free. -/

theorem target_full_face_coupled_cap_receipt :
    91368 - 24948 = 66420 ∧
      262144 * 66420 = 17411604480 ∧
      17434693359 - 17411604480 = 23088879 := by
  norm_num

theorem target_first_positive_rawS_tier_receipt :
    14002159565 + 25165875 = 262144 * 53510 ∧
      262144 * 59145 + 73983 = 15504580863 := by
  norm_num

#print axioms weightedVector_passiveDegree
#print axioms weightedVector_flat_contact_zero
#print axioms kernelFaceMake_injective
#print axioms kernelFaceVector_passiveDegree
#print axioms kernelFaceMake_zero
#print axioms target_kernelFaceCount
#print axioms target_kernelFace_card
#print axioms target_localSourceFaceCount
#print axioms target_localSourceFace_card
#print axioms target_exact_face_cap_from_actual_cards
#print axioms target_full_face_coupled_cap_receipt
#print axioms target_first_positive_rawS_tier_receipt

end
end ProximityPrize.SubmissionLower.K0FullFaceCoupledCap6900
