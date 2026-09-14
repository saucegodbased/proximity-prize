import Mathlib

/-!
# Minimal exact-k0 raw index and contact core

This is a definition-for-definition extraction of the small part of the
accepted `LowerGeometry` second-jet development needed to state the literal
exact-G raw source.  It deliberately avoids importing the 75k-line aggregate
`LowerFoundation`/`LowerGeometry` pair.

The five flat variables are ordered `(X,S,Y,R,Z)`.  After localization they
are `(epsilon,S,A,R,Z)`, and the contact substitution is

`A = R - epsilon*S + epsilon^2*T`.

No local-rank estimate or kernel-dimension certificate is asserted here.
-/

namespace ProximityPrize.SubmissionLower.K0RawIndexContactCore6900

open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000

variable {K : Type*} [Field K]

/-! ## The literal local contact map -/

abbrev FlatPoly (K : Type*) [Field K] := MvPolynomial (Fin 5) K
abbrev LocalBase (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev Jet (K : Type*) [Field K] := Polynomial (Polynomial (LocalBase K))
abbrev Target (K : Type*) [Field K] := Polynomial (MvPolynomial (Fin 4) K)

/-- Flatten `(epsilon,S,A,R,Z)` into the accepted nested polynomial order. -/
def flatEquiv : FlatPoly K ≃ₐ[K] Jet K :=
  (MvPolynomial.finSuccEquiv K 4).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.finSuccEquiv K 3))

/-- Global-to-local translation
`(X,S,Y,R,Z) -> (x+epsilon,S,u0+u1*Z+epsilon*A,R,Z)`. -/
def localize (x u0 u1 : K) : FlatPoly K →ₐ[K] FlatPoly K :=
  MvPolynomial.aeval ![
    MvPolynomial.C x + MvPolynomial.X 0,
    MvPolynomial.X 1,
    MvPolynomial.C u0 + MvPolynomial.C u1 * MvPolynomial.X 4 +
      MvPolynomial.X 0 * MvPolynomial.X 2,
    MvPolynomial.X 3,
    MvPolynomial.X 4]

/-- Substitute `A = R-epsilon*S+epsilon^2*T` in the local base. -/
def baseEval : LocalBase K →ₐ[K] Target K :=
  MvPolynomial.aeval ![
    Polynomial.C (MvPolynomial.X 2) -
        Polynomial.X * Polynomial.C (MvPolynomial.X 0) +
      Polynomial.X ^ 2 * Polynomial.C (MvPolynomial.X 1),
    Polynomial.C (MvPolynomial.X 2),
    Polynomial.C (MvPolynomial.X 3)]

def innerEval : Polynomial (LocalBase K) →ₐ[K] Target K :=
  Polynomial.eval₂AlgHom baseEval
    (Polynomial.C (MvPolynomial.X 0)) (fun _ ↦ Commute.all _ _)

def contact : Jet K →ₐ[K] Target K :=
  Polynomial.eval₂AlgHom innerEval Polynomial.X (fun _ ↦ Commute.all _ _)

def truncateOuter (m : Nat) : Jet K →ₗ[K] Jet K :=
  (Polynomial.modByMonicHom (Polynomial.X ^ m : Jet K)).restrictScalars K

def contactMap (m : Nat) : Jet K →ₗ[K] Target K :=
  ((Polynomial.modByMonicHom (Polynomial.X ^ m : Target K)).restrictScalars K).comp
    (contact (K := K)).toLinearMap

/-! ## Finite raw coordinates -/

def reconstruct {I : Type*} [Fintype I]
    (e : I → Fin 5 →₀ Nat) : (I → K) →ₗ[K] FlatPoly K :=
  ∑ i, (MvPolynomial.monomial (e i)).comp (LinearMap.proj i)

theorem reconstruct_apply {I : Type*} [Fintype I]
    (e : I → Fin 5 →₀ Nat) (c : I → K) :
    reconstruct e c = ∑ i, MvPolynomial.monomial (e i) (c i) := by
  simp [reconstruct]

def budget (D : Nat → Nat) (w h r : Nat) :=
  D h - (w - 2) * h - (w - 1) * r

def yCount (D : Nat → Nat) (w U h r : Nat) :=
  min ((budget D w h r - 1) / w + 1) (U + 1 - h - r)

/-- The accepted relaxed raw index, in dependent order `(S,R,Y,X,Z)`. -/
abbrev Index (D : Nat → Nat) (w L B s U : Nat) :=
  Σ h : Fin (s + 1),
    Σ r : Fin (B - 2 * h.val + 1),
      Σ y : Fin (yCount D w U h.val r.val),
        Fin (budget D w h.val r.val - w * y.val) ×
          Fin (L + 1 - h.val - r.val - y.val)

/-- Flatten a dependent index into exponents ordered `(X,S,Y,R,Z)`. -/
def exponent {D : Nat → Nat} {w L B s U : Nat}
    (i : Index D w L B s U) : Fin 5 →₀ Nat :=
  Finsupp.equivFunOnFinite.symm
    ![i.2.2.2.1.val, i.1.val, i.2.2.1.val, i.2.1.val, i.2.2.2.2.val]

@[simp] theorem exponent_apply {D : Nat → Nat} {w L B s U : Nat}
    (i : Index D w L B s U) (k : Fin 5) :
    exponent i k =
      ![i.2.2.2.1.val, i.1.val, i.2.2.1.val,
        i.2.1.val, i.2.2.2.2.val] k := by
  simp [exponent]

theorem exponent_injective (D : Nat → Nat) (w L B s U : Nat) :
    Function.Injective
      (exponent (D := D) (w := w) (L := L) (B := B) (s := s) (U := U)) := by
  rintro ⟨h, r, y, x, z⟩ ⟨h', r', y', x', z'⟩ he
  have hv : ∀ k : Fin 5,
      ![x.val, h.val, y.val, r.val, z.val] k =
        ![x'.val, h'.val, y'.val, r'.val, z'.val] k := by
    intro k
    simpa [exponent] using congrArg (fun d : Fin 5 →₀ Nat ↦ d k) he
  have hh : h = h' := Fin.ext (hv 1)
  subst h'
  have hr : r = r' := Fin.ext (hv 3)
  subst r'
  have hy : y = y' := Fin.ext (hv 2)
  subst y'
  have hx : x = x' := Fin.ext (hv 0)
  have hz : z = z' := Fin.ext (hv 4)
  subst x'
  subst z'
  rfl

/-- The exact five source inequalities encoded by `Index`. -/
theorem exponent_bounds (D : Nat → Nat) (w L B s U : Nat)
    (hsB : 2 * s ≤ B) (i : Index D w L B s U) :
    2 * exponent i 1 + exponent i 3 ≤ B ∧
      exponent i 1 ≤ s ∧
      exponent i 1 + exponent i 2 + exponent i 3 ≤ U ∧
      exponent i 1 + exponent i 2 + exponent i 3 + exponent i 4 ≤ L ∧
      exponent i 0 + w * exponent i 2 + (w - 1) * exponent i 3 +
          (w - 2) * exponent i 1 < D (exponent i 1) := by
  rcases i with ⟨h, r, y, x, z⟩
  have hh := h.isLt
  have hr := r.isLt
  have hy := y.isLt
  have hx := x.isLt
  have hz := z.isLt
  simp only [budget] at hx
  simp only [yCount] at hy
  simp [exponent]
  omega

/-! ## Exact m47 profile and its direct raw map -/

def k0Cutoff (g : Nat) (_h : Nat) : Nat := 47 * g

abbrev K0RawIndex (g : Nat) :=
  Index (k0Cutoff g) 131071 3757 16 8 64

abbrev K0RawSource (K : Type*) [Field K] (g : Nat) := K0RawIndex g → K

/-- The raw polynomial represented by one coefficient vector. -/
def k0RawPolynomial (g : Nat) : K0RawSource K g →ₗ[K] FlatPoly K :=
  reconstruct
    (exponent (D := k0Cutoff g) (w := 131071) (L := 3757)
      (B := 16) (s := 8) (U := 64))

/-- Literal reconstruction, node translation, flattening, and outer
truncation.  This omits only the redundant codomain subtype used by the
accepted rank proof. -/
def k0RawLocalLift (g : Nat) (x u0 u1 : K) :
    K0RawSource K g →ₗ[K] Jet K :=
  (truncateOuter (K := K) 47).comp
    ((flatEquiv (K := K)).toLinearMap.comp
      ((localize (K := K) x u0 u1).toLinearMap.comp (k0RawPolynomial g)))

/-- The complete non-scalar local contact block. -/
def k0RawLocalContact (g : Nat) (x u0 u1 : K) :
    K0RawSource K g →ₗ[K] Target K :=
  (contactMap (K := K) 47).comp (k0RawLocalLift g x u0 u1)

def k0RawGlobalContact {I : Type*} [Fintype I]
    (g : Nat) (nodes u0 u1 : I → K) :
    K0RawSource K g →ₗ[K] (I → Target K) :=
  LinearMap.pi (fun i ↦ k0RawLocalContact g (nodes i) (u0 i) (u1 i))

def k0RawBasis (g : Nat) (c : K0RawIndex g) : K0RawSource K g := by
  classical
  exact LinearMap.single K (fun _ : K0RawIndex g ↦ K) c 1

theorem reconstruct_k0RawBasis (g : Nat) (c : K0RawIndex g) :
    k0RawPolynomial (K := K) g (k0RawBasis (K := K) g c) =
      MvPolynomial.monomial (exponent c) 1 := by
  classical
  rw [k0RawPolynomial, reconstruct_apply]
  calc
    _ = MvPolynomial.monomial (exponent c)
        (k0RawBasis (K := K) g c c) := by
      apply Finset.sum_eq_single c
      · intro b _ hbc
        simp [k0RawBasis, hbc]
      · simp
    _ = MvPolynomial.monomial (exponent c) 1 := by
      simp [k0RawBasis]

/-- One raw coordinate travels through the literal full contact composite. -/
theorem k0RawLocalContact_basis
    (g : Nat) (x u0 u1 : K) (c : K0RawIndex g) :
    k0RawLocalContact g x u0 u1 (k0RawBasis (K := K) g c) =
      contactMap (K := K) 47
        (truncateOuter (K := K) 47
          (flatEquiv (K := K)
            (localize (K := K) x u0 u1
              (MvPolynomial.monomial (exponent c) 1)))) := by
  simp only [k0RawLocalContact, k0RawLocalLift, LinearMap.comp_apply]
  rw [reconstruct_k0RawBasis]
  rfl

theorem k0RawIndex_bounds (g : Nat) (c : K0RawIndex g) :
    2 * exponent c 1 + exponent c 3 ≤ 16 ∧
      exponent c 1 ≤ 8 ∧
      exponent c 1 + exponent c 2 + exponent c 3 ≤ 64 ∧
      exponent c 1 + exponent c 2 + exponent c 3 + exponent c 4 ≤ 3757 ∧
      exponent c 0 + 131071 * exponent c 2 + 131070 * exponent c 3 +
          131069 * exponent c 1 < 47 * g := by
  simpa [k0Cutoff] using
    exponent_bounds (k0Cutoff g) 131071 3757 16 8 64 (by norm_num) c

/-! ## Corrected critical selectors -/

/-- `{1,R}` keeps all legal `Y,Z`; subcritical `S` keeps all legal `Z`;
the critical `Y^47*S` band keeps precisely `Z^0,Z^1`. -/
def k0CriticalFilteredCarrier (g : Nat) (c : K0RawIndex g) : Prop :=
  (exponent c 1 = 0 ∧ exponent c 3 ≤ 1) ∨
    (exponent c 1 = 1 ∧ exponent c 3 = 0 ∧
      (exponent c 2 < 47 ∨ (exponent c 2 = 47 ∧ exponent c 4 ≤ 1)))

abbrev K0BaseRIndex (g : Nat) :=
  {c : K0RawIndex g // exponent c 1 = 0 ∧ exponent c 3 ≤ 1}

abbrev K0SubcriticalYSIndex (g : Nat) :=
  {c : K0RawIndex g //
    exponent c 1 = 1 ∧ exponent c 3 = 0 ∧ exponent c 2 < 47}

abbrev K0CriticalYmSBandIndex (g : Nat) :=
  {c : K0RawIndex g //
    exponent c 1 = 1 ∧ exponent c 2 = 47 ∧
      exponent c 3 = 0 ∧ exponent c 4 ≤ 1}

/-- Auxiliary `S*Y^46*R` connector, deliberately outside the selector.
Its `X,Z` coordinates retain every value already legal in `K0RawIndex`. -/
def k0CriticalSYRConnector (g : Nat) (c : K0RawIndex g) : Prop :=
  exponent c 1 = 1 ∧ exponent c 2 = 46 ∧ exponent c 3 = 1

abbrev K0CriticalSYRConnectorIndex (g : Nat) :=
  {c : K0RawIndex g // k0CriticalSYRConnector g c}

theorem k0BaseRIndex_mem_criticalFilteredCarrier
    (g : Nat) (c : K0BaseRIndex g) :
    k0CriticalFilteredCarrier g c.val := Or.inl c.property

theorem k0SubcriticalYSIndex_mem_criticalFilteredCarrier
    (g : Nat) (c : K0SubcriticalYSIndex g) :
    k0CriticalFilteredCarrier g c.val :=
  Or.inr ⟨c.property.1, c.property.2.1, Or.inl c.property.2.2⟩

theorem k0CriticalYmSBandIndex_mem_criticalFilteredCarrier
    (g : Nat) (c : K0CriticalYmSBandIndex g) :
    k0CriticalFilteredCarrier g c.val :=
  Or.inr ⟨c.property.1, c.property.2.2.1,
    Or.inr ⟨c.property.2.1, c.property.2.2.2⟩⟩

theorem k0CriticalSYRConnectorIndex_spec
    (g : Nat) (c : K0CriticalSYRConnectorIndex g) :
    exponent c.val 1 = 1 ∧ exponent c.val 2 = 46 ∧
      exponent c.val 3 = 1 := c.property

def k0SupportedOnCriticalFiltration
    (g : Nat) (v : K0RawSource K g) : Prop :=
  ∀ c, v c ≠ 0 → k0CriticalFilteredCarrier g c

#print axioms exponent_bounds
#print axioms reconstruct_k0RawBasis
#print axioms k0RawLocalContact_basis
#print axioms k0RawIndex_bounds
#print axioms k0BaseRIndex_mem_criticalFilteredCarrier
#print axioms k0SubcriticalYSIndex_mem_criticalFilteredCarrier
#print axioms k0CriticalYmSBandIndex_mem_criticalFilteredCarrier
#print axioms k0CriticalSYRConnectorIndex_spec

end
end ProximityPrize.SubmissionLower.K0RawIndexContactCore6900
