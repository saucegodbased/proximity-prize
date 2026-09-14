import ProximityPrize.SubmissionLower.PackedLocatorTail

/-!
# A degree-bounded polynomial CRT

This is the source-independent interpolation lemma needed by the tapered
error-node elimination.  Pairwise distinct nodes and a positive uniform
depth admit simultaneous residues modulo the corresponding powered linear
factors, with a representative of degree strictly below `card * depth`.
-/

namespace ProximityPrize.SubmissionLower.PolynomialHermiteCRTDegree

open scoped Classical BigOperators Function

noncomputable section

set_option autoImplicit false

variable {K I : Type*} [Field K] [Fintype I] [Nonempty I]

def nodePowerIdeal (nodes : I → K) (depth : ℕ) (i : I) :
    Ideal (Polynomial K) :=
  Ideal.span {(Polynomial.X - Polynomial.C (nodes i)) ^ depth}

def nodePowerProduct (nodes : I → K) (depth : ℕ) : Polynomial K :=
  ∏ i : I, (Polynomial.X - Polynomial.C (nodes i)) ^ depth

theorem nodePowerProduct_monic (nodes : I → K) (depth : ℕ) :
    (nodePowerProduct nodes depth).Monic := by
  unfold nodePowerProduct
  exact Polynomial.monic_prod_of_monic Finset.univ _
    (fun i _ ↦ (Polynomial.monic_X_sub_C (nodes i)).pow depth)

theorem nodePowerProduct_natDegree (nodes : I → K) (depth : ℕ) :
    (nodePowerProduct nodes depth).natDegree = Fintype.card I * depth := by
  unfold nodePowerProduct
  rw [Polynomial.natDegree_prod_of_monic]
  · simp [Polynomial.natDegree_pow]
  · intro i hi
    exact (Polynomial.monic_X_sub_C (nodes i)).pow depth

theorem nodePowerIdeals_pairwise_coprime
    (nodes : I → K) (hnodes : Function.Injective nodes) (depth : ℕ) :
    Pairwise (IsCoprime on nodePowerIdeal nodes depth) := by
  intro i j hij
  apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
  exact (Polynomial.pairwise_coprime_X_sub_C hnodes hij).pow

theorem nodePower_dvd_product (nodes : I → K) (depth : ℕ) (i : I) :
    (Polynomial.X - Polynomial.C (nodes i)) ^ depth ∣
      nodePowerProduct nodes depth := by
  unfold nodePowerProduct
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

/-- Simultaneous Hermite residues have a representative with the sharp
total-multiplicity degree bound. -/
theorem exists_degree_lt_card_mul_of_residues
    (nodes : I → K) (hnodes : Function.Injective nodes)
    (depth : ℕ) (hdepth : 0 < depth) (residue : I → Polynomial K) :
    ∃ P : Polynomial K,
      P.natDegree < Fintype.card I * depth ∧
      ∀ i, P - residue i ∈ nodePowerIdeal nodes depth i := by
  have hcoprime := nodePowerIdeals_pairwise_coprime nodes hnodes depth
  obtain ⟨A, hA⟩ := Ideal.exists_forall_sub_mem_ideal hcoprime residue
  let M := nodePowerProduct nodes depth
  let P := A %ₘ M
  have hMmonic : M.Monic := nodePowerProduct_monic nodes depth
  have hMdegree : M.natDegree = Fintype.card I * depth :=
    nodePowerProduct_natDegree nodes depth
  have hMpositive : 0 < M.natDegree := by
    rw [hMdegree]
    exact Nat.mul_pos (Fintype.card_pos_iff.mpr inferInstance) hdepth
  have hPdegree : P.natDegree < Fintype.card I * depth := by
    have hdegree := Polynomial.degree_modByMonic_lt A hMmonic
    rw [Polynomial.degree_eq_natDegree hMmonic.ne_zero] at hdegree
    by_cases hPzero : P = 0
    · rw [hPzero, Polynomial.natDegree_zero]
      simpa only [hMdegree] using hMpositive
    · rw [Polynomial.degree_eq_natDegree hPzero] at hdegree
      exact_mod_cast hMdegree ▸ hdegree
  refine ⟨P, hPdegree, ?_⟩
  intro i
  have hfactor :
      (Polynomial.X - Polynomial.C (nodes i)) ^ depth ∣ M :=
    nodePower_dvd_product nodes depth i
  have hMA : M ∣ P - A := by
    dsimp only [P]
    rw [Polynomial.modByMonic_eq_sub_mul_div]
    refine ⟨-(A /ₘ M), ?_⟩
    ring
  have hPA : P - A ∈ nodePowerIdeal nodes depth i := by
    apply Ideal.mem_span_singleton.mpr
    exact hfactor.trans hMA
  have hAi : A - residue i ∈ nodePowerIdeal nodes depth i := hA i
  convert (nodePowerIdeal nodes depth i).add_mem hPA hAi using 1 <;> ring

/-- A polynomial with nonzero constant coefficient is a unit modulo `X^n`.
This is the one-variable lower-triangular Toeplitz inversion used after each
Hermite-CRT coefficient has been separated. -/
theorem exists_degree_lt_mul_congr_X_pow
    (a b : Polynomial K) (n : ℕ) (hn : 0 < n)
    (ha : a.coeff 0 ≠ 0) :
    ∃ p : Polynomial K,
      p.natDegree < n ∧ Polynomial.X ^ n ∣ a * p - b := by
  have hnot : ¬ Polynomial.X ∣ a := by
    rw [Polynomial.X_dvd_iff]
    exact ha
  have hcoprime : IsCoprime a (Polynomial.X ^ n) :=
    ((Polynomial.irreducible_X.coprime_iff_not_dvd.mpr hnot).symm).pow_right
  obtain ⟨u, v, huv⟩ := hcoprime
  let M : Polynomial K := Polynomial.X ^ n
  let p : Polynomial K := (u * b) %ₘ M
  have hMmonic : M.Monic := Polynomial.monic_X.pow n
  have hMdegree : M.natDegree = n := by simp [M, Polynomial.natDegree_pow]
  have hpdegree : p.natDegree < n := by
    have hdegree := Polynomial.degree_modByMonic_lt (u * b) hMmonic
    rw [Polynomial.degree_eq_natDegree hMmonic.ne_zero] at hdegree
    by_cases hpzero : p = 0
    · rw [hpzero, Polynomial.natDegree_zero]
      exact hn
    · rw [Polynomial.degree_eq_natDegree hpzero] at hdegree
      exact_mod_cast hMdegree ▸ hdegree
  refine ⟨p, hpdegree, ?_⟩
  have hrem : M ∣ p - u * b := by
    dsimp only [p]
    rw [Polynomial.modByMonic_eq_sub_mul_div]
    refine ⟨-((u * b) /ₘ M), ?_⟩
    ring
  obtain ⟨q, hq⟩ := hrem
  refine ⟨a * q - v * b, ?_⟩
  dsimp only [M] at huv hq ⊢
  linear_combination a * hq + b * huv

/-- Simultaneous bounded Hermite CRT with a different unit multiplier at
each node.  This is the exact one-grade operation in the derivative-rich
error peel: invert the nonzero diagonal locally, then use one global
polynomial of degree below total error multiplicity. -/
theorem exists_degree_lt_card_mul_congr_of_eval_ne_zero
    (nodes : I → K) (hnodes : Function.Injective nodes)
    (depth : ℕ) (hdepth : 0 < depth)
    (a b : I → Polynomial K)
    (ha : ∀ i, (a i).eval (nodes i) ≠ 0) :
    ∃ P : Polynomial K,
      P.natDegree < Fintype.card I * depth ∧
      ∀ i, (Polynomial.X - Polynomial.C (nodes i)) ^ depth ∣
        a i * P - b i := by
  have hcoprime : ∀ i,
      IsCoprime (a i)
        ((Polynomial.X - Polynomial.C (nodes i)) ^ depth) := by
    intro i
    have hnot : ¬ (Polynomial.X - Polynomial.C (nodes i)) ∣ a i := by
      rw [Polynomial.dvd_iff_isRoot]
      simpa [Polynomial.IsRoot] using ha i
    have hbase : IsCoprime
        (Polynomial.X - Polynomial.C (nodes i)) (a i) :=
      (Polynomial.irreducible_X_sub_C (nodes i)).coprime_iff_not_dvd.mpr hnot
    exact hbase.symm.pow_right
  choose u v huv using hcoprime
  obtain ⟨P, hPdegree, hP⟩ :=
    exists_degree_lt_card_mul_of_residues nodes hnodes depth hdepth
      (fun i ↦ u i * b i)
  refine ⟨P, hPdegree, ?_⟩
  intro i
  have hPi : (Polynomial.X - Polynomial.C (nodes i)) ^ depth ∣
      P - u i * b i := by
    exact Ideal.mem_span_singleton.mp (hP i)
  obtain ⟨q, hq⟩ := hPi
  refine ⟨a i * q - v i * b i, ?_⟩
  linear_combination a i * hq + b i * huv i

/-! ## Mixed agreement-Hermite and error-value interpolation -/

/-- Simultaneously prescribe a depth-`depth` polynomial residue at every
agreement node and one arbitrary scalar value at every disjoint error node.
The representative has the sharp mixed degree bound

`card agreements * depth + card errors`.

This is the exact algebraic meaning of the strong affine-capacity inequality
used by the Full187 terminal audit.  The construction first performs Hermite
CRT on the agreements and then adds their common vanishing product times a
degree-`< card errors` Lagrange correction. -/
theorem exists_degree_lt_agreement_mul_add_error_of_residues_values
    {Agreement Error : Type*}
    [Fintype Agreement] [Nonempty Agreement]
    [Fintype Error] [Nonempty Error]
    (agreementNode : Agreement → K) (errorNode : Error → K)
    (hAgreement : Function.Injective agreementNode)
    (hError : Function.Injective errorNode)
    (hDisjoint : ∀ i j, agreementNode i ≠ errorNode j)
    (depth : Nat) (hdepth : 0 < depth)
    (residue : Agreement → Polynomial K) (value : Error → K) :
    ∃ P : Polynomial K,
      P.natDegree < Fintype.card Agreement * depth + Fintype.card Error ∧
      (∀ i, P - residue i ∈ nodePowerIdeal agreementNode depth i) ∧
      ∀ j, P.eval (errorNode j) = value j := by
  obtain ⟨A, hAdegree, hA⟩ :=
    exists_degree_lt_card_mul_of_residues
      agreementNode hAgreement depth hdepth residue
  let M : Polynomial K := nodePowerProduct agreementNode depth
  have hMdegree : M.natDegree = Fintype.card Agreement * depth := by
    exact nodePowerProduct_natDegree agreementNode depth
  have hMeval : ∀ j, M.eval (errorNode j) ≠ 0 := by
    intro j
    dsimp only [M]
    unfold nodePowerProduct
    rw [Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    simp only [Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    exact pow_ne_zero _ (sub_ne_zero.mpr (hDisjoint i j).symm)
  let correctionValue : Error → K := fun j ↦
    (value j - A.eval (errorNode j)) / M.eval (errorNode j)
  obtain ⟨T, hTdegree, hT⟩ :=
    exists_degree_lt_card_mul_of_residues
      errorNode hError 1 (by omega)
      (fun j ↦ Polynomial.C (correctionValue j))
  have hTeval : ∀ j, T.eval (errorNode j) = correctionValue j := by
    intro j
    have hmem := hT j
    have hdvd : Polynomial.X - Polynomial.C (errorNode j) ∣
        T - Polynomial.C (correctionValue j) := by
      simpa [nodePowerIdeal] using
        (Ideal.mem_span_singleton.mp hmem)
    rw [Polynomial.dvd_iff_isRoot] at hdvd
    have hz : T.eval (errorNode j) - correctionValue j = 0 := by
      simpa [Polynomial.IsRoot] using hdvd
    exact sub_eq_zero.mp hz
  refine ⟨A + M * T, ?_, ?_, ?_⟩
  · have hMTdegree : (M * T).natDegree <
        Fintype.card Agreement * depth + Fintype.card Error := by
      calc
        (M * T).natDegree ≤ M.natDegree + T.natDegree :=
          Polynomial.natDegree_mul_le
        _ = Fintype.card Agreement * depth + T.natDegree := by
          rw [hMdegree]
        _ < Fintype.card Agreement * depth + Fintype.card Error := by
          exact Nat.add_lt_add_left (by simpa using hTdegree) _
    have hAdegree' : A.natDegree <
        Fintype.card Agreement * depth + Fintype.card Error :=
      hAdegree.trans (Nat.lt_add_of_pos_right
        (Fintype.card_pos_iff.mpr inferInstance))
    exact (Polynomial.natDegree_add_le A (M * T)).trans_lt
      (max_lt hAdegree' hMTdegree)
  · intro i
    have hMi : (Polynomial.X - Polynomial.C (agreementNode i)) ^ depth ∣ M :=
      nodePower_dvd_product agreementNode depth i
    have hMT : M * T ∈ nodePowerIdeal agreementNode depth i := by
      apply Ideal.mem_span_singleton.mpr
      exact hMi.mul_right T
    have hAi : A - residue i ∈ nodePowerIdeal agreementNode depth i := hA i
    convert (nodePowerIdeal agreementNode depth i).add_mem hAi hMT using 1 <;>
      ring
  · intro j
    rw [Polynomial.eval_add, Polynomial.eval_mul, hTeval]
    dsimp only [correctionValue]
    field_simp [hMeval j]
    ring

end

end ProximityPrize.SubmissionLower.PolynomialHermiteCRTDegree

#print axioms ProximityPrize.SubmissionLower.PolynomialHermiteCRTDegree.exists_degree_lt_card_mul_of_residues
#print axioms ProximityPrize.SubmissionLower.PolynomialHermiteCRTDegree.exists_degree_lt_mul_congr_X_pow
#print axioms ProximityPrize.SubmissionLower.PolynomialHermiteCRTDegree.exists_degree_lt_card_mul_congr_of_eval_ne_zero
#print axioms ProximityPrize.SubmissionLower.PolynomialHermiteCRTDegree.exists_degree_lt_agreement_mul_add_error_of_residues_values
