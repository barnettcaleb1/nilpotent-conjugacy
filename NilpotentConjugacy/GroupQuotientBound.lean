import NilpotentConjugacy.IntegralGroupAction
import NilpotentConjugacy.DescentLocalization
import NilpotentConjugacy.DescentGroupImage
import NilpotentConjugacy.SpecialPairs

/-!
# Lower bounds for arbitrary finite separating group quotients

The normal image, its local scalar action, relation kernel, shift invariance,
and obstruction are all constructed from the given group homomorphism.
-/

namespace NilpotentConjugacy

/-- The acting element whose matrix is the integral exponential of `m! J`. -/
noncomputable def quotientShiftActor (m : ℕ) (hm : 2 ≤ m) : CoefficientGroup m :=
  SemidirectProduct.inl (Multiplicative.ofAdd
    (Pi.single (⟨0, by omega⟩ : Fin (m - 1)) 1))

/-- The manuscript's cyclic acting generator. -/
noncomputable def quotientWeightedActor (m : ℕ) : CoefficientGroup m :=
  SemidirectProduct.inr (Multiplicative.ofAdd 1)

theorem manuscriptAction_lattice_apply (m : ℕ) (c : Fin (m - 1) → ℤ)
    (v : Fin m → ℤ) :
    (manuscriptAction m (SemidirectProduct.inl (Multiplicative.ofAdd c))
      (Multiplicative.ofAdd v)).toAdd =
      (integralExponential m (latticePolynomial m c)).mulVec v := by
  simp [manuscriptAction, manuscriptRhoHom, SemidirectProduct.lift_inl,
    integerMatrixAction_apply, latticeExponentialHom, latticeExponential]
  rfl

theorem manuscriptAction_shiftActor (m : ℕ) (hm : 2 ≤ m) (v : Fin m → ℤ) :
    (manuscriptAction m (quotientShiftActor m hm) (Multiplicative.ofAdd v)).toAdd =
      (integralExponential m (shiftJ m)).mulVec v := by
  rw [quotientShiftActor, manuscriptAction_lattice_apply, latticePolynomial_single]
  simp

theorem manuscriptAction_weightedActor (m : ℕ) (v : Fin m → ℤ) :
    (manuscriptAction m (quotientWeightedActor m) (Multiplicative.ofAdd v)).toAdd =
      (weightedExponential m 1).mulVec v := by
  simp [quotientWeightedActor, manuscriptAction, manuscriptRhoHom,
    SemidirectProduct.lift_inr, integerMatrixAction_apply, weightedExponentialHom]

/-- The actual local relation kernel attached to a group quotient. -/
noncomputable def groupQuotientLocalKernel (p m : ℕ) [Fact p.Prime]
    {Q : Type*} [Group Q] (f : ManuscriptGroup m →* Q) :
    Submodule (PrimeLocalIntegers p) (Fin m → PrimeLocalIntegers p) :=
  (localizedLatticeMap p m (normalImageMap (manuscriptAction m) f)).ker

/-- Every group quotient forces invariance of its actual local kernel under
both shifts; no shift-invariance hypothesis is imposed on the quotient. -/
theorem groupQuotientLocalKernel_shifts (p m : ℕ) [Fact p.Prime]
    (hm : 2 ≤ m) (hp : m < p) {Q : Type*} [Group Q]
    (f : ManuscriptGroup m →* Q) :
    (∀ x ∈ groupQuotientLocalKernel p m f,
      (shiftJ m).mulVec x ∈ groupQuotientLocalKernel p m f) ∧
    (∀ x ∈ groupQuotientLocalKernel p m f,
      (shiftY m).mulVec x ∈ groupQuotientLocalKernel p m f) := by
  apply localizedLatticeMap_kernel_shifts p m hm hp
    (normalImageMap (manuscriptAction m) f)
    (normalImageAction (manuscriptAction m) f (quotientShiftActor m hm))
    (normalImageAction (manuscriptAction m) f (quotientWeightedActor m))
  · intro v
    rw [normalImageAction_map, manuscriptAction_shiftActor]
  · intro v
    rw [normalImageAction_map, manuscriptAction_weightedActor]

/-- The local quotient is finite and its order is bounded by the original
finite group, even when the group homomorphism is not surjective. -/
theorem groupQuotientLocalKernel_finite (p m : ℕ) [Fact p.Prime]
    {Q : Type*} [Group Q] [Finite Q] (f : ManuscriptGroup m →* Q) :
    Finite ((Fin m → PrimeLocalIntegers p) ⧸ groupQuotientLocalKernel p m f) := by
  have := normalImage_finite (manuscriptAction m) f
  exact localizedLatticeMap_quotient_finite p m _
    (normalImageMap_surjective (manuscriptAction m) f)

theorem groupQuotientLocalKernel_card_le (p m : ℕ) [Fact p.Prime]
    {Q : Type*} [Group Q] [Finite Q] (f : ManuscriptGroup m →* Q) :
    Nat.card ((Fin m → PrimeLocalIntegers p) ⧸ groupQuotientLocalKernel p m f) ≤
      Nat.card Q := by
  have := normalImage_finite (manuscriptAction m) f
  exact (localizedLatticeMap_quotient_card_le p m _
    (normalImageMap_surjective (manuscriptAction m) f)).trans
      (normalImage_card_le (manuscriptAction m) f)

/-- Every positive shift exponent makes the bidiagonal matrix strictly lower
triangular, including at truncated boundary indices. -/
theorem lowerGap_shiftedBidiagonalMatrix (m w : ℕ) (t : ℤ) (hw : 0 < w) :
    LowerGap 1 (shiftedBidiagonalMatrix m w t) := by
  rw [shiftedBidiagonalMatrix, mul_add, Matrix.mul_smul, mul_one, ← pow_succ]
  intro i j hij
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [lowerGap_pow lowerGap_shiftJ w i j (by omega),
    lowerGap_pow lowerGap_shiftJ (w + 1) i j (by omega)]
  simp

/-- The bidiagonal matrix commutes with the actual integer scalar extension. -/
theorem integerMatrixMap_shiftedBidiagonal (R : Type*) [CommRing R]
    (m w : ℕ) (t : ℤ) :
    integerMatrixMap R m (shiftedBidiagonalMatrix m w t) =
      shiftedBidiagonalMatrix m w (t : R) := by
  simp only [shiftedBidiagonalMatrix, map_mul, map_add, map_pow,
    integerMatrixMap_smul, map_one, integerMatrixMap_shiftJ]

/-- A finite separating group quotient satisfies the full module cardinality
bound whenever the original acting element has the displayed exponential
matrix and the original lattice has the displayed prime-multiple witness.
All quotient invariance, localization and nonmembership facts are derived. -/
theorem finite_quotient_card_bound_of_exp_action
    (p m w s D : ℕ) [Fact p.Prime]
    (hm : 4 ≤ m) (hp : m < p) (hwlo : m / 2 ≤ w) (hwhi : w ≤ m - 2)
    (hs : 0 < s) (a : CoefficientGroup m) (c v : Fin m → ℤ)
    (hact : ∀ x : Fin m → ℤ,
      (manuscriptAction m a (Multiplicative.ofAdd x)).toAdd =
        (integralExponential m (shiftedBidiagonalMatrix m w (p ^ s : ℤ))).mulVec x)
    (hc : c = D • (p ^ (s - 1) • coordinateVector ℤ m (m - 1)))
    (hpc : (manuscriptAction m a (Multiplicative.ofAdd v)).toAdd - v = (p : ℤ) • c)
    {Q : Type*} [Group Q] [Finite Q] (f : ManuscriptGroup m →* Q)
    (hsep : ¬ IsConj (f (SemidirectProduct.inr a))
      (f (SemidirectProduct.inl (Multiplicative.ofAdd c) * SemidirectProduct.inr a))) :
    p ^ (s * (m - w) * (w + 1 - m / 2)) ≤ Nat.card Q := by
  let π := normalImageMap (manuscriptAction m) f
  let T := normalImageDifference (manuscriptAction m) f a
  let S := groupQuotientLocalKernel p m f
  let B : Matrix (Fin m) (Fin m) ℤ := shiftedBidiagonalMatrix m w (p ^ s : ℤ)
  have : Finite (NormalImage (manuscriptAction m) f) := normalImage_finite _ _
  have : Finite ((Fin m → PrimeLocalIntegers p) ⧸ S) :=
    groupQuotientLocalKernel_finite p m f
  obtain ⟨hJ, hY⟩ := groupQuotientLocalKernel_shifts p m (by omega) hp f
  have hmap : integerMatrixMap (PrimeLocalIntegers p) m B =
      shiftedBidiagonalMatrix m w ((p ^ s : ℕ) : PrimeLocalIntegers p) := by
    dsimp only [B]
    rw [integerMatrixMap_shiftedBidiagonal]
    simp
  have hpres : ∀ x ∈ S, (integerMatrixMap (PrimeLocalIntegers p) m B).mulVec x ∈ S := by
    rw [hmap]
    exact shiftedBidiagonalMatrix_preserves S hJ w _
  have hT : ∀ x, π ((integralExponential m B - 1).mulVec x) = T (π x) := by
    intro x
    simp only [π, T, normalImageDifference_map, hact, Matrix.sub_mulVec,
      Matrix.one_mulVec, B]
  have hq := localizedLatticeMap_quotient_obstruction p m (by omega) hp π
    (normalImageMap_surjective (manuscriptAction m) f) B
    (lowerGap_shiftedBidiagonalMatrix m w _ (by omega)) T hT c
    (normalImage_separating_obstruction (manuscriptAction m) f a c hsep)
    (normalImage_prime_smul_mem (manuscriptAction m) f a p c v hpc) hpres
  have hcast : (fun i => (c i : PrimeLocalIntegers p)) =
      D • (p ^ (s - 1) • coordinateVector (PrimeLocalIntegers p) m (m - 1)) := by
    rw [hc]
    ext i
    simp [coordinateVector]
  have hmatrix : quotientMatrix S (integerMatrixMap (PrimeLocalIntegers p) m B) hpres =
      quotientBidiagonal S hJ w ((p ^ s : ℕ) : PrimeLocalIntegers p) := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := S.mkQ_surjective z
    simp only [quotientMatrix_mk, quotientBidiagonal, hmap]
  have hdetect : D • (p ^ (s - 1) • quotientCoordinate S (m - 1)) ∉
      (quotientBidiagonal S hJ w ((p ^ s : ℕ) : PrimeLocalIntegers p)).range := by
    change S.mkQ (fun i => (c i : PrimeLocalIntegers p)) ∉
      (quotientMatrix S (integerMatrixMap (PrimeLocalIntegers p) m B) hpres).range at hq
    rw [hcast, map_nsmul, map_nsmul, hmatrix] at hq
    exact hq
  exact (primeLocal_quotient_cardinality p hm hp hwlo hwhi hs S hJ hY D hdetect).trans
    (groupQuotientLocalKernel_card_le p m f)

/-- Every finite homomorphism that separates the manuscript's exact special
pair has the claimed order. The quotient is arbitrary and need not itself be
a semidirect product or a p-group. No module or kernel hypotheses remain. -/
theorem specialPair_finite_quotient_cardinality (p m w s : ℕ) [Fact p.Prime]
    (hm : 4 ≤ m) (hmw : m ≤ 2 * w) (hwhi : w ≤ m - 2)
    (hp : m < p) (hs : 0 < s)
    {Q : Type*} [Group Q] [Finite Q] (f : ManuscriptGroup m →* Q)
    (hsep : ¬ IsConj (f (specialPairLeft m w p s)) (f (specialPairRight m w p s))) :
    p ^ (s * (m - w) * (w + 1 - m / 2)) ≤ Nat.card Q := by
  apply finite_quotient_card_bound_of_exp_action p m w s (m.factorial ^ (m - 1))
    hm hp (by omega) hwhi hs (pairActor m w ((p : ℤ) ^ s))
    (pairCentralVector m p s)
    ((m.factorial : ℤ) ^ (m - 2) • coordinateVector ℤ m (m - w - 1))
  · intro x
    rw [pairActor, manuscriptAction_lattice_apply,
      pairCoefficients_polynomial m w (by omega) (by omega)]
  · simp only [pairCentralVector, ← Nat.cast_pow, mul_smul, Nat.cast_smul_eq_nsmul]
  · exact pair_prime_commutator m w p s hm (by omega) (by omega) hmw (by omega)
  · exact hsep

/-- The dimension `4d`, shift `3d` family gives the explicit prime-power bound
used for the cubic growth exponent. -/
theorem cubicFamily_finite_quotient_cardinality (p d s : ℕ) [Fact p.Prime]
    (hd : 2 ≤ d) (hp : 4 * d < p) (hs : 0 < s)
    {Q : Type*} [Group Q] [Finite Q] (f : ManuscriptGroup (4 * d) →* Q)
    (hsep : ¬ IsConj (f (specialPairLeft (4 * d) (3 * d) p s))
      (f (specialPairRight (4 * d) (3 * d) p s))) :
    p ^ (s * d * (d + 1)) ≤ Nat.card Q := by
  have h := specialPair_finite_quotient_cardinality p (4 * d) (3 * d) s
    (by omega) (by omega) (by omega) hp hs f hsep
  have hr : 4 * d - 3 * d = d := by omega
  have hq : 3 * d + 1 - 4 * d / 2 = d + 1 := by omega
  simpa only [hr, hq] using h

end NilpotentConjugacy
