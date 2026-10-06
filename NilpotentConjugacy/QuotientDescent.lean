import NilpotentConjugacy.QuotientModule
import NilpotentConjugacy.IntegralGroup
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Inductions

/-!
# Recovering nilpotent operators from integral unipotent actions

Polynomial recovery replaces the truncated logarithm. It works over an arbitrary
commutative coefficient ring when the linear coefficient is a unit, so no
rational-algebra structure is silently imposed on prime-local integers.
-/

namespace NilpotentConjugacy

open Polynomial

section PolynomialRecovery

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- A polynomial with zero constant term and unit linear term generates every
nilpotent element from its value. The proof recovers descending powers and uses
only inversion of the stated unit. -/
theorem nilpotent_mem_of_polynomial_mem (S : Subalgebra R A) (x : A)
    (n : ℕ) (hx : x ^ n = 0) (f : R[X])
    (hf0 : f.coeff 0 = 0) (hf1 : IsUnit (f.coeff 1))
    (hfS : aeval x f ∈ S) : x ∈ S := by
  obtain ⟨g, hg⟩ := X_dvd_iff.mpr hf0
  have hg0 : IsUnit (g.coeff 0) := by
    simpa [hg] using hf1
  have hdesc : ∀ k ≤ n, ∀ q : R[X], x ^ k * aeval x q ∈ S := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self => intro q; simp [hx]
    | of_succ k hk ih =>
      have heq : (aeval x f) ^ k =
          x ^ (k + 1) * aeval x ((g ^ k).divX) +
            (g.coeff 0) ^ k • x ^ k := by
        rw [hg, ← map_pow, mul_pow, map_mul, map_pow, aeval_X]
        conv_lhs => arg 2; rw [← X_mul_divX_add (g ^ k)]
        simp only [map_add, map_mul, aeval_X, aeval_C, mul_add,
          ← mul_assoc, ← pow_succ]
        congr 1
        rw [Algebra.smul_def, Algebra.commutes]
        congr 1
        exact congrArg (algebraMap R A) (map_pow (constantCoeff : R[X] →+* R) g k)
      have hscalar : (g.coeff 0) ^ k • x ^ k ∈ S := by
        have hh := S.sub_mem (S.pow_mem hfS k) (ih ((g ^ k).divX))
        simpa [heq] using hh
      have hxk : x ^ k ∈ S :=
        (S.toSubmodule.smul_mem_iff_of_isUnit (hg0.pow k)).mp hscalar
      intro q
      rw [← X_mul_divX_add q, map_add, map_mul, aeval_X, aeval_C,
        mul_add, ← mul_assoc, ← pow_succ]
      apply S.add_mem (ih q.divX)
      exact S.mul_mem hxk (S.algebraMap_mem (q.coeff 0))
  simpa using hdesc 0 (Nat.zero_le n) X

end PolynomialRecovery

section TruncatedExponential

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The finite exponential polynomial. Its coefficient inverses are ring
inverses, and are used as genuine inverses only under separate unit proofs. -/
noncomputable def truncatedExpPolynomial (R : Type*) [CommRing R] (m : ℕ) : R[X] :=
  ∑ k ∈ Finset.range m, C (Ring.inverse (k.factorial : R)) * X ^ k

/-- Finite polynomial exponential over the specified coefficient ring. -/
noncomputable def truncatedExp (R : Type*) [CommRing R] {A : Type*}
    [Ring A] [Algebra R A] (m : ℕ) (x : A) : A :=
  aeval x (truncatedExpPolynomial R m)

theorem truncatedExp_eq_sum (m : ℕ) (x : A) :
    truncatedExp R m x =
      ∑ k ∈ Finset.range m, Ring.inverse (k.factorial : R) • x ^ k := by
  simp [truncatedExp, truncatedExpPolynomial, Algebra.smul_def]

theorem truncatedExpPolynomial_coeff (m k : ℕ) :
    (truncatedExpPolynomial R m).coeff k =
      if k < m then Ring.inverse (k.factorial : R) else 0 := by
  classical
  simp [truncatedExpPolynomial, coeff_C_mul, coeff_X_pow]

/-- Every invariant submodule for a finite exponential is invariant for its
nilpotent exponent. This is the exact descent supplied by the logarithm in the
manuscript, proved by polynomial recovery. -/
theorem nilpotent_mem_of_truncatedExp_mem (S : Subalgebra R A)
    (x : A) (n m : ℕ) (hx : x ^ n = 0) (hm : 2 ≤ m)
    (hexp : truncatedExp R m x ∈ S) : x ∈ S := by
  apply nilpotent_mem_of_polynomial_mem S x n hx
    (truncatedExpPolynomial R m - 1)
  · simp [truncatedExpPolynomial_coeff, show 0 < m by omega]
  · simp [truncatedExpPolynomial_coeff, coeff_one, show 1 < m by omega]
  · simpa [truncatedExp] using S.sub_mem hexp S.one_mem

/-- Factorial denominators below the prime are units in the actual local ring. -/
theorem factorial_isUnit_primeLocalIntegers (p n : ℕ) [Fact p.Prime]
    (hn : n < p) : IsUnit (n.factorial : PrimeLocalIntegers p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.cast_mul]
    exact (small_nat_isUnit_primeLocalIntegers p (n + 1) (by omega) hn).mul
      (ih (by omega))

theorem shiftJ_pow_dimension (m : ℕ) :
    (shiftJ m : Matrix (Fin m) (Fin m) R) ^ m = 0 := by
  rw [shiftJ_pow]
  ext j i
  simp [shiftBand, show j.val ≠ i.val + m by omega]

theorem shiftY_pow_dimension (m : ℕ) :
    (shiftY m : Matrix (Fin m) (Fin m) R) ^ m = 0 := by
  rw [shiftY_pow]
  ext j i
  simp [shiftBand, show j.val ≠ i.val + m by omega]

/-- Recover `J` and `Y` from the two finite exponential actions on any local
relation submodule. The exponent `m! J` is the manuscript's integral action. -/
theorem primeLocal_shifts_preserve_of_exponentials (p m : ℕ) [Fact p.Prime]
    (hm : 2 ≤ m) (hp : m < p)
    (S : Submodule (PrimeLocalIntegers p) (Fin m → PrimeLocalIntegers p))
    (hU : ∀ x ∈ S,
      (truncatedExp (PrimeLocalIntegers p) m
        ((m.factorial : PrimeLocalIntegers p) • shiftJ m)).mulVec x ∈ S)
    (hE : ∀ x ∈ S,
      (truncatedExp (PrimeLocalIntegers p) m (shiftY m)).mulVec x ∈ S) :
    (∀ x ∈ S, (shiftJ m).mulVec x ∈ S) ∧
      (∀ x ∈ S, (shiftY m).mulVec x ∈ S) := by
  have hMJ : (m.factorial : PrimeLocalIntegers p) • shiftJ m ∈
      preservingSubalgebra S := by
    apply nilpotent_mem_of_truncatedExp_mem (preservingSubalgebra S) _ m m _ hm hU
    rw [smul_pow, shiftJ_pow_dimension, smul_zero]
  constructor
  · exact ((preservingSubalgebra S).toSubmodule.smul_mem_iff_of_isUnit
      (factorial_isUnit_primeLocalIntegers p m hp)).mp hMJ
  · exact nilpotent_mem_of_truncatedExp_mem (preservingSubalgebra S)
      (shiftY m) m m (shiftY_pow_dimension m) hm hE

/-- The integer exponential actions of the actual group force local kernel
invariance under both shift matrices. -/
theorem primeLocal_shifts_preserve_of_integral_actions (p m : ℕ) [Fact p.Prime]
    (hm : 2 ≤ m) (hp : m < p)
    (S : Submodule (PrimeLocalIntegers p) (Fin m → PrimeLocalIntegers p))
    (hU : ∀ x ∈ S,
      (integerMatrixMap (PrimeLocalIntegers p) m
        (integralExponential m (shiftJ m))).mulVec x ∈ S)
    (hE : ∀ x ∈ S,
      (integerMatrixMap (PrimeLocalIntegers p) m
        (weightedExponential m 1)).mulVec x ∈ S) :
    (∀ x ∈ S, (shiftJ m).mulVec x ∈ S) ∧
      (∀ x ∈ S, (shiftY m).mulVec x ∈ S) := by
  have hu : ∀ k < m, IsUnit (k.factorial : PrimeLocalIntegers p) :=
    fun k hk => factorial_isUnit_primeLocalIntegers p k (lt_trans hk hp)
  apply primeLocal_shifts_preserve_of_exponentials p m hm hp S
  · simpa only [integerMatrixMap_integralExponential (PrimeLocalIntegers p) m _ hu,
      integerMatrixMap_shiftJ, ← truncatedExp_eq_sum] using hU
  · simpa only [integerMatrixMap_weightedExponential (PrimeLocalIntegers p) m 1 hu,
      Int.cast_one, one_smul, ← truncatedExp_eq_sum] using hE

/-- A polynomial with constant coefficient one is invertible when evaluated
at a nilpotent operator. -/
theorem isUnit_aeval_of_nilpotent_of_coeff_zero_one (x : A) (hx : IsNilpotent x)
    (g : R[X]) (hg : g.coeff 0 = 1) : IsUnit (aeval x g) := by
  have hc : Commute x (aeval x g.divX) := by
    simpa using (Commute.all (X : R[X]) g.divX).map (aeval x).toRingHom
  have hn := hc.isNilpotent_mul_right hx
  rw [← X_mul_divX_add g, map_add, map_mul, aeval_X, aeval_C, hg, map_one]
  exact hn.isUnit_add_one

/-- The image of `exp(X)-1` equals the image of `X`, with the exponential
interpreted as the finite polynomial over the coefficient ring. -/
theorem range_truncatedExp_sub_one {V : Type*} [AddCommGroup V] [Module R V]
    (x : Module.End R V) (hx : IsNilpotent x) (m : ℕ) (hm : 2 ≤ m) :
    (truncatedExp R m x - 1).range = x.range := by
  have hf0 : (truncatedExpPolynomial R m - 1).coeff 0 = 0 := by
    simp [truncatedExpPolynomial_coeff, show 0 < m by omega]
  obtain ⟨g, hg⟩ := X_dvd_iff.mpr hf0
  have hg0 : g.coeff 0 = 1 := by
    have h1 := congrArg (fun f : R[X] => f.coeff 1) hg
    simpa [truncatedExpPolynomial_coeff, coeff_one, show 1 < m by omega] using h1.symm
  have hfactor : truncatedExp R m x - 1 = x * aeval x g := by
    have hh := congrArg (aeval x) hg
    simpa [truncatedExp] using hh
  have hu := isUnit_aeval_of_nilpotent_of_coeff_zero_one x hx g hg0
  have hsurj := ((Module.End.isUnit_iff _).mp hu).surjective
  ext y
  rw [hfactor]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨aeval x g v, rfl⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨w, rfl⟩ := hsurj v
    exact ⟨w, rfl⟩

/-- Multiplication by a unit scalar does not change a linear map's image. -/
theorem range_smul_of_isUnit {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module R V] [Module R W] (F : V →ₗ[R] W) (r : R) (hr : IsUnit r) :
    (r • F).range = F.range := by
  apply le_antisymm (LinearMap.range_smul_le_range F r)
  rintro y ⟨v, rfl⟩
  refine ⟨Ring.inverse r • v, ?_⟩
  simp only [LinearMap.smul_apply, map_smul, smul_smul,
    Ring.inverse_mul_cancel r hr, one_smul]

/-- The finite exponential difference has exactly the same image as the
nilpotent matrix exponent. -/
theorem range_truncatedExp_matrix_sub_one (m : ℕ) (hm : 2 ≤ m)
    (B : Matrix (Fin m) (Fin m) R) (hB : IsNilpotent B) :
    (truncatedExp R m B - 1).mulVecLin.range = B.mulVecLin.range := by
  have heq : (truncatedExp R m B - 1).mulVecLin =
      truncatedExp R m B.mulVecLin - 1 := by
    change Matrix.toLin' (truncatedExp R m B - 1) =
      truncatedExp R m (Matrix.toLin' B) - 1
    simp only [truncatedExp_eq_sum, map_sub, map_sum, map_smul,
      Matrix.toLin'_pow, Matrix.toLin'_one]
    rfl
  rw [heq]
  exact range_truncatedExp_sub_one B.mulVecLin
    (hB.map (Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) R ≃ₐ[R]
      Module.End R (Fin m → R))) m hm

/-- After localizing at `p>m`, the actual integral exponential difference and
its unscaled integer exponent have identical images. -/
theorem primeLocal_integralExponential_range (p m : ℕ) [Fact p.Prime]
    (hm : 2 ≤ m) (hp : m < p)
    (B : Matrix (Fin m) (Fin m) ℤ) (hB : LowerGap 1 B) :
    (integerMatrixMap (PrimeLocalIntegers p) m (integralExponential m B - 1)).mulVecLin.range =
      (integerMatrixMap (PrimeLocalIntegers p) m B).mulVecLin.range := by
  have hu : ∀ k < m, IsUnit (k.factorial : PrimeLocalIntegers p) :=
    fun k hk => factorial_isUnit_primeLocalIntegers p k (lt_trans hk hp)
  rw [map_sub, map_one, integerMatrixMap_integralExponential _ m B hu,
    ← truncatedExp_eq_sum]
  have hn : IsNilpotent ((m.factorial : PrimeLocalIntegers p) •
      integerMatrixMap (PrimeLocalIntegers p) m B) := by
    refine ⟨m, ?_⟩
    rw [smul_pow, ← map_pow, lowerGap_nilpotent hB, map_zero, smul_zero]
  rw [range_truncatedExp_matrix_sub_one m hm _ hn]
  rw [show ((m.factorial : PrimeLocalIntegers p) •
      integerMatrixMap (PrimeLocalIntegers p) m B).mulVecLin =
      (m.factorial : PrimeLocalIntegers p) •
        (integerMatrixMap (PrimeLocalIntegers p) m B).mulVecLin by
    ext v i
    simp]
  exact range_smul_of_isUnit _ _ (factorial_isUnit_primeLocalIntegers p m hp)

end TruncatedExponential

end NilpotentConjugacy
