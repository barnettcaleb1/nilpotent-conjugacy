import NilpotentConjugacy.IntegralGroupAction
import NilpotentConjugacy.Unitriangular
import NilpotentConjugacy.SemidirectConjugacy

/-! Explicit pairs used for the cubic lower bound. We use m≤2w, a restriction
satisfied by m=4d,w=3d, so their exponential is exactly square-zero. -/
namespace NilpotentConjugacy
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

def pairCoefficients (m w : ℕ) (t : ℤ) : Fin (m-1) → ℤ :=
  t • coordinateVector ℤ (m-1) (w-1) + coordinateVector ℤ (m-1) w

def pairActor (m w : ℕ) (t : ℤ) : CoefficientGroup m :=
  SemidirectProduct.inl (Multiplicative.ofAdd (pairCoefficients m w t))

def pairCentralVector (m p s : ℕ) : Fin m → ℤ :=
  ((m.factorial : ℤ)^(m-1) * (p : ℤ)^(s-1)) • coordinateVector ℤ m (m-1)

def specialPairLeft (m w p s : ℕ) : ManuscriptGroup m :=
  SemidirectProduct.inr (pairActor m w ((p : ℤ)^s))

def specialPairRight (m w p s : ℕ) : ManuscriptGroup m :=
  SemidirectProduct.inl (Multiplicative.ofAdd (pairCentralVector m p s)) *
    specialPairLeft m w p s

theorem latticePolynomial_coordinate (m k : ℕ) (hk : k < m-1) :
    latticePolynomial m (coordinateVector ℤ (m-1) k) = (shiftJ m)^ (k+1) := by
  rw [coordinateVector_fin (⟨k,hk⟩ : Fin (m-1))]
  simp [latticePolynomial, Pi.single_apply]

theorem pairCoefficients_polynomial (m w : ℕ) (hw : 1 ≤ w) (hwm : w < m-1) (t : ℤ) :
    latticePolynomial m (pairCoefficients m w t) = shiftedBidiagonalMatrix m w t := by
  unfold pairCoefficients
  rw [latticePolynomial_add]
  have hsm : latticePolynomial m (t • coordinateVector ℤ (m-1) (w-1)) =
      t • latticePolynomial m (coordinateVector ℤ (m-1) (w-1)) := by
    exact (latticePolynomialHom m).map_zsmul t _
  rw [hsm, latticePolynomial_coordinate m (w-1) (by omega),
    latticePolynomial_coordinate m w hwm, show w-1+1=w by omega]
  rw [shiftedBidiagonalMatrix, mul_add, Matrix.mul_smul, mul_one, ← pow_succ]

theorem shiftedBidiagonalMatrix_gap (m w : ℕ) (t : ℤ) :
    LowerGap w (shiftedBidiagonalMatrix m w t) := by
  unfold shiftedBidiagonalMatrix
  have hj : LowerGap w ((shiftJ m : Matrix (Fin m) (Fin m) ℤ)^w) := lowerGap_pow lowerGap_shiftJ w
  have ht := gap_add (gap_smul t lowerGap_one)
    (gap_mono (lowerGap_shiftJ (R:=ℤ) (m:=m)) (by omega : 0 ≤ 1))
  simpa using lowerGap_mul hj ht

theorem shiftedBidiagonalMatrix_sq (m w : ℕ) (hmw : m ≤ 2*w) (t : ℤ) :
    (shiftedBidiagonalMatrix m w t)^2 = 0 := by
  apply gap_eq_zero (gap_pow (shiftedBidiagonalMatrix_gap m w t) 2)
  omega

theorem integralExponential_of_square_zero {m : ℕ} (hm : 2 ≤ m)
    (B : Matrix (Fin m) (Fin m) ℤ) (hB : B^2=0) :
    integralExponential m B = 1+(m.factorial : ℤ) • B := by
  unfold integralExponential
  have hsum : (∑ k ∈ Finset.range m, ((m.factorial^k/k.factorial : ℕ) : ℤ) • B^k) =
      ∑ k ∈ Finset.range 2, ((m.factorial^k/k.factorial : ℕ) : ℤ) • B^k := by
    symm
    apply Finset.sum_subset (Finset.range_mono hm)
    intro k hk hk2
    have h2 : 2 ≤ k := by simp only [Finset.mem_range] at hk2; omega
    rw [pow_eq_zero_of_le h2 hB, smul_zero]
  rw [hsum]
  simp [Finset.sum_range_succ, add_comm]

theorem pairActor_matrix (m w : ℕ) (hm : 4 ≤ m) (hw : 1 ≤ w) (hwm : w < m-1)
    (hmw : m ≤ 2*w) (t : ℤ) :
    (manuscriptRhoHom m (pairActor m w t)).val =
      1+(m.factorial : ℤ) • shiftedBidiagonalMatrix m w t := by
  simp only [pairActor, manuscriptRhoHom, SemidirectProduct.lift_inl]
  change integralExponential m (latticePolynomial m (pairCoefficients m w t)) = _
  rw [pairCoefficients_polynomial m w hw hwm,
    integralExponential_of_square_zero (by omega) _ (shiftedBidiagonalMatrix_sq m w hmw t)]

theorem pairActor_action_difference (m w : ℕ) (hm : 4 ≤ m) (hw : 1 ≤ w)
    (hwm : w < m-1) (hmw : m ≤ 2*w) (t : ℤ) (v : Fin m → ℤ) :
    (manuscriptAction m (pairActor m w t) (Multiplicative.ofAdd v)).toAdd-v =
      (m.factorial : ℤ) • (shiftedBidiagonalMatrix m w t).mulVec v := by
  change (manuscriptRhoHom m (pairActor m w t)).val.mulVec v-v = _
  rw [pairActor_matrix m w hm hw hwm hmw t, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  abel

theorem pair_prime_commutator (m w p s : ℕ) (hm : 4 ≤ m) (hw : 1 ≤ w)
    (hwm : w < m-1) (hmw : m ≤ 2*w) (hs : 1 ≤ s) :
    let v := (m.factorial : ℤ)^(m-2) • coordinateVector ℤ m (m-w-1)
    (manuscriptAction m (pairActor m w ((p : ℤ)^s)) (Multiplicative.ofAdd v)).toAdd-v =
      (p : ℤ) • pairCentralVector m p s := by
  dsimp only
  rw [pairActor_action_difference m w hm hw hwm hmw,
    Matrix.mulVec_smul, shiftedBidiagonalMatrix_coordinate w (m-w-1) _ (by omega)]
  rw [show m-w-1+w=m-1 by omega, show m-1+1=m by omega,
    coordinateVector_outside m (le_refl m), add_zero]
  simp only [pairCentralVector, smul_smul]
  congr 1
  have heM : m-1=(m-2)+1 := by omega
  have heS : s=(s-1)+1 := by omega
  rw [heM, heS, pow_succ, pow_succ]
  simp only [Nat.add_sub_cancel]
  ring

end
end NilpotentConjugacy
