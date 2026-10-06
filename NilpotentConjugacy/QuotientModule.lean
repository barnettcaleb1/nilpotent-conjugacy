import NilpotentConjugacy.MatrixUnits
import NilpotentConjugacy.FiniteCharacters
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The finite module quotient bridge

This file uses the actual quotient of `R^m` by an invariant submodule. Matrix
units and the bidiagonal map are descended by proofs of preservation. The group
construction and the passage from a separating group quotient to this module
and its obstruction remain separate obligations.
-/

namespace NilpotentConjugacy

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The coordinate vector at a natural index, zero outside the dimension. -/
def coordinateVector (R : Type*) [CommRing R] (m k : ℕ) : Fin m → R :=
  fun i => if i.val = k then 1 else 0

@[simp] theorem coordinateVector_fin (i : Fin m) :
    coordinateVector R m i.val = Pi.single i 1 := by
  ext j
  simp [coordinateVector, Pi.single_apply, Fin.ext_iff, eq_comm]

@[simp] theorem coordinateVector_outside (k : ℕ) (hk : m ≤ k) :
    coordinateVector R m k = 0 := by
  ext i
  simp [coordinateVector, show i.val ≠ k by omega]

/-- A preserving matrix induces an actual linear endomorphism of the quotient. -/
def quotientMatrix (S : Submodule R (Fin m → R))
    (M : Matrix (Fin m) (Fin m) R)
    (hM : ∀ x ∈ S, M.mulVec x ∈ S) :
    ((Fin m → R) ⧸ S) →ₗ[R] ((Fin m → R) ⧸ S) :=
  S.mapQ S M.mulVecLin hM

@[simp] theorem quotientMatrix_mk (S : Submodule R (Fin m → R))
    (M : Matrix (Fin m) (Fin m) R)
    (hM : ∀ x ∈ S, M.mulVec x ∈ S) (x : Fin m → R) :
    quotientMatrix S M hM (S.mkQ x) = S.mkQ (M.mulVec x) := rfl

/-- The image of a coordinate vector in the actual module quotient. -/
def quotientCoordinate (S : Submodule R (Fin m → R)) (k : ℕ) : (Fin m → R) ⧸ S :=
  S.mkQ (coordinateVector R m k)

@[simp] theorem quotientCoordinate_outside (S : Submodule R (Fin m → R))
    (k : ℕ) (hk : m ≤ k) : quotientCoordinate S k = 0 := by
  simp [quotientCoordinate, coordinateVector_outside k hk]

/-- Descended matrix units have the required delta values on quotient coordinates. -/
theorem quotientMatrix_single_coordinate (S : Submodule R (Fin m → R))
    (i j k : Fin m)
    (hM : ∀ x ∈ S, (Matrix.single j i (1 : R)).mulVec x ∈ S) :
    quotientMatrix S (Matrix.single j i 1) hM (quotientCoordinate S k.val) =
      if k = i then quotientCoordinate S j.val else 0 := by
  simp only [quotientCoordinate, quotientMatrix_mk, coordinateVector_fin,
    Matrix.single_mulVec_eq, one_mul]
  by_cases hk : k = i
  · subst k
    simp
  · simp [hk, Ne.symm hk]

/-- Powers of the shift move a standard coordinate by their exponent. -/
theorem shiftJ_pow_coordinate (d k : ℕ) (hk : k < m) :
    ((shiftJ m : Matrix (Fin m) (Fin m) R) ^ d).mulVec
      (coordinateVector R m k) = coordinateVector R m (k + d) := by
  have he : coordinateVector R m k = Pi.single (⟨k, hk⟩ : Fin m) 1 :=
    coordinateVector_fin ⟨k, hk⟩
  rw [he, Matrix.mulVec_single_one, shiftJ_pow]
  ext j
  simp [shiftBand, coordinateVector, Matrix.col_apply]

/-- The full truncated matrix `J^w (t I + J)`. -/
def shiftedBidiagonalMatrix (m w : ℕ) (t : R) : Matrix (Fin m) (Fin m) R :=
  shiftJ m ^ w * (t • 1 + shiftJ m)

/-- Every column, including its truncation at the bottom boundary. -/
theorem shiftedBidiagonalMatrix_coordinate (w k : ℕ) (t : R) (hk : k < m) :
    (shiftedBidiagonalMatrix m w t).mulVec (coordinateVector R m k) =
      t • coordinateVector R m (k + w) + coordinateVector R m (k + w + 1) := by
  rw [shiftedBidiagonalMatrix, mul_add, Matrix.mul_smul, mul_one,
    ← pow_succ, Matrix.add_mulVec, Matrix.smul_mulVec,
    shiftJ_pow_coordinate w k hk, shiftJ_pow_coordinate (w + 1) k hk]
  simp only [Nat.add_assoc]

/-- Stability under `J` implies stability under the entire bidiagonal polynomial. -/
theorem shiftedBidiagonalMatrix_preserves (S : Submodule R (Fin m → R))
    (hJ : ∀ x ∈ S, (shiftJ m).mulVec x ∈ S) (w : ℕ) (t : R) :
    ∀ x ∈ S, (shiftedBidiagonalMatrix m w t).mulVec x ∈ S := by
  change shiftedBidiagonalMatrix m w t ∈ preservingSubalgebra S
  exact (preservingSubalgebra S).mul_mem
    ((preservingSubalgebra S).pow_mem hJ w)
    ((preservingSubalgebra S).add_mem
      ((preservingSubalgebra S).smul_mem (preservingSubalgebra S).one_mem t) hJ)

/-- The induced bidiagonal polynomial endomorphism of the quotient. -/
def quotientBidiagonal (S : Submodule R (Fin m → R))
    (hJ : ∀ x ∈ S, (shiftJ m).mulVec x ∈ S) (w : ℕ) (t : R) :
    ((Fin m → R) ⧸ S) →ₗ[R] ((Fin m → R) ⧸ S) :=
  quotientMatrix S (shiftedBidiagonalMatrix m w t)
    (shiftedBidiagonalMatrix_preserves S hJ w t)

/-- The quotient polynomial has the same adjacent columns on quotient coordinates. -/
theorem quotientBidiagonal_coordinate (S : Submodule R (Fin m → R))
    (hJ : ∀ x ∈ S, (shiftJ m).mulVec x ∈ S) (w k : ℕ) (t : R) (hk : k < m) :
    quotientBidiagonal S hJ w t (quotientCoordinate S k) =
      t • quotientCoordinate S (k + w) + quotientCoordinate S (k + w + 1) := by
  simp only [quotientBidiagonal, quotientCoordinate, quotientMatrix_mk,
    shiftedBidiagonalMatrix_coordinate w k t hk, map_add, map_smul]

/-- The actual finite module quotient bound. The subgroup and matrix-unit
hypotheses of `finite_quotient_character_bound` are derived here from `J,Y`
invariance and the explicit polynomial `J^w(p^s I+J)`.

The only obstruction hypothesis is nonmembership in the image of that actual
quotient endomorphism. It has not been derived here from a group quotient. -/
theorem primeLocal_quotient_cardinality (p : ℕ) [Fact p.Prime]
    {m w s : ℕ} (hm : 4 ≤ m) (hp : m < p)
    (hwlo : m / 2 ≤ w) (hwhi : w ≤ m - 2) (hs : 0 < s)
    (S : Submodule (PrimeLocalIntegers p) (Fin m → PrimeLocalIntegers p))
    [Finite ((Fin m → PrimeLocalIntegers p) ⧸ S)]
    (hJ : ∀ x ∈ S, (shiftJ m).mulVec x ∈ S)
    (hY : ∀ x ∈ S, (shiftY m).mulVec x ∈ S)
    (D : ℕ)
    (hdetect : D • (p ^ (s - 1) • quotientCoordinate S (m - 1)) ∉
      (quotientBidiagonal S hJ w ((p ^ s : ℕ) : PrimeLocalIntegers p)).range) :
    p ^ (s * (m - w) * (w + 1 - m / 2)) ≤
      Nat.card ((Fin m → PrimeLocalIntegers p) ⧸ S) := by
  let q := w + 1 - m / 2
  let A := (Fin m → PrimeLocalIntegers p) ⧸ S
  let H : AddSubgroup A :=
    (quotientBidiagonal S hJ w ((p ^ s : ℕ) : PrimeLocalIntegers p)).range.toAddSubgroup
  let v : ℕ → A := fun k => quotientCoordinate S (w + k)
  let e : Fin q → A := fun i => quotientCoordinate S i.val
  let target : Fin m := ⟨w, by omega⟩
  let input : Fin q → Fin m := fun i => ⟨i.val, by have := i.isLt; dsimp [q] at *; omega⟩
  have hpres (i : Fin q) :
      ∀ x ∈ S, (Matrix.single target (input i) (1 : PrimeLocalIntegers p)).mulVec x ∈ S := by
    apply matrixUnit_preserves_primeLocal p hp S hJ hY
    · have := i.isLt
      dsimp [input, target, q] at *
      omega
    · have := i.isLt
      dsimp [input, target, q] at *
      omega
  let E : Fin q → A →+ A := fun i =>
    (quotientMatrix S (Matrix.single target (input i) 1) (hpres i)).toAddMonoidHom
  have hcolumns : ∀ k < (m - w) - 1, p ^ s • v k + v (k + 1) ∈ H := by
    intro k hk
    refine ⟨quotientCoordinate S k, ?_⟩
    rw [quotientBidiagonal_coordinate S hJ w k _ (by omega)]
    rw [Nat.cast_smul_eq_nsmul]
    simp only [v, Nat.add_comm k w, Nat.add_assoc]
  have hterminal : p ^ s • v (m - w - 1) ∈ H := by
    refine ⟨quotientCoordinate S (m - w - 1), ?_⟩
    rw [quotientBidiagonal_coordinate S hJ w (m - w - 1) _ (by omega)]
    have hlast : m - w - 1 + w = m - 1 := by omega
    have hout : m - w - 1 + w + 1 = m := by omega
    rw [Nat.cast_smul_eq_nsmul, hout, hlast,
      quotientCoordinate_outside S m (le_refl m), add_zero]
    simp only [v, show w + (m - w - 1) = m - 1 by omega]
  have hdet : D • (p ^ (s - 1) • v (m - w - 1)) ∉ H := by
    change D • (p ^ (s - 1) • quotientCoordinate S (w + (m - w - 1))) ∉
      (quotientBidiagonal S hJ w ((p ^ s : ℕ) : PrimeLocalIntegers p)).range
    simpa only [show w + (m - w - 1) = m - 1 by omega] using hdetect
  have hδ : ∀ i j, E i (e j) = if j = i then v 0 else 0 := by
    intro i j
    have h := quotientMatrix_single_coordinate S (input i) target (input j) (hpres i)
    simpa [E, e, v, input, target, Fin.ext_iff] using h
  exact finite_quotient_character_bound H v e E (Fact.out : p.Prime) hs (by omega)
    D hcolumns hterminal hdet hδ

end NilpotentConjugacy
