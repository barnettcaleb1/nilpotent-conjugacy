import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Tactic

/-!
# Matrix units from two truncated shifts

Indices in this file are zero based. `shiftJ` sends the basis vector at `i`
to that at `i+1`, and `shiftY` sends it to `(i+1)` times that vector.
Thus these are the matrices `J,Y` in the frozen manuscript.

The interpolation result is over an arbitrary commutative ring. Its unit
hypotheses are explicit; no field assumption silently inverts denominators.
-/

namespace NilpotentConjugacy

open scoped BigOperators

variable {R : Type*} [CommRing R] {m : ℕ}

/-- A single lower diagonal, with coefficient determined by the input index. -/
def shiftBand (m d : ℕ) (f : ℕ → R) : Matrix (Fin m) (Fin m) R :=
  fun j i => if j.val = i.val + d then f i.val else 0

/-- The truncated unweighted shift. -/
def shiftJ (m : ℕ) : Matrix (Fin m) (Fin m) R := shiftBand m 1 (fun _ => 1)

/-- The truncated shift weighted by the manuscript's one-based input index. -/
def shiftY (m : ℕ) : Matrix (Fin m) (Fin m) R :=
  shiftBand m 1 (fun i => (i : R) + 1)

theorem shiftBand_zero_one : shiftBand m 0 (fun _ => (1 : R)) = 1 := by
  ext j i
  simp [shiftBand, Matrix.one_apply, Fin.ext_iff]

theorem shiftBand_mul (d e : ℕ) (f g : ℕ → R) :
    shiftBand m d f * shiftBand m e g =
      shiftBand m (e + d) (fun i => f (i + e) * g i) := by
  ext j i
  by_cases h : i.val + e < m
  · let k : Fin m := ⟨i.val + e, h⟩
    rw [Matrix.mul_apply, Finset.sum_eq_single k]
    · simp only [shiftBand, k, ↓reduceIte]
      split_ifs <;> simp_all [Nat.add_assoc]
    · intro b _ hbk
      have hb : b.val ≠ i.val + e := by
        intro hh
        exact hbk (Fin.ext hh)
      simp [shiftBand, hb]
    · simp
  · have hj : j.val ≠ i.val + (e + d) := by omega
    rw [Matrix.mul_apply]
    simp only [shiftBand, hj, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro b _
    have hb : b.val ≠ i.val + e := by omega
    simp [hb]

theorem shiftJ_pow (d : ℕ) :
    (shiftJ m : Matrix (Fin m) (Fin m) R) ^ d =
      shiftBand m d (fun _ => 1) := by
  induction d with
  | zero => exact shiftBand_zero_one.symm
  | succ d ih =>
    rw [pow_succ, ih, shiftJ, shiftBand_mul]
    simp [Nat.add_comm]

theorem shiftY_pow (d : ℕ) :
    (shiftY m : Matrix (Fin m) (Fin m) R) ^ d =
      shiftBand m d (fun i => (ascPochhammer R d).eval ((i : R) + 1)) := by
  induction d with
  | zero => simpa using (shiftBand_zero_one (R := R) (m := m)).symm
  | succ d ih =>
    rw [pow_succ', ih, shiftY, shiftBand_mul]
    congr 1
    funext i
    rw [ascPochhammer_succ_eval]
    push_cast
    ring

/-- The rising factorial formula used in the manuscript, including boundary truncation. -/
theorem shiftJ_pow_mul_shiftY_pow (d v : ℕ) (hv : v ≤ d) :
    (shiftJ m : Matrix (Fin m) (Fin m) R) ^ (d - v) * shiftY m ^ v =
      shiftBand m d (fun i => (ascPochhammer R v).eval ((i : R) + 1)) := by
  rw [shiftJ_pow, shiftY_pow, shiftBand_mul, Nat.add_sub_of_le hv]
  simp

/-- Multiplying by an adjusted first-order factor appends the root `a`.
The correction `d+1+a` compensates for the preceding shift by `d`. -/
theorem shifted_factor_mul (d a : ℕ) (f : ℕ → R) :
    (shiftY m - ((d : R) + 1 + (a : R)) • shiftJ m) * shiftBand m d f =
      shiftBand m (d + 1) (fun i => ((i : R) - (a : R)) * f i) := by
  have hf : shiftY m - ((d : R) + 1 + (a : R)) • shiftJ m =
      shiftBand m 1 (fun i => (i : R) + 1 - ((d : R) + 1 + (a : R))) := by
    ext j i
    simp only [shiftY, shiftJ, shiftBand, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul]
    split_ifs <;> ring
  rw [hf, shiftBand_mul]
  congr 1
  funext i
  push_cast
  ring

/-- Every factored polynomial of degree `s.card` is realized on that lower diagonal
inside any subalgebra containing `J` and `Y`. -/
theorem rootProduct_band_mem (A : Subalgebra R (Matrix (Fin m) (Fin m) R))
    (hJ : shiftJ m ∈ A) (hY : shiftY m ∈ A) (s : Finset ℕ) :
    shiftBand m s.card (fun i => ∏ a ∈ s, ((i : R) - (a : R))) ∈ A := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [shiftBand_zero_one]
  | @insert a s ha ih =>
    have hh := A.mul_mem (A.sub_mem hY (A.smul_mem hJ ((s.card : R) + 1 + a))) ih
    rw [shifted_factor_mul] at hh
    simpa [Finset.card_insert_of_notMem ha, Finset.prod_insert ha] using hh

/-- Additional powers of `J` pad a polynomial of degree at most the desired gap. -/
theorem rootProduct_band_mem_of_card_le (A : Subalgebra R (Matrix (Fin m) (Fin m) R))
    (hJ : shiftJ m ∈ A) (hY : shiftY m ∈ A) (s : Finset ℕ) (d : ℕ)
    (hd : s.card ≤ d) :
    shiftBand m d (fun i => ∏ a ∈ s, ((i : R) - (a : R))) ∈ A := by
  have hh := A.mul_mem (A.pow_mem hJ (d - s.card)) (rootProduct_band_mem A hJ hY s)
  rw [shiftJ_pow, shiftBand_mul, Nat.add_sub_of_le hd] at hh
  simpa using hh

/-- General interpolation theorem: the indicated matrix unit belongs to every
subalgebra containing `J,Y`. There are `m-d` active input indices, so the exact
degree hypothesis is `m-d-1 ≤ d`. Every difference occurring in the Lagrange
denominator is explicitly required to be a unit in `R`. -/
theorem matrixUnit_mem_of_gap (A : Subalgebra R (Matrix (Fin m) (Fin m) R))
    (hJ : shiftJ m ∈ A) (hY : shiftY m ∈ A) (d i : ℕ)
    (hi : i + d < m) (hgap : m - d - 1 ≤ d)
    (hunit : ∀ a < m - d, a ≠ i → IsUnit ((i : R) - (a : R))) :
    Matrix.single (⟨i + d, hi⟩ : Fin m) (⟨i, by omega⟩ : Fin m) (1 : R) ∈ A := by
  classical
  let s := (Finset.range (m - d)).erase i
  have his : i ∈ Finset.range (m - d) := Finset.mem_range.mpr (by omega)
  have hs : s.card = m - d - 1 := by simp [s, Finset.card_erase_of_mem his]
  let c : R := ∏ a ∈ s, ((i : R) - (a : R))
  have hc : IsUnit c := by
    apply IsUnit.prod_iff.mpr
    intro a ha
    have hsa := Finset.mem_erase.mp ha
    exact hunit a (Finset.mem_range.mp hsa.2) hsa.1
  obtain ⟨u, hu⟩ := hc
  have hp := rootProduct_band_mem_of_card_le A hJ hY s d (by omega)
  have hh := A.smul_mem hp (↑(u⁻¹) : R)
  convert hh using 1
  ext j k
  simp only [Matrix.single_apply, Matrix.smul_apply, smul_eq_mul, shiftBand]
  by_cases hk : k.val = i
  · have hki : (⟨i, by omega⟩ : Fin m) = k := Fin.ext hk.symm
    have heq : ((⟨i + d, hi⟩ : Fin m) = j) ↔ j.val = k.val + d := by
      simp only [Fin.ext_iff]
      omega
    rw [hki]
    simp only [and_true, heq]
    split_ifs
    · rw [hk]
      change 1 = (↑(u⁻¹) : R) * c
      rw [← hu]
      simp
    · simp
  · have hki : (⟨i, by omega⟩ : Fin m) ≠ k := by
      intro heq
      exact hk (congrArg Fin.val heq).symm
    simp only [hki, and_false, ↓reduceIte]
    split_ifs with hband
    · have hks : k.val ∈ s := by
        apply Finset.mem_erase.mpr
        exact ⟨hk, Finset.mem_range.mpr (by omega)⟩
      have hz : (∏ a ∈ s, ((k.val : R) - (a : R))) = 0 :=
        Finset.prod_eq_zero hks (sub_self _)
      rw [hz, mul_zero]
    · simp

/-- The matrix-unit conclusion stated as membership in the generated algebra.
The natural-number threshold `m / 2` is `ceil ((m-1)/2)` for positive `m`. -/
theorem matrixUnit_mem_adjoin (i j : Fin m) (hij : i.val ≤ j.val)
    (hgap : m / 2 ≤ j.val - i.val)
    (hunit : ∀ a < m - (j.val - i.val), a ≠ i.val →
      IsUnit ((i.val : R) - (a : R))) :
    Matrix.single j i (1 : R) ∈
      Algebra.adjoin R ({shiftJ m, shiftY m} : Set (Matrix (Fin m) (Fin m) R)) := by
  have hh := matrixUnit_mem_of_gap
    (Algebra.adjoin R ({shiftJ m, shiftY m} : Set (Matrix (Fin m) (Fin m) R)))
    (Algebra.subset_adjoin (by simp)) (Algebra.subset_adjoin (by simp))
    (j.val - i.val) i.val (by omega) (by omega) hunit
  convert hh using 1
  congr 1
  apply Fin.ext
  simp
  omega

/-- A convenient exact sufficient denominator hypothesis: all positive natural
numbers below the dimension are units. This is the condition supplied by
localization at a prime greater than `m`. -/
theorem index_difference_isUnit
    (hsmall : ∀ n : ℕ, 0 < n → n < m → IsUnit (n : R))
    (i a : ℕ) (hi : i < m) (ha : a < m) (hne : a ≠ i) :
    IsUnit ((i : R) - (a : R)) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [← Nat.cast_sub (Nat.le_of_lt hlt)]
    exact hsmall (i - a) (by omega) (by omega)
  · have hh := hsmall (a - i) (by omega) (by omega)
    rw [Nat.cast_sub (Nat.le_of_lt hgt)] at hh
    simpa only [neg_sub] using hh.neg

theorem matrixUnit_mem_adjoin_of_small_units (i j : Fin m) (hij : i.val ≤ j.val)
    (hgap : m / 2 ≤ j.val - i.val)
    (hsmall : ∀ n : ℕ, 0 < n → n < m → IsUnit (n : R)) :
    Matrix.single j i (1 : R) ∈
      Algebra.adjoin R ({shiftJ m, shiftY m} : Set (Matrix (Fin m) (Fin m) R)) := by
  apply matrixUnit_mem_adjoin i j hij hgap
  intro a ha hne
  exact index_difference_isUnit hsmall i.val a i.isLt (by omega) hne

/-- Matrices preserving a fixed submodule form a subalgebra. -/
def preservingSubalgebra (S : Submodule R (Fin m → R)) :
    Subalgebra R (Matrix (Fin m) (Fin m) R) where
  carrier := {M | ∀ x ∈ S, M.mulVec x ∈ S}
  add_mem' := by
    intro M N hM hN x hx
    rw [Matrix.add_mulVec]
    exact S.add_mem (hM x hx) (hN x hx)
  mul_mem' := by
    intro M N hM hN x hx
    rw [← Matrix.mulVec_mulVec]
    exact hM _ (hN x hx)
  algebraMap_mem' := by
    intro r x hx
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact S.smul_mem r hx

/-- In particular the matrix unit preserves every submodule preserved by `J,Y`.
This is the descent assertion of the matrix-unit lemma; constructing the
manuscript's particular localized kernel is a separate obligation. -/
theorem matrixUnit_preserves (S : Submodule R (Fin m → R))
    (hJ : ∀ x ∈ S, (shiftJ m).mulVec x ∈ S)
    (hY : ∀ x ∈ S, (shiftY m).mulVec x ∈ S)
    (i j : Fin m) (hij : i.val ≤ j.val) (hgap : m / 2 ≤ j.val - i.val)
    (hsmall : ∀ n : ℕ, 0 < n → n < m → IsUnit (n : R)) :
    ∀ x ∈ S, (Matrix.single j i (1 : R)).mulVec x ∈ S := by
  have hh := matrixUnit_mem_of_gap (preservingSubalgebra S) hJ hY
    (j.val - i.val) i.val (by omega) (by omega)
    (fun a ha hne => index_difference_isUnit hsmall i.val a i.isLt (by omega) hne)
  change Matrix.single j i (1 : R) ∈ preservingSubalgebra S
  convert hh using 1
  congr 1
  apply Fin.ext
  simp
  omega

/-- The prime ideal `(p)` in the integers. -/
def integerPrimeIdeal (p : ℕ) : Ideal ℤ := Ideal.span {(p : ℤ)}

instance integerPrimeIdeal_isPrime (p : ℕ) [Fact p.Prime] :
    (integerPrimeIdeal p).IsPrime := by
  apply Ideal.isPrime_span_singleton_of_prime
  exact Nat.prime_iff_prime_int.mp Fact.out

/-- The ring `ℤ_(p)`: integers localized at the complement of `(p)`. -/
abbrev PrimeLocalIntegers (p : ℕ) [Fact p.Prime] :=
  Localization.AtPrime (integerPrimeIdeal p)

/-- Every positive integer less than `p` is a unit in `ℤ_(p)`. -/
theorem small_nat_isUnit_primeLocalIntegers (p n : ℕ) [Fact p.Prime]
    (hn : 0 < n) (hnp : n < p) : IsUnit (n : PrimeLocalIntegers p) := by
  have hh : IsUnit (algebraMap ℤ (PrimeLocalIntegers p) (n : ℤ)) := by
    apply (IsLocalization.AtPrime.isUnit_to_map_iff
      (PrimeLocalIntegers p) (integerPrimeIdeal p) (n : ℤ)).mpr
    rw [Ideal.mem_primeCompl_iff, integerPrimeIdeal, Ideal.mem_span_singleton,
      Int.natCast_dvd_natCast]
    exact Nat.not_dvd_of_pos_of_lt hn hnp
  simpa using hh

/-- The manuscript's matrix-unit conclusion over the actual localized coefficient
ring, for any prime `p>m` and any lower-diagonal gap at least `ceil ((m-1)/2)`. -/
theorem matrixUnit_mem_primeLocal_adjoin (p : ℕ) [Fact p.Prime] (hp : m < p)
    (i j : Fin m) (hij : i.val ≤ j.val) (hgap : m / 2 ≤ j.val - i.val) :
    Matrix.single j i (1 : PrimeLocalIntegers p) ∈
      Algebra.adjoin (PrimeLocalIntegers p)
        ({shiftJ m, shiftY m} : Set (Matrix (Fin m) (Fin m) (PrimeLocalIntegers p))) := by
  apply matrixUnit_mem_adjoin_of_small_units i j hij hgap
  intro n hn hnm
  exact small_nat_isUnit_primeLocalIntegers p n hn (lt_trans hnm hp)

/-- The invariant-kernel conclusion over the paper's prime localization. -/
theorem matrixUnit_preserves_primeLocal (p : ℕ) [Fact p.Prime] (hp : m < p)
    (S : Submodule (PrimeLocalIntegers p) (Fin m → PrimeLocalIntegers p))
    (hJ : ∀ x ∈ S, (shiftJ m).mulVec x ∈ S)
    (hY : ∀ x ∈ S, (shiftY m).mulVec x ∈ S)
    (i j : Fin m) (hij : i.val ≤ j.val) (hgap : m / 2 ≤ j.val - i.val) :
    ∀ x ∈ S, (Matrix.single j i (1 : PrimeLocalIntegers p)).mulVec x ∈ S := by
  apply matrixUnit_preserves S hJ hY i j hij hgap
  intro n hn hnm
  exact small_nat_isUnit_primeLocalIntegers p n hn (lt_trans hnm hp)

end NilpotentConjugacy
