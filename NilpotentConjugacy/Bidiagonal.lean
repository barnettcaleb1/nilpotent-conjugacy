import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Bidiagonal arithmetic used in the nilpotent-conjugacy draft

The integer matrix below is the square nonzero block of `J^w (t I + J)`.
Its dimension is `n + 1`; all coordinate indices are zero based. Theorems in
this file concern that block and additive characters, not the construction
or conjugacy growth of the group in the paper.
-/

namespace NilpotentConjugacy

/-- The lower shift: coordinate zero vanishes and coordinate `i+1` is `x i`. -/
def lowerShift {R : Type*} [Zero R] (n : ℕ) (x : Fin (n + 1) → R) : Fin (n + 1) → R :=
  Fin.cases 0 (fun i => x i.castSucc)

/-- The integral lower bidiagonal matrix `t I + J`, as a genuine linear map. -/
def bidiagonal {R : Type*} [CommRing R] (t : R) (n : ℕ) :
    (Fin (n + 1) → R) →ₗ[R] (Fin (n + 1) → R) where
  toFun x i := t * x i + lowerShift n x i
  map_add' x y := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [lowerShift, mul_add, add_assoc, add_left_comm, add_comm]
  map_smul' c x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [lowerShift, mul_add] <;> ring

@[simp] theorem bidiagonal_zero {R : Type*} [CommRing R]
    (t : R) (n : ℕ) (x : Fin (n + 1) → R) :
    bidiagonal t n x 0 = t * x 0 := by
  simp [bidiagonal, lowerShift]

@[simp] theorem bidiagonal_succ {R : Type*} [CommRing R]
    (t : R) (n : ℕ) (x : Fin (n + 1) → R)
    (i : Fin n) :
    bidiagonal t n x i.succ = t * x i.succ + x i.castSucc := by
  simp [bidiagonal, lowerShift]

/-- Vanishing output through coordinate `i` forces the same input coordinates
    to vanish whenever the diagonal entry is nonzero. -/
theorem bidiagonal_initial_zero (t : ℤ) (ht : t ≠ 0) (n : ℕ)
    (x : Fin (n + 1) → ℤ) (i : Fin (n + 1))
    (h : ∀ j : Fin (n + 1), j ≤ i → bidiagonal t n x j = 0) : x i = 0 := by
  induction i using Fin.induction with
  | zero =>
      have h0 := h 0 (le_refl _)
      simpa [ht] using h0
  | succ i ih =>
      have hi : x i.castSucc = 0 := ih (fun j hj => h j (le_trans hj (by change i.val ≤ i.val + 1; omega)))
      have hs := h i.succ (le_refl _)
      simpa [hi, ht] using hs

/-- A multiple of the last basis vector lies in the integral bidiagonal image
    exactly when its coefficient is divisible by the diagonal entry. -/
theorem last_mem_bidiagonal_range_iff (t : ℤ) (ht : t ≠ 0) (n : ℕ) (k : ℤ) :
    (∃ x : Fin (n + 1) → ℤ, bidiagonal t n x = Pi.single (Fin.last n) k) ↔ t ∣ k := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x (Fin.last n), ?_⟩
    have hout := congrFun hx (Fin.last n)
    have hz : lowerShift n x (Fin.last n) = 0 := by
      cases n with
      | zero => simp [lowerShift]
      | succ n =>
          change x (Fin.last n).castSucc = 0
          apply bidiagonal_initial_zero t ht (n + 1) x (Fin.last n).castSucc
          intro j hj
          rw [hx]
          apply Pi.single_eq_of_ne
          intro heq
          subst j
          simp at hj
    simpa [bidiagonal, hz] using hout.symm
  · rintro ⟨a, rfl⟩
    refine ⟨Pi.single (Fin.last n) a, ?_⟩
    ext i
    have hs : lowerShift n (Pi.single (Fin.last n) a) i = 0 := by
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [lowerShift]
      · simp [lowerShift, Fin.castSucc_ne_last]
    simp only [bidiagonal, LinearMap.coe_mk, AddHom.coe_mk, hs, add_zero]
    by_cases hi : i = Fin.last n <;> simp [hi]

section AdditiveCharacters

variable {A : Type*} [AddCommGroup A]

/-- All solutions of the adjacent-column recurrence have the claimed signed
    geometric form, with no finiteness or primary-group hypothesis. -/
theorem bidiagonal_recurrence (t : ℤ) (a : ℕ → A) (n : ℕ)
    (h : ∀ i < n, t • a i + a (i + 1) = 0) :
    a n = (-t) ^ n • a 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn : a (n + 1) = -(t • a n) := eq_neg_of_add_eq_zero_right (h n (by omega))
      rw [hn, ih (fun i hi => h i (by omega)), pow_succ', mul_zsmul, neg_zsmul]

/-- Changing the sign of the scalar does not change whether its power kills
    an element. -/
theorem neg_pow_zsmul_eq_zero_iff (t : ℤ) (n : ℕ) (a : A) :
    (-t) ^ n • a = 0 ↔ t ^ n • a = 0 := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, mul_zsmul, mul_zsmul, neg_zsmul, zsmul_neg, neg_eq_zero]
      exact ih (t • a)


/-- The sign in the chain disappears when testing annihilation by a prime
    power. This elementary identity does not require `p` to be prime. -/
theorem primePow_smul_chain_eq_zero_iff (p s k n : ℕ) (a : A) :
    p ^ k • ((-(p : ℤ) ^ s) ^ n • a) = 0 ↔ p ^ (k + s * n) • a = 0 := by
  rw [smul_comm (p ^ k), neg_pow_zsmul_eq_zero_iff]
  have hcast : ((p : ℤ) ^ s) ^ n = ((p ^ (s * n) : ℕ) : ℤ) := by
    simp [pow_mul]
  rw [hcast, Nat.cast_smul_eq_nsmul, ← mul_nsmul, ← pow_add, Nat.add_comm]

/-- Detecting a multiple of `p^(s-1)` in the terminal coordinate forces the
    initial coordinate to have exactly order `p^(s*(n+1))`. In particular,
    no primary-group assumption needs to be hidden in this arithmetic step. -/
theorem bidiagonal_recurrence_exact_order (p : ℕ) (hp : p.Prime) (s : ℕ)
    (hs : 0 < s) (n : ℕ) (a : ℕ → A) (C : ℤ)
    (hrec : ∀ i < n, (p ^ s : ℕ) • a i + a (i + 1) = 0)
    (hend : (p ^ s : ℕ) • a n = 0)
    (hdetect : C • ((p ^ (s - 1) : ℕ) • a n) ≠ 0) :
    addOrderOf (a 0) = p ^ (s * (n + 1)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hrec' : ∀ i < n, (p : ℤ) ^ s • a i + a (i + 1) = 0 := by
    simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using hrec
  have ha := bidiagonal_recurrence ((p : ℤ) ^ s) a n hrec'
  have hkill : p ^ (s * (n + 1)) • a 0 = 0 := by
    have h := (primePow_smul_chain_eq_zero_iff p s s n (a 0)).mp (by rw [← ha]; exact hend)
    simpa [Nat.mul_add, Nat.add_comm] using h
  have hne : p ^ (s * (n + 1) - 1) • a 0 ≠ 0 := by
    intro hz
    apply hdetect
    have he : s - 1 + s * n = s * (n + 1) - 1 := by rw [Nat.mul_add, Nat.mul_one]; omega
    have h := (primePow_smul_chain_eq_zero_iff p s (s - 1) n (a 0)).mpr (by simpa [he] using hz)
    rw [← ha] at h
    simp [h]
  have hpos : 0 < s * (n + 1) := Nat.mul_pos hs (by omega)
  have he : s * (n + 1) - 1 + 1 = s * (n + 1) := by omega
  have h := addOrderOf_eq_prime_pow hne (by simpa [he] using hkill)
  simpa [he] using h


/-- The additive character of an integer lattice specified by its values on
    the standard basis. -/
def latticeCharacter {n : ℕ} (a : Fin (n + 1) → A) : (Fin (n + 1) → ℤ) →+ A where
  toFun x := ∑ i, x i • a i
  map_zero' := by simp
  map_add' x y := by simp [add_zsmul, Finset.sum_add_distrib]

@[simp] theorem latticeCharacter_single {n : ℕ} (a : Fin (n + 1) → A)
    (j : Fin (n + 1)) (k : ℤ) :
    latticeCharacter a (Pi.single j k) = k • a j := by
  classical
  simp [latticeCharacter, Pi.single_apply]

/-- The value on a bidiagonal output is the sum of the adjacent-column
    obstructions and the terminal-column obstruction. -/
theorem latticeCharacter_bidiagonal (t : ℤ) (n : ℕ) (a : Fin (n + 1) → A)
    (x : Fin (n + 1) → ℤ) :
    latticeCharacter a (bidiagonal t n x) =
      (∑ i : Fin n, x i.castSucc • (t • a i.castSucc + a i.succ)) +
        x (Fin.last n) • (t • a (Fin.last n)) := by
  change (∑ i, (t * x i + lowerShift n x i) • a i) = _
  simp only [add_zsmul, Finset.sum_add_distrib]
  have hs : (∑ i : Fin (n + 1), lowerShift n x i • a i) =
      ∑ i : Fin n, x i.castSucc • a i.succ := by
    rw [Fin.sum_univ_succ]
    simp [lowerShift]
  rw [hs, Fin.sum_univ_castSucc (fun i : Fin (n + 1) => (t * x i) • a i)]
  simp only [zsmul_add, Finset.sum_add_distrib, mul_zsmul]
  simp_rw [smul_comm t]
  abel

/-- Adjacent cancellation and terminal annihilation make the character vanish
    on the whole image of the bidiagonal operator. -/
theorem latticeCharacter_annihilates_bidiagonal (t : ℤ) (n : ℕ)
    (a : Fin (n + 1) → A)
    (hrec : ∀ i : Fin n, t • a i.castSucc + a i.succ = 0)
    (hend : t • a (Fin.last n) = 0) (x : Fin (n + 1) → ℤ) :
    latticeCharacter a (bidiagonal t n x) = 0 := by
  rw [latticeCharacter_bidiagonal]
  simp [hrec, hend]

/-- The signed geometric values satisfy every adjacent-column cancellation. -/
theorem geometric_adjacent (t : ℤ) (a : A) (i : ℕ) :
    t • ((-t) ^ i • a) + (-t) ^ (i + 1) • a = 0 := by
  rw [pow_succ', mul_zsmul, neg_zsmul]
  exact add_neg_cancel _

/-- A detection certificate immediately proves nonmembership in the image. -/
theorem not_mem_bidiagonal_image_of_character (t : ℤ) (n : ℕ)
    (a : Fin (n + 1) → A) (v : Fin (n + 1) → ℤ)
    (hrec : ∀ i : Fin n, t • a i.castSucc + a i.succ = 0)
    (hend : t • a (Fin.last n) = 0)
    (hdetect : latticeCharacter a v ≠ 0) :
    ¬∃ x, bidiagonal t n x = v := by
  rintro ⟨x, rfl⟩
  exact hdetect (latticeCharacter_annihilates_bidiagonal t n a hrec hend x)

end AdditiveCharacters


section FiniteDetector

variable {R : Type*} [CommRing R]

/-- A coordinate character with values in a commutative ring. -/
def coefficientCharacter {n : ℕ} (a : Fin (n + 1) → R) : (Fin (n + 1) → R) →ₗ[R] R where
  toFun x := ∑ i, x i * a i
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_assoc]

@[simp] theorem coefficientCharacter_single {n : ℕ} (a : Fin (n + 1) → R)
    (j : Fin (n + 1)) (k : R) :
    coefficientCharacter a (Pi.single j k) = k * a j := by
  classical
  simp [coefficientCharacter, Pi.single_apply]

/-- The same column computation over an arbitrary commutative ring. -/
theorem coefficientCharacter_bidiagonal (t : R) (n : ℕ) (a : Fin (n + 1) → R)
    (x : Fin (n + 1) → R) :
    coefficientCharacter a (bidiagonal t n x) =
      (∑ i : Fin n, x i.castSucc * (t * a i.castSucc + a i.succ)) +
        x (Fin.last n) * (t * a (Fin.last n)) := by
  change (∑ i, (t * x i + lowerShift n x i) * a i) = _
  simp only [add_mul, Finset.sum_add_distrib]
  have hs : (∑ i : Fin (n + 1), lowerShift n x i * a i) =
      ∑ i : Fin n, x i.castSucc * a i.succ := by
    rw [Fin.sum_univ_succ]
    simp [lowerShift]
  rw [hs, Fin.sum_univ_castSucc (fun i : Fin (n + 1) => (t * x i) * a i)]
  simp only [mul_add, Finset.sum_add_distrib]
  simp_rw [mul_assoc, mul_left_comm t]
  ring

/-- The explicit finite character. Under the usual identification of the
    cyclic additive group `ZMod N` with `(1/N)ℤ/ℤ`, this has the values printed
    in the paper's detector construction. -/
def finiteDetector (p s n : ℕ) :
    (Fin (n + 1) → ZMod (p ^ (s * (n + 1)))) →ₗ[ZMod (p ^ (s * (n + 1)))]
      ZMod (p ^ (s * (n + 1))) :=
  coefficientCharacter (fun i => (-(p : ZMod (p ^ (s * (n + 1)))) ^ s) ^ i.val)

/-- Every bidiagonal column is annihilated by the explicit finite character. -/
theorem finiteDetector_annihilates (p s n : ℕ)
    (x : Fin (n + 1) → ZMod (p ^ (s * (n + 1)))) :
    finiteDetector p s n (bidiagonal ((p : ZMod (p ^ (s * (n + 1)))) ^ s) n x) = 0 := by
  rw [finiteDetector, coefficientCharacter_bidiagonal]
  have hrec (i : Fin n) :
      (p : ZMod (p ^ (s * (n + 1)))) ^ s *
          (-(p : ZMod (p ^ (s * (n + 1)))) ^ s) ^ i.castSucc.val +
        (-(p : ZMod (p ^ (s * (n + 1)))) ^ s) ^ i.succ.val = 0 := by
    simp only [Fin.val_castSucc, Fin.val_succ, pow_succ']
    ring
  have hend : (p : ZMod (p ^ (s * (n + 1)))) ^ s *
      (-(p : ZMod (p ^ (s * (n + 1)))) ^ s) ^ n = 0 := by
    rw [neg_pow, ← mul_assoc, mul_comm _ ((-1) ^ n), mul_assoc,
      ← pow_mul, ← pow_add]
    have he : s + s * n = s * (n + 1) := by ring
    rw [he, ← Nat.cast_pow, ZMod.natCast_self, mul_zero]
  simp only [hrec, Fin.val_last, hend, mul_zero, Finset.sum_const_zero, add_zero]


/-- The chosen last-coordinate multiple is detected whenever its fixed
    coefficient is prime to `p` (expressed by the equivalent nondivisibility
    condition). -/
theorem finiteDetector_detects (p : ℕ) (hp : p.Prime) (s : ℕ) (hs : 0 < s)
    (n C : ℕ) (hC : ¬p ∣ C) :
    finiteDetector p s n
      (Pi.single (Fin.last n)
        ((C : ZMod (p ^ (s * (n + 1)))) * (p : ZMod (p ^ (s * (n + 1)))) ^ (s - 1))) ≠ 0 := by
  intro hz
  rw [finiteDetector, coefficientCharacter_single] at hz
  have hscalar : (-(p : ℤ) ^ s) ^ n •
      ((C : ZMod (p ^ (s * (n + 1)))) * (p : ZMod (p ^ (s * (n + 1)))) ^ (s - 1)) = 0 := by
    simpa [zsmul_eq_mul, mul_comm] using hz
  have hpos := (neg_pow_zsmul_eq_zero_iff ((p : ℤ) ^ s) n
    ((C : ZMod (p ^ (s * (n + 1)))) * (p : ZMod (p ^ (s * (n + 1)))) ^ (s - 1))).mp hscalar
  have hcast : ((C * p ^ (s - 1 + s * n) : ℕ) : ZMod (p ^ (s * (n + 1)))) = 0 := by
    simpa [zsmul_eq_mul, pow_mul, pow_add, mul_comm, mul_left_comm, mul_assoc] using hpos
  have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp hcast
  have he : s - 1 + s * n + 1 = s * (n + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [← he, pow_succ, Nat.mul_comm (p ^ (s - 1 + s * n)) p] at hdvd
  have hn : 0 < p ^ (s - 1 + s * n) := pow_pos hp.pos _
  exact hC ((Nat.mul_dvd_mul_iff_right hn).mp hdvd)

/-- The explicit finite module separates the last-coordinate vector from
    the bidiagonal image. This is a statement about a finite module; it does
    not assume or assert any unformalized group conjugacy theorem. -/
theorem finiteDetector_separates_image (p : ℕ) (hp : p.Prime) (s : ℕ) (hs : 0 < s)
    (n C : ℕ) (hC : ¬p ∣ C) :
    ¬∃ x : Fin (n + 1) → ZMod (p ^ (s * (n + 1))),
      bidiagonal ((p : ZMod (p ^ (s * (n + 1)))) ^ s) n x =
        Pi.single (Fin.last n)
          ((C : ZMod (p ^ (s * (n + 1)))) * (p : ZMod (p ^ (s * (n + 1)))) ^ (s - 1)) := by
  rintro ⟨x, hx⟩
  apply finiteDetector_detects p hp s hs n C hC
  rw [← hx]
  exact finiteDetector_annihilates p s n x

end FiniteDetector

end NilpotentConjugacy
