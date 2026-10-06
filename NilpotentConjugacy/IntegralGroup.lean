import NilpotentConjugacy.QuotientModule
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Finiteness

/-!
# Concrete integral exponential matrices

This module constructs the manuscript's integral exponential generators and
an actual semidirect product acting on the integer lattice. `IntegralGroupAction`
proves the representation law, and `GroupProperties` identifies the generated
acting subgroup with `W ⋊ ℤ` for m ≥ 3. `GroupClass` and `GroupSeries` prove the
exact nilpotency class and construct its series of infinite cyclic quotients.
-/

namespace NilpotentConjugacy
open scoped BigOperators

/-- Entries vanish below the indicated minimum lower-diagonal gap. -/
def LowerGap {R : Type*} [Zero R] {m : ℕ}
    (d : ℕ) (A : Matrix (Fin m) (Fin m) R) : Prop :=
  ∀ i j, i.val < j.val + d → A i j = 0

section LowerGap
variable {R : Type*} [CommRing R] {m : ℕ}
variable {A B : Matrix (Fin m) (Fin m) R} {d e : ℕ}

theorem lowerGap_one : LowerGap 0 (1 : Matrix (Fin m) (Fin m) R) := by
  intro i j h
  have hij : i ≠ j := by intro he; subst j; omega
  simp [hij]

theorem lowerGap_mul (hA : LowerGap d A) (hB : LowerGap e B) :
    LowerGap (d + e) (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases h : i.val < k.val + d
  · rw [hA i k h, zero_mul]
  · rw [hB k j (by omega), mul_zero]

theorem lowerGap_pow (hA : LowerGap 1 A) (n : ℕ) : LowerGap n (A ^ n) := by
  induction n with
  | zero => simpa using (lowerGap_one (R := R) (m := m))
  | succ n ih => simpa [pow_succ] using lowerGap_mul ih hA

theorem lowerGap_nilpotent (hA : LowerGap 1 A) : A ^ m = 0 := by
  ext i j
  exact lowerGap_pow hA m i j (by omega)

theorem lowerGap_shiftJ : LowerGap 1 (shiftJ m : Matrix (Fin m) (Fin m) R) := by
  intro i j hij
  simp [shiftJ, shiftBand, show i.val ≠ j.val + 1 by omega]

theorem lowerGap_shiftY : LowerGap 1 (shiftY m : Matrix (Fin m) (Fin m) R) := by
  intro i j hij
  simp [shiftY, shiftBand, show i.val ≠ j.val + 1 by omega]

theorem shiftJ_nilpotent : (shiftJ m : Matrix (Fin m) (Fin m) R) ^ m = 0 :=
  lowerGap_nilpotent lowerGap_shiftJ

theorem shiftY_nilpotent : (shiftY m : Matrix (Fin m) (Fin m) R) ^ m = 0 :=
  lowerGap_nilpotent lowerGap_shiftY

end LowerGap

/-- Integer matrices mapped entrywise to rational matrices. -/
def ratMatrix (m : ℕ) : Matrix (Fin m) (Fin m) ℤ →+* Matrix (Fin m) (Fin m) ℚ :=
  (Int.castRingHom ℚ).mapMatrix

theorem ratMatrix_injective (m : ℕ) : Function.Injective (ratMatrix m) := by
  intro A B h
  ext i j
  exact Int.cast_injective (congrArg (fun C => C i j) h)

@[simp] theorem ratMatrix_apply (m : ℕ) (A : Matrix (Fin m) (Fin m) ℤ) (i j : Fin m) :
    ratMatrix m A i j = (A i j : ℚ) := rfl

@[simp] theorem ratMatrix_smul (m : ℕ) (a : ℤ) (A : Matrix (Fin m) (Fin m) ℤ) :
    ratMatrix m (a • A) = (a : ℚ) • ratMatrix m A := by
  ext i j
  change ((a * A i j : ℤ) : ℚ) = (a : ℚ) * (A i j : ℚ)
  exact Int.cast_mul _ _

@[simp] theorem ratMatrix_shiftJ (m : ℕ) : ratMatrix m (shiftJ m) = shiftJ m := by
  ext i j
  simp [shiftJ, shiftBand]

@[simp] theorem ratMatrix_shiftY (m : ℕ) : ratMatrix m (shiftY m) = shiftY m := by
  ext i j
  simp [shiftY, shiftBand]

/-- The factorial-cleared finite exponential `exp(m! A)` over the integers. -/
def integralExponential (m : ℕ) (A : Matrix (Fin m) (Fin m) ℤ) :
    Matrix (Fin m) (Fin m) ℤ :=
  ∑ k ∈ Finset.range m, ((m.factorial ^ k / k.factorial : ℕ) : ℤ) • A ^ k

theorem factorial_dvd_factorial_pow {m k : ℕ} (hk : k ≤ m) :
    k.factorial ∣ m.factorial ^ k := by
  by_cases h : k = 0
  · subst k; simp
  · exact dvd_trans (Nat.factorial_dvd_factorial hk) (dvd_pow_self _ h)

theorem ratMatrix_integralExponential (m : ℕ) (A : Matrix (Fin m) (Fin m) ℤ)
    (hA : LowerGap 1 A) :
    ratMatrix m (integralExponential m A) =
      IsNilpotent.exp ((m.factorial : ℚ) • ratMatrix m A) := by
  have hnil : ((m.factorial : ℚ) • ratMatrix m A) ^ m = 0 := by
    rw [smul_pow, ← map_pow, lowerGap_nilpotent hA, map_zero, smul_zero]
  rw [IsNilpotent.exp_eq_sum hnil, integralExponential, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [ratMatrix_smul, map_pow, smul_pow, smul_smul]
  congr 1
  have hdiv := factorial_dvd_factorial_pow (Nat.le_of_lt (Finset.mem_range.mp hk))
  rw [Int.cast_natCast, Nat.cast_div hdiv (by exact_mod_cast Nat.factorial_ne_zero k), Nat.cast_pow]
  ring

/-- Integral formula for `exp(aY)`, valid for positive and negative `a`. -/
def weightedExponential (m : ℕ) (a : ℤ) : Matrix (Fin m) (Fin m) ℤ :=
  ∑ k ∈ Finset.range m, shiftBand m k (fun i => a ^ k * ((i + k).choose k : ℤ))

theorem ratMatrix_weightedExponential (m : ℕ) (a : ℤ) :
    ratMatrix m (weightedExponential m a) =
      IsNilpotent.exp ((a : ℚ) • (shiftY m : Matrix (Fin m) (Fin m) ℚ)) := by
  have hnil : ((a : ℚ) • (shiftY m : Matrix (Fin m) (Fin m) ℚ)) ^ m = 0 := by
    rw [smul_pow, shiftY_nilpotent, smul_zero]
  rw [IsNilpotent.exp_eq_sum hnil, weightedExponential, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [smul_pow, shiftY_pow, smul_smul]
  ext i j
  simp only [ratMatrix_apply, shiftBand, Matrix.smul_apply, smul_eq_mul]
  split_ifs
  · rw [← Nat.cast_add_one, ascPochhammer_nat_eq_natCast_ascFactorial,
      Nat.ascFactorial_eq_factorial_mul_choose]
    push_cast
    have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    field_simp
  · simp

theorem lowerGap_neg {m : ℕ} {A : Matrix (Fin m) (Fin m) ℤ}
    (hA : LowerGap 1 A) : LowerGap 1 (-A) := by
  intro i j hij
  simp [hA i j hij]

/-- The factorial-cleared exponential as an invertible integer matrix. -/
noncomputable def integralExponentialUnit (m : ℕ) (A : Matrix (Fin m) (Fin m) ℤ)
    (hA : LowerGap 1 A) : (Matrix (Fin m) (Fin m) ℤ)ˣ where
  val := integralExponential m A
  inv := integralExponential m (-A)
  val_inv := by
    apply ratMatrix_injective m
    rw [map_mul, map_one, ratMatrix_integralExponential m A hA,
      ratMatrix_integralExponential m (-A) (lowerGap_neg hA), map_neg, smul_neg]
    apply IsNilpotent.exp_mul_exp_neg_self
    refine ⟨m, ?_⟩
    rw [smul_pow, ← map_pow, lowerGap_nilpotent hA, map_zero, smul_zero]
  inv_val := by
    apply ratMatrix_injective m
    rw [map_mul, map_one, ratMatrix_integralExponential m A hA,
      ratMatrix_integralExponential m (-A) (lowerGap_neg hA), map_neg, smul_neg]
    apply IsNilpotent.exp_neg_mul_exp_self
    refine ⟨m, ?_⟩
    rw [smul_pow, ← map_pow, lowerGap_nilpotent hA, map_zero, smul_zero]

/-- `exp(aY)` is an integer unit; its inverse is exactly `exp(-aY)`. -/
noncomputable def weightedExponentialUnit (m : ℕ) (a : ℤ) :
    (Matrix (Fin m) (Fin m) ℤ)ˣ where
  val := weightedExponential m a
  inv := weightedExponential m (-a)
  val_inv := by
    apply ratMatrix_injective m
    rw [map_mul, map_one, ratMatrix_weightedExponential, ratMatrix_weightedExponential,
      Int.cast_neg, neg_smul]
    apply IsNilpotent.exp_mul_exp_neg_self
    refine ⟨m, ?_⟩
    rw [smul_pow, shiftY_nilpotent, smul_zero]
  inv_val := by
    apply ratMatrix_injective m
    rw [map_mul, map_one, ratMatrix_weightedExponential, ratMatrix_weightedExponential,
      Int.cast_neg, neg_smul]
    apply IsNilpotent.exp_neg_mul_exp_self
    refine ⟨m, ?_⟩
    rw [smul_pow, shiftY_nilpotent, smul_zero]

@[simp] theorem weightedExponentialUnit_val (m : ℕ) (a : ℤ) :
    (weightedExponentialUnit m a).val = weightedExponential m a := rfl

/-- Exact integral exponential action law for the weighted shift. -/
theorem weightedExponential_add (m : ℕ) (a b : ℤ) :
    weightedExponential m (a + b) =
      weightedExponential m a * weightedExponential m b := by
  apply ratMatrix_injective m
  rw [map_mul, ratMatrix_weightedExponential, ratMatrix_weightedExponential,
    ratMatrix_weightedExponential, Int.cast_add, add_smul]
  apply IsNilpotent.exp_add_of_commute
  · exact (Commute.refl _).smul_left _ |>.smul_right _
  · exact ⟨m, by rw [smul_pow, shiftY_nilpotent, smul_zero]⟩
  · exact ⟨m, by rw [smul_pow, shiftY_nilpotent, smul_zero]⟩

@[simp] theorem weightedExponential_zero (m : ℕ) : weightedExponential m 0 = 1 := by
  apply ratMatrix_injective m
  simp [ratMatrix_weightedExponential]

/-- Each integer invertible matrix acts faithfully on the integer lattice. -/
def integerMatrixAction (m : ℕ) :
    (Matrix (Fin m) (Fin m) ℤ)ˣ →* MulAut (Multiplicative (Fin m → ℤ)) where
  toFun U := AddEquiv.toMultiplicative
    { toFun := U.val.mulVec
      invFun := U.inv.mulVec
      left_inv := by intro v; rw [Matrix.mulVec_mulVec, U.inv_val, Matrix.one_mulVec]
      right_inv := by intro v; rw [Matrix.mulVec_mulVec, U.val_inv, Matrix.one_mulVec]
      map_add' := Matrix.mulVec_add U.val }
  map_one' := by ext v i; simp
  map_mul' U V := by ext v i; exact congrFun (Matrix.mulVec_mulVec v.toAdd U.val V.val).symm i

@[simp] theorem integerMatrixAction_apply (m : ℕ)
    (U : (Matrix (Fin m) (Fin m) ℤ)ˣ) (v : Multiplicative (Fin m → ℤ)) :
    (integerMatrixAction m U v).toAdd = U.val.mulVec v.toAdd := rfl

/-- The cyclic action on `m-1` coefficients of the acting lattice. -/
noncomputable def coefficientAction (m : ℕ) :
    Multiplicative ℤ →* MulAut (Multiplicative (Fin (m - 1) → ℤ)) :=
  (integerMatrixAction (m - 1)).comp
    { toFun := fun a => weightedExponentialUnit (m - 1) a.toAdd
      map_one' := by apply Units.ext; exact weightedExponential_zero _
      map_mul' := by intro a b; apply Units.ext; exact weightedExponential_add _ _ _ }

/-- The explicit coefficient semidirect product for the paper's acting group.
Its interpretation as conjugation on the dimension-`m` exponential lattice
is proved in `IntegralGroupAction.lean`. -/
abbrev CoefficientGroup (m : ℕ) :=
  SemidirectProduct (Multiplicative (Fin (m - 1) → ℤ)) (Multiplicative ℤ)
    (coefficientAction m)

/-- The unscaled polynomial whose factorial multiple is an element of `W`. -/
def latticePolynomial (m : ℕ) (c : Fin (m - 1) → ℤ) : Matrix (Fin m) (Fin m) ℤ :=
  ∑ j, c j • shiftJ m ^ (j.val + 1)

theorem lowerGap_latticePolynomial (m : ℕ) (c : Fin (m - 1) → ℤ) :
    LowerGap 1 (latticePolynomial m c) := by
  intro i j hij
  simp only [latticePolynomial, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro k _
  change c k * (shiftJ m ^ (k.val + 1)) i j = 0
  rw [lowerGap_pow lowerGap_shiftJ (k.val + 1) i j (by omega), mul_zero]

/-- The actual `exp(P)` for every coefficient vector `P ∈ W`. -/
noncomputable def latticeExponential (m : ℕ) (c : Fin (m - 1) → ℤ) :
    (Matrix (Fin m) (Fin m) ℤ)ˣ :=
  integralExponentialUnit m (latticePolynomial m c) (lowerGap_latticePolynomial m c)

/-- A finite list: the stable letter and all `exp(m! J^j)`, `1 ≤ j < m`. -/
noncomputable def actingMatrixGenerator (m : ℕ) : Fin m → (Matrix (Fin m) (Fin m) ℤ)ˣ :=
  fun j => if h : j.val = 0 then weightedExponentialUnit m 1
    else integralExponentialUnit m (shiftJ m ^ j.val)
      (fun i k hik => lowerGap_pow lowerGap_shiftJ j.val i k (by omega))

/-- The concrete subgroup of integral units generated by the manuscript's
acting generators. `coefficientGeneratedEquiv` in `GroupProperties` identifies it
with `CoefficientGroup m` for m ≥ 3. -/
def GeneratedActingGroup (m : ℕ) : Subgroup (Matrix (Fin m) (Fin m) ℤ)ˣ :=
  Subgroup.closure (Set.range (actingMatrixGenerator m))

instance generatedActingGroup_fg (m : ℕ) : Group.FG (GeneratedActingGroup m) := by
  unfold GeneratedActingGroup
  exact Group.closure_finite_fg _

/-- The genuine integral action of the generated acting subgroup. -/
def generatedAction (m : ℕ) : GeneratedActingGroup m →*
    MulAut (Multiplicative (Fin m → ℤ)) :=
  (integerMatrixAction m).comp (GeneratedActingGroup m).subtype

/-- An actual integral semidirect-product group, using the concrete generators.
`manuscriptGeneratedEquiv` in `GroupProperties` identifies this with the paper's
`G(m)` for m ≥ 3. -/
abbrev IntegralGeneratedGroup (m : ℕ) :=
  SemidirectProduct (Multiplicative (Fin m → ℤ)) (GeneratedActingGroup m)
    (generatedAction m)

/-- The standard normal integer lattice inclusion. -/
def integralVector (m : ℕ) : Multiplicative (Fin m → ℤ) →* IntegralGeneratedGroup m :=
  SemidirectProduct.inl

/-- The standard acting subgroup inclusion. -/
def integralActor (m : ℕ) : GeneratedActingGroup m →* IntegralGeneratedGroup m :=
  SemidirectProduct.inr

@[simp] theorem integralVector_injective (m : ℕ) : Function.Injective (integralVector m) :=
  SemidirectProduct.inl_injective

theorem integral_action_conjugation (m : ℕ) (U : GeneratedActingGroup m)
    (v : Multiplicative (Fin m → ℤ)) :
    integralActor m U * integralVector m v * (integralActor m U)⁻¹ =
      integralVector m (Multiplicative.ofAdd (U.val.val.mulVec v.toAdd)) := by
  have ha : generatedAction m U v =
      Multiplicative.ofAdd (U.val.val.mulVec v.toAdd) := by
    exact congrArg Multiplicative.ofAdd (integerMatrixAction_apply m U.val v)
  rw [← ha]
  simpa only [integralActor, integralVector, map_inv] using
    (SemidirectProduct.inl_aut (φ := generatedAction m) U v).symm

section ScalarExtension
variable (R : Type*) [CommRing R]

/-- Scalar extension of an integral matrix to any commutative ring. -/
def integerMatrixMap (m : ℕ) :
    Matrix (Fin m) (Fin m) ℤ →+* Matrix (Fin m) (Fin m) R :=
  (Int.castRingHom R).mapMatrix

@[simp] theorem integerMatrixMap_apply (m : ℕ)
    (A : Matrix (Fin m) (Fin m) ℤ) (i j : Fin m) :
    integerMatrixMap R m A i j = (A i j : R) := rfl

@[simp] theorem integerMatrixMap_smul (m : ℕ) (a : ℤ)
    (A : Matrix (Fin m) (Fin m) ℤ) :
    integerMatrixMap R m (a • A) = (a : R) • integerMatrixMap R m A := by
  ext i j
  change ((a * A i j : ℤ) : R) = (a : R) * (A i j : R)
  exact Int.cast_mul _ _

@[simp] theorem integerMatrixMap_shiftJ (m : ℕ) :
    integerMatrixMap R m (shiftJ m) = shiftJ m := by
  ext i j
  simp [shiftJ, shiftBand]

@[simp] theorem integerMatrixMap_shiftY (m : ℕ) :
    integerMatrixMap R m (shiftY m) = shiftY m := by
  ext i j
  simp [shiftY, shiftBand]

/-- The exact finite-exponential identity after any scalar extension in which
all relevant factorials are units. This includes the paper's localization. -/
theorem integerMatrixMap_integralExponential (m : ℕ)
    (A : Matrix (Fin m) (Fin m) ℤ)
    (hu : ∀ k < m, IsUnit (k.factorial : R)) :
    integerMatrixMap R m (integralExponential m A) =
      ∑ k ∈ Finset.range m, Ring.inverse (k.factorial : R) •
        (((m.factorial : R) • integerMatrixMap R m A) ^ k) := by
  rw [integralExponential, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integerMatrixMap_smul, map_pow, smul_pow, smul_smul]
  congr 1
  rw [Int.cast_natCast]
  symm
  apply (Ring.inverse_mul_eq_iff_eq_mul _ _ _ (hu k (Finset.mem_range.mp hk))).mpr
  have hd := Nat.mul_div_cancel' (factorial_dvd_factorial_pow
    (Nat.le_of_lt (Finset.mem_range.mp hk)))
  simpa only [Nat.cast_mul, Nat.cast_pow] using
    congrArg (fun n : ℕ => (n : R)) hd.symm

/-- The exact finite-exponential identity for the weighted action over a ring
where factorial denominators can be inverted. -/
theorem integerMatrixMap_weightedExponential (m : ℕ) (a : ℤ)
    (hu : ∀ k < m, IsUnit (k.factorial : R)) :
    integerMatrixMap R m (weightedExponential m a) =
      ∑ k ∈ Finset.range m, Ring.inverse (k.factorial : R) •
        (((a : R) • (shiftY m : Matrix (Fin m) (Fin m) R)) ^ k) := by
  rw [weightedExponential, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [smul_pow, shiftY_pow, smul_smul]
  ext i j
  simp only [integerMatrixMap_apply, shiftBand, Matrix.smul_apply, smul_eq_mul]
  split_ifs
  · rw [← Nat.cast_add_one, ascPochhammer_nat_eq_natCast_ascFactorial,
      Nat.ascFactorial_eq_factorial_mul_choose]
    push_cast
    calc
      (a : R) ^ k * ((j.val + k).choose k : R) =
          (Ring.inverse (k.factorial : R) * (k.factorial : R)) *
            ((a : R) ^ k * ((j.val + k).choose k : R)) := by
              rw [Ring.inverse_mul_cancel _ (hu k (Finset.mem_range.mp hk)), one_mul]
      _ = _ := by ring
  · simp

end ScalarExtension

/-- Finite generation passes through the actual semidirect-product constructor. -/
theorem semidirectProduct_finitelyGenerated {N H : Type*} [Group N] [Group H]
    [Group.FG N] [Group.FG H] (φ : H →* MulAut N) :
    Group.FG (SemidirectProduct N H φ) := by
  let iN : N →* SemidirectProduct N H φ := SemidirectProduct.inl
  let iH : H →* SemidirectProduct N H φ := SemidirectProduct.inr
  have hN : iN.range.FG := (Group.fg_iff_subgroup_fg _).mp inferInstance
  have hH : iH.range.FG := (Group.fg_iff_subgroup_fg _).mp inferInstance
  have htop : iN.range ⊔ iH.range = ⊤ := by
    apply top_unique
    intro x _
    rw [← SemidirectProduct.inl_left_mul_inr_right x]
    exact Subgroup.mul_mem _
      ((show iN.range ≤ iN.range ⊔ iH.range from le_sup_left) (show SemidirectProduct.inl x.left ∈ iN.range from ⟨x.left, rfl⟩))
      ((show iH.range ≤ iN.range ⊔ iH.range from le_sup_right) (show SemidirectProduct.inr x.right ∈ iH.range from ⟨x.right, rfl⟩))
  exact ⟨htop ▸ hN.sup hH⟩

instance coefficientGroup_fg (m : ℕ) : Group.FG (CoefficientGroup m) := by
  apply semidirectProduct_finitelyGenerated

instance integralGeneratedGroup_fg (m : ℕ) : Group.FG (IntegralGeneratedGroup m) := by
  apply semidirectProduct_finitelyGenerated

@[simp] theorem latticePolynomial_zero (m : ℕ) : latticePolynomial m 0 = 0 := by
  simp [latticePolynomial]

theorem latticePolynomial_add (m : ℕ) (c d : Fin (m - 1) → ℤ) :
    latticePolynomial m (c + d) = latticePolynomial m c + latticePolynomial m d := by
  simp [latticePolynomial, add_smul, Finset.sum_add_distrib]

/-- The unscaled coefficient lattice is mapped additively to its matrices. -/
def latticePolynomialHom (m : ℕ) :
    (Fin (m - 1) → ℤ) →+ Matrix (Fin m) (Fin m) ℤ where
  toFun := latticePolynomial m
  map_zero' := latticePolynomial_zero m
  map_add' := latticePolynomial_add m

theorem latticePolynomial_commute (m : ℕ) (c d : Fin (m - 1) → ℤ) :
    Commute (latticePolynomial m c) (latticePolynomial m d) := by
  unfold latticePolynomial
  apply Commute.sum_left
  intro i _
  apply Commute.sum_right
  intro j _
  exact ((Commute.refl (shiftJ m : Matrix (Fin m) (Fin m) ℤ)).pow_pow _ _).smul_left _
    |>.smul_right _

/-- The exponential is additive-to-multiplicative on the actual coefficient lattice. -/
theorem latticeExponential_add (m : ℕ) (c d : Fin (m - 1) → ℤ) :
    latticeExponential m (c + d) = latticeExponential m c * latticeExponential m d := by
  apply Units.ext
  apply ratMatrix_injective m
  change ratMatrix m (integralExponential m (latticePolynomial m (c + d))) =
    ratMatrix m (integralExponential m (latticePolynomial m c) *
      integralExponential m (latticePolynomial m d))
  rw [map_mul, ratMatrix_integralExponential _ _ (lowerGap_latticePolynomial m (c + d)),
    ratMatrix_integralExponential _ _ (lowerGap_latticePolynomial m c),
    ratMatrix_integralExponential _ _ (lowerGap_latticePolynomial m d),
    latticePolynomial_add, map_add, smul_add]
  apply IsNilpotent.exp_add_of_commute
  · exact ((latticePolynomial_commute m c d).map (ratMatrix m)).smul_left _ |>.smul_right _
  · refine ⟨m, ?_⟩
    rw [smul_pow, ← map_pow, lowerGap_nilpotent (lowerGap_latticePolynomial m c),
      map_zero, smul_zero]
  · refine ⟨m, ?_⟩
    rw [smul_pow, ← map_pow, lowerGap_nilpotent (lowerGap_latticePolynomial m d),
      map_zero, smul_zero]

@[simp] theorem latticeExponential_zero (m : ℕ) : latticeExponential m 0 = 1 := by
  have h := latticeExponential_add m 0 0
  simpa using (mul_left_cancel (show latticeExponential m 0 * latticeExponential m 0 =
    latticeExponential m 0 * 1 by simpa using h.symm))

/-- The whole lattice `W` has an actual homomorphism into integral matrix units. -/
noncomputable def latticeExponentialHom (m : ℕ) :
    Multiplicative (Fin (m - 1) → ℤ) →* (Matrix (Fin m) (Fin m) ℤ)ˣ where
  toFun c := latticeExponential m c.toAdd
  map_one' := latticeExponential_zero m
  map_mul' c d := latticeExponential_add m c.toAdd d.toAdd

/-- The manuscript's exact matrix commutator identity over any commutative ring. -/
theorem shiftY_commutator_shiftJ_pow {R : Type*} [CommRing R] (m j : ℕ) :
    (shiftY m : Matrix (Fin m) (Fin m) R) * shiftJ m ^ j -
      shiftJ m ^ j * shiftY m = (j : R) • shiftJ m ^ (j + 1) := by
  rw [shiftJ_pow, shiftY, shiftBand_mul, shiftBand_mul, shiftJ_pow]
  ext i k
  simp only [shiftBand, Matrix.sub_apply, Matrix.smul_apply, Nat.add_comm 1 j]
  split_ifs <;> push_cast <;> ring

/-- Every factorial-cleared exponential is lower unitriangular. -/
theorem lowerGap_integralExponential_sub_one (m : ℕ)
    (A : Matrix (Fin m) (Fin m) ℤ) (hA : LowerGap 1 A) :
    LowerGap 1 (integralExponential m A - 1) := by
  intro i j hij
  have hm : 0 < m := by omega
  change integralExponential m A i j - (1 : Matrix (Fin m) (Fin m) ℤ) i j = 0
  apply sub_eq_zero.mpr
  simp only [integralExponential, Matrix.sum_apply]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    change ((m.factorial ^ k / k.factorial : ℕ) : ℤ) * (A ^ k) i j = 0
    rw [lowerGap_pow hA k i j (by omega), mul_zero]
  · simp [hm]

/-- The weighted exponentials are lower unitriangular for every integer parameter. -/
theorem lowerGap_weightedExponential_sub_one (m : ℕ) (a : ℤ) :
    LowerGap 1 (weightedExponential m a - 1) := by
  intro i j hij
  have hm : 0 < m := by omega
  change weightedExponential m a i j - (1 : Matrix (Fin m) (Fin m) ℤ) i j = 0
  apply sub_eq_zero.mpr
  simp only [weightedExponential, Matrix.sum_apply]
  rw [Finset.sum_eq_single 0]
  · simp [shiftBand, Matrix.one_apply, Fin.ext_iff]
  · intro k _ hk
    have hne : i.val ≠ j.val + k := by omega
    simp [shiftBand, hne]
  · simp [hm]

theorem lowerGap_actingMatrixGenerator_sub_one (m : ℕ) (j : Fin m) :
    LowerGap 1 ((actingMatrixGenerator m j).val - 1) := by
  unfold actingMatrixGenerator
  split
  · exact lowerGap_weightedExponential_sub_one m 1
  · apply lowerGap_integralExponential_sub_one
    intro i k hik
    exact lowerGap_pow lowerGap_shiftJ j.val i k (by omega)

/-- Reading the first column recovers every unscaled lattice coefficient. -/
theorem latticePolynomial_first_column (m : ℕ) (c : Fin (m - 1) → ℤ)
    (j : Fin (m - 1)) :
    latticePolynomial m c ⟨j.val + 1, by have := j.isLt; omega⟩ ⟨0, by have := j.isLt; omega⟩ = c j := by
  simp only [latticePolynomial, Matrix.sum_apply, Matrix.smul_apply, shiftJ_pow, shiftBand]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    have h : j.val ≠ k.val := by
      intro he
      apply hkj
      apply Fin.ext
      omega
    simp [h]
  · simp

/-- Thus this coefficient lattice has exactly `m-1` independent integer coordinates. -/
theorem latticePolynomial_injective (m : ℕ) : Function.Injective (latticePolynomial m) := by
  intro c d h
  funext j
  have hh := congrArg (fun A : Matrix (Fin m) (Fin m) ℤ =>
    A ⟨j.val + 1, by have := j.isLt; omega⟩ ⟨0, by have := j.isLt; omega⟩) h
  simpa only [latticePolynomial_first_column] using hh

theorem latticePolynomial_single (m : ℕ) (j : Fin (m - 1)) (a : ℤ) :
    latticePolynomial m (Pi.single j a) = a • shiftJ m ^ (j.val + 1) := by
  classical
  simp [latticePolynomial, Pi.single_apply]

theorem latticeExponential_zsmul (m : ℕ) (a : ℤ) (c : Fin (m - 1) → ℤ) :
    latticeExponential m (a • c) = latticeExponential m c ^ a := by
  exact map_zpow (latticeExponentialHom m) (Multiplicative.ofAdd c) a

/-- Every `exp(P)` in the paper's full lattice occurs in the concrete acting subgroup. -/
theorem latticeExponential_mem_generatedActingGroup (m : ℕ) (c : Fin (m - 1) → ℤ) :
    latticeExponential m c ∈ GeneratedActingGroup m := by
  have hc : c = ∑ j : Fin (m - 1), c j • Pi.single j (1 : ℤ) := by
    funext i
    simp [Pi.single_apply]
  have hsingle (j : Fin (m - 1)) :
      latticeExponential m (c j • Pi.single j (1 : ℤ)) ∈ GeneratedActingGroup m := by
    rw [latticeExponential_zsmul]
    apply Subgroup.zpow_mem
    have hg : actingMatrixGenerator m ⟨j.val + 1, by have := j.isLt; omega⟩ ∈
      GeneratedActingGroup m := Subgroup.subset_closure ⟨_, rfl⟩
    convert hg using 1
    apply Units.ext
    change integralExponential m (latticePolynomial m (Pi.single j 1)) = _
    rw [latticePolynomial_single, one_smul]
    simp [actingMatrixGenerator, integralExponentialUnit]
  have hsum (s : Finset (Fin (m - 1))) :
      latticeExponential m (∑ j ∈ s, c j • Pi.single j (1 : ℤ)) ∈
        GeneratedActingGroup m := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, latticeExponential_add]
      exact Subgroup.mul_mem _ (hsingle a) ih
  rw [hc]
  exact hsum Finset.univ

/-- The weighted exponentials form an explicit homomorphism from the integers. -/
noncomputable def weightedExponentialHom (m : ℕ) :
    Multiplicative ℤ →* (Matrix (Fin m) (Fin m) ℤ)ˣ where
  toFun a := weightedExponentialUnit m a.toAdd
  map_one' := by apply Units.ext; exact weightedExponential_zero m
  map_mul' a b := by apply Units.ext; exact weightedExponential_add m a.toAdd b.toAdd

theorem weightedExponentialUnit_zsmul (m : ℕ) (a : ℤ) :
    weightedExponentialUnit m a = weightedExponentialUnit m 1 ^ a := by
  have h := map_zpow (weightedExponentialHom m) (Multiplicative.ofAdd 1) a
  change weightedExponentialUnit m (a • (1 : ℤ)) = weightedExponentialUnit m 1 ^ a at h
  simpa only [zsmul_eq_mul, mul_one, Int.cast_id] using h

/-- Every `exp(aY)` belongs to the same concrete acting subgroup. -/
theorem weightedExponentialUnit_mem_generatedActingGroup (m : ℕ) (hm : 0 < m) (a : ℤ) :
    weightedExponentialUnit m a ∈ GeneratedActingGroup m := by
  rw [weightedExponentialUnit_zsmul]
  apply Subgroup.zpow_mem
  have hg : actingMatrixGenerator m ⟨0, hm⟩ ∈ GeneratedActingGroup m :=
    Subgroup.subset_closure ⟨_, rfl⟩
  simpa [actingMatrixGenerator] using hg

/-- The manuscript's formula `rho(P,a)=exp(P)exp(aY)` as an actual integral unit.
The homomorphism law for this formula is proved in `IntegralGroupAction.lean`. -/
noncomputable def manuscriptRho (m : ℕ) (h : CoefficientGroup m) :
    (Matrix (Fin m) (Fin m) ℤ)ˣ :=
  latticeExponential m h.left.toAdd * weightedExponentialUnit m h.right.toAdd

theorem manuscriptRho_mem_generatedActingGroup (m : ℕ) (hm : 0 < m)
    (h : CoefficientGroup m) : manuscriptRho m h ∈ GeneratedActingGroup m :=
  Subgroup.mul_mem _ (latticeExponential_mem_generatedActingGroup m _)
    (weightedExponentialUnit_mem_generatedActingGroup m hm _)

section CoefficientDerivation
variable (R : Type*) [CommRing R]

/-- Polynomial coordinates over an arbitrary ring, with no constant term. -/
def shiftPolynomial (m : ℕ) (c : Fin (m - 1) → R) : Matrix (Fin m) (Fin m) R :=
  ∑ j, c j • shiftJ m ^ (j.val + 1)

def shiftPolynomialLinear (m : ℕ) :
    (Fin (m - 1) → R) →ₗ[R] Matrix (Fin m) (Fin m) R where
  toFun := shiftPolynomial R m
  map_add' c d := by simp [shiftPolynomial, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [shiftPolynomial, Finset.smul_sum, smul_smul]

@[simp] theorem shiftPolynomial_single (m : ℕ) (j : Fin (m - 1)) (a : R) :
    shiftPolynomial R m (Pi.single j a) = a • shiftJ m ^ (j.val + 1) := by
  classical
  simp [shiftPolynomial, Pi.single_apply]

/-- The infinitesimal conjugation operator induced by the concrete weighted shift. -/
def shiftAdjoint (m : ℕ) : Module.End R (Matrix (Fin m) (Fin m) R) :=
  LinearMap.mulLeft R (shiftY m) - LinearMap.mulRight R (shiftY m)

theorem shiftY_mulVec_single (n : ℕ) (j : Fin n) (a : R) :
    (shiftY n : Matrix (Fin n) (Fin n) R).mulVec (Pi.single j a) =
      if h : j.val + 1 < n then
        Pi.single (⟨j.val + 1, h⟩ : Fin n) (((j.val + 1 : ℕ) : R) * a)
      else 0 := by
  classical
  rw [Matrix.mulVec_single]
  ext i
  by_cases h : j.val + 1 < n
  · simp [h, shiftY, shiftBand, Pi.single_apply, Fin.ext_iff, add_mul]
  · have hn : i.val ≠ j.val + 1 := by omega
    simp [h, shiftY, shiftBand, hn]

/-- The matrix commutator on `W` is precisely the smaller weighted shift on
its coefficients. This is the exact infinitesimal form of the required
semidirect-product conjugation correspondence. -/
theorem shiftAdjoint_intertwines (m : ℕ) :
    (shiftAdjoint R m).comp (shiftPolynomialLinear R m) =
      (shiftPolynomialLinear R m).comp (shiftY (m - 1)).mulVecLin := by
  apply LinearMap.pi_ext
  intro j a
  change (shiftY m * shiftPolynomial R m (Pi.single j a) -
      shiftPolynomial R m (Pi.single j a) * shiftY m) =
    shiftPolynomial R m ((shiftY (m - 1)).mulVec (Pi.single j a))
  rw [shiftPolynomial_single, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub,
    shiftY_commutator_shiftJ_pow, smul_smul, shiftY_mulVec_single]
  split_ifs with h
  · rw [shiftPolynomial_single]
    congr 1
    ring
  · have hj : j.val + 1 + 1 = m := by have := j.isLt; omega
    rw [hj, shiftJ_nilpotent, smul_zero]
    simp [shiftPolynomial]

end CoefficientDerivation

/-- The concrete adjoint operator is nilpotent because its commuting left and
right multiplication components are nilpotent. -/
theorem shiftAdjoint_isNilpotent (m : ℕ) : IsNilpotent (shiftAdjoint ℚ m) := by
  have hL : IsNilpotent (LinearMap.mulLeft ℚ (shiftY m : Matrix (Fin m) (Fin m) ℚ)) := by
    refine ⟨m, ?_⟩
    rw [LinearMap.pow_mulLeft, shiftY_nilpotent, LinearMap.mulLeft_zero_eq_zero]
  have hR : IsNilpotent (LinearMap.mulRight ℚ (shiftY m : Matrix (Fin m) (Fin m) ℚ)) := by
    refine ⟨m, ?_⟩
    rw [LinearMap.pow_mulRight, shiftY_nilpotent, LinearMap.mulRight_zero_eq_zero]
  exact (LinearMap.commute_mulLeft_right _ _).isNilpotent_sub hL hR

/-- Finite polynomial exponentiation of `ad Y` is exactly conjugation by
`exp Y`; this identity is proved for the concrete rational matrix algebra. -/
theorem shiftAdjoint_exp_apply (m : ℕ) (A : Matrix (Fin m) (Fin m) ℚ) :
    IsNilpotent.exp (shiftAdjoint ℚ m) A =
      IsNilpotent.exp (shiftY m) * A * IsNilpotent.exp (-shiftY m) := by
  let Y : Matrix (Fin m) (Fin m) ℚ := shiftY m
  let L := LinearMap.mulLeft ℚ Y
  let R := LinearMap.mulRight ℚ (-Y)
  have hY : Y ^ m = 0 := shiftY_nilpotent
  have hneg : (-Y) ^ m = 0 := by rw [neg_pow, hY, mul_zero]
  have hL : L ^ m = 0 := by
    dsimp [L]
    rw [LinearMap.pow_mulLeft, hY, LinearMap.mulLeft_zero_eq_zero]
  have hR : R ^ m = 0 := by
    dsimp [R]
    rw [LinearMap.pow_mulRight, hneg, LinearMap.mulRight_zero_eq_zero]
  have had : shiftAdjoint ℚ m = L + R := by
    ext B i j
    simp [shiftAdjoint, L, R, Y, sub_eq_add_neg]
  have hEL : IsNilpotent.exp L = LinearMap.mulLeft ℚ (IsNilpotent.exp Y) := by
    rw [IsNilpotent.exp_eq_sum hL, IsNilpotent.exp_eq_sum hY]
    ext B i j
    simp [L, LinearMap.pow_mulLeft, Finset.sum_mul]
  have hER : IsNilpotent.exp R = LinearMap.mulRight ℚ (IsNilpotent.exp (-Y)) := by
    rw [IsNilpotent.exp_eq_sum hR, IsNilpotent.exp_eq_sum hneg]
    ext B i j
    simp [R, LinearMap.pow_mulRight, Finset.mul_sum]
  rw [had, IsNilpotent.exp_add_of_commute (LinearMap.commute_mulLeft_right Y (-Y))
    ⟨m, hL⟩ ⟨m, hR⟩, hEL, hER]
  change IsNilpotent.exp Y * (A * IsNilpotent.exp (-Y)) = _
  exact (mul_assoc _ _ _).symm

/-- The coefficient action has the same exponential as the adjoint action on
its polynomial matrices, proved by exponentiating the exact intertwiner. -/
theorem shiftAdjoint_exp_intertwines (m : ℕ) :
    (IsNilpotent.exp (shiftAdjoint ℚ m)).comp (shiftPolynomialLinear ℚ m) =
      (shiftPolynomialLinear ℚ m).comp
        (IsNilpotent.exp ((shiftY (m - 1) : Matrix (Fin (m - 1)) (Fin (m - 1)) ℚ).mulVecLin)) := by
  apply Module.End.commute_exp_left_of_commute
  · exact (show IsNilpotent (shiftY (m - 1) : Matrix (Fin (m - 1)) (Fin (m - 1)) ℚ)
      from ⟨m - 1, shiftY_nilpotent⟩).map Matrix.toLinAlgEquiv'
  · exact shiftAdjoint_isNilpotent m
  · exact shiftAdjoint_intertwines ℚ m

/-- The rational conjugation formula on the full polynomial coefficient space. -/
theorem rational_weighted_conjugation (m : ℕ) (c : Fin (m - 1) → ℚ) :
    IsNilpotent.exp (shiftY m) * shiftPolynomial ℚ m c *
      IsNilpotent.exp (-shiftY m) =
    shiftPolynomial ℚ m ((IsNilpotent.exp
      (shiftY (m - 1) : Matrix (Fin (m - 1)) (Fin (m - 1)) ℚ)).mulVec c) := by
  have h := LinearMap.congr_fun (shiftAdjoint_exp_intertwines m) c
  simp only [LinearMap.comp_apply] at h
  rw [shiftAdjoint_exp_apply] at h
  have hmap := (show IsNilpotent
      (shiftY (m - 1) : Matrix (Fin (m - 1)) (Fin (m - 1)) ℚ)
      from ⟨m - 1, shiftY_nilpotent⟩).map_exp Matrix.toLinAlgEquiv'
  change (IsNilpotent.exp (shiftY (m - 1))).mulVecLin =
    IsNilpotent.exp ((shiftY (m - 1)).mulVecLin) at hmap
  rw [← hmap] at h
  exact h

@[simp] theorem ratMatrix_latticePolynomial (m : ℕ) (c : Fin (m - 1) → ℤ) :
    ratMatrix m (latticePolynomial m c) =
      shiftPolynomial ℚ m (fun i => (c i : ℚ)) := by
  simp only [latticePolynomial, map_sum, ratMatrix_smul, map_pow, ratMatrix_shiftJ]
  rfl

theorem ratMatrix_mulVec (m : ℕ) (A : Matrix (Fin m) (Fin m) ℤ) (v : Fin m → ℤ) :
    (fun i => ((A.mulVec v) i : ℚ)) =
      (ratMatrix m A).mulVec (fun i => (v i : ℚ)) := by
  ext i
  simp [Matrix.mulVec, dotProduct]

/-- Conjugation by the actual integral `exp(Y)` preserves the full lattice of
polynomial matrices, with exactly the coefficient action used in `CoefficientGroup`. -/
theorem integral_weighted_conjugation (m : ℕ) (c : Fin (m - 1) → ℤ) :
    weightedExponential m 1 * latticePolynomial m c * weightedExponential m (-1) =
      latticePolynomial m ((weightedExponential (m - 1) 1).mulVec c) := by
  apply ratMatrix_injective m
  rw [map_mul, map_mul, ratMatrix_latticePolynomial, ratMatrix_latticePolynomial,
    ratMatrix_weightedExponential, ratMatrix_weightedExponential, ratMatrix_mulVec,
    ratMatrix_weightedExponential]
  simpa only [Int.cast_one, Int.cast_neg, one_smul, neg_smul] using
    rational_weighted_conjugation m (fun i => (c i : ℚ))

end NilpotentConjugacy
