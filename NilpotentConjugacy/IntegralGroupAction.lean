import NilpotentConjugacy.IntegralGroup
import Mathlib.Algebra.Ring.Action.ConjAct

namespace NilpotentConjugacy

/-- Conjugation by an actual invertible integer matrix. -/
def integerMatrixConjugation (m : ℕ) (U : (Matrix (Fin m) (Fin m) ℤ)ˣ) :
    Matrix (Fin m) (Fin m) ℤ ≃+* Matrix (Fin m) (Fin m) ℤ :=
  MulSemiringAction.toRingEquiv _ _ (ConjAct.toConjAct U)

@[simp] theorem integerMatrixConjugation_apply (m : ℕ)
    (U : (Matrix (Fin m) (Fin m) ℤ)ˣ) (A : Matrix (Fin m) (Fin m) ℤ) :
    integerMatrixConjugation m U A = U.val * A * U.inv := rfl

/-- Conjugation commutes with the factorial-cleared finite exponential. -/
theorem integerMatrixConjugation_integralExponential (m : ℕ)
    (U : (Matrix (Fin m) (Fin m) ℤ)ˣ) (A : Matrix (Fin m) (Fin m) ℤ) :
    integerMatrixConjugation m U (integralExponential m A) =
      integralExponential m (integerMatrixConjugation m U A) := by
  simp only [integralExponential, map_sum, map_zsmul, map_pow]

/-- The exact conjugation identity for the paper's full exponential lattice. -/
theorem latticeExponential_conjugation (m : ℕ) (c : Fin (m - 1) → ℤ) :
    weightedExponentialUnit m 1 * latticeExponential m c *
      (weightedExponentialUnit m 1)⁻¹ =
    latticeExponential m ((weightedExponential (m - 1) 1).mulVec c) := by
  apply Units.ext
  have h := integerMatrixConjugation_integralExponential m
    (weightedExponentialUnit m 1) (latticePolynomial m c)
  have hc : integerMatrixConjugation m (weightedExponentialUnit m 1)
      (latticePolynomial m c) =
      latticePolynomial m ((weightedExponential (m - 1) 1).mulVec c) :=
    integral_weighted_conjugation m c
  rw [hc] at h
  exact h

private theorem equivariant_npow {N K : Type*} [Group N] [Group K]
    (f : N →* K) (T : MulAut N) (u : K)
    (h : ∀ x, f (T x) = u * f x * u⁻¹) (n : ℕ) (x : N) :
    f ((T ^ n) x) = u ^ n * f x * (u ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, h, ih, pow_succ']
    simp [mul_assoc]

private theorem equivariant_zpow {N K : Type*} [Group N] [Group K]
    (f : N →* K) (T : MulAut N) (u : K)
    (h : ∀ x, f (T x) = u * f x * u⁻¹) (a : ℤ) (x : N) :
    f ((T ^ a) x) = u ^ a * f x * (u ^ a)⁻¹ := by
  have hinv (x : N) : f (T⁻¹ x) = u⁻¹ * f x * (u⁻¹)⁻¹ := by
    have hh := h (T⁻¹ x)
    simp only [MulAut.apply_inv_self] at hh
    rw [hh]
    simp [mul_assoc]
  cases a with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using equivariant_npow f T u h n x
  | negSucc n =>
    simpa only [zpow_negSucc, ← inv_pow, inv_inv] using
      equivariant_npow f T⁻¹ u⁻¹ hinv (n + 1) x

/-- Full integral equivariance, including every positive and negative cyclic parameter. -/
theorem latticeExponential_equivariant (m : ℕ)
    (a : Multiplicative ℤ) (c : Multiplicative (Fin (m - 1) → ℤ)) :
    latticeExponentialHom m (coefficientAction m a c) =
      weightedExponentialHom m a * latticeExponentialHom m c *
        (weightedExponentialHom m a)⁻¹ := by
  have hone (x : Multiplicative (Fin (m - 1) → ℤ)) :
      latticeExponentialHom m (coefficientAction m (Multiplicative.ofAdd 1) x) =
        weightedExponentialUnit m 1 * latticeExponentialHom m x *
          (weightedExponentialUnit m 1)⁻¹ := by
    exact (latticeExponential_conjugation m x.toAdd).symm
  have h := equivariant_zpow (latticeExponentialHom m)
    (coefficientAction m (Multiplicative.ofAdd 1)) (weightedExponentialUnit m 1)
    hone a.toAdd c
  have ha : (Multiplicative.ofAdd (1 : ℤ)) ^ a.toAdd = a := by
    change Multiplicative.ofAdd (a.toAdd • (1 : ℤ)) = a
    simp
  rw [← map_zpow, ha, ← weightedExponentialUnit_zsmul] at h
  exact h

/-- The paper's actual representation, with its action law proved from the
explicit integral exponentials and the coefficient semidirect product. -/
noncomputable def manuscriptRhoHom (m : ℕ) :
    CoefficientGroup m →* (Matrix (Fin m) (Fin m) ℤ)ˣ :=
  SemidirectProduct.lift (latticeExponentialHom m) (weightedExponentialHom m)
    (by
      intro a
      apply MonoidHom.ext
      intro c
      exact latticeExponential_equivariant m a c)

@[simp] theorem manuscriptRhoHom_apply (m : ℕ) (h : CoefficientGroup m) :
    manuscriptRhoHom m h = manuscriptRho m h := rfl

/-- The actual integral action `rho(P,a)=exp(P)exp(aY)` from the manuscript. -/
noncomputable def manuscriptAction (m : ℕ) :
    CoefficientGroup m →* MulAut (Multiplicative (Fin m → ℤ)) :=
  (integerMatrixAction m).comp (manuscriptRhoHom m)

/-- The manuscript's exact group `Z^m ⋊ (W ⋊ Z)`, now with a proved integral action.
`GroupProperties` proves torsion-freeness and nilpotency; `GroupClass` proves
its exact class, and `GroupSeries` constructs 2m actual infinite cyclic quotients. -/
abbrev ManuscriptGroup (m : ℕ) :=
  SemidirectProduct (Multiplicative (Fin m → ℤ)) (CoefficientGroup m) (manuscriptAction m)

instance manuscriptGroup_fg (m : ℕ) : Group.FG (ManuscriptGroup m) := by
  apply semidirectProduct_finitelyGenerated

end NilpotentConjugacy
