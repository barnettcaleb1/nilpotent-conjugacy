import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic.Group

/-! Conjugacy and finite-image obstructions for actual semidirect products.
The normal factor is written multiplicatively; use Multiplicative V for a lattice.
No particular integral action is assumed to exist in this file.
-/

namespace NilpotentConjugacy

variable {N H : Type*} [CommGroup N] [Group H]

/-- The difference between an action and the identity, in multiplicative notation. -/
def actionDifference (φ : H →* MulAut N) (h : H) : N →* N where
  toFun n := φ h n * n⁻¹
  map_one' := by simp
  map_mul' := by intro x y; simp [mul_comm, mul_left_comm, mul_assoc]

/-- Conjugating a pure acting element by a general semidirect-product element. -/
theorem semidirect_conjugate_inr (φ : H →* MulAut N) (h : H)
    (x : N ⋊[φ] H) :
    x * SemidirectProduct.inr h * x⁻¹ =
      ⟨x.left * φ (x.right * h * x.right⁻¹) x.left⁻¹,
        x.right * h * x.right⁻¹⟩ := by
  ext <;> simp [mul_assoc]

/-- The conjugacy criterion includes every possible conjugator, with no
restriction to the normal subgroup in the forward direction. -/
theorem semidirect_isConj_iff_difference_range (φ : H →* MulAut N)
    (h : H) (c : N) :
    IsConj (SemidirectProduct.inr h : N ⋊[φ] H)
      (SemidirectProduct.inl c * SemidirectProduct.inr h) ↔
      c ∈ (actionDifference φ h).range := by
  rw [isConj_iff]
  constructor
  · rintro ⟨x, hx⟩
    have hr := congrArg SemidirectProduct.right hx
    simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inr,
      SemidirectProduct.right_inl, SemidirectProduct.inv_right, one_mul] at hr
    have hl := congrArg SemidirectProduct.left hx
    rw [semidirect_conjugate_inr] at hl
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, SemidirectProduct.left_inr, map_one, mul_one] at hl
    rw [hr] at hl
    exact ⟨x.left⁻¹, by simpa [actionDifference, mul_comm] using hl⟩
  · rintro ⟨n, hn⟩
    refine ⟨SemidirectProduct.inl n⁻¹, ?_⟩
    rw [semidirect_conjugate_inr]
    ext
    · simpa [actionDifference, mul_comm] using hn
    · simp

/-- A homomorphism sends conjugate elements to conjugate elements. -/
theorem isConj_map {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) {a b : G} (h : IsConj a b) : IsConj (f a) (f b) := by
  obtain ⟨x, hx⟩ := isConj_iff.mp h
  apply isConj_iff.mpr
  exact ⟨f x, by simpa using congrArg f hx⟩

/-- In every group image, membership in the image of the action difference
forces conjugacy. This supplies the obstruction used before primary projection. -/
theorem separating_image_obstruction (φ : H →* MulAut N) (h : H) (c : N)
    {Q : Type*} [Group Q] (f : (N ⋊[φ] H) →* Q)
    (hsep : ¬ IsConj (f (SemidirectProduct.inr h))
      (f (SemidirectProduct.inl c * SemidirectProduct.inr h))) :
    ¬ ∃ n : N, f (SemidirectProduct.inl (actionDifference φ h n)) =
      f (SemidirectProduct.inl c) := by
  rintro ⟨n, hn⟩
  have hc := (semidirect_isConj_iff_difference_range φ h
    (actionDifference φ h n)).mpr ⟨n, rfl⟩
  have hc' := isConj_map f hc
  apply hsep
  simpa only [map_mul, hn] using hc'

end NilpotentConjugacy
