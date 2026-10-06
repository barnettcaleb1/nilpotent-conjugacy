import NilpotentConjugacy.QuotientModule
import NilpotentConjugacy.SemidirectConjugacy
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The finite abelian image and its induced actions are constructed from an
arbitrary homomorphism of an actual semidirect product. -/

namespace NilpotentConjugacy

variable {V H Q : Type*} [AddCommGroup V] [Group H] [Group Q]
    (φ : H →* MulAut (Multiplicative V))
    (f : (Multiplicative V ⋊[φ] H) →* Q)

/-- The restriction of the group quotient to its abelian normal factor. -/
def normalImageRestriction : Multiplicative V →* Q :=
  f.comp SemidirectProduct.inl

/-- The actual abelian image, represented by the first isomorphism theorem. -/
abbrev NormalImage := Additive (Multiplicative V ⧸ (normalImageRestriction φ f).ker)

/-- The surjective additive map from the normal factor to its image. -/
def normalImageMap : V →ₗ[ℤ] NormalImage φ f :=
  (QuotientGroup.mk' (normalImageRestriction φ f).ker).toAdditive.toIntLinearMap

theorem normalImageMap_surjective : Function.Surjective (normalImageMap φ f) := by
  intro z
  obtain ⟨v, hv⟩ := (QuotientGroup.mk'_surjective (normalImageRestriction φ f).ker) z.toMul
  exact ⟨v.toAdd, congrArg Additive.ofMul hv⟩

/-- Every finite group quotient has a finite abelian normal image. -/
theorem normalImage_finite [Finite Q] : Finite (NormalImage φ f) := by
  exact Finite.of_injective (QuotientGroup.kerLift (normalImageRestriction φ f))
    (QuotientGroup.kerLift_injective _)

/-- The abelian image has at most the order of the finite group quotient. -/
theorem normalImage_card_le [Finite Q] : Nat.card (NormalImage φ f) ≤ Nat.card Q := by
  exact Nat.card_le_card_of_injective (QuotientGroup.kerLift (normalImageRestriction φ f))
    (QuotientGroup.kerLift_injective _)

/-- Normality of the group kernel forces invariance under the actual action. -/
theorem normalImage_kernel_stable (h : H) :
    (normalImageRestriction φ f).ker ≤
      (normalImageRestriction φ f).ker.comap (φ h).toMonoidHom := by
  intro v hv
  change f (SemidirectProduct.inl (φ h v)) = 1
  have hv' : f (SemidirectProduct.inl v) = 1 := hv
  rw [SemidirectProduct.inl_aut, map_mul, map_mul, hv', mul_one]
  simp

/-- The actual action on the quotient, constructed by descent. -/
def normalImageAction (h : H) : NormalImage φ f →ₗ[ℤ] NormalImage φ f :=
  (QuotientGroup.map (normalImageRestriction φ f).ker (normalImageRestriction φ f).ker
    (φ h).toMonoidHom (normalImage_kernel_stable φ f h)).toAdditive.toIntLinearMap

@[simp] theorem normalImageAction_map (h : H) (v : V) :
    normalImageAction φ f h (normalImageMap φ f v) =
      normalImageMap φ f ((φ h (Multiplicative.ofAdd v)).toAdd) := rfl

/-- The action difference induced on the actual abelian group image. -/
def normalImageDifference (h : H) : NormalImage φ f →ₗ[ℤ] NormalImage φ f :=
  normalImageAction φ f h - LinearMap.id

@[simp] theorem normalImageDifference_map (h : H) (v : V) :
    normalImageDifference φ f h (normalImageMap φ f v) =
      normalImageMap φ f ((φ h (Multiplicative.ofAdd v)).toAdd - v) := by
  simp [normalImageDifference]

/-- Nonconjugacy in any group quotient supplies the actual additive obstruction. -/
theorem normalImage_separating_obstruction (h : H) (c : V)
    (hsep : ¬ IsConj (f (SemidirectProduct.inr h))
      (f (SemidirectProduct.inl (Multiplicative.ofAdd c) * SemidirectProduct.inr h))) :
    normalImageMap φ f c ∉ (normalImageDifference φ f h).range := by
  rintro ⟨z, hz⟩
  obtain ⟨v, rfl⟩ := normalImageMap_surjective φ f z
  rw [normalImageDifference_map] at hz
  apply separating_image_obstruction φ h (Multiplicative.ofAdd c) f hsep
  refine ⟨Multiplicative.ofAdd v, ?_⟩
  have hh := congrArg (fun a : NormalImage φ f =>
    QuotientGroup.kerLift (normalImageRestriction φ f) a.toMul) hz
  change f (SemidirectProduct.inl
    (Multiplicative.ofAdd ((φ h (Multiplicative.ofAdd v)).toAdd - v))) =
      f (SemidirectProduct.inl (Multiplicative.ofAdd c)) at hh
  simpa [actionDifference, sub_eq_add_neg] using hh

/-- An exact prime-multiple commutator identity in the original lattice yields
prime-multiple image membership in every quotient. -/
theorem normalImage_prime_smul_mem (h : H) (p : ℕ) (c v : V)
    (hpc : (φ h (Multiplicative.ofAdd v)).toAdd - v = (p : ℤ) • c) :
    (p : ℤ) • normalImageMap φ f c ∈ (normalImageDifference φ f h).range := by
  refine ⟨normalImageMap φ f v, ?_⟩
  rw [normalImageDifference_map, hpc, map_smul]

end NilpotentConjugacy
