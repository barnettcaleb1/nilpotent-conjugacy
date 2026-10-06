import NilpotentConjugacy.SemidirectConjugacy
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.Card

/-! Conjugacy depth using actual finite group quotients. The infimum of an empty
family is infinity. A finite quotient has an actual group carrier, homomorphism,
and surjectivity proof; no numerical surrogate for its order is supplied.
-/

namespace NilpotentConjugacy

universe u

/-- A finite group together with a surjective homomorphism from G. -/
structure FiniteGroupQuotient (G : Type u) [Group G] where
  Carrier : Type u
  [group : Group Carrier]
  [finite : Finite Carrier]
  hom : G →* Carrier
  surjective : Function.Surjective hom

attribute [instance] FiniteGroupQuotient.group FiniteGroupQuotient.finite

variable {G : Type u} [Group G]

/-- Any actual surjective homomorphism to a finite group is an admissible quotient. -/
def finiteGroupQuotientOfHom {Q : Type u} [Group Q] [Finite Q]
    (f : G →* Q) (hf : Function.Surjective f) : FiniteGroupQuotient G :=
  { Carrier := Q, group := inferInstance, finite := inferInstance,
    hom := f, surjective := hf }

/-- The actual finite quotients separating two elements up to conjugacy. -/
def SeparatingQuotient (a b : G) :=
  {q : FiniteGroupQuotient G // ¬ IsConj (q.hom a) (q.hom b)}

/-- Minimum finite separating quotient order, or infinity if none exists. -/
noncomputable def conjugacyDepth (a b : G) : ℕ∞ :=
  ⨅ q : SeparatingQuotient a b, (Nat.card q.val.Carrier : ℕ∞)

/-- Every separating finite quotient supplies an upper bound for the depth. -/
theorem conjugacyDepth_le_card (a b : G) (q : FiniteGroupQuotient G)
    (hq : ¬ IsConj (q.hom a) (q.hom b)) :
    conjugacyDepth a b ≤ Nat.card q.Carrier :=
  iInf_le (fun q : SeparatingQuotient a b => (Nat.card q.val.Carrier : ℕ∞)) ⟨q, hq⟩

/-- A bound holding for every finite separating quotient is a bound on actual depth. -/
theorem le_conjugacyDepth {a b : G} {n : ℕ}
    (h : ∀ q : FiniteGroupQuotient G,
      ¬ IsConj (q.hom a) (q.hom b) → n ≤ Nat.card q.Carrier) :
    (n : ℕ∞) ≤ conjugacyDepth a b := by
  apply le_iInf
  intro q
  exact_mod_cast h q.val q.property

/-- Quotient orders are positive, including when the depth is infinite. -/
theorem one_le_conjugacyDepth (a b : G) : 1 ≤ conjugacyDepth a b := by
  apply le_conjugacyDepth
  intro q _
  exact Nat.card_pos

/-- A separating quotient certifies that the original elements are nonconjugate. -/
theorem not_isConj_of_separating {a b : G} (q : FiniteGroupQuotient G)
    (hq : ¬ IsConj (q.hom a) (q.hom b)) : ¬ IsConj a b :=
  fun h => hq (isConj_map q.hom h)

/-- Finiteness of depth is exactly existence of a finite separating quotient. -/
theorem conjugacyDepth_lt_top_iff (a b : G) :
    conjugacyDepth a b < ⊤ ↔ Nonempty (SeparatingQuotient a b) := by
  exact ENat.iInf_natCast_lt_top

/-- A conjugate pair has no separating quotient. -/
theorem conjugacyDepth_eq_top_of_isConj {a b : G} (h : IsConj a b) :
    conjugacyDepth a b = ⊤ := by
  apply eq_top_iff.mpr
  apply le_iInf
  intro q
  exact False.elim (q.property (isConj_map q.val.hom h))

/-- When the depth is finite, the infimum is attained by an actual quotient. -/
theorem conjugacyDepth_attained {a b : G} {n : ℕ}
    (hn : conjugacyDepth a b = n) :
    ∃ q : SeparatingQuotient a b, Nat.card q.val.Carrier = n := by
  obtain ⟨q, hq⟩ := (ENat.iInf_eq_natCast_iff.mp hn).1
  exact ⟨q, by exact_mod_cast hq⟩

end NilpotentConjugacy
