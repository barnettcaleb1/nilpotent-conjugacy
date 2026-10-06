import Mathlib.Algebra.Module.CharacterModule
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring

/-!
# The finite character argument

This file verifies the character and counting core of the arbitrary finite quotient
argument in the frozen 6 October 2026 draft. The group construction, primary
projection, and descent of the matrix units are not asserted here.

`AddCircle (1 : ℚ)` is the additive group ℚ/ℤ. The counting theorem works for
characters with values in any additive commutative group; it does not assume the
cardinality conclusion or invoke equality with the cardinality of a dual group.
-/

namespace NilpotentConjugacy

open scoped BigOperators

/-- A character into ℚ/ℤ detects an element outside a prescribed subgroup and
vanishes on that subgroup. -/
theorem exists_detecting_character {A : Type*} [AddCommGroup A]
    (H : AddSubgroup A) {c : A} (hc : c ∉ H) :
    ∃ χ : A →+ AddCircle (1 : ℚ), (∀ x ∈ H, χ x = 0) ∧ χ c ≠ 0 := by
  have hq : (QuotientAddGroup.mk' H) c ≠ 0 := by
    exact fun h => hc ((QuotientAddGroup.eq_zero_iff c).mp h)
  obtain ⟨χ, hχ⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hq
  refine ⟨χ.comp (QuotientAddGroup.mk' H), ?_, hχ⟩
  intro x hx
  change χ ((QuotientAddGroup.mk' H) x) = 0
  rw [show (QuotientAddGroup.mk' H) x = 0 from (QuotientAddGroup.eq_zero_iff x).mpr hx]
  exact map_zero χ

/-- Evaluation on the selected elements extracts one coefficient from a sum. -/
theorem character_evaluate_coordinate_sum {A B ι : Type*}
    [AddCommGroup A] [AddCommGroup B] [Fintype ι] [DecidableEq ι]
    (e : ι → A) (χ : ι → A →+ B) (α : B)
    (hδ : ∀ i j, χ i (e j) = if j = i then α else 0)
    (b : ι → ℕ) (i : ι) :
    χ i (∑ j, b j • e j) = b i • α := by
  simp [map_sum, hδ]

/-- Delta evaluations give an injection of the `N^q` coefficient grid into `A`.
No assertion about the orders of the selected elements `e i` is needed. -/
theorem character_coordinate_sum_injective {A B ι : Type*}
    [AddCommGroup A] [AddCommGroup B] [Fintype ι] [DecidableEq ι]
    (e : ι → A) (χ : ι → A →+ B) (α : B) {N : ℕ}
    (hN : addOrderOf α = N)
    (hδ : ∀ i j, χ i (e j) = if j = i then α else 0) :
    Function.Injective (fun b : ι → Fin N => ∑ j, (b j).val • e j) := by
  intro b d h
  funext i
  apply Fin.ext
  have hi := congrArg (χ i) h
  simp only [character_evaluate_coordinate_sum e χ α hδ] at hi
  exact nsmul_injOn_Iio_addOrderOf (by simp [hN])
    (by simp [hN]) hi

/-- The cardinality core: `q` delta characters with a common value of exact
order `N` force `N^q ≤ |A|` for an arbitrary finite abelian group `A`. -/
theorem finite_cardinality_of_delta_characters {A B ι : Type*}
    [AddCommGroup A] [AddCommGroup B] [Finite A] [Fintype ι] [DecidableEq ι]
    (e : ι → A) (χ : ι → A →+ B) (α : B) {N : ℕ}
    (hN : addOrderOf α = N)
    (hδ : ∀ i j, χ i (e j) = if j = i then α else 0) :
    N ^ Fintype.card ι ≤ Nat.card A := by
  have h := Nat.card_le_card_of_injective _
    (character_coordinate_sum_injective e χ α hN hδ)
  simpa [Nat.card_fun, Nat.card_eq_fintype_card] using h

/-- An integral relation among delta characters has every coefficient divisible
by the order of their common nonzero value. -/
theorem delta_characters_relation_divisibility {A B ι : Type*}
    [AddCommGroup A] [AddCommGroup B] [Fintype ι] [DecidableEq ι]
    (e : ι → A) (χ : ι → A →+ B) (α : B) {N : ℕ}
    (hN : addOrderOf α = N)
    (hδ : ∀ i j, χ i (e j) = if j = i then α else 0)
    (b : ι → ℤ) (h : ∑ j, b j • χ j = 0) :
    ∀ i, (N : ℤ) ∣ b i := by
  intro i
  have hi := DFunLike.congr_fun h (e i)
  have hz : b i • α = 0 := by simpa [hδ, eq_comm] using hi
  rw [← hN]
  exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr hz

/-- Signs in a bidiagonal recurrence do not affect whether an integer multiple
vanishes. This statement includes the exact accumulated factor. -/
theorem annihilation_iff_of_bidiagonal_recurrence {B : Type*} [AddCommGroup B]
    (β : ℕ → B) (t r : ℕ)
    (hrec : ∀ k < r, β (k + 1) = -(t • β k))
    {k : ℕ} (hk : k ≤ r) (n : ℕ) :
    n • β k = 0 ↔ (n * t ^ k) • β 0 = 0 := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [hrec k (by omega), smul_neg, neg_eq_zero, ← mul_smul]
    rw [ih (by omega)]
    simp only [pow_succ, mul_assoc, mul_comm, mul_left_comm]

/-- Detecting the last term of a bidiagonal recurrence forces the first term to
have the full accumulated prime power order. `s + 1` and `r + 1` are the paper's
positive parameters `s` and `r`, respectively. -/
theorem exact_order_of_detecting_bidiagonal_character {B : Type*} [AddCommGroup B]
    (β : ℕ → B) {p : ℕ} (hp : p.Prime) (s r : ℕ)
    (hrec : ∀ k < r, β (k + 1) = -(p ^ (s + 1) • β k))
    (hterminal : p ^ (s + 1) • β r = 0)
    (hdetect : p ^ s • β r ≠ 0) :
    addOrderOf (β 0) = p ^ ((s + 1) * (r + 1)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hzero := (annihilation_iff_of_bidiagonal_recurrence β (p ^ (s + 1)) r
    hrec (le_refl r) (p ^ (s + 1))).mp hterminal
  have hnonzero := mt (annihilation_iff_of_bidiagonal_recurrence β (p ^ (s + 1)) r
    hrec (le_refl r) (p ^ s)).mpr hdetect
  have hexp : s + (s + 1) * r + 1 = (s + 1) * (r + 1) := by ring
  have hzero' : p ^ (s + (s + 1) * r + 1) • β 0 = 0 := by
    simpa only [← pow_mul, ← pow_add,
      show s + 1 + (s + 1) * r = s + (s + 1) * r + 1 by omega] using hzero
  have hnonzero' : p ^ (s + (s + 1) * r) • β 0 ≠ 0 := by
    simpa [← pow_mul, ← pow_add] using hnonzero
  simpa [hexp] using addOrderOf_eq_prime_pow hnonzero' hzero'

/-- An abstract form of the paper's finite quotient bound. The hypotheses are
precisely a subgroup obstruction, the bidiagonal columns modulo that subgroup,
and descended coordinate matrix units. The ambient finite abelian group is
arbitrary. The proof constructs a detecting character, proves its exact order,
and derives the cardinality bound from an actual injection.

The chain has `r + 1` entries and its coefficient is `p ^ (s + 1)`. Thus the
paper's parameters are `s_paper = s + 1`, `r_paper = r + 1`, and
`q = Fintype.card ι`. -/
theorem finite_cardinality_from_obstruction_and_matrix_units {A ι : Type*}
    [AddCommGroup A] [Finite A] [Fintype ι] [DecidableEq ι]
    (H : AddSubgroup A) (v : ℕ → A) (e : ι → A) (E : ι → A →+ A)
    {p : ℕ} (hp : p.Prime) (s r D : ℕ)
    (hcolumns : ∀ k < r, p ^ (s + 1) • v k + v (k + 1) ∈ H)
    (hterminal : p ^ (s + 1) • v r ∈ H)
    (hdetect : D • (p ^ s • v r) ∉ H)
    (hunits : ∀ i j, E i (e j) = if j = i then v 0 else 0) :
    p ^ ((s + 1) * (r + 1) * Fintype.card ι) ≤ Nat.card A := by
  obtain ⟨lam, hvanish, hlam⟩ := exists_detecting_character H hdetect
  have hrec : ∀ k < r, lam (v (k + 1)) = -(p ^ (s + 1) • lam (v k)) := by
    intro k hk
    have h := hvanish _ (hcolumns k hk)
    simp only [map_add, map_nsmul] at h
    exact eq_neg_of_add_eq_zero_right h
  have hlast : p ^ (s + 1) • lam (v r) = 0 := by
    simpa only [map_nsmul] using hvanish _ hterminal
  have hdet : p ^ s • lam (v r) ≠ 0 := by
    intro h
    apply hlam
    simp only [map_nsmul, h, smul_zero]
  have horder := exact_order_of_detecting_bidiagonal_character
    (fun k => lam (v k)) hp s r hrec hlast hdet
  have hδ : ∀ i j, (lam.comp (E i)) (e j) = if j = i then lam (v 0) else 0 := by
    intro i j
    simp only [AddMonoidHom.comp_apply, hunits]
    split_ifs <;> simp
  have hbound := finite_cardinality_of_delta_characters
    e (fun i => lam.comp (E i)) (lam (v 0)) horder hδ
  simpa only [← pow_mul] using hbound

/-- The preceding bound in the paper's positive indexing convention:
`r` tail coordinates and the coefficient `p^s` give the bound `p^(s*r*q)`.
Only the listed algebraic hypotheses are certified by this declaration. -/
theorem finite_quotient_character_bound {A : Type*} [AddCommGroup A] [Finite A]
    (H : AddSubgroup A) (v : ℕ → A) {q : ℕ}
    (e : Fin q → A) (E : Fin q → A →+ A)
    {p s r : ℕ} (hp : p.Prime) (hs : 0 < s) (hr : 0 < r) (D : ℕ)
    (hcolumns : ∀ k < r - 1, p ^ s • v k + v (k + 1) ∈ H)
    (hterminal : p ^ s • v (r - 1) ∈ H)
    (hdetect : D • (p ^ (s - 1) • v (r - 1)) ∉ H)
    (hunits : ∀ i j, E i (e j) = if j = i then v 0 else 0) :
    p ^ (s * r * q) ≤ Nat.card A := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simpa using finite_cardinality_from_obstruction_and_matrix_units
    H v e E hp s r D hcolumns hterminal hdetect hunits

/-- The same character bound transfers through an injective realization of `A`
inside an arbitrary finite quotient `Q`. -/
theorem ambient_finite_quotient_character_bound {A Q : Type*}
    [AddCommGroup A] [Finite A] [Finite Q]
    (ι : A → Q) (hι : Function.Injective ι)
    (H : AddSubgroup A) (v : ℕ → A) {q : ℕ}
    (e : Fin q → A) (E : Fin q → A →+ A)
    {p s r : ℕ} (hp : p.Prime) (hs : 0 < s) (hr : 0 < r) (D : ℕ)
    (hcolumns : ∀ k < r - 1, p ^ s • v k + v (k + 1) ∈ H)
    (hterminal : p ^ s • v (r - 1) ∈ H)
    (hdetect : D • (p ^ (s - 1) • v (r - 1)) ∉ H)
    (hunits : ∀ i j, E i (e j) = if j = i then v 0 else 0) :
    p ^ (s * r * q) ≤ Nat.card Q :=
  (finite_quotient_character_bound H v e E hp hs hr D hcolumns hterminal hdetect hunits).trans
    (Nat.card_le_card_of_injective ι hι)

end NilpotentConjugacy
