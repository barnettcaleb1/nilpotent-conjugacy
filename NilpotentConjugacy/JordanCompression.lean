import NilpotentConjugacy.WordCompression

/-!
Full descending word compression for nilpotent chains in actual integral
abelian-by-cyclic groups. Bounds refer exclusively to `WordRep` and actual
finite words. The coefficient and base-digit construction is imported from
`WordCompression`; the higher-coordinate corrections are proved here.
-/

namespace NilpotentConjugacy

open scoped BigOperators

section Chain

variable {A : Type*} [AddCommGroup A] (α : AddAut A)

@[simp] theorem normalElement_neg (v : A) :
    normalElement α (-v) = (normalElement α v)⁻¹ :=
  map_inv SemidirectProduct.inl (Multiplicative.ofAdd v)

private theorem coefficient_radius_bound (K B k : ℕ) (hB : 1 ≤ B) (hk : 1 ≤ k) :
    K * (B + 1) ^ k ≤ (2 * (K + 1) * B) ^ k := by
  have hK : K ≤ (K + 1) ^ k :=
    (Nat.le_succ K).trans (le_self_pow (by omega) (by omega))
  calc
    K * (B + 1) ^ k ≤ (K + 1) ^ k * (2 * B) ^ k :=
      Nat.mul_le_mul hK (Nat.pow_le_pow_left (by omega) k)
    _ = (2 * (K + 1) * B) ^ k := by rw [← mul_pow]; congr 1; ring

/-- Full arbitrary-weight compression along an integral nilpotent chain.
The constant is uniform over all nonnegative coefficients and all scales. -/
theorem nilpotent_chain_compression_nat
    {S : Set (CyclicSemidirect α)} (N : AddMonoid.End A)
    (hα : automorphismEnd α = 1 + N) (e : A)
    (he : normalElement α e ∈ S) (ht : stableLetter α ∈ S)
    (ell : ℕ) (hN : N ^ ell = 0) (j : ℕ) (hj : 1 ≤ j) (hjell : j ≤ ell) :
    ∃ C : ℕ, ∀ B : ℕ, 1 ≤ B → ∀ a : ℕ, a ≤ B ^ j →
      WordRep S (C * B) (normalElement α (a • (N ^ (j - 1)) e)) := by
  classical
  suffices h : ∀ d j : ℕ, ell - j = d → 1 ≤ j → j ≤ ell →
      ∃ C : ℕ, ∀ B : ℕ, 1 ≤ B → ∀ a : ℕ, a ≤ B ^ j →
        WordRep S (C * B) (normalElement α (a • (N ^ (j - 1)) e)) from
    h (ell - j) j rfl hj hjell
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro j hd hj hjell
    have hCs : ∀ i : Fin ell, ∃ C : ℕ, ∀ B : ℕ, 1 ≤ B → ∀ a : ℕ,
        a ≤ B ^ (i.val + 1) → j ≤ i.val →
        WordRep S (C * B) (normalElement α (a • (N ^ i.val) e)) := by
      intro i
      by_cases hji : j ≤ i.val
      · obtain ⟨C, hC⟩ := ih (ell - (i.val + 1)) (by omega)
          (i.val + 1) rfl (by omega) (by omega)
        exact ⟨C, fun B hB a ha _ => by simpa using hC B hB a ha⟩
      · exact ⟨0, fun _ _ _ _ hji' => (hji hji').elim⟩
    choose Cs hCs using hCs
    let Cmax := Finset.univ.sup Cs
    let K := ell ^ (ell + 1)
    let R := 2 * (K + 1)
    let W := j * (3 * 2 ^ (j - 1))
    refine ⟨2 * W + ell * Cmax * R, ?_⟩
    intro B hB a ha
    have hab : a < (B + 1) ^ j := by
      exact lt_of_le_of_lt ha (Nat.pow_lt_pow_left (by omega) (by omega))
    obtain ⟨p, hp, hlo, hcoeff, hw⟩ :=
      chain_approximation α N hα e he ht ell (B + 1) j a (by omega) hj hjell hab
    let f : ℕ → A := fun i => if j ≤ i then -(p.coeff i • (N ^ i) e) else 0
    have hf : ∀ i ∈ Finset.range ell,
        WordRep S (Cmax * (R * B)) (normalElement α (f i)) := by
      intro i hi
      have hiell := Finset.mem_range.mp hi
      by_cases hji : j ≤ i
      · have hci : p.coeff i ≤ (R * B) ^ (i + 1) :=
          (hcoeff i hiell).trans (coefficient_radius_bound K B (i + 1) hB (by omega))
        have hRB : 1 ≤ R * B := by
          dsimp [R]
          nlinarith
        have hc := hCs ⟨i, hiell⟩ (R * B) hRB (p.coeff i) hci hji
        have hCmax : Cs ⟨i, hiell⟩ ≤ Cmax := Finset.le_sup (f := Cs) (by simp)
        have hc' := hc.inv.mono (Nat.mul_le_mul_right (R * B) hCmax)
        simpa only [f, if_pos hji, normalElement_neg] using hc'
      · have hz := (WordRep.one S).mono (Nat.zero_le (Cmax * (R * B)))
        simpa [f, hji, normalElement] using hz
    have hcorr := normalElement_sum_rep α (Finset.range ell) f (Cmax * (R * B)) hf
    have hsum : (natPolynomialEval N p) e + ∑ i ∈ Finset.range ell, f i =
        a • (N ^ (j - 1)) e := by
      rw [natPolynomialEval_chain N ell hN, ← Finset.sum_add_distrib]
      rw [Finset.sum_eq_single (j - 1)]
      · simp only [f, hp, show ¬j ≤ j - 1 by omega, if_false, add_zero]
      · intro i hi hne
        have hiell := Finset.mem_range.mp hi
        by_cases hji : j ≤ i
        · simp [f, hji]
        · simp [f, hji, hlo i (by omega)]
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
    have hjoined := hw.mul hcorr
    rw [← normalElement_add, hsum] at hjoined
    apply hjoined.mono
    simp only [Finset.card_range]
    have hmain : j * (3 * 2 ^ (j - 1) * (B + 1)) ≤ 2 * W * B := by
      have hmul := Nat.mul_le_mul_left W (show B + 1 ≤ 2 * B by omega)
      dsimp [W] at hmul ⊢
      nlinarith
    calc
      j * (3 * 2 ^ (j - 1) * (B + 1)) + ell * (Cmax * (R * B)) ≤
          2 * W * B + ell * (Cmax * (R * B)) := Nat.add_le_add_right hmain _
      _ = (2 * W + ell * Cmax * R) * B := by ring

/-- The complete signed-integer form of nilpotent-chain compression. -/
theorem nilpotent_chain_compression
    {S : Set (CyclicSemidirect α)} (N : AddMonoid.End A)
    (hα : automorphismEnd α = 1 + N) (e : A)
    (he : normalElement α e ∈ S) (ht : stableLetter α ∈ S)
    (ell : ℕ) (hN : N ^ ell = 0) (j : ℕ) (hj : 1 ≤ j) (hjell : j ≤ ell) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ B : ℕ, 1 ≤ B → ∀ a : ℤ, a.natAbs ≤ B ^ j →
      WordRep S (C * B) (normalElement α (a • (N ^ (j - 1)) e)) := by
  obtain ⟨C, hC⟩ := nilpotent_chain_compression_nat α N hα e he ht ell hN j hj hjell
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro B hB a ha
  have h := (hC B hB a.natAbs ha).mono (Nat.mul_le_mul_right B (le_max_right 1 C))
  cases a with
  | ofNat a => simpa using h
  | negSucc a =>
    have hneg := h.inv
    simpa only [Int.natAbs_negSucc, negSucc_zsmul, neg_smul, normalElement_neg,
      Nat.cast_add, Nat.cast_one] using hneg

/-- Nilpotent-chain compression survives every group homomorphism into a group
with any specified finite generating set. Only the images of the two fixed
input generators contribute to the comparison constant. -/
theorem nilpotent_chain_compression_map {G : Type*} [Group G]
    (f : CyclicSemidirect α →* G) (S : WordGeneratingSet G)
    (N : AddMonoid.End A) (hα : automorphismEnd α = 1 + N) (e : A)
    (ell : ℕ) (hN : N ^ ell = 0) (j : ℕ) (hj : 1 ≤ j) (hjell : j ≤ ell) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ B : ℕ, 1 ≤ B → ∀ a : ℤ, a.natAbs ≤ B ^ j →
      wordLength S (f (normalElement α (a • (N ^ (j - 1)) e))) ≤ C * B := by
  classical
  let T : Set (CyclicSemidirect α) := {normalElement α e, stableLetter α}
  obtain ⟨C, _, hC⟩ := nilpotent_chain_compression α (S := T) N hα e
    (by simp [T]) (by simp [T]) ell hN j hj hjell
  let L := wordLength S (f (normalElement α e)) + wordLength S (f (stableLetter α))
  have hgen : ∀ x ∈ f '' T, WordRep S.generators L x := by
    rintro x ⟨y, hy, rfl⟩
    rcases (by simpa [T] using hy : y = normalElement α e ∨ y = stableLetter α) with rfl | rfl
    · exact (wordLength_rep S _).mono (Nat.le_add_right _ _)
    · exact (wordLength_rep S _).mono (Nat.le_add_left _ _)
  refine ⟨max 1 (L * C), le_max_left _ _, ?_⟩
  intro B hB a ha
  apply (wordLength_le_iff _ _ _).2
  have hw := ((hC B hB a ha).map f).substitute hgen
  apply hw.mono
  calc
    L * (C * B) = (L * C) * B := by ring
    _ ≤ max 1 (L * C) * B := Nat.mul_le_mul_right B (le_max_right _ _)

end Chain

end NilpotentConjugacy
