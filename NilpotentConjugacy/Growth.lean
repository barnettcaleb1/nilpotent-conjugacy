import Mathlib

/-!
Arithmetic and growth-scale consequences used in the nilpotent-conjugacy draft.
These results do not construct the groups or establish their quotient-depth bounds.
-/

namespace NilpotentConjugacy

/-- The exponent resulting from the paper's specialization m = 4d, w = 3d. -/
theorem specialized_exponent (d : ℕ) :
    (3 * d) * (4 * d - 3 * d) * (3 * d + 1 - (4 * d) / 2) =
      3 * d ^ 2 * (d + 1) := by
  have hr : 4 * d - 3 * d = d := by omega
  have hq : 3 * d + 1 - (4 * d) / 2 = d + 1 := by omega
  rw [hr, hq]
  ring

/-- All parameter restrictions used in the cubic specialization hold for d ≥ 2. -/
theorem specialized_parameters {d : ℕ} (hd : 2 ≤ d) :
    4 ≤ 4 * d ∧ (4 * d) / 2 ≤ 3 * d ∧ 3 * d ≤ 4 * d - 2 ∧
      4 * d - 3 * d = d ∧ 3 * d + 1 - (4 * d) / 2 = d + 1 := by
  omega

/-- The claimed lower degree is at least (3/512) h^3 when h = 8d,
written without rational division. -/
theorem cubic_degree_lower (d : ℕ) :
    3 * (8 * d) ^ 3 ≤ 512 * (3 * d ^ 2 * (d + 1)) := by
  nlinarith [Nat.zero_le (d ^ 2)]

/-- No fixed real coefficient of (8d)^2 dominates the proposed degrees.
This is an arithmetic comparison, not a formal construction of groups. -/
theorem degrees_exceed_every_quadratic (C : ℝ) :
    ∃ d : ℕ, 2 ≤ d ∧ C * (8 * (d : ℝ)) ^ 2 <
      3 * (d : ℝ) ^ 2 * ((d : ℝ) + 1) := by
  obtain ⟨d, hd⟩ := exists_nat_gt (max (2 : ℝ) (64 * C))
  have hd2 : (2 : ℝ) < d := lt_of_le_of_lt (le_max_left _ _) hd
  have hdC : 64 * C < (d : ℝ) := lt_of_le_of_lt (le_max_right _ _) hd
  have hdNat : 2 ≤ d := by exact_mod_cast (le_of_lt hd2)
  refine ⟨d, hdNat, ?_⟩
  have hcoeff : 64 * C < 3 * ((d : ℝ) + 1) := by linarith
  have hpos : 0 < (d : ℝ) ^ 2 := sq_pos_of_pos (by linarith)
  have hmul := mul_lt_mul_of_pos_right hcoeff hpos
  nlinarith [hmul]

/-- Adjacent geometric scales bracket every sufficiently large real radius.
The sequence starts at index one, as in the paper. -/
theorem geometric_bracket {C b n : ℝ} (hC : 0 < C) (hb : 1 < b)
    (hn : C * b ≤ n) :
    ∃ s : ℕ, 1 ≤ s ∧ C * b ^ s ≤ n ∧ n < C * b ^ (s + 1) := by
  have hbn : b ≤ n / C := (le_div_iff₀ hC).2 (by nlinarith [hn])
  obtain ⟨s, hslo, hshi⟩ := exists_nat_pow_near (le_trans (le_of_lt hb) hbn) hb
  have hs : 1 ≤ s := by
    by_contra h
    have : s = 0 := by omega
    subst s
    simp only [zero_add, pow_one] at hshi
    exact (not_lt_of_ge hbn) hshi
  refine ⟨s, hs, ?_, ?_⟩
  · simpa [mul_comm] using (le_div_iff₀ hC).1 hslo
  · have := (div_lt_iff₀ hC).1 hshi
    nlinarith

/-- Convert a bound supplied at all geometric scales to an all-radius
polynomial lower bound. The hypothesis explicitly supplies the sequence bound;
this lemma does not assert that the manuscript's groups satisfy it. -/
theorem geometric_polynomial_lower {F : ℝ → ℝ} {C b : ℝ} {E : ℕ}
    (hC : 0 < C) (hb : 1 < b)
    (hseq : ∀ s : ℕ, 1 ≤ s → ∀ n : ℝ, C * b ^ s ≤ n →
      (b ^ s) ^ E ≤ F n) :
    ∀ n : ℝ, C * b ≤ n → (n / (C * b)) ^ E ≤ F n := by
  intro n hn
  obtain ⟨s, hs, hslo, hshi⟩ := geometric_bracket hC hb hn
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have hCb : 0 < C * b := mul_pos hC hb0
  have hbase : n / (C * b) ≤ b ^ s := by
    apply (div_le_iff₀ hCb).2
    rw [pow_succ] at hshi
    nlinarith [hshi]
  have hn0 : 0 ≤ n / (C * b) := div_nonneg (by nlinarith [hn]) (le_of_lt hCb)
  exact (pow_le_pow_left₀ hn0 hbase E).trans (hseq s hs n hslo)

end NilpotentConjugacy
