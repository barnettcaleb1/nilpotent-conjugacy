import NilpotentConjugacy.CubicTheorem
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace NilpotentConjugacy

/-- The paper's comparison, including its integer prefactor and radius scaling. -/
def GrowthLE (f g : ℕ → ℕ∞) : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → f n ≤ (C : ℕ∞)*g (C*n)

def polynomialGrowth (D : ℕ) (n : ℕ) : ℕ∞ := (n : ℕ∞)^D

theorem polynomialConjugacyLower_not_growthLE {G : Type*} [Group G]
    (S : WordGeneratingSet G) {D E : ℕ} (hDE : D < E)
    (hlower : PolynomialConjugacyLower S E) :
    ¬ GrowthLE (conjugacyGrowth S) (polynomialGrowth D) := by
  obtain ⟨L,N,hL,hN,hlo⟩ := hlower
  rintro ⟨C,hC,hup⟩
  let K := L*C*C^D
  let n := max N (K+1)
  have hnN : N ≤ n := le_max_left _ _
  have hnK : K < n := lt_of_lt_of_le (Nat.lt_succ_self K) (le_max_right _ _)
  have hn1 : 1 ≤ n := hN.trans hnN
  have hboth : (n^E : ℕ∞) ≤ (L : ℕ∞)*((C : ℕ∞)*((C*n : ℕ) : ℕ∞)^D) :=
    (hlo n hnN).trans (mul_le_mul_right (hup n hn1) _)
  have hnumerical : n^E ≤ K*n^D := by
    have hboth' : (n^E : ℕ∞) ≤ ((L*C*(C*n)^D : ℕ) : ℕ∞) := by
      simpa only [polynomialGrowth, Nat.cast_mul, Nat.cast_pow, mul_assoc] using hboth
    have hnat : n^E ≤ L*C*(C*n)^D := by exact_mod_cast hboth'
    simpa [K, mul_pow, mul_assoc] using hnat
  have hlarge : n*n^D ≤ n^E := by
    simpa [pow_succ, mul_comm] using Nat.pow_le_pow_right hn1 (show D+1 ≤ E by omega)
  have hcancel : n ≤ K := Nat.le_of_mul_le_mul_right
    (hlarge.trans hnumerical) (pow_pos (by omega : 0<n) D)
  omega

/-- Comparison with a real polynomial exponent for the actual finite-valued
growth function. Finiteness is explicit so `toNat` cannot erase infinity. -/
def RealPolynomialGrowthUpper {G : Type*} [Group G]
    (S : WordGeneratingSet G) (e : ℝ) : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
    conjugacyGrowth S n < ⊤ ∧
    ((conjugacyGrowth S n).toNat : ℝ) ≤ (C : ℝ)*((C*n : ℕ) : ℝ)^e

theorem realPolynomialGrowthUpper_to_growthLE {G : Type*} [Group G]
    (S : WordGeneratingSet G) {e : ℝ} {D : ℕ} (he : e ≤ (D : ℝ))
    (hup : RealPolynomialGrowthUpper S e) :
    GrowthLE (conjugacyGrowth S) (polynomialGrowth D) := by
  obtain ⟨C,hC,hup⟩ := hup
  refine ⟨C,hC,?_⟩
  intro n hn
  obtain ⟨hfin,hbound⟩ := hup n hn
  have hbase : (1 : ℝ) ≤ ((C*n : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ C*n from Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
  have hpow := Real.rpow_le_rpow_of_exponent_le hbase he
  have hmul := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
  rw [Real.rpow_natCast] at hmul
  have hnat : (conjugacyGrowth S n).toNat ≤ C*(C*n)^D := by
    exact_mod_cast hbound.trans hmul
  rw [← ENat.natCast_toNat hfin.ne]
  unfold polynomialGrowth
  exact_mod_cast hnat

/-- Every proposed universal real coefficient of the square of the Hirsch
length fails on a member of the explicit family, in every finite word metric. -/
theorem no_universal_quadratic_exponent (A : ℝ) :
    ∃ d : ℕ, 2 ≤ d ∧
      ∀ S : WordGeneratingSet (ManuscriptGroup (4*d)),
        ¬ RealPolynomialGrowthUpper S (A*((8*d : ℕ) : ℝ)^2) := by
  obtain ⟨C,hC⟩ := exists_nat_ge A
  let d := 64*C+2
  have hd : 2 ≤ d := by dsimp [d]; omega
  refine ⟨d,hd,?_⟩
  intro S hup
  have he : A*((8*d : ℕ) : ℝ)^2 ≤ ((C*(8*d)^2 : ℕ) : ℝ) := by
    push_cast
    exact mul_le_mul_of_nonneg_right hC (sq_nonneg _)
  have hdegree : C*(8*d)^2 < 3*d^2*(d+1) := by
    have hdpos : 0 < d := by omega
    have hdC : 64*C < 3*(d+1) := by dsimp [d]; omega
    have hmult := Nat.mul_lt_mul_of_pos_right hdC (pow_pos hdpos 2)
    nlinarith
  exact polynomialConjugacyLower_not_growthLE S hdegree
    (cubicFamily_polynomialConjugacyLower d hd S)
    (realPolynomialGrowthUpper_to_growthLE S he hup)

end NilpotentConjugacy
