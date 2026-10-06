import NilpotentConjugacy.ConjugacyDepth
import NilpotentConjugacy.WordLength
import Mathlib.Data.Nat.Log
import Mathlib.Data.ENat.Basic

/-! The actual conjugacy-separation growth function in an actual finite word
metric, and its passage from integer geometric scales to all large radii.
-/

namespace NilpotentConjugacy

universe u
variable {G : Type u} [Group G]

/-- Nonconjugate pairs in the word ball of radius n. -/
def WordBallPair (S : WordGeneratingSet G) (n : ℕ) :=
  {ab : G × G // wordLength S ab.1 ≤ n ∧ wordLength S ab.2 ≤ n ∧ ¬ IsConj ab.1 ab.2}

/-- The supremum of actual separating depths in the actual word ball, with
value one when the ball contains no nonconjugate pair. -/
noncomputable def conjugacyGrowth (S : WordGeneratingSet G) (n : ℕ) : ℕ∞ :=
  max 1 (⨆ ab : WordBallPair S n, conjugacyDepth ab.val.1 ab.val.2)

theorem one_le_conjugacyGrowth (S : WordGeneratingSet G) (n : ℕ) :
    1 ≤ conjugacyGrowth S n := le_max_left _ _

theorem conjugacyDepth_le_growth (S : WordGeneratingSet G) {n : ℕ} {a b : G}
    (ha : wordLength S a ≤ n) (hb : wordLength S b ≤ n) (hab : ¬ IsConj a b) :
    conjugacyDepth a b ≤ conjugacyGrowth S n := by
  exact le_max_of_le_right (le_iSup
    (fun ab : WordBallPair S n => conjugacyDepth ab.val.1 ab.val.2) ⟨(a,b), ha,hb,hab⟩)

theorem conjugacyGrowth_mono (S : WordGeneratingSet G) : Monotone (conjugacyGrowth S) := by
  intro n m hnm
  apply max_le_max le_rfl
  apply iSup_le
  intro ab
  exact le_iSup_of_le ⟨ab.val, ab.property.1.trans hnm,
    ab.property.2.1.trans hnm, ab.property.2.2⟩ le_rfl

/-- Generator comparison applies to the actual growth functions. -/
theorem conjugacyGrowth_compare (S T : WordGeneratingSet G) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ n, conjugacyGrowth S n ≤ conjugacyGrowth T (C * n) := by
  obtain ⟨C, hC, hlen⟩ := wordLength_compare S T
  refine ⟨C, hC, fun n => ?_⟩
  apply max_le
  · exact one_le_conjugacyGrowth _ _
  · apply iSup_le
    intro ab
    exact conjugacyDepth_le_growth T
      ((hlen ab.val.1).trans (Nat.mul_le_mul_left C ab.property.1))
      ((hlen ab.val.2).trans (Nat.mul_le_mul_left C ab.property.2.1)) ab.property.2.2

/-- Conjugacy separability quantified over actual finite group quotients. -/
def ConjugacySeparable (G : Type u) [Group G] : Prop :=
  ∀ a b : G, ¬ IsConj a b → Nonempty (SeparatingQuotient a b)

theorem finite_wordBallPair (S : WordGeneratingSet G) (n : ℕ) : Finite (WordBallPair S n) := by
  have h := (finite_wordLength_ball S n).prod (finite_wordLength_ball S n)
  apply Set.Finite.to_subtype
  exact h.subset (fun ab hab => ⟨hab.1, hab.2.1⟩)

/-- Finite word balls and conjugacy separability make actual growth finite. -/
theorem conjugacyGrowth_lt_top (S : WordGeneratingSet G) (hG : ConjugacySeparable G)
    (n : ℕ) : conjugacyGrowth S n < ⊤ := by
  classical
  let : Finite (WordBallPair S n) := finite_wordBallPair S n
  let : Fintype (WordBallPair S n) := Fintype.ofFinite _
  let B : ℕ := ∑ ab : WordBallPair S n, (conjugacyDepth ab.val.1 ab.val.2).toNat
  have hb : conjugacyGrowth S n ≤ (max 1 B : ℕ) := by
    apply max_le
    · exact_mod_cast (le_max_left 1 B)
    · apply iSup_le
      intro ab
      have hf := (conjugacyDepth_lt_top_iff _ _).mpr (hG _ _ ab.property.2.2)
      calc
        conjugacyDepth ab.val.1 ab.val.2 =
            ((conjugacyDepth ab.val.1 ab.val.2).toNat : ℕ∞) :=
          (ENat.natCast_toNat hf.ne).symm
        _ ≤ (B : ℕ∞) := by
          exact_mod_cast (Finset.single_le_sum
            (f:=fun x : WordBallPair S n => (conjugacyDepth x.val.1 x.val.2).toNat)
            (fun x _ => Nat.zero_le _) (Finset.mem_univ ab))
        _ ≤ (max 1 B : ℕ) := by exact_mod_cast (le_max_right 1 B)
  exact hb.trans_lt (ENat.natCast_lt_top _)

/-- A positive constant polynomial lower bound, expressed in extended naturals
so the definition also applies before conjugacy separability is established. -/
def PolynomialConjugacyLower (S : WordGeneratingSet G) (E : ℕ) : Prop :=
  ∃ C N : ℕ, 1 ≤ C ∧ 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n → (n ^ E : ℕ∞) ≤ (C : ℕ∞) * conjugacyGrowth S n

/-- Integer geometric scales bracket every radius above the first scale. -/
theorem nat_geometric_bracket {C p n : ℕ} (hC : 0 < C) (hp : 1 < p)
    (hn : C * p ≤ n) :
    ∃ k : ℕ, 1 ≤ k ∧ C * p ^ k ≤ n ∧ n < C * p ^ (k + 1) := by
  have hdiv : p ≤ n / C := (Nat.le_div_iff_mul_le hC).2 (by simpa [mul_comm] using hn)
  let k := Nat.log p (n / C)
  have hk : 1 ≤ k := Nat.log_pos hp hdiv
  have hpow : p ^ k ≤ n / C := Nat.pow_log_le_self p (by omega)
  have hlo : C * p ^ k ≤ n := by
    simpa [mul_comm] using (Nat.le_div_iff_mul_le hC).1 hpow
  have hhi : n / C < p ^ (k + 1) := Nat.lt_pow_succ_log_self hp _
  refine ⟨k, hk, hlo, ?_⟩
  simpa [mul_comm] using (Nat.div_lt_iff_lt_mul hC).1 hhi

/-- Actual nonconjugate pairs at all integer geometric scales give a polynomial
lower bound at every sufficiently large integer radius. The depth premise
quantifies over all actual finite separating group quotients. -/
theorem polynomialConjugacyLower_of_geometric_pairs (S : WordGeneratingSet G)
    {C p E : ℕ} (hC : 0 < C) (hp : 1 < p)
    (hpairs : ∀ k : ℕ, 1 ≤ k → ∃ a b : G,
      wordLength S a ≤ C * p ^ k ∧ wordLength S b ≤ C * p ^ k ∧
      ¬ IsConj a b ∧ ∀ q : FiniteGroupQuotient G,
        ¬ IsConj (q.hom a) (q.hom b) → p ^ (k * E) ≤ Nat.card q.Carrier) :
    PolynomialConjugacyLower S E := by
  refine ⟨(C * p) ^ E, C * p, one_le_pow₀ (by nlinarith), by nlinarith, ?_⟩
  intro n hn
  obtain ⟨k, hk, hlo, hhi⟩ := nat_geometric_bracket hC hp hn
  obtain ⟨a, b, ha, hb, hab, hdepth⟩ := hpairs k hk
  have hg : (p ^ (k * E) : ℕ∞) ≤ conjugacyGrowth S n :=
    (le_conjugacyDepth hdepth).trans (conjugacyDepth_le_growth S (ha.trans hlo) (hb.trans hlo) hab)
  have hnle : n ≤ (C * p) * p ^ k := by
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using Nat.le_of_lt hhi
  have hnpow : n ^ E ≤ (C * p) ^ E * p ^ (k * E) := by
    simpa [mul_pow, pow_mul] using Nat.pow_le_pow_left hnle E
  calc
    (n ^ E : ℕ∞) ≤ (((C * p) ^ E * p ^ (k * E) : ℕ) : ℕ∞) := by exact_mod_cast hnpow
    _ = (((C * p) ^ E : ℕ) : ℕ∞) * (p ^ (k * E) : ℕ∞) := by norm_cast
    _ ≤ (((C * p) ^ E : ℕ) : ℕ∞) * conjugacyGrowth S n := by gcongr

/-- The lower bound is witnessed at every large radius by a pair whose actual
separating depth is finite. Thus it does not rely on any infinite depths. -/
def FiniteDepthPolynomialWitness (S : WordGeneratingSet G) (E : ℕ) : Prop :=
  ∃ C N : ℕ, 1 ≤ C ∧ 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∃ a b : G,
    wordLength S a ≤ n ∧ wordLength S b ≤ n ∧ ¬ IsConj a b ∧
    conjugacyDepth a b < ⊤ ∧ (n ^ E : ℕ∞) ≤ (C : ℕ∞) * conjugacyDepth a b

theorem FiniteDepthPolynomialWitness.lowerBound (S : WordGeneratingSet G) (E : ℕ)
    (h : FiniteDepthPolynomialWitness S E) : PolynomialConjugacyLower S E := by
  obtain ⟨C,N,hC,hN,h⟩ := h
  refine ⟨C,N,hC,hN,fun n hn => ?_⟩
  obtain ⟨a,b,ha,hb,hab,_,hdepth⟩ := h n hn
  exact hdepth.trans (mul_le_mul_right (conjugacyDepth_le_growth S ha hb hab) _)

theorem finiteDepthPolynomialWitness_of_geometric_pairs (S : WordGeneratingSet G)
    {C p E : ℕ} (hC : 0 < C) (hp : 1 < p)
    (hpairs : ∀ k : ℕ, 1 ≤ k → ∃ a b : G,
      wordLength S a ≤ C*p^k ∧ wordLength S b ≤ C*p^k ∧ ¬ IsConj a b ∧
      conjugacyDepth a b < ⊤ ∧ (p^(k*E) : ℕ∞) ≤ conjugacyDepth a b) :
    FiniteDepthPolynomialWitness S E := by
  refine ⟨(C*p)^E,C*p,one_le_pow₀ (by nlinarith),by nlinarith,?_⟩
  intro n hn
  obtain ⟨k,hk,hlo,hhi⟩ := nat_geometric_bracket hC hp hn
  obtain ⟨a,b,ha,hb,hab,hfin,hd⟩ := hpairs k hk
  refine ⟨a,b,ha.trans hlo,hb.trans hlo,hab,hfin,?_⟩
  have hnle : n ≤ (C*p)*p^k := by
    simpa [pow_succ,mul_assoc,mul_left_comm,mul_comm] using Nat.le_of_lt hhi
  have hnpow : n^E ≤ (C*p)^E*p^(k*E) := by
    simpa [mul_pow,pow_mul] using Nat.pow_le_pow_left hnle E
  calc
    (n^E : ℕ∞) ≤ (((C*p)^E*p^(k*E) : ℕ) : ℕ∞) := by exact_mod_cast hnpow
    _ = (((C*p)^E : ℕ) : ℕ∞) * (p^(k*E) : ℕ∞) := by norm_cast
    _ ≤ (((C*p)^E : ℕ) : ℕ∞) * conjugacyDepth a b := mul_le_mul_right hd _

end NilpotentConjugacy
