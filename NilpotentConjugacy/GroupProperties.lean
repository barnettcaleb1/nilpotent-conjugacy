import NilpotentConjugacy.IntegralGroupAction
import NilpotentConjugacy.AffineGroup

namespace NilpotentConjugacy
open scoped BigOperators commutatorElement

/-- All terms after the linear term in the factorial-cleared exponential have
strictly larger lower-diagonal gap. -/
theorem integralExponential_remainder_gap {m d : ℕ} (hm : 2 ≤ m) (hd : 1 ≤ d)
    (A : Matrix (Fin m) (Fin m) ℤ) (hA : LowerGap d A) :
    LowerGap (d + 1) (integralExponential m A - 1 - (m.factorial : ℤ) • A) := by
  let f : ℕ → Matrix (Fin m) (Fin m) ℤ :=
    fun k => ((m.factorial ^ k / k.factorial : ℕ) : ℤ) • A ^ k
  have he : integralExponential m A - 1 - (m.factorial : ℤ) • A =
      ∑ k ∈ Finset.Ico 2 m, f k := by
    have hh := Finset.sum_range_add_sum_Ico f hm
    change (∑ k ∈ Finset.range m, f k) - 1 - (m.factorial : ℤ) • A = _
    rw [← hh]
    simp [f, Finset.sum_range_succ]
    abel
  rw [he]
  apply gap_sum
  intro k hk
  apply gap_smul
  exact gap_mono (gap_pow hA k) (by have := (Finset.mem_Ico.mp hk).1; nlinarith)

/-- The actual factorial-cleared exponential has trivial kernel on strictly
lower triangular integer matrices. -/
theorem integralExponential_eq_one_iff {m : ℕ} (hm : 2 ≤ m)
    (A : Matrix (Fin m) (Fin m) ℤ) (hA : LowerGap 1 A) :
    integralExponential m A = 1 ↔ A = 0 := by
  constructor
  · intro he
    have hgap : ∀ d : ℕ, LowerGap (d + 1) A := by
      intro d
      induction d with
      | zero => exact hA
      | succ d ih =>
        have h := integralExponential_remainder_gap hm (by omega) A ih
        rw [he, sub_self, zero_sub] at h
        intro i j hij
        have hh := h i j hij
        change -((m.factorial : ℤ) * A i j) = 0 at hh
        have hM : (m.factorial : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
        exact (mul_eq_zero.mp (neg_eq_zero.mp hh)).resolve_left hM
    exact gap_eq_zero (hgap m) (by omega)
  · rintro rfl
    apply ratMatrix_injective m
    simp [ratMatrix_integralExponential m 0 gap_zero]

/-- The first lower diagonal contains only the linear term of the exponential. -/
theorem integralExponential_first_subdiagonal {m : ℕ} (hm : 2 ≤ m)
    (A : Matrix (Fin m) (Fin m) ℤ) (hA : LowerGap 1 A)
    (i j : Fin m) (hij : i.val = j.val + 1) :
    integralExponential m A i j = (m.factorial : ℤ) * A i j := by
  have h := integralExponential_remainder_gap hm (by omega : 1 ≤ 1) A hA i j (by omega)
  have hne : i ≠ j := by intro h; have := congrArg Fin.val h; omega
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    hne, if_false, sub_zero] at h
  exact sub_eq_zero.mp h

theorem weightedExponential_first_subdiagonal {m : ℕ} (a : ℤ)
    (i j : Fin m) (hij : i.val = j.val + 1) :
    weightedExponential m a i j = a * (j.val + 1) := by
  have hm : 1 < m := by omega
  simp only [weightedExponential, Matrix.sum_apply]
  rw [Finset.sum_eq_single 1]
  · simp [shiftBand, hij]
  · intro k _ hk
    have hne : i.val ≠ j.val + k := by omega
    simp [shiftBand, hne]
  · simp [hm]

theorem latticePolynomial_first_subdiagonal {m : ℕ} (hm : 2 ≤ m)
    (c : Fin (m - 1) → ℤ) (i j : Fin m) (hij : i.val = j.val + 1) :
    latticePolynomial m c i j = c ⟨0, by omega⟩ := by
  simp only [latticePolynomial, Matrix.sum_apply, Matrix.smul_apply, shiftJ_pow, shiftBand]
  rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · simp [hij]
  · intro k _ hk
    have hk0 : k.val ≠ 0 := by intro he; exact hk (Fin.ext he)
    have hne : i.val ≠ j.val + (k.val + 1) := by omega
    simp [hne]
  · simp

theorem lowerUnipotent_product_first_subdiagonal {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) ℤ)
    (hA : LowerGap 1 (A - 1)) (hB : LowerGap 1 (B - 1))
    (i j : Fin m) (hij : i.val = j.val + 1) :
    (A * B) i j = A i j + B i j := by
  have hgap : LowerGap 2 ((A * B - 1) - (A - 1) - (B - 1)) := by
    convert lowerGap_mul hA hB using 1
    noncomm_ring
  have h := hgap i j (by omega)
  have hne : i ≠ j := by intro he; have := congrArg Fin.val he; omega
  simp only [Matrix.sub_apply, Matrix.one_apply, hne, if_false, sub_zero] at h
  linarith

/-- Two entries of the first lower diagonal distinguish the cyclic coordinate
from the constant first lower diagonal of a polynomial in J. -/
theorem manuscriptRho_first_subdiagonal {m : ℕ} (hm : 2 ≤ m)
    (h : CoefficientGroup m) (i j : Fin m) (hij : i.val = j.val + 1) :
    (manuscriptRho m h).val i j =
      (m.factorial : ℤ) * h.left.toAdd ⟨0, by omega⟩ + h.right.toAdd * (j.val + 1) := by
  change (integralExponential m (latticePolynomial m h.left.toAdd) *
    weightedExponential m h.right.toAdd) i j = _
  rw [lowerUnipotent_product_first_subdiagonal _ _
    (lowerGap_integralExponential_sub_one m _ (lowerGap_latticePolynomial m _))
    (lowerGap_weightedExponential_sub_one m _) i j hij,
    integralExponential_first_subdiagonal hm _ (lowerGap_latticePolynomial m _) i j hij,
    latticePolynomial_first_subdiagonal hm _ i j hij,
    weightedExponential_first_subdiagonal _ i j hij]

/-- Faithfulness of the paper's exact integral representation. -/
theorem manuscriptRhoHom_injective {m : ℕ} (hm : 3 ≤ m) :
    Function.Injective (manuscriptRhoHom m) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro h hh
  have hr : manuscriptRho m h = 1 := hh
  have h1 := manuscriptRho_first_subdiagonal (by omega : 2 ≤ m) h
    ⟨1, by omega⟩ ⟨0, by omega⟩ (by rfl)
  have h2 := manuscriptRho_first_subdiagonal (by omega : 2 ≤ m) h
    ⟨2, by omega⟩ ⟨1, by omega⟩ (by rfl)
  rw [hr] at h1 h2
  norm_num [Matrix.one_apply, Fin.ext_iff] at h1 h2
  have ha : h.right.toAdd = 0 := by linarith
  have he : integralExponential m (latticePolynomial m h.left.toAdd) = 1 := by
    have hmat := congrArg Units.val hr
    change integralExponential m (latticePolynomial m h.left.toAdd) *
      weightedExponential m h.right.toAdd = 1 at hmat
    simpa only [ha, weightedExponential_zero, mul_one] using hmat
  have hp := (integralExponential_eq_one_iff (by omega : 2 ≤ m) _
    (lowerGap_latticePolynomial m _)).mp he
  have hc : h.left.toAdd = 0 := latticePolynomial_injective m (by simpa using hp)
  apply Subgroup.mem_bot.mpr
  apply SemidirectProduct.ext
  · exact congrArg Multiplicative.ofAdd hc
  · exact congrArg Multiplicative.ofAdd ha

/-- The exact representation lands in the concrete generated matrix subgroup. -/
noncomputable def manuscriptRhoToGenerated (m : ℕ) (hm : 0 < m) :
    CoefficientGroup m →* GeneratedActingGroup m :=
  (manuscriptRhoHom m).codRestrict _ (manuscriptRho_mem_generatedActingGroup m hm)

theorem manuscriptRhoHom_range (m : ℕ) (hm : 0 < m) :
    (manuscriptRhoHom m).range = GeneratedActingGroup m := by
  apply le_antisymm
  · rintro U ⟨h, rfl⟩
    exact manuscriptRho_mem_generatedActingGroup m hm h
  · apply (Subgroup.closure_le _).mpr
    rintro U ⟨j, rfl⟩
    by_cases hj : j.val = 0
    · refine ⟨SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)), ?_⟩
      rw [manuscriptRhoHom, SemidirectProduct.lift_inr]
      change weightedExponentialHom m (Multiplicative.ofAdd 1) = _
      simp [actingMatrixGenerator, hj, weightedExponentialHom]
    · let k : Fin (m - 1) := ⟨j.val - 1, by have := j.isLt; omega⟩
      refine ⟨SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single k (1 : ℤ))), ?_⟩
      rw [manuscriptRhoHom, SemidirectProduct.lift_inl]
      change latticeExponential m (Pi.single k 1) = _
      apply Units.ext
      change integralExponential m (latticePolynomial m (Pi.single k 1)) = _
      rw [latticePolynomial_single, one_smul]
      have hk : k.val + 1 = j.val := by dsimp [k]; omega
      simp [actingMatrixGenerator, hj, integralExponentialUnit, hk]

theorem manuscriptRhoToGenerated_bijective {m : ℕ} (hm : 3 ≤ m) :
    Function.Bijective (manuscriptRhoToGenerated m (by omega)) := by
  constructor
  · intro h k he
    apply manuscriptRhoHom_injective hm
    exact congrArg Subtype.val he
  · intro U
    have hu : U.val ∈ (manuscriptRhoHom m).range := by
      rw [manuscriptRhoHom_range m (by omega)]
      exact U.property
    obtain ⟨h, hh⟩ := hu
    exact ⟨h, Subtype.ext hh⟩

/-- Exact equivalence of the two acting-group models. -/
noncomputable def coefficientGeneratedEquiv {m : ℕ} (hm : 3 ≤ m) :
    CoefficientGroup m ≃* GeneratedActingGroup m :=
  MulEquiv.ofBijective (manuscriptRhoToGenerated m (by omega))
    (manuscriptRhoToGenerated_bijective hm)

/-- The explicit correspondence from the manuscript group to the generated
integral matrix model fixes every vector of the normal integer lattice. -/
noncomputable def manuscriptGeneratedEquiv {m : ℕ} (hm : 3 ≤ m) :
    ManuscriptGroup m ≃* IntegralGeneratedGroup m :=
  SemidirectProduct.congr (MulEquiv.refl _) (coefficientGeneratedEquiv hm)
    (by intro h; rfl)

instance manuscriptGroup_torsionFree (m : ℕ) [Fact (3 ≤ m)] :
    IsMulTorsionFree (ManuscriptGroup m) :=
  Function.Injective.isMulTorsionFree (manuscriptGeneratedEquiv (Fact.out : 3 ≤ m)).toMonoidHom
    (manuscriptGeneratedEquiv (Fact.out : 3 ≤ m)).injective

instance manuscriptGroup_nilpotent (m : ℕ) [Fact (3 ≤ m)] :
    Group.IsNilpotent (ManuscriptGroup m) :=
  Group.nilpotent_of_mulEquiv (manuscriptGeneratedEquiv (Fact.out : 3 ≤ m)).symm

theorem manuscriptGroup_nilpotencyClass_le {m : ℕ} (hm : 3 ≤ m) :
    Group.nilpotencyClass (ManuscriptGroup m) ≤ m := by
  calc
    Group.nilpotencyClass (ManuscriptGroup m) ≤
        Group.nilpotencyClass (IntegralGeneratedGroup m) :=
      Group.nilpotencyClass_le_of_surjective (manuscriptGeneratedEquiv hm).symm.toMonoidHom
        (manuscriptGeneratedEquiv hm).symm.surjective
    _ ≤ m := integralGeneratedGroup_nilpotencyClass_le m

/-- Powers have the same leading lower diagonal when their linear terms agree. -/
theorem gap_pow_compare {R : Type*} [CommRing R] {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) R)
    (hA : LowerGap 1 A) (hB : LowerGap 1 B) (hAB : LowerGap 2 (A - B)) (n : ℕ) :
    LowerGap (n + 1) (A ^ n - B ^ n) := by
  induction n with
  | zero => simpa using (gap_zero (R := R) (m := m) (d := 1))
  | succ n ih =>
    have h1 := lowerGap_mul ih hA
    have h2 := lowerGap_mul (lowerGap_pow hB n) hAB
    have hsum := gap_add h1 (by simpa [Nat.add_assoc] using h2)
    convert hsum using 1
    simp only [pow_succ]
    noncomm_ring

theorem weightedExponential_remainder_gap (m : ℕ) (a : ℤ) :
    LowerGap 2 (weightedExponential m a - 1 - a • shiftY m) := by
  intro i j hij
  by_cases hij1 : i.val < j.val + 1
  · have h := lowerGap_weightedExponential_sub_one m a i j hij1
    have hY := (lowerGap_shiftY (R := ℤ) (m := m)) i j hij1
    change (weightedExponential m a - 1) i j - a * shiftY m i j = 0
    rw [h, hY, mul_zero, sub_self]
  · have he : i.val = j.val + 1 := by omega
    have hne : i ≠ j := by intro h; have := congrArg Fin.val h; omega
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      weightedExponential_first_subdiagonal a i j he, Matrix.one_apply, hne,
      if_false, sub_zero, shiftY, shiftBand, he, if_true]
    ring

/-- The large power of the concrete unweighted action has exactly the leading
term from the paper, with every higher term killed by the dimension. -/
theorem integralExponential_shiftJ_top_power {m : ℕ} (hm : 2 ≤ m) :
    (integralExponential m (shiftJ m) - 1) ^ (m - 1) =
      (m.factorial : ℤ) ^ (m - 1) • (shiftJ m : Matrix (Fin m) (Fin m) ℤ) ^ (m - 1) := by
  have h := gap_pow_compare (integralExponential m (shiftJ m) - 1)
    ((m.factorial : ℤ) • shiftJ m)
    (lowerGap_integralExponential_sub_one m _ lowerGap_shiftJ)
    (gap_smul _ lowerGap_shiftJ)
    (integralExponential_remainder_gap hm (by omega) _ lowerGap_shiftJ) (m - 1)
  have he := sub_eq_zero.mp (gap_eq_zero h (by omega))
  simpa only [smul_pow] using he

theorem weightedExponential_top_power {m : ℕ} (hm : 1 ≤ m) :
    (weightedExponential m 1 - 1) ^ (m - 1) =
      (shiftY m : Matrix (Fin m) (Fin m) ℤ) ^ (m - 1) := by
  have h := gap_pow_compare (weightedExponential m 1 - 1) (shiftY m)
    (lowerGap_weightedExponential_sub_one m 1) lowerGap_shiftY
    (by simpa only [one_smul] using weightedExponential_remainder_gap m 1) (m - 1)
  exact sub_eq_zero.mp (gap_eq_zero h (by omega))

end NilpotentConjugacy
