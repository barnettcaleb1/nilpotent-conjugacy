import NilpotentConjugacy.JordanCompression
import NilpotentConjugacy.IntegralGroupAction

namespace NilpotentConjugacy
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Matrices acting on the integer lattice, as a ring of additive endomorphisms. -/
def matrixAddEnd (m : ℕ) : Matrix (Fin m) (Fin m) ℤ →+* AddMonoid.End (Fin m → ℤ) where
  toFun M := M.mulVecLin.toAddMonoidHom
  map_one' := by ext v i; change ((1 : Matrix (Fin m) (Fin m) ℤ).mulVec v) i = v i; simp
  map_mul' M N := by ext v i; exact congrFun (Matrix.mulVec_mulVec v M N).symm i
  map_zero' := by ext v i; change ((0 : Matrix (Fin m) (Fin m) ℤ).mulVec v) i = 0; simp
  map_add' M N := by ext v i; exact congrFun (Matrix.add_mulVec M N v) i

@[simp] theorem matrixAddEnd_apply (m : ℕ) (M : Matrix (Fin m) (Fin m) ℤ)
    (v : Fin m → ℤ) : matrixAddEnd m M v = M.mulVec v := rfl

/-- The actual integral weighted-exponential automorphism. -/
noncomputable def weightedAut (m : ℕ) : AddAut (Fin m → ℤ) :=
  AddEquiv.toMultiplicative.symm (integerMatrixAction m (weightedExponentialUnit m 1))

/-- Its difference from the identity, in the integral endomorphism ring. -/
noncomputable def weightedDifference (m : ℕ) : AddMonoid.End (Fin m → ℤ) :=
  matrixAddEnd m (weightedExponential m 1 - 1)

theorem weightedAut_eq (m : ℕ) :
    automorphismEnd (weightedAut m) = 1 + weightedDifference m := by
  ext v i
  change ((weightedExponential m 1).mulVec v) i = v i + ((weightedExponential m 1 - 1).mulVec v) i
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  change _ = v i + (((weightedExponential m 1).mulVec v) i - v i)
  omega

theorem weightedDifference_nilpotent (m : ℕ) : weightedDifference m ^ m = 0 := by
  rw [weightedDifference, ← map_pow, lowerGap_nilpotent (lowerGap_weightedExponential_sub_one m 1), map_zero]

theorem weightedDifference_first_diagonal (m : ℕ) (i k : Fin m)
    (hi : i.val = k.val + 1) :
    (weightedExponential m 1 - 1) i k = (k.val + 1 : ℤ) := by
  have hik : i ≠ k := by intro h; subst k; omega
  simp only [Matrix.sub_apply, Matrix.one_apply, if_neg hik, sub_zero,
    weightedExponential, Matrix.sum_apply]
  rw [Finset.sum_eq_single 1]
  · simp [shiftBand, hi]
  · intro b _ hb
    have hne : i.val ≠ k.val + b := by omega
    simp [shiftBand, hne]
  · intro hb
    have hm : 1 < m := by omega
    exact False.elim (hb (Finset.mem_range.mpr hm))

/-- The first nonzero entry of the `j`th difference-power is exactly `j!`. -/
theorem weightedDifference_power_leading (m j : ℕ) (i z : Fin m)
    (hi : i.val = j) (hz : z.val = 0) :
    ((weightedExponential m 1 - 1) ^ j) i z = (j.factorial : ℤ) := by
  induction j generalizing i with
  | zero =>
    have hiz : i = z := Fin.ext (by omega)
    simp [hiz]
  | succ j ih =>
    let k : Fin m := ⟨j, by omega⟩
    rw [pow_succ', Matrix.mul_apply, Finset.sum_eq_single k]
    · rw [weightedDifference_first_diagonal m i k (by dsimp [k]; omega), ih k rfl,
        Nat.factorial_succ]
      push_cast
      rfl
    · intro b _ hbk
      by_cases hb : b.val < j
      · rw [lowerGap_pow (lowerGap_weightedExponential_sub_one m 1) j b z (by omega), mul_zero]
      · have hne : b.val ≠ j := by intro h; exact hbk (Fin.ext h)
        rw [lowerGap_weightedExponential_sub_one m 1 i b (by omega), zero_mul]
    · simp

@[simp] theorem weighted_chain_coordinate (m j : ℕ) (z : Fin m) (i : Fin m) :
    (weightedDifference m ^ j) (coordinateVector ℤ m z.val) i =
      ((weightedExponential m 1 - 1) ^ j) i z := by
  rw [weightedDifference, ← map_pow, matrixAddEnd_apply, coordinateVector_fin z]
  simp [Matrix.mulVec_single]

/-- The chain has no coordinate below its weight. -/
theorem weighted_chain_below (m j : ℕ) (z i : Fin m) (hz : z.val = 0)
    (hi : i.val < j) :
    (weightedDifference m ^ j) (coordinateVector ℤ m z.val) i = 0 := by
  rw [weighted_chain_coordinate]
  exact lowerGap_pow (lowerGap_weightedExponential_sub_one m 1) j i z (by omega)

/-- The chain's leading coordinate is a nonzero integer factorial. -/
theorem weighted_chain_leading (m : ℕ) (z i : Fin m) (hz : z.val = 0) :
    (weightedDifference m ^ i.val) (coordinateVector ℤ m z.val) i = (i.val.factorial : ℤ) := by
  rw [weighted_chain_coordinate]
  exact weightedDifference_power_leading m i.val i z rfl hz

theorem fixed_coefficient_radius (K B j k : ℕ)
    (hB : 1 ≤ B) (hj : j ≤ k) (hk : 1 ≤ k) :
    K * B ^ j ≤ ((K + 1) * B) ^ k := by
  have hK : K ≤ (K + 1) ^ k :=
    (Nat.le_succ K).trans (le_self_pow (by omega) (by omega))
  calc
    K * B ^ j ≤ (K + 1) ^ k * B ^ k :=
      Nat.mul_le_mul hK (Nat.pow_le_pow_right hB hj)
    _ = ((K + 1) * B) ^ k := (mul_pow _ _ _).symm

private theorem mapped_normal_sum_rep {A I G : Type*} [AddCommGroup A] [Group G]
    (α : AddAut A) (F : CyclicSemidirect α →* G) {S : Set G}
    (s : Finset I) (f : I → A) (L : ℕ)
    (hf : ∀ i ∈ s, WordRep S L (F (normalElement α (f i)))) :
    WordRep S (s.card * L) (F (normalElement α (∑ i ∈ s, f i))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [normalElement] using WordRep.one S
  | @insert i s hi ih =>
    have hfi := hf i (by simp)
    have hrest := ih (fun k hk => hf k (by simp [hk]))
    rw [Finset.sum_insert hi, normalElement_add, map_mul, Finset.card_insert_of_notMem hi]
    simpa [Nat.add_mul, Nat.add_comm] using hfi.mul hrest

/-- Every standard integer coordinate has its correct weight in the weighted
exponential action. The proof clears the nonzero factorial leading coefficient
by the proved fixed-power transfer, rather than assuming rational compression. -/
theorem weighted_coordinate_compression_rep {G : Type*} [Group G]
    (m : ℕ) (F : CyclicSemidirect (weightedAut m) →* G) (S : WordGeneratingSet G)
    (i : Fin m) :
    ∃ C : ℕ, ∀ B : ℕ, 1 ≤ B → ∀ a : ℤ, a.natAbs ≤ B ^ (i.val + 1) →
      WordRep S.generators (C * B)
        (F (normalElement (weightedAut m) (a • coordinateVector ℤ m i.val))) := by
  classical
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  let z : Fin m := ⟨0, hm⟩
  let N := weightedDifference m
  let e := coordinateVector ℤ m 0
  suffices h : ∀ d : ℕ, ∀ i : Fin m, m - 1 - i.val = d →
      ∃ C : ℕ, ∀ B : ℕ, 1 ≤ B → ∀ a : ℤ, a.natAbs ≤ B ^ (i.val + 1) →
        WordRep S.generators (C * B)
          (F (normalElement (weightedAut m) (a • coordinateVector ℤ m i.val))) from
    h (m - 1 - i.val) i rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro i hdi
    have hCs : ∀ k : Fin m, ∃ C : ℕ, ∀ B : ℕ, 1 ≤ B → ∀ a : ℤ,
        a.natAbs ≤ B ^ (k.val + 1) → i.val < k.val →
        WordRep S.generators (C * B)
          (F (normalElement (weightedAut m) (a • coordinateVector ℤ m k.val))) := by
      intro k
      by_cases hik : i.val < k.val
      · obtain ⟨C, hC⟩ := ih (m - 1 - k.val) (by omega) k rfl
        exact ⟨C, fun B hB a ha _ => hC B hB a ha⟩
      · exact ⟨0, fun _ _ _ _ hik' => (hik hik').elim⟩
    choose Cs hCs using hCs
    let Cmax := Finset.univ.sup Cs
    let v := (N ^ i.val) e
    let K := Finset.univ.sup (fun k : Fin m => (v k).natAbs)
    let R := K + 1
    obtain ⟨Cbase, _, hbase⟩ := nilpotent_chain_compression_map (weightedAut m) F S N
      (weightedAut_eq m) e m (weightedDifference_nilpotent m) (i.val + 1)
      (by omega) (by omega)
    let g := F (normalElement (weightedAut m) (coordinateVector ℤ m i.val))
    let D := i.val.factorial
    have hpre : ∀ B : ℕ, 1 ≤ B → ∀ a : ℤ, a.natAbs ≤ B ^ (i.val + 1) →
        WordRep S.generators ((Cbase + m * Cmax * R) * B) ((g ^ D) ^ a) := by
      intro B hB a ha
      let corr : Fin m → Fin m → ℤ := fun k =>
        if i.val < k.val then (-(a * v k)) • coordinateVector ℤ m k.val else 0
      have hcorr : ∀ k ∈ (Finset.univ : Finset (Fin m)),
          WordRep S.generators (Cmax * (R * B))
            (F (normalElement (weightedAut m) (corr k))) := by
        intro k _
        by_cases hik : i.val < k.val
        · have hcoeff : (-(a * v k)).natAbs ≤ (R * B) ^ (k.val + 1) := by
            have hk : (v k).natAbs ≤ K := Finset.le_sup (f := fun k : Fin m => (v k).natAbs) (by simp)
            rw [Int.natAbs_neg, Int.natAbs_mul]
            calc
              a.natAbs * (v k).natAbs ≤ B ^ (i.val + 1) * K := Nat.mul_le_mul ha hk
              _ = K * B ^ (i.val + 1) := Nat.mul_comm _ _
              _ ≤ (R * B) ^ (k.val + 1) := fixed_coefficient_radius K B _ _ hB (by omega) (by omega)
          have hRB : 1 ≤ R * B := by dsimp [R]; nlinarith
          have hc := hCs k (R * B) hRB (-(a * v k)) hcoeff hik
          have hCmax : Cs k ≤ Cmax := Finset.le_sup (f := Cs) (by simp)
          simpa only [corr, if_pos hik] using hc.mono (Nat.mul_le_mul_right (R * B) hCmax)
        · simp only [corr, if_neg hik]
          change WordRep S.generators (Cmax * (R * B)) (F 1)
          simpa only [map_one] using
            (WordRep.one S.generators).mono (Nat.zero_le (Cmax * (R * B)))
      have hsum : a • v + ∑ k : Fin m, corr k =
          (a * (D : ℤ)) • coordinateVector ℤ m i.val := by
        ext k
        have hleading : v i = (D : ℤ) := weighted_chain_leading m z i rfl
        have hlow : ∀ k : Fin m, k.val < i.val → v k = 0 :=
          fun k hk => weighted_chain_below m i.val z k rfl hk
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
        have hcorrk : (∑ x : Fin m, corr x k) =
            if i.val < k.val then -(a * v k) else 0 := by
          rw [Finset.sum_eq_single k]
          · simp only [corr, ite_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
              coordinateVector, if_true, mul_one]
          · intro b _ hbk
            have hne : k.val ≠ b.val := by intro h; exact hbk (Fin.ext h.symm)
            simp only [corr, ite_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
              coordinateVector, if_neg hne, mul_zero, ite_self]
          · simp
        rw [hcorrk]
        by_cases hki : k = i
        · subst k
          simp [coordinateVector, hleading]
        · have hne : k.val ≠ i.val := by intro h; exact hki (Fin.ext h)
          by_cases hik : i.val < k.val
          · simp [coordinateVector, hne, hik]
          · simp [coordinateVector, hne, hik, hlow k (by omega)]
      have hmain : WordRep S.generators (Cbase * B)
          (F (normalElement (weightedAut m) (a • v))) := by
        apply (wordLength_le_iff _ _ _).1
        simpa only [Nat.add_sub_cancel] using hbase B hB a ha
      have hcor := mapped_normal_sum_rep (weightedAut m) F Finset.univ corr (Cmax * (R * B)) hcorr
      have hw := hmain.mul hcor
      rw [← map_mul, ← normalElement_add, hsum] at hw
      have heq : F (normalElement (weightedAut m) ((a * (D : ℤ)) • coordinateVector ℤ m i.val)) =
          (g ^ D) ^ a := by
        rw [normalElement_zsmul, map_zpow]
        change g ^ (a * (D : ℤ)) = (g ^ D) ^ a
        rw [Int.mul_comm, zpow_mul, zpow_natCast]
      rw [heq] at hw
      convert hw using 1
      simp only [Finset.card_univ, Fintype.card_fin]
      ring
    have hD : 1 ≤ D := Nat.factorial_pos _
    have hfinal := compression_of_power g D (Cbase + m * Cmax * R) (wordLength S g)
      (i.val + 1) hD (wordLength_rep S g) hpre
    refine ⟨Cbase + m * Cmax * R + D * wordLength S g, ?_⟩
    intro B hB a ha
    rw [normalElement_zsmul, map_zpow]
    exact hfinal B hB a ha

theorem weighted_coordinate_compression {G : Type*} [Group G]
    (m : ℕ) (F : CyclicSemidirect (weightedAut m) →* G) (S : WordGeneratingSet G)
    (i : Fin m) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ B : ℕ, 1 ≤ B → ∀ a : ℤ, a.natAbs ≤ B ^ (i.val + 1) →
      wordLength S (F (normalElement (weightedAut m) (a • coordinateVector ℤ m i.val))) ≤ C * B := by
  obtain ⟨C, hC⟩ := weighted_coordinate_compression_rep m F S i
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro B hB a ha
  exact (wordLength_le_iff _ _ _).2 ((hC B hB a ha).mono
    (Nat.mul_le_mul_right B (le_max_right 1 C)))

/-- Map the actual cyclic semidirect product into an arbitrary semidirect
product when its stable letter has the specified action. -/
noncomputable def cyclicSemidirectMap {A H : Type*} [AddCommGroup A] [Group H]
    (φ : H →* MulAut (Multiplicative A)) (t : H) (α : AddAut A)
    (ht : φ t = AddEquiv.toMultiplicative α) :
    CyclicSemidirect α →* SemidirectProduct (Multiplicative A) H φ :=
  SemidirectProduct.map (MonoidHom.id _) (zpowersHom H t) (by
    intro z
    have hact : cyclicAction α z = φ ((zpowersHom H t) z) := by
      change AddEquiv.toMultiplicative α ^ z.toAdd = φ (t ^ z.toAdd)
      rw [map_zpow, ht]
    simpa only [MonoidHom.id_comp, MonoidHom.comp_id] using
      congrArg MulEquiv.toMonoidHom hact)

@[simp] theorem cyclicSemidirectMap_normal {A H : Type*} [AddCommGroup A] [Group H]
    (φ : H →* MulAut (Multiplicative A)) (t : H) (α : AddAut A)
    (ht : φ t = AddEquiv.toMultiplicative α) (v : A) :
    cyclicSemidirectMap φ t α ht (normalElement α v) =
      SemidirectProduct.inl (Multiplicative.ofAdd v) := by
  simp [cyclicSemidirectMap, normalElement]

/-- The coefficient-lattice compression subgroup inside the manuscript group. -/
noncomputable def coefficientCompressionMap (m : ℕ) :
    CyclicSemidirect (weightedAut (m - 1)) →* ManuscriptGroup m :=
  SemidirectProduct.inr.comp
    (cyclicSemidirectMap (coefficientAction m) (Multiplicative.ofAdd (1 : ℤ))
      (weightedAut (m - 1)) (by simp [coefficientAction, weightedAut]))

@[simp] theorem coefficientCompressionMap_normal (m : ℕ) (v : Fin (m - 1) → ℤ) :
    coefficientCompressionMap m (normalElement (weightedAut (m - 1)) v) =
      SemidirectProduct.inr (SemidirectProduct.inl (Multiplicative.ofAdd v)) := by
  unfold coefficientCompressionMap
  rw [MonoidHom.comp_apply, cyclicSemidirectMap_normal]

/-- The normal-vector compression subgroup inside the manuscript group. -/
noncomputable def vectorCompressionMap (m : ℕ) :
    CyclicSemidirect (weightedAut m) →* ManuscriptGroup m :=
  cyclicSemidirectMap (manuscriptAction m)
    (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ))) (weightedAut m)
    (by simp [manuscriptAction, manuscriptRhoHom, weightedExponentialHom, weightedAut])

@[simp] theorem vectorCompressionMap_normal (m : ℕ) (v : Fin m → ℤ) :
    vectorCompressionMap m (normalElement (weightedAut m) v) =
      SemidirectProduct.inl (Multiplicative.ofAdd v) := by
  simp [vectorCompressionMap]

/-- Actual word bound for every weighted coordinate in the acting lattice. -/
theorem coefficient_coordinate_wordLength (m : ℕ) (S : WordGeneratingSet (ManuscriptGroup m))
    (i : Fin (m - 1)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ B : ℕ, 1 ≤ B → ∀ a : ℤ, a.natAbs ≤ B ^ (i.val + 1) →
      wordLength S (SemidirectProduct.inr (SemidirectProduct.inl
        (Multiplicative.ofAdd (a • coordinateVector ℤ (m - 1) i.val)))) ≤ C * B := by
  simpa only [coefficientCompressionMap_normal] using
    weighted_coordinate_compression (m - 1) (coefficientCompressionMap m) S i

/-- Actual word bound for every weighted coordinate of the normal vector lattice. -/
theorem vector_coordinate_wordLength (m : ℕ) (S : WordGeneratingSet (ManuscriptGroup m))
    (i : Fin m) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ B : ℕ, 1 ≤ B → ∀ a : ℤ, a.natAbs ≤ B ^ (i.val + 1) →
      wordLength S (SemidirectProduct.inl
        (Multiplicative.ofAdd (a • coordinateVector ℤ m i.val))) ≤ C * B := by
  simpa only [vectorCompressionMap_normal] using
    weighted_coordinate_compression m (vectorCompressionMap m) S i

end NilpotentConjugacy
