import NilpotentConjugacy.GroupProperties

namespace NilpotentConjugacy
open scoped commutatorElement

/-- Exact commutation with the normal vector lattice, for the paper's actual group. -/
theorem manuscript_commutator_vector (m : ℕ) (h : CoefficientGroup m) (v : Fin m → ℤ) :
    ⁅(SemidirectProduct.inr h : ManuscriptGroup m),
      (SemidirectProduct.inl (Multiplicative.ofAdd v) : ManuscriptGroup m)⁆ =
      SemidirectProduct.inl (Multiplicative.ofAdd
        (((manuscriptRhoHom m h).val - 1).mulVec v)) := by
  rw [commutatorElement_def, ← map_inv, ← SemidirectProduct.inl_aut, ← map_inv, ← map_mul]
  apply congrArg SemidirectProduct.inl
  change Multiplicative.ofAdd ((manuscriptRhoHom m h).val.mulVec v - v) = _
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]

/-- Every iterated matrix difference is the corresponding actual iterated
commutator, and therefore belongs to the ordinary lower central series. -/
theorem manuscript_difference_power_mem_lowerCentralSeries (m : ℕ)
    (h : CoefficientGroup m) (v : Fin m → ℤ) (n : ℕ) :
    (SemidirectProduct.inl (Multiplicative.ofAdd
      ((((manuscriptRhoHom m h).val - 1) ^ n).mulVec v)) : ManuscriptGroup m) ∈
        (⊤ : Subgroup (ManuscriptGroup m)).lowerCentralSeries n := by
  induction n with
  | zero => exact Subgroup.mem_top _
  | succ n ih =>
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
    have hh := Subgroup.commutator_mem_commutator
      (show (SemidirectProduct.inr h : ManuscriptGroup m) ∈ ⊤ from Subgroup.mem_top _) ih
    rw [manuscript_commutator_vector, Matrix.mulVec_mulVec, ← pow_succ'] at hh
    exact hh

/-- The acting element whose matrix is exactly `exp(m! J)`. -/
noncomputable def classWitnessActor (m : ℕ) (hm : 2 ≤ m) : CoefficientGroup m :=
  SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single (⟨0, by omega⟩ : Fin (m - 1)) 1))

@[simp] theorem classWitnessActor_matrix (m : ℕ) (hm : 2 ≤ m) :
    (manuscriptRhoHom m (classWitnessActor m hm)).val = integralExponential m (shiftJ m) := by
  rw [classWitnessActor, manuscriptRhoHom, SemidirectProduct.lift_inl]
  change integralExponential m
    (latticePolynomial m (Pi.single (⟨0, by omega⟩ : Fin (m - 1)) 1)) = _
  rw [latticePolynomial_single]
  simp

/-- The exact nonzero final vector of the commutator chain in the manuscript. -/
theorem classWitness_terminal_vector {m : ℕ} (hm : 2 ≤ m) :
    (((manuscriptRhoHom m (classWitnessActor m hm)).val - 1) ^ (m - 1)).mulVec
      (coordinateVector ℤ m 0) =
    (m.factorial : ℤ) ^ (m - 1) • coordinateVector ℤ m (m - 1) := by
  rw [classWitnessActor_matrix, integralExponential_shiftJ_top_power hm, Matrix.smul_mulVec,
    shiftJ_pow_coordinate (m - 1) 0 (by omega), Nat.zero_add]

/-- The top commutator vector is nontrivial as an element of the actual group. -/
theorem classWitness_nontrivial {m : ℕ} (hm : 2 ≤ m) :
    (SemidirectProduct.inl (Multiplicative.ofAdd
      ((m.factorial : ℤ) ^ (m - 1) • coordinateVector ℤ m (m - 1))) : ManuscriptGroup m) ≠ 1 := by
  intro h
  have hv : (m.factorial : ℤ) ^ (m - 1) • coordinateVector ℤ m (m - 1) = 0 :=
    congrArg (fun x : ManuscriptGroup m => x.left.toAdd) h
  have ht := congrFun hv (⟨m - 1, by omega⟩ : Fin m)
  have hM : (m.factorial : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  apply pow_ne_zero (m - 1) hM
  simpa [coordinateVector] using ht

/-- Exact nilpotency class of the actual manuscript group, proved by the
nonzero length-m ordinary commutator chain and the faithful affine upper bound. -/
theorem manuscriptGroup_nilpotencyClass {m : ℕ} (hm : 3 ≤ m) :
    Group.nilpotencyClass (ManuscriptGroup m) = m := by
  have : Fact (3 ≤ m) := ⟨hm⟩
  apply le_antisymm (manuscriptGroup_nilpotencyClass_le hm)
  by_contra hc
  have hle : Group.nilpotencyClass (ManuscriptGroup m) ≤ m - 1 := by omega
  have hbot := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hle
  have hw := manuscript_difference_power_mem_lowerCentralSeries m
    (classWitnessActor m (by omega)) (coordinateVector ℤ m 0) (m - 1)
  rw [classWitness_terminal_vector (by omega), hbot, Subgroup.mem_bot] at hw
  exact classWitness_nontrivial (by omega) hw

/-- Every lower unitriangular matrix fixes the final standard vector. -/
theorem lowerUnipotent_fixes_terminalVector {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin m) (Fin m) ℤ) (hA : LowerGap 1 (A - 1)) :
    A.mulVec (coordinateVector ℤ m (m - 1)) = coordinateVector ℤ m (m - 1) := by
  have hzero : (A - 1).mulVec (coordinateVector ℤ m (m - 1)) = 0 := by
    rw [show coordinateVector ℤ m (m - 1) = Pi.single (⟨m - 1, by omega⟩ : Fin m) 1 from
      coordinateVector_fin ⟨m - 1, by omega⟩, Matrix.mulVec_single_one]
    ext i
    exact hA i ⟨m - 1, by omega⟩ (by change i.val < (m - 1) + 1; omega)
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hzero
  exact sub_eq_zero.mp hzero

/-- The final coordinate and every integer multiple of it are central in the
actual manuscript group, as claimed in its structural proposition. -/
theorem manuscript_terminalVector_central {m : ℕ} (hm : 0 < m) (a : ℤ) :
    (SemidirectProduct.inl (Multiplicative.ofAdd
      (a • coordinateVector ℤ m (m - 1))) : ManuscriptGroup m) ∈
        Subgroup.center (ManuscriptGroup m) := by
  have hfix (h : CoefficientGroup m) :
      manuscriptAction m h (Multiplicative.ofAdd (a • coordinateVector ℤ m (m - 1))) =
        Multiplicative.ofAdd (a • coordinateVector ℤ m (m - 1)) := by
    have hgap := generatedActingGroup_lowerUnitriangular m
      (manuscriptRho_mem_generatedActingGroup m hm h)
    have hvec := lowerUnipotent_fixes_terminalVector hm (manuscriptRho m h).val hgap
    apply Multiplicative.toAdd.injective
    change (manuscriptRho m h).val.mulVec (a • coordinateVector ℤ m (m - 1)) = _
    rw [Matrix.mulVec_smul, hvec]
    rfl
  rw [Subgroup.mem_center_iff]
  intro x
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply, hfix]
    exact mul_comm _ _
  · simp

end NilpotentConjugacy
