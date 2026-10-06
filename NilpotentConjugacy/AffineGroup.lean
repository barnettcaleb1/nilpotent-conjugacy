import NilpotentConjugacy.Unitriangular
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Group.Units.Hom

/-! Faithful affine matrix realization of the concrete generated group. -/
namespace NilpotentConjugacy
set_option backward.isDefEq.respectTransparency false

theorem generatedActingGroup_lowerUnitriangular (m : ℕ) :
    GeneratedActingGroup m ≤ lowerUnitriangular ℤ m := by
  apply (Subgroup.closure_le _).2
  rintro U ⟨j,rfl⟩
  exact lowerGap_actingMatrixGenerator_sub_one m j

def affineBlock (m : ℕ) (x : IntegralGeneratedGroup m) :
    Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) ℤ :=
  Matrix.fromBlocks 1 0 (fun i _ => x.left.toAdd i) x.right.val.val

def affineBlockHom (m : ℕ) : IntegralGeneratedGroup m →*
    Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) ℤ where
  toFun := affineBlock m
  map_one' := by
    change Matrix.fromBlocks 1 0 0 1 = 1
    exact Matrix.fromBlocks_one
  map_mul' x y := by
    unfold affineBlock
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]
    congr 1

def affineMatrixHom (m : ℕ) : IntegralGeneratedGroup m →*
    Matrix (Fin (1+m)) (Fin (1+m)) ℤ :=
  (Matrix.reindexRingEquiv ℤ (finSumFinEquiv : Fin 1 ⊕ Fin m ≃ Fin (1+m))).toMonoidHom.comp
    (affineBlockHom m)

theorem affineBlockHom_injective (m : ℕ) : Function.Injective (affineBlockHom m) := by
  intro x y h
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    exact congrArg (fun A => A (Sum.inr i) (Sum.inl 0)) h
  · apply Subtype.ext
    apply Units.ext
    ext i j
    exact congrArg (fun A => A (Sum.inr i) (Sum.inr j)) h

theorem affineMatrixHom_injective (m : ℕ) : Function.Injective (affineMatrixHom m) :=
  (Matrix.reindexRingEquiv ℤ (finSumFinEquiv : Fin 1 ⊕ Fin m ≃ Fin (1+m))).injective.comp
    (affineBlockHom_injective m)

theorem affineMatrix_lowerGap (m : ℕ) (x : IntegralGeneratedGroup m) :
    LowerGap 1 (affineMatrixHom m x - 1) := by
  intro i j hij
  obtain ⟨i,rfl⟩ := (finSumFinEquiv : Fin 1 ⊕ Fin m ≃ Fin (1+m)).surjective i
  obtain ⟨j,rfl⟩ := (finSumFinEquiv : Fin 1 ⊕ Fin m ≃ Fin (1+m)).surjective j
  have hx := generatedActingGroup_lowerUnitriangular m x.right.property
  change LowerGap 1 (x.right.val.val-1) at hx
  change (Matrix.reindex finSumFinEquiv finSumFinEquiv (affineBlock m x) - 1)
    (finSumFinEquiv i) (finSumFinEquiv j) = 0
  simp only [Matrix.sub_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  cases i with
  | inl i =>
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    cases j with
    | inl j =>
      have hj : j=0 := Subsingleton.elim _ _
      subst j
      simp [affineBlock]
    | inr j =>
      simp [affineBlock, Matrix.one_apply, Fin.ext_iff]
      omega
  | inr i =>
    cases j with
    | inl j =>
      have hj : j=0 := Subsingleton.elim _ _
      subst j
      simp only [finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
        Fin.val_natAdd, Fin.val_castAdd, Fin.val_zero] at hij
      omega
    | inr j =>
      have hgap : i.val < j.val+1 := by
        simp only [finSumFinEquiv_apply_right, Fin.val_natAdd] at hij
        omega
      have h := hx i j hgap
      simpa [affineBlock, Matrix.one_apply, Fin.ext_iff] using h

def affineUnitriangularHom (m : ℕ) : IntegralGeneratedGroup m →*
    lowerUnitriangular ℤ (1+m) :=
  (affineMatrixHom m).toHomUnits.codRestrict _ (affineMatrix_lowerGap m)

theorem affineUnitriangularHom_injective (m : ℕ) :
    Function.Injective (affineUnitriangularHom m) := by
  intro x y h
  apply affineMatrixHom_injective m
  exact congrArg (fun U => (U.val : Matrix (Fin (1+m)) (Fin (1+m)) ℤ)) h

instance integralGeneratedGroup_torsionFree (m : ℕ) : IsMulTorsionFree (IntegralGeneratedGroup m) :=
  Function.Injective.isMulTorsionFree (affineUnitriangularHom m) (affineUnitriangularHom_injective m)

instance integralGeneratedGroup_nilpotent (m : ℕ) : Group.IsNilpotent (IntegralGeneratedGroup m) := by
  let f := affineUnitriangularHom m
  let e := MonoidHom.ofInjective (affineUnitriangularHom_injective m)
  exact Group.nilpotent_of_mulEquiv e.symm

theorem integralGeneratedGroup_nilpotencyClass_le (m : ℕ) :
    Group.nilpotencyClass (IntegralGeneratedGroup m) ≤ m := by
  let f := affineUnitriangularHom m
  let e := MonoidHom.ofInjective (affineUnitriangularHom_injective m)
  calc
    Group.nilpotencyClass (IntegralGeneratedGroup m) ≤ Group.nilpotencyClass f.range :=
      Group.nilpotencyClass_le_of_surjective e.symm.toMonoidHom e.symm.surjective
    _ ≤ Group.nilpotencyClass (lowerUnitriangular ℤ (1+m)) := Subgroup.nilpotencyClass_le _
    _ ≤ m := by simpa using lowerUnitriangular_nilpotencyClass_le (R:=ℤ) (m:=1+m)

end NilpotentConjugacy
