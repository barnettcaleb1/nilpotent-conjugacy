import NilpotentConjugacy.IntegralGroup
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.NoncommRing

/-! Lower unitriangular matrix groups and their explicit central filtration. -/
namespace NilpotentConjugacy
open scoped BigOperators commutatorElement

section Gaps
variable {R : Type*} [CommRing R] {m d e : ℕ}
variable {A B : Matrix (Fin m) (Fin m) R}

theorem gap_zero : LowerGap d (0 : Matrix (Fin m) (Fin m) R) := by
  intro i j h; rfl
theorem gap_mono (hA : LowerGap d A) (he : e ≤ d) : LowerGap e A := by
  intro i j h; exact hA i j (by omega)
theorem gap_add (hA : LowerGap d A) (hB : LowerGap d B) : LowerGap d (A+B) := by
  intro i j h; simp [hA i j h, hB i j h]
theorem gap_sub (hA : LowerGap d A) (hB : LowerGap d B) : LowerGap d (A-B) := by
  intro i j h; simp [hA i j h, hB i j h]
theorem gap_neg (hA : LowerGap d A) : LowerGap d (-A) := by
  intro i j h; simp [hA i j h]
theorem gap_smul (r : R) (hA : LowerGap d A) : LowerGap d (r • A) := by
  intro i j h; simp [hA i j h]
theorem gap_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin m) (Fin m) R)
    (hf : ∀ a ∈ s, LowerGap d (f a)) : LowerGap d (∑ a ∈ s, f a) := by
  intro i j h
  simp only [Matrix.sum_apply]
  exact Finset.sum_eq_zero (fun a ha => hf a ha i j h)
theorem gap_pow (hA : LowerGap d A) (n : ℕ) : LowerGap (d*n) (A^n) := by
  induction n with
  | zero => simpa using (lowerGap_one (R:=R) (m:=m))
  | succ n ih => simpa [pow_succ, Nat.mul_succ] using lowerGap_mul ih hA
theorem gap_eq_zero (hA : LowerGap d A) (hd : m ≤ d) : A=0 := by
  ext i j; exact hA i j (by omega)

theorem gap_unit_inverse {u : (Matrix (Fin m) (Fin m) R)ˣ}
    (hd : 1 ≤ d) (hu : LowerGap d ((u : Matrix (Fin m) (Fin m) R)-1)) :
    LowerGap d ((↑u⁻¹ : Matrix (Fin m) (Fin m) R)-1) := by
  let A : Matrix (Fin m) (Fin m) R := (u : Matrix (Fin m) (Fin m) R)-1
  have hA : LowerGap d A := hu
  have hn : (-A)^(m+1)=0 := by
    rw [pow_succ, lowerGap_nilpotent (gap_mono (gap_neg hA) hd), zero_mul]
  have hprod : (∑ k ∈ Finset.range (m+1), (-A)^k) * (u : Matrix (Fin m) (Fin m) R)=1 := by
    have h := geom_sum_mul_neg (-A) (m+1)
    rw [hn, sub_zero] at h
    simpa [A] using h
  rw [u.inv_eq_of_mul_eq_one_left hprod, Finset.sum_range_succ']
  simp only [pow_zero, add_sub_cancel_right]
  apply gap_sum
  intro k hk
  exact gap_mono (gap_pow (gap_neg hA) (k+1)) (by nlinarith)

theorem gap_unit_product {u v : (Matrix (Fin m) (Fin m) R)ˣ}
    (hu : LowerGap d ((u : Matrix (Fin m) (Fin m) R)-1))
    (hv : LowerGap d ((v : Matrix (Fin m) (Fin m) R)-1)) :
    LowerGap d ((↑(u*v) : Matrix (Fin m) (Fin m) R)-1) := by
  have he : (↑(u*v) : Matrix (Fin m) (Fin m) R)-1 =
      ((u : Matrix (Fin m) (Fin m) R)-1) + ((v : Matrix (Fin m) (Fin m) R)-1) +
      ((u : Matrix (Fin m) (Fin m) R)-1)*((v : Matrix (Fin m) (Fin m) R)-1) := by
    simp only [Units.val_mul]; noncomm_ring
  rw [he]
  exact gap_add (gap_add hu hv) (gap_mono (lowerGap_mul hu hv) (by omega))

end Gaps

/-- The actual group of lower unitriangular matrices of size m. -/
def lowerUnitriangular (R : Type*) [CommRing R] (m : ℕ) :
    Subgroup (Matrix (Fin m) (Fin m) R)ˣ where
  carrier := {u | LowerGap 1 ((u : Matrix (Fin m) (Fin m) R)-1)}
  one_mem' := by change LowerGap 1 (1-1 : Matrix (Fin m) (Fin m) R); rw [sub_self]; exact gap_zero
  mul_mem' := gap_unit_product
  inv_mem' := gap_unit_inverse (by omega)

section Filtration
variable {R : Type*} [CommRing R] {m : ℕ}
local notation "UT" => lowerUnitriangular R m
local notation "Mat" => Matrix (Fin m) (Fin m) R

def unitriangularLayer (k : ℕ) : Subgroup UT where
  carrier := {u | LowerGap (k+1) ((u.val : Mat)-1)}
  one_mem' := by change LowerGap (k+1) (1-1 : Mat); rw [sub_self]; exact gap_zero
  mul_mem' := gap_unit_product
  inv_mem' := gap_unit_inverse (by omega)

theorem gap_commutator {d e : ℕ} (u v : UT)
    (hu : LowerGap d ((u.val : Mat)-1)) (hv : LowerGap e ((v.val : Mat)-1)) :
    LowerGap (d+e) ((↑(⁅u,v⁆ : UT).val : Mat)-1) := by
  have hui : LowerGap 0 (↑(u.val⁻¹) : Mat) := by
    have h := gap_add (gap_mono (u⁻¹).property (by omega : 0 ≤ 1)) lowerGap_one
    simpa using h
  have hvi : LowerGap 0 (↑(v.val⁻¹) : Mat) := by
    have h := gap_add (gap_mono (v⁻¹).property (by omega : 0 ≤ 1)) lowerGap_one
    simpa using h
  have hd : LowerGap (d+e) ((u.val : Mat)*(v.val : Mat)-(v.val : Mat)*(u.val : Mat)) := by
    have h := gap_sub (lowerGap_mul hu hv) (by simpa [Nat.add_comm] using lowerGap_mul hv hu)
    convert h using 1; noncomm_ring
  have he : (↑(⁅u,v⁆ : UT).val : Mat)-1 =
      ((u.val : Mat)*(v.val : Mat)-(v.val : Mat)*(u.val : Mat)) *
      (↑u.val⁻¹ : Mat) * (↑v.val⁻¹ : Mat) := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    rw [sub_mul, sub_mul]
    simp [mul_assoc]
  rw [he]
  simpa using lowerGap_mul (lowerGap_mul hd hui) hvi

theorem unitriangularLayer_central :
    Subgroup.IsDescendingCentralSeries (unitriangularLayer (R:=R) (m:=m)) := by
  constructor
  · ext u
    change LowerGap (0+1) ((u.val : Mat)-1) ↔ True
    exact iff_true_intro u.property
  · intro u n hu v
    exact gap_commutator u v hu v.property

theorem unitriangularLayer_eq_bot (k : ℕ) (hk : m ≤ k+1) :
    unitriangularLayer (R:=R) (m:=m) k = ⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  have h : (u.val : Mat)-1=0 := gap_eq_zero hu hk
  have he : (u.val : Mat)=1 := sub_eq_zero.mp h
  exact Subgroup.mem_bot.mpr (Subtype.ext (Units.ext he))

instance lowerUnitriangular_isNilpotent : Group.IsNilpotent UT :=
  (Subgroup.nilpotent_iff_finite_descending_central_series _).mpr
    ⟨m, unitriangularLayer, unitriangularLayer_central, unitriangularLayer_eq_bot m (by omega)⟩

theorem lowerUnitriangular_nilpotencyClass_le : Group.nilpotencyClass UT ≤ m-1 := by
  apply Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
  apply le_antisymm _ bot_le
  have h := Subgroup.descending_central_series_ge_lower _
    (unitriangularLayer_central (R:=R) (m:=m)) (m-1)
  rw [unitriangularLayer_eq_bot (m-1) (by omega)] at h
  exact h

theorem gap_nsmul {d : ℕ} {A : Mat} (n : ℕ) (hA : LowerGap d A) : LowerGap d (n • A) := by
  intro i j h
  simp [hA i j h]

/-- Modulo the next diagonal, taking an nth power multiplies a difference by n. -/
theorem gap_power_difference {d : ℕ} (u v : UT)
    (huv : LowerGap d ((u.val : Mat)-(v.val : Mat))) (n : ℕ) :
    LowerGap (d+1) (((u.val : Mat)^n-(v.val : Mat)^n)-n • ((u.val : Mat)-(v.val : Mat))) := by
  induction n with
  | zero => simpa using (gap_zero (R:=R) (m:=m) (d:=d+1))
  | succ n ih =>
    have hu0 : LowerGap 0 (u.val : Mat) := by
      simpa using gap_add (gap_mono u.property (by omega : 0 ≤ 1)) lowerGap_one
    have hvn : LowerGap 1 ((v.val : Mat)^n-1) := by
      have h := (v^n).property
      change LowerGap 1 ((↑(v^n).val : Mat)-1) at h
      simpa using h
    have h₁ : LowerGap (d+1)
        ((((u.val : Mat)^n-(v.val : Mat)^n)-n • ((u.val : Mat)-(v.val : Mat)))*(u.val : Mat)) := by
      simpa using lowerGap_mul ih hu0
    have h₂ := lowerGap_mul (gap_nsmul n huv) u.property
    have h₃ : LowerGap (d+1) (((v.val : Mat)^n-1)*((u.val : Mat)-(v.val : Mat))) := by
      simpa [Nat.add_comm] using lowerGap_mul hvn huv
    have h := gap_add (gap_add h₁ h₂) h₃
    convert h using 1
    simp only [pow_succ, sub_mul, mul_sub, one_mul, mul_one, succ_nsmul]
    abel

theorem unitriangular_pow_injective [IsAddTorsionFree R] {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (fun u : UT => u^n) := by
  intro u v huv
  have hmat : (u.val : Mat)^n=(v.val : Mat)^n := by
    simpa using congrArg (fun z : UT => (z.val : Mat)) huv
  have hgap : ∀ d : ℕ, LowerGap d ((u.val : Mat)-(v.val : Mat)) := by
    intro d
    induction d with
    | zero =>
      have h := gap_sub (gap_mono u.property (by omega : 0 ≤ 1))
        (gap_mono v.property (by omega : 0 ≤ 1))
      simpa using h
    | succ d ih =>
      have h := gap_power_difference u v ih n
      rw [hmat, sub_self, zero_sub] at h
      intro i j hij
      have he := h i j hij
      have hz : n • (((u.val : Mat)-(v.val : Mat)) i j) = 0 := by
        change -(n • (((u.val : Mat)-(v.val : Mat)) i j)) = 0 at he
        exact neg_eq_zero.mp he
      exact (nsmul_right_injective hn) (by simpa using hz)
  exact Subtype.ext (Units.ext (sub_eq_zero.mp (gap_eq_zero (hgap m) (le_refl m))))

instance lowerUnitriangular_torsionFree [IsAddTorsionFree R] : IsMulTorsionFree UT where
  pow_left_injective {n} hn := unitriangular_pow_injective (n:=n) hn

end Filtration
end NilpotentConjugacy
