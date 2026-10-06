import NilpotentConjugacy.SpecialPairs
import Mathlib.Data.Nat.Prime.Factorial

namespace NilpotentConjugacy
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem shiftJ_pow_mulVec_apply {R : Type*} [CommRing R] {m : ℕ}
    (d : ℕ) (x : Fin m → R) (i : Fin m) :
    ((shiftJ m : Matrix (Fin m) (Fin m) R)^d).mulVec x i =
      if h : d ≤ i.val then x ⟨i.val-d, by omega⟩ else 0 := by
  rw [shiftJ_pow, Matrix.mulVec, dotProduct]
  by_cases h : d ≤ i.val
  · let j : Fin m := ⟨i.val-d, by omega⟩
    rw [Finset.sum_eq_single j]
    · simp [shiftBand, j, h, Nat.sub_add_cancel h]
    · intro k _ hkj
      have hk : i.val ≠ k.val+d := by
        intro he
        apply hkj
        apply Fin.ext
        dsimp [j]
        omega
      simp [shiftBand, hk]
    · simp
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro k _
    have hk : i.val ≠ k.val+d := by omega
    simp [shiftBand, hk]

theorem shiftedBidiagonal_first {R : Type*} [CommRing R] {m w : ℕ}
    (hw : w < m) (t : R) (x : Fin m → R) :
    (shiftedBidiagonalMatrix m w t).mulVec x ⟨w,hw⟩ = t*x ⟨0,by omega⟩ := by
  rw [shiftedBidiagonalMatrix, mul_add, Matrix.mul_smul, mul_one, ← pow_succ,
    Matrix.add_mulVec, Matrix.smul_mulVec]
  simp [shiftJ_pow_mulVec_apply]

theorem shiftedBidiagonal_successor {R : Type*} [CommRing R] {m w i : ℕ}
    (hi : i+w+1 < m) (t : R) (x : Fin m → R) :
    (shiftedBidiagonalMatrix m w t).mulVec x ⟨i+w+1,hi⟩ =
      t*x ⟨i+1,by omega⟩ + x ⟨i,by omega⟩ := by
  rw [shiftedBidiagonalMatrix, mul_add, Matrix.mul_smul, mul_one, ← pow_succ,
    Matrix.add_mulVec, Matrix.smul_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, shiftJ_pow_mulVec_apply]
  rw [dif_pos (by omega : w ≤ i+w+1), dif_pos (by omega : w+1 ≤ i+w+1)]
  simp only [show i+w+1-w=i+1 by omega, show i+w+1-(w+1)=i by omega]

/-- Divisibility in the full shifted matrix follows from its actual entries. -/
theorem shiftedBidiagonal_terminal_dvd {m w : ℕ} (hwm : w < m-1)
    (t k : ℤ) (ht : t ≠ 0) (x : Fin m → ℤ)
    (hx : (shiftedBidiagonalMatrix m w t).mulVec x =
      k • coordinateVector ℤ m (m-1)) : t ∣ k := by
  have hz : ∀ i : ℕ, ∀ hi : i < m-w-1, x ⟨i,by omega⟩ = 0 := by
    intro i
    induction i with
    | zero =>
      intro hi
      have h := congrFun hx ⟨w,by omega⟩
      rw [shiftedBidiagonal_first (by omega)] at h
      have he : (k • coordinateVector ℤ m (m-1)) ⟨w,by omega⟩ = 0 := by
        simp [coordinateVector, show w ≠ m-1 by omega]
      rw [he] at h
      exact (mul_eq_zero.mp h).resolve_left ht
    | succ i ih =>
      intro hi
      have h := congrFun hx ⟨i+w+1,by omega⟩
      rw [shiftedBidiagonal_successor (by omega), ih (by omega)] at h
      have he : (k • coordinateVector ℤ m (m-1)) ⟨i+w+1,by omega⟩ = 0 := by
        simp [coordinateVector, show i+w+1 ≠ m-1 by omega]
      rw [he, add_zero] at h
      exact (mul_eq_zero.mp h).resolve_left ht
  have hl := congrFun hx ⟨m-1,by omega⟩
  have he : m-1=(m-w-2)+w+1 := by omega
  have hl' : (shiftedBidiagonalMatrix m w t).mulVec x ⟨(m-w-2)+w+1,by omega⟩ = k := by
    simpa [coordinateVector, he] using hl
  rw [shiftedBidiagonal_successor (by omega), hz (m-w-2) (by omega), add_zero] at hl'
  exact ⟨x ⟨m-w-2+1,by omega⟩, hl'.symm⟩

/-- The exact paper pair is nonconjugate in the actual constructed group. -/
theorem specialPair_not_isConj (p : ℕ) [Fact p.Prime] (m w s : ℕ)
    (hm : 4 ≤ m) (hmw : m ≤ 2*w) (hwhi : w ≤ m-2) (hp : m < p) (hs : 0 < s) :
    ¬ IsConj (specialPairLeft m w p s) (specialPairRight m w p s) := by
  have hprime := (Fact.out : p.Prime)
  have hw : 1 ≤ w := by omega
  have hwm : w < m-1 := by omega
  intro hconj
  obtain ⟨v,hv⟩ := (semidirect_isConj_iff_difference_range (manuscriptAction m)
    (pairActor m w ((p:ℤ)^s)) (Multiplicative.ofAdd (pairCentralVector m p s))).mp hconj
  have hv' := congrArg Multiplicative.toAdd hv
  change (manuscriptAction m (pairActor m w ((p:ℤ)^s))
    (Multiplicative.ofAdd v.toAdd)).toAdd-v.toAdd =
    pairCentralVector m p s at hv'
  rw [pairActor_action_difference m w hm hw hwm hmw] at hv'
  have hM : (m.factorial : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hx : (shiftedBidiagonalMatrix m w ((p:ℤ)^s)).mulVec v.toAdd =
      ((m.factorial : ℤ)^(m-2)*(p:ℤ)^(s-1)) • coordinateVector ℤ m (m-1) := by
    apply (smul_right_injective (M:=Fin m → ℤ) hM)
    dsimp only
    rw [hv']
    unfold pairCentralVector
    rw [smul_smul, show m-1=m-2+1 by omega, pow_succ]
    congr 1
    ring
  have ht : (p : ℤ)^s ≠ 0 := pow_ne_zero _ (by exact_mod_cast hprime.ne_zero)
  have hd := shiftedBidiagonal_terminal_dvd hwm ((p:ℤ)^s)
    ((m.factorial : ℤ)^(m-2)*(p:ℤ)^(s-1)) ht v.toAdd hx
  have hdNat : p^s ∣ m.factorial^(m-2)*p^(s-1) := by exact_mod_cast hd
  have he : s=(s-1)+1 := by omega
  rw [he, pow_succ] at hdNat
  have hpos : 0 < p^(s-1) := pow_pos hprime.pos _
  have hdP : p ∣ m.factorial^(m-2) := by
    apply (Nat.mul_dvd_mul_iff_right hpos).mp
    simpa [Nat.add_sub_cancel, mul_comm] using hdNat
  have hpM : ¬p ∣ m.factorial := (hprime.dvd_factorial).not.mpr (by omega)
  exact hpM (hprime.dvd_of_dvd_pow hdP)

end NilpotentConjugacy
