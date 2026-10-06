import NilpotentConjugacy.QuotientDescent
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Localization of actual finite additive quotients

Localization of a finite module is itself a quotient of that module. An
obstruction killed by a prime survives localization at that prime. These facts
avoid assuming a primary decomposition or an unexplained local scalar action.
-/

namespace NilpotentConjugacy

section FiniteLocalization

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- For a finite source, the numerator map to its localization is surjective. -/
theorem localizedModule_mk_surjective_of_finite (S : Submonoid R) [Finite M] :
    Function.Surjective (LocalizedModule.mkLinearMap S M) := by
  let f := LocalizedModule.mkLinearMap S M
  have : Finite f.range := Finite.of_surjective f.rangeRestrict (by
    rintro ⟨y, ⟨x, rfl⟩⟩
    exact ⟨x, rfl⟩)
  intro z
  induction z using LocalizedModule.induction_on with
  | h m s =>
    have hinj : Function.Injective (fun b : f.range => (s : R) • b) := by
      intro b c heq
      apply Subtype.ext
      apply IsLocalizedModule.smul_injective f s
      exact congrArg Subtype.val heq
    have hsurj := (Finite.injective_iff_surjective).mp hinj
    obtain ⟨b, hb⟩ := hsurj ⟨f m, LinearMap.mem_range_self f m⟩
    obtain ⟨a, ha⟩ := b.property
    refine ⟨a, ?_⟩
    apply IsLocalizedModule.smul_injective f s
    change (s : R) • f a = (s : R) • LocalizedModule.mk m s
    rw [ha]
    have hb' := congrArg Subtype.val hb
    change (s : R) • b.val = f m at hb'
    rw [hb']
    change LocalizedModule.mk m 1 = (s : R) • LocalizedModule.mk m s
    rw [LocalizedModule.smul'_mk]
    exact (LocalizedModule.mk_cancel s m).symm

/-- The localized module is finite as a type, not merely finitely generated. -/
theorem localizedModule_finite (S : Submonoid R) [Finite M] :
    Finite (LocalizedModule S M) :=
  Finite.of_surjective (LocalizedModule.mkLinearMap S M)
    (localizedModule_mk_surjective_of_finite S)

/-- Localization of a finite abelian quotient cannot increase its order. -/
theorem localizedModule_card_le (S : Submonoid R) [Finite M] :
    Nat.card (LocalizedModule S M) ≤ Nat.card M :=
  Nat.card_le_card_of_surjective _ (localizedModule_mk_surjective_of_finite S)

end FiniteLocalization

section PrimeObstruction

variable {M : Type*} [AddCommGroup M]

/-- Every denominator permitted at `(p)` is coprime to `p`. -/
theorem primeLocal_denominator_coprime (p : ℕ) [Fact p.Prime]
    (s : (integerPrimeIdeal p).primeCompl) : IsCoprime (p : ℤ) (s : ℤ) := by
  have hnd : ¬ (p : ℤ) ∣ (s : ℤ) := by
    simpa [Ideal.mem_primeCompl_iff, integerPrimeIdeal, Ideal.mem_span_singleton]
      using s.property
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast]
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  exact fun hd => hnd (Int.natCast_dvd.mpr hd)

/-- A nonzero element annihilated by `p` stays nonzero after actual localization
at `(p)`; this uses Bézout and no decomposition assumption. -/
theorem primeLocal_mk_ne_zero_of_prime_smul_zero (p : ℕ) [Fact p.Prime]
    (c : M) (hc : c ≠ 0) (hpc : (p : ℤ) • c = 0) :
    LocalizedModule.mkLinearMap (integerPrimeIdeal p).primeCompl M c ≠ 0 := by
  intro hzero
  have hz : LocalizedModule.mk c (1 : (integerPrimeIdeal p).primeCompl) =
      LocalizedModule.mk (0 : M) 1 := by simpa using hzero
  obtain ⟨s, hs⟩ := LocalizedModule.mk_eq.mp hz
  simp only [one_smul, smul_zero] at hs
  obtain ⟨a, b, hab⟩ := primeLocal_denominator_coprime p s
  apply hc
  calc
    c = (1 : ℤ) • c := (one_smul ℤ c).symm
    _ = (a * (p : ℤ) + b * (s : ℤ)) • c := by rw [hab]
    _ = 0 := by simp [add_smul, mul_smul, hpc, show (s : ℤ) • c = 0 from hs]

/-- The separating obstruction survives in the image of the actual localized
endomorphism. Finiteness is used to lift a localized preimage to the original
finite group. -/
theorem primeLocal_not_mem_range (p : ℕ) [Fact p.Prime] [Finite M]
    (T : M →ₗ[ℤ] M) (c : M) (hc : c ∉ T.range)
    (hpc : (p : ℤ) • c ∈ T.range) :
    LocalizedModule.mkLinearMap (integerPrimeIdeal p).primeCompl M c ∉
      (LocalizedModule.map (integerPrimeIdeal p).primeCompl T).range := by
  let S := (integerPrimeIdeal p).primeCompl
  let f := LocalizedModule.mkLinearMap S M
  rintro ⟨z, hz⟩
  obtain ⟨a, rfl⟩ := localizedModule_mk_surjective_of_finite S z
  have hzero : f (c - T a) = 0 := by
    rw [map_sub]
    apply sub_eq_zero.mpr
    simpa only [f, LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk] using hz.symm
  have hz0 : LocalizedModule.mk (c - T a) (1 : S) =
      LocalizedModule.mk (0 : M) 1 := by simpa [f] using hzero
  obtain ⟨s, hs⟩ := LocalizedModule.mk_eq.mp hz0
  simp only [one_smul, smul_zero] at hs
  have hsc : (s : ℤ) • c ∈ T.range := by
    have heq : (s : ℤ) • c = T ((s : ℤ) • a) := by
      rw [map_smul]
      exact sub_eq_zero.mp (by simpa [smul_sub, Submonoid.smul_def] using hs)
    rw [heq]
    exact LinearMap.mem_range_self T _
  obtain ⟨u, v, huv⟩ := primeLocal_denominator_coprime p s
  apply hc
  have hmem := T.range.add_mem (T.range.smul_mem u hpc) (T.range.smul_mem v hsc)
  simpa only [← mul_smul, ← add_smul, huv, one_smul] using hmem

end PrimeObstruction

section LocalizedLattice

variable {M : Type*} [AddCommGroup M]

/-- Extend an actual integer-lattice quotient map by local scalar multiplication.
The codomain is the standard localized module, with its constructed action. -/
noncomputable def localizedLatticeMap (p m : ℕ) [Fact p.Prime]
    (π : (Fin m → ℤ) →ₗ[ℤ] M) :
    (Fin m → PrimeLocalIntegers p) →ₗ[PrimeLocalIntegers p]
      LocalizedModule (integerPrimeIdeal p).primeCompl M :=
  (Pi.basisFun (PrimeLocalIntegers p) (Fin m)).constr (PrimeLocalIntegers p)
    (fun i => LocalizedModule.mkLinearMap (integerPrimeIdeal p).primeCompl M
      (π (Pi.single i 1)))

/-- The extension agrees with the original quotient on every integer vector. -/
theorem localizedLatticeMap_intVector (p m : ℕ) [Fact p.Prime]
    (π : (Fin m → ℤ) →ₗ[ℤ] M) (v : Fin m → ℤ) :
    localizedLatticeMap p m π (fun i => (v i : PrimeLocalIntegers p)) =
      LocalizedModule.mkLinearMap (integerPrimeIdeal p).primeCompl M (π v) := by
  classical
  rw [localizedLatticeMap, Module.Basis.constr_apply_fintype]
  simp only [Pi.basisFun_equivFun, LinearEquiv.refl_apply, Int.cast_smul_eq_zsmul]
  have hv : (∑ i, v i • Pi.single i (1 : ℤ)) = v := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  calc
    _ = LocalizedModule.mkLinearMap (integerPrimeIdeal p).primeCompl M
        (π (∑ i, v i • Pi.single i (1 : ℤ))) := by simp only [map_sum, map_zsmul]
    _ = _ := by rw [hv]

/-- A surjective map from the integer lattice gives a surjective map from the
local lattice onto the actual localized finite quotient. -/
theorem localizedLatticeMap_surjective (p m : ℕ) [Fact p.Prime] [Finite M]
    (π : (Fin m → ℤ) →ₗ[ℤ] M) (hπ : Function.Surjective π) :
    Function.Surjective (localizedLatticeMap p m π) := by
  intro z
  obtain ⟨a, rfl⟩ := localizedModule_mk_surjective_of_finite
    (integerPrimeIdeal p).primeCompl z
  obtain ⟨v, rfl⟩ := hπ a
  exact ⟨fun i => (v i : PrimeLocalIntegers p), localizedLatticeMap_intVector p m π v⟩

/-- The actual quotient by the extended kernel is finite. -/
theorem localizedLatticeMap_quotient_finite (p m : ℕ) [Fact p.Prime] [Finite M]
    (π : (Fin m → ℤ) →ₗ[ℤ] M) (hπ : Function.Surjective π) :
    Finite ((Fin m → PrimeLocalIntegers p) ⧸ (localizedLatticeMap p m π).ker) := by
  have := localizedModule_finite (M := M) (integerPrimeIdeal p).primeCompl
  let e := (localizedLatticeMap p m π).quotKerEquivOfSurjective
    (localizedLatticeMap_surjective p m π hπ)
  exact Finite.of_injective e e.injective

/-- The order of the constructed module quotient is bounded by the original
finite abelian image. -/
theorem localizedLatticeMap_quotient_card_le (p m : ℕ) [Fact p.Prime] [Finite M]
    (π : (Fin m → ℤ) →ₗ[ℤ] M) (hπ : Function.Surjective π) :
    Nat.card ((Fin m → PrimeLocalIntegers p) ⧸ (localizedLatticeMap p m π).ker) ≤
      Nat.card M := by
  rw [Nat.card_congr ((localizedLatticeMap p m π).quotKerEquivOfSurjective
    (localizedLatticeMap_surjective p m π hπ)).toEquiv]
  exact localizedModule_card_le (integerPrimeIdeal p).primeCompl

/-- Scalar extension intertwines every descended integral matrix action. -/
theorem localizedLatticeMap_matrix (p m : ℕ) [Fact p.Prime]
    (π : (Fin m → ℤ) →ₗ[ℤ] M) (B : Matrix (Fin m) (Fin m) ℤ)
    (T : M →ₗ[ℤ] M) (hB : ∀ v, π (B.mulVec v) = T (π v))
    (x : Fin m → PrimeLocalIntegers p) :
    localizedLatticeMap p m π ((integerMatrixMap (PrimeLocalIntegers p) m B).mulVec x) =
      LocalizedModule.map (integerPrimeIdeal p).primeCompl T (localizedLatticeMap p m π x) := by
  classical
  have heq : (localizedLatticeMap p m π).comp
      (integerMatrixMap (PrimeLocalIntegers p) m B).mulVecLin =
      (LocalizedModule.map (integerPrimeIdeal p).primeCompl T).comp
        (localizedLatticeMap p m π) := by
    apply (Pi.basisFun (PrimeLocalIntegers p) (Fin m)).ext
    intro i
    simp only [LinearMap.comp_apply, Pi.basisFun_apply, Matrix.mulVecLin_apply]
    have hcol : (integerMatrixMap (PrimeLocalIntegers p) m B).mulVec (Pi.single i 1) =
        fun j => (B.mulVec (Pi.single i 1) j : PrimeLocalIntegers p) := by
      simp only [Matrix.mulVec_single_one]
      rfl
    rw [hcol, localizedLatticeMap_intVector]
    have hei : localizedLatticeMap p m π (Pi.single i 1) =
        LocalizedModule.mkLinearMap (integerPrimeIdeal p).primeCompl M (π (Pi.single i 1)) := by
      have hvec : (fun j => ((Pi.single i (1 : ℤ) : Fin m → ℤ) j : PrimeLocalIntegers p)) =
          Pi.single i 1 := by
        ext j
        simp [Pi.single_apply]
      rw [← hvec, localizedLatticeMap_intVector]
    rw [hei]
    simp only [LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk, hB]
  exact LinearMap.congr_fun heq x

/-- The kernel of the constructed local quotient is preserved by every
integral matrix action that descends to the original quotient. -/
theorem localizedLatticeMap_kernel_preserves (p m : ℕ) [Fact p.Prime]
    (π : (Fin m → ℤ) →ₗ[ℤ] M) (B : Matrix (Fin m) (Fin m) ℤ)
    (T : M →ₗ[ℤ] M) (hB : ∀ v, π (B.mulVec v) = T (π v)) :
    ∀ x ∈ (localizedLatticeMap p m π).ker,
      (integerMatrixMap (PrimeLocalIntegers p) m B).mulVec x ∈
        (localizedLatticeMap p m π).ker := by
  intro x hx
  change localizedLatticeMap p m π
    ((integerMatrixMap (PrimeLocalIntegers p) m B).mulVec x) = 0
  rw [localizedLatticeMap_matrix p m π B T hB,
    show localizedLatticeMap p m π x = 0 from hx, map_zero]

/-- Invariance under `J,Y` for the actual local kernel follows from the two
integer group actions on the given quotient. -/
theorem localizedLatticeMap_kernel_shifts (p m : ℕ) [Fact p.Prime]
    (hm : 2 ≤ m) (hp : m < p)
    (π : (Fin m → ℤ) →ₗ[ℤ] M) (U E : M →ₗ[ℤ] M)
    (hU : ∀ v, π ((integralExponential m (shiftJ m)).mulVec v) = U (π v))
    (hE : ∀ v, π ((weightedExponential m 1).mulVec v) = E (π v)) :
    (∀ x ∈ (localizedLatticeMap p m π).ker,
      (shiftJ m).mulVec x ∈ (localizedLatticeMap p m π).ker) ∧
    (∀ x ∈ (localizedLatticeMap p m π).ker,
      (shiftY m).mulVec x ∈ (localizedLatticeMap p m π).ker) :=
  primeLocal_shifts_preserve_of_integral_actions p m hm hp _
    (localizedLatticeMap_kernel_preserves p m π _ U hU)
    (localizedLatticeMap_kernel_preserves p m π _ E hE)

/-- The actual finite-quotient obstruction passes from the exponential
commutator to the unscaled polynomial matrix, after localization. -/
theorem localizedLatticeMap_not_mem_exponent_range (p m : ℕ) [Fact p.Prime]
    [Finite M] (hm : 2 ≤ m) (hp : m < p)
    (π : (Fin m → ℤ) →ₗ[ℤ] M)
    (B : Matrix (Fin m) (Fin m) ℤ) (hB : LowerGap 1 B)
    (T : M →ₗ[ℤ] M)
    (hT : ∀ v, π ((integralExponential m B - 1).mulVec v) = T (π v))
    (c : M) (hc : c ∉ T.range) (hpc : (p : ℤ) • c ∈ T.range) :
    LocalizedModule.mkLinearMap (integerPrimeIdeal p).primeCompl M c ∉
      ((localizedLatticeMap p m π).comp
        (integerMatrixMap (PrimeLocalIntegers p) m B).mulVecLin).range := by
  rintro ⟨v, hv⟩
  have hvB : (integerMatrixMap (PrimeLocalIntegers p) m B).mulVec v ∈
      (integerMatrixMap (PrimeLocalIntegers p) m (integralExponential m B - 1)).mulVecLin.range := by
    rw [primeLocal_integralExponential_range p m hm hp B hB]
    exact LinearMap.mem_range_self _ v
  obtain ⟨w, hw⟩ := hvB
  apply primeLocal_not_mem_range p T c hc hpc
  refine ⟨localizedLatticeMap p m π w, ?_⟩
  rw [← localizedLatticeMap_matrix p m π (integralExponential m B - 1) T hT w]
  exact (congrArg (localizedLatticeMap p m π) hw).trans hv

/-- Transport the proved localized obstruction to the actual quotient by the
constructed kernel. The preservation proof only makes the displayed map defined. -/
theorem localizedLatticeMap_quotient_obstruction (p m : ℕ) [Fact p.Prime]
    [Finite M] (hm : 2 ≤ m) (hp : m < p)
    (π : (Fin m → ℤ) →ₗ[ℤ] M) (hπ : Function.Surjective π)
    (B : Matrix (Fin m) (Fin m) ℤ) (hB : LowerGap 1 B)
    (T : M →ₗ[ℤ] M)
    (hT : ∀ v, π ((integralExponential m B - 1).mulVec v) = T (π v))
    (c : Fin m → ℤ) (hc : π c ∉ T.range) (hpc : (p : ℤ) • π c ∈ T.range)
    (hpres : ∀ x ∈ (localizedLatticeMap p m π).ker,
      (integerMatrixMap (PrimeLocalIntegers p) m B).mulVec x ∈
        (localizedLatticeMap p m π).ker) :
    (localizedLatticeMap p m π).ker.mkQ (fun i => (c i : PrimeLocalIntegers p)) ∉
      (quotientMatrix (localizedLatticeMap p m π).ker
        (integerMatrixMap (PrimeLocalIntegers p) m B) hpres).range := by
  let S := (localizedLatticeMap p m π).ker
  let e := (localizedLatticeMap p m π).quotKerEquivOfSurjective
    (localizedLatticeMap_surjective p m π hπ)
  rintro ⟨z, hz⟩
  obtain ⟨x, rfl⟩ := S.mkQ_surjective z
  have hh := congrArg e hz
  change e (S.mkQ ((integerMatrixMap (PrimeLocalIntegers p) m B).mulVec x)) =
    e (S.mkQ (fun i => (c i : PrimeLocalIntegers p))) at hh
  have hx : localizedLatticeMap p m π
      ((integerMatrixMap (PrimeLocalIntegers p) m B).mulVec x) =
      LocalizedModule.mkLinearMap (integerPrimeIdeal p).primeCompl M (π c) := by
    change localizedLatticeMap p m π
      ((integerMatrixMap (PrimeLocalIntegers p) m B).mulVec x) = _ at hh
    rw [← localizedLatticeMap_intVector p m π c]
    exact hh
  exact localizedLatticeMap_not_mem_exponent_range p m hm hp π B hB T hT
    (π c) hc hpc ⟨x, hx⟩

end LocalizedLattice

end NilpotentConjugacy
