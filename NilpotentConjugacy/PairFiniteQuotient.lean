import NilpotentConjugacy.GroupQuotientBound
import NilpotentConjugacy.ConjugacyDepth
import NilpotentConjugacy.PairNonconjugacy
import NilpotentConjugacy.Bidiagonal
import Mathlib.Algebra.Group.Units.Hom

/-! An explicit finite separating quotient of the actual manuscript group. -/

namespace NilpotentConjugacy

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Invertible matrices over a commutative ring act on its column vectors. -/
def ringMatrixAction (R : Type*) [CommRing R] (m : ℕ) :
    (Matrix (Fin m) (Fin m) R)ˣ →* MulAut (Multiplicative (Fin m → R)) where
  toFun U := AddEquiv.toMultiplicative
    { toFun := U.val.mulVec
      invFun := U.inv.mulVec
      left_inv := by intro v; rw [Matrix.mulVec_mulVec, U.inv_val, Matrix.one_mulVec]
      right_inv := by intro v; rw [Matrix.mulVec_mulVec, U.val_inv, Matrix.one_mulVec]
      map_add' := Matrix.mulVec_add U.val }
  map_one' := by ext v i; simp
  map_mul' U V := by ext v i; exact congrFun (Matrix.mulVec_mulVec v.toAdd U.val V.val).symm i

@[simp] theorem ringMatrixAction_apply (R : Type*) [CommRing R] (m : ℕ)
    (U : (Matrix (Fin m) (Fin m) R)ˣ) (v : Multiplicative (Fin m → R)) :
    (ringMatrixAction R m U v).toAdd = U.val.mulVec v.toAdd := rfl

/-- Entrywise reduction of the integer normal lattice. -/
def latticeReduction (m N : ℕ) : (Fin m → ℤ) →+ (Fin m → ZMod N) where
  toFun v i := (v i : ZMod N)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

/-- The actual acting representation reduced modulo N. -/
noncomputable def actorReduction (m N : ℕ) :
    CoefficientGroup m →* (Matrix (Fin m) (Fin m) (ZMod N))ˣ :=
  (Units.map (integerMatrixMap (ZMod N) m).toMonoidHom).comp (manuscriptRhoHom m)

/-- The finite ambient affine group in which the detector lives. -/
abbrev ModularAffineGroup (m N : ℕ) :=
  SemidirectProduct (Multiplicative (Fin m → ZMod N))
    (Matrix (Fin m) (Fin m) (ZMod N))ˣ (ringMatrixAction (ZMod N) m)

theorem latticeReduction_equivariant (m N : ℕ) (h : CoefficientGroup m) :
    (latticeReduction m N).toMultiplicative.comp (manuscriptAction m h).toMonoidHom =
      (ringMatrixAction (ZMod N) m (actorReduction m N h)).toMonoidHom.comp
        (latticeReduction m N).toMultiplicative := by
  apply MonoidHom.ext
  intro v
  apply Multiplicative.toAdd.injective
  ext i
  change ((manuscriptRhoHom m h).val.mulVec v.toAdd i : ZMod N) =
    (integerMatrixMap (ZMod N) m (manuscriptRhoHom m h).val).mulVec
      (fun j => (v.toAdd j : ZMod N)) i
  exact (Int.castRingHom (ZMod N)).map_mulVec _ _ i

/-- The homomorphism reducing the actual group to a modular affine group. -/
noncomputable def manuscriptReduction (m N : ℕ) :
    ManuscriptGroup m →* ModularAffineGroup m N :=
  SemidirectProduct.map (latticeReduction m N).toMultiplicative (actorReduction m N)
    (latticeReduction_equivariant m N)

instance modularAffineGroup_finite (m N : ℕ) [NeZero N] :
    Finite (ModularAffineGroup m N) := by
  exact Finite.of_injective (fun x : ModularAffineGroup m N => (x.left, x.right))
    (by intro x y h; cases x; cases y; cases h; rfl)

@[simp] theorem manuscriptReduction_inl (m N : ℕ) (v : Fin m → ℤ) :
    manuscriptReduction m N (SemidirectProduct.inl (Multiplicative.ofAdd v)) =
      SemidirectProduct.inl (Multiplicative.ofAdd (latticeReduction m N v)) := by
  exact SemidirectProduct.map_inl _ _ _ _

@[simp] theorem manuscriptReduction_inr (m N : ℕ) (h : CoefficientGroup m) :
    manuscriptReduction m N (SemidirectProduct.inr h) =
      SemidirectProduct.inr (actorReduction m N h) := by
  exact SemidirectProduct.map_inr _ _ _ _

/-- The square nonzero block is obtained by restricting actual matrix rows;
this statement works over every commutative coefficient ring. -/
theorem shiftedBidiagonal_block {R : Type*} [CommRing R]
    (m w n : ℕ) (hn : m - w = n + 1) (hw : w < m)
    (t : R) (x : Fin m → R) (i : Fin (n + 1)) :
    (shiftedBidiagonalMatrix m w t).mulVec x ⟨i.val + w, by have := i.isLt; omega⟩ =
      bidiagonal t n (fun j => x ⟨j.val, by have := j.isLt; omega⟩) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using shiftedBidiagonal_first hw t x
  · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (shiftedBidiagonal_successor (m := m) (w := w) (i := j.val)
        (by have := j.isLt; omega) t x)

/-- The explicit finite character rules out the full shifted matrix image,
with the exact modulus `p^(s*(m-w))` and the original terminal coordinate. -/
theorem modular_shiftedBidiagonal_separates (p : ℕ) (hp : p.Prime)
    (m w s C : ℕ) (hw : w < m) (hs : 0 < s) (hC : ¬ p ∣ C) :
    ¬ ∃ x : Fin m → ZMod (p ^ (s * (m - w))),
      (shiftedBidiagonalMatrix m w ((p : ZMod (p ^ (s * (m - w)))) ^ s)).mulVec x =
        ((C : ZMod (p ^ (s * (m - w)))) *
          (p : ZMod (p ^ (s * (m - w)))) ^ (s - 1)) •
            coordinateVector (ZMod (p ^ (s * (m - w)))) m (m - 1) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m - w ≠ 0)
  rw [hn]
  rintro ⟨x, hx⟩
  apply finiteDetector_separates_image p hp s hs n C hC
  refine ⟨fun j => x ⟨j.val, by have := j.isLt; omega⟩, ?_⟩
  ext i
  rw [← shiftedBidiagonal_block m w n hn hw _ x i]
  have hi := congrFun hx ⟨i.val + w, by have := i.isLt; omega⟩
  have hlast : i.val + w = m - 1 ↔ i = Fin.last n := by
    constructor
    · intro he
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    · intro he
      subst i
      simp only [Fin.val_last]
      omega
  simpa [coordinateVector, Pi.single_apply, hlast] using hi

theorem actorReduction_pair_matrix (m N w : ℕ) (hm : 4 ≤ m)
    (hw : 1 ≤ w) (hwm : w < m - 1) (hmw : m ≤ 2*w) (t : ℤ) :
    (actorReduction m N (pairActor m w t)).val =
      1 + (m.factorial : ZMod N) • shiftedBidiagonalMatrix m w (t : ZMod N) := by
  change integerMatrixMap (ZMod N) m (manuscriptRhoHom m (pairActor m w t)).val = _
  rw [pairActor_matrix m w hm hw hwm hmw t, map_add, map_one,
    integerMatrixMap_smul, integerMatrixMap_shiftedBidiagonal]
  simp

theorem actorReduction_pair_difference (m N w : ℕ) (hm : 4 ≤ m)
    (hw : 1 ≤ w) (hwm : w < m - 1) (hmw : m ≤ 2*w) (t : ℤ)
    (v : Fin m → ZMod N) :
    (ringMatrixAction (ZMod N) m (actorReduction m N (pairActor m w t))
      (Multiplicative.ofAdd v)).toAdd - v =
      (m.factorial : ZMod N) • (shiftedBidiagonalMatrix m w (t : ZMod N)).mulVec v := by
  rw [ringMatrixAction_apply, actorReduction_pair_matrix m N w hm hw hwm hmw t,
    Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  change v + _ - v = _
  abel

theorem latticeReduction_central (m N p s : ℕ) :
    latticeReduction m N (pairCentralVector m p s) =
      (((m.factorial ^ (m - 1) : ℕ) : ZMod N) * (p : ZMod N) ^ (s - 1)) •
        coordinateVector (ZMod N) m (m - 1) := by
  ext i
  by_cases hi : i.val = m - 1 <;>
    simp [latticeReduction, pairCentralVector, coordinateVector, hi]

/-- Reduction modulo the detector modulus separates the exact manuscript pair,
including conjugation by every element of the full modular affine group. -/
theorem manuscriptReduction_separates_specialPair (p m w s : ℕ) [Fact p.Prime]
    (hm : 4 ≤ m) (hmw : m ≤ 2*w) (hwhi : w ≤ m - 2)
    (hp : m < p) (hs : 0 < s) :
    ¬ IsConj (manuscriptReduction m (p ^ (s * (m - w))) (specialPairLeft m w p s))
      (manuscriptReduction m (p ^ (s * (m - w))) (specialPairRight m w p s)) := by
  have hprime : p.Prime := Fact.out
  have hw : 1 ≤ w := by omega
  have hwm : w < m - 1 := by omega
  have hpM : ¬ p ∣ m.factorial := (hprime.dvd_factorial).not.mpr (by omega)
  have hC : ¬ p ∣ m.factorial ^ (m - 1) := fun h => hpM (hprime.dvd_of_dvd_pow h)
  intro hc
  simp only [specialPairRight, specialPairLeft, map_mul, manuscriptReduction_inl,
    manuscriptReduction_inr] at hc
  obtain ⟨v, hv⟩ := (semidirect_isConj_iff_difference_range _ _ _).mp hc
  have hv' := congrArg Multiplicative.toAdd hv
  change (ringMatrixAction _ _ _ v).toAdd + -v.toAdd = _ at hv'
  rw [← sub_eq_add_neg] at hv'
  have hact := actorReduction_pair_difference m (p ^ (s * (m - w))) w
    hm hw hwm hmw ((p : ℤ)^s) v.toAdd
  simp only [ofAdd_toAdd] at hact
  rw [hact, toAdd_ofAdd, latticeReduction_central] at hv'
  simp only [Int.cast_pow, Int.cast_natCast] at hv'
  apply modular_shiftedBidiagonal_separates p hprime m w s
    (m.factorial ^ (m - 1)) (by omega) hs hC
  refine ⟨(m.factorial : ZMod (p ^ (s * (m - w)))) • v.toAdd, ?_⟩
  rw [Matrix.mulVec_smul]
  exact hv'

/-- Restricting modular reduction to its image gives an actual surjective
finite group quotient; no residual-finiteness assumption is used. -/
noncomputable def modularFiniteQuotient (m N : ℕ) [NeZero N] :
    FiniteGroupQuotient (ManuscriptGroup m) :=
  finiteGroupQuotientOfHom (manuscriptReduction m N).rangeRestrict
    (manuscriptReduction m N).rangeRestrict_surjective

theorem rangeRestrict_not_isConj {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (a b : G) (hsep : ¬ IsConj (f a) (f b)) :
    ¬ IsConj (f.rangeRestrict a) (f.rangeRestrict b) := by
  intro hc
  exact hsep (isConj_map f.range.subtype hc)

/-- The manuscript pair has an actual finite separating quotient with the
explicit detector modulus. -/
theorem specialPair_exists_separatingQuotient (p m w s : ℕ) [Fact p.Prime]
    (hm : 4 ≤ m) (hmw : m ≤ 2*w) (hwhi : w ≤ m - 2)
    (hp : m < p) (hs : 0 < s) :
    Nonempty (SeparatingQuotient (specialPairLeft m w p s) (specialPairRight m w p s)) := by
  have hprime : p.Prime := Fact.out
  let : NeZero (p ^ (s * (m - w))) := ⟨pow_ne_zero _ hprime.ne_zero⟩
  exact ⟨⟨modularFiniteQuotient m (p ^ (s * (m - w))),
    rangeRestrict_not_isConj (manuscriptReduction m (p ^ (s * (m - w)))) _ _
      (manuscriptReduction_separates_specialPair p m w s hm hmw hwhi hp hs)⟩⟩

/-- The named pair has finite conjugacy depth, with no general conjugacy
separability assumption on the manuscript group. -/
theorem specialPair_conjugacyDepth_lt_top (p m w s : ℕ) [Fact p.Prime]
    (hm : 4 ≤ m) (hmw : m ≤ 2*w) (hwhi : w ≤ m - 2)
    (hp : m < p) (hs : 0 < s) :
    conjugacyDepth (specialPairLeft m w p s) (specialPairRight m w p s) < ⊤ :=
  (conjugacyDepth_lt_top_iff _ _).mpr
    (specialPair_exists_separatingQuotient p m w s hm hmw hwhi hp hs)

/-- The full lower bound is attained at a finite depth for the exact pair. -/
theorem specialPair_conjugacyDepth_bounds (p m w s : ℕ) [Fact p.Prime]
    (hm : 4 ≤ m) (hmw : m ≤ 2*w) (hwhi : w ≤ m - 2)
    (hp : m < p) (hs : 0 < s) :
    (p ^ (s * (m-w) * (w+1-m/2)) : ℕ) ≤
        conjugacyDepth (specialPairLeft m w p s) (specialPairRight m w p s) ∧
      conjugacyDepth (specialPairLeft m w p s) (specialPairRight m w p s) < ⊤ := by
  constructor
  · apply le_conjugacyDepth
    intro q hq
    exact specialPair_finite_quotient_cardinality p m w s hm hmw hwhi hp hs q.hom hq
  · exact (conjugacyDepth_lt_top_iff _ _).mpr
      (specialPair_exists_separatingQuotient p m w s hm hmw hwhi hp hs)

end NilpotentConjugacy
