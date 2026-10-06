import NilpotentConjugacy.GroupClass
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Actual series with infinite cyclic factors

`PolyZSeries G n` records a nested sequence of actual normal kernel subgroups,
terminating in the trivial group, with exactly n successive quotients isomorphic
to the infinite cyclic group. Each step includes a surjective homomorphism onto
`Multiplicative ℤ`; `cyclicStepQuotientEquiv` supplies its actual quotient isomorphism.
This is a series certificate, not an assigned numeric rank or a replacement group.
-/

namespace NilpotentConjugacy
universe u

/-- A genuine nested subnormal series with n infinite cyclic factors. -/
inductive PolyZSeries : (G : Type u) → [Group G] → ℕ → Prop
  | trivial {G : Type u} [Group G] (h : ∀ g : G, g = 1) : PolyZSeries G 0
  | step {G : Type u} [Group G] {n : ℕ}
      (f : G →* Multiplicative ℤ) (hf : Function.Surjective f)
      (kernelSeries : PolyZSeries f.ker n) : PolyZSeries G (n + 1)

/-- The quotient at every step is the actual quotient by its normal kernel. -/
noncomputable def cyclicStepQuotientEquiv {G : Type u} [Group G]
    (f : G →* Multiplicative ℤ) (hf : Function.Surjective f) :
    G ⧸ f.ker ≃* Multiplicative ℤ :=
  QuotientGroup.quotientKerEquivOfSurjective f hf

/-- Transport of a kernel along an explicit group equivalence. -/
def kernelCompEquiv {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (f : H →* Multiplicative ℤ) :
    (f.comp e.toMonoidHom).ker ≃* f.ker where
  toFun x := ⟨e x.val, x.property⟩
  invFun y := ⟨e.symm y.val, by
    change f (e (e.symm y.val)) = 1
    rw [e.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_mul' x y := Subtype.ext (e.map_mul x.val y.val)

/-- A group equivalence transports the complete subgroup-series certificate. -/
theorem PolyZSeries.of_equiv {G H : Type u} [Group G] [Group H] {n : ℕ}
    (e : G ≃* H) (h : PolyZSeries H n) : PolyZSeries G n := by
  induction h generalizing G with
  | trivial h =>
    apply PolyZSeries.trivial
    intro g
    apply e.injective
    simpa using h (e g)
  | step f hf hs ih =>
    exact PolyZSeries.step (f.comp e.toMonoidHom) (hf.comp e.surjective)
      (ih (kernelCompEquiv e f))

/-- Restrict a surjection to the kernel of a further cyclic quotient. -/
def restrictedKernelHom {G H : Type u} [Group G] [Group H]
    (f : G →* H) (q : H →* Multiplicative ℤ) :
    (q.comp f).ker →* q.ker where
  toFun x := ⟨f x.val, x.property⟩
  map_one' := Subtype.ext f.map_one
  map_mul' x y := Subtype.ext (f.map_mul x.val y.val)

theorem restrictedKernelHom_surjective {G H : Type u} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (q : H →* Multiplicative ℤ) :
    Function.Surjective (restrictedKernelHom f q) := by
  intro y
  obtain ⟨x, hx⟩ := hf y.val
  refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
  change q (f x) = 1
  rw [hx]
  exact y.property

/-- The kernel of the restricted homomorphism is exactly the original kernel. -/
def restrictedKernelKerEquiv {G H : Type u} [Group G] [Group H]
    (f : G →* H) (q : H →* Multiplicative ℤ) :
    (restrictedKernelHom f q).ker ≃* f.ker where
  toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
  invFun y := ⟨⟨y.val, by change q (f y.val) = 1; rw [y.property, map_one]⟩,
    Subtype.ext y.property⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl

/-- If the quotient is trivial, the actual kernel is the entire group. -/
def wholeKernelEquiv {G H : Type u} [Group G] [Group H]
    (f : G →* H) (hH : ∀ h : H, h = 1) : G ≃* f.ker where
  toFun g := ⟨g, hH (f g)⟩
  invFun g := g.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Concatenation of genuine cyclic subgroup series through an exact surjection.
The proof constructs each new subgroup as an actual kernel, rather than merely
adding formal labels for ranks. -/
theorem PolyZSeries.extension {G H : Type u} [Group G] [Group H] {a b : ℕ}
    (f : G →* H) (hf : Function.Surjective f)
    (hk : PolyZSeries f.ker a) (hH : PolyZSeries H b) : PolyZSeries G (a + b) := by
  induction hH generalizing G with
  | trivial h =>
    simpa using PolyZSeries.of_equiv (wholeKernelEquiv f h) hk
  | @step H _ b q hq hqk ih =>
    have hker : PolyZSeries (restrictedKernelHom f q).ker a :=
      PolyZSeries.of_equiv (restrictedKernelKerEquiv f q) hk
    have hseries := ih (restrictedKernelHom f q) (restrictedKernelHom_surjective f hf q) hker
    simpa only [Nat.add_assoc] using PolyZSeries.step (q.comp f) (hq.comp hf) hseries

/-- The head coordinate of the actual free abelian integer lattice. -/
def integerVectorHead (n : ℕ) :
    Multiplicative (Fin (n + 1) → ℤ) →* Multiplicative ℤ where
  toFun v := Multiplicative.ofAdd (v.toAdd 0)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem integerVectorHead_surjective (n : ℕ) : Function.Surjective (integerVectorHead n) := by
  intro a
  exact ⟨Multiplicative.ofAdd (fun _ => a.toAdd), rfl⟩

/-- Its actual kernel is explicitly the remaining n integer coordinates. -/
def integerVectorHeadKernelEquiv (n : ℕ) :
    (integerVectorHead n).ker ≃* Multiplicative (Fin n → ℤ) where
  toFun x := Multiplicative.ofAdd (fun i => x.val.toAdd i.succ)
  invFun v := ⟨Multiplicative.ofAdd (Fin.cons 0 v.toAdd), rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (congrArg Multiplicative.toAdd x.property).symm
    · rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The free abelian group of rank n has a checked series of n infinite cyclic quotients. -/
theorem integerVector_polyZSeries (n : ℕ) : PolyZSeries (Multiplicative (Fin n → ℤ)) n := by
  induction n with
  | zero =>
    apply PolyZSeries.trivial
    intro g
    exact Subsingleton.elim _ _
  | succ n ih =>
    exact PolyZSeries.step (integerVectorHead n) (integerVectorHead_surjective n)
      (PolyZSeries.of_equiv (integerVectorHeadKernelEquiv n) ih)

/-- The infinite cyclic group itself has one genuine cyclic factor. -/
theorem integers_polyZSeries : PolyZSeries (Multiplicative ℤ) 1 := by
  apply PolyZSeries.step (MonoidHom.id _) Function.surjective_id
  apply PolyZSeries.trivial
  intro g
  exact Subtype.ext g.property

/-- The kernel of the canonical projection of the actual semidirect product
is explicitly equivalent to its normal factor. -/
noncomputable def semidirectRightKernelEquiv {N H : Type u} [Group N] [Group H]
    (φ : H →* MulAut N) :
    (SemidirectProduct.rightHom : SemidirectProduct N H φ →* H).ker ≃* N :=
  (MulEquiv.subgroupCongr (SemidirectProduct.range_inl_eq_ker_rightHom (φ := φ))).symm.trans
    (MonoidHom.ofInjective (SemidirectProduct.inl_injective (φ := φ))).symm

theorem semidirect_polyZSeries {N H : Type u} [Group N] [Group H] {a b : ℕ}
    (φ : H →* MulAut N) (hN : PolyZSeries N a) (hH : PolyZSeries H b) :
    PolyZSeries (SemidirectProduct N H φ) (a + b) :=
  PolyZSeries.extension SemidirectProduct.rightHom SemidirectProduct.rightHom_surjective
    (PolyZSeries.of_equiv (semidirectRightKernelEquiv φ) hN) hH

/-- A genuine series of m infinite cyclic quotients for W ⋊ ℤ. -/
theorem coefficientGroup_polyZSeries {m : ℕ} (hm : 1 ≤ m) : PolyZSeries (CoefficientGroup m) m := by
  convert semidirect_polyZSeries (coefficientAction m) (integerVector_polyZSeries (m - 1))
    integers_polyZSeries using 1
  omega

/-- The manuscript group has an actual subnormal series with exactly 2m
infinite cyclic factors. This is the structural series certificate underlying
its Hirsch-length calculation. -/
theorem manuscriptGroup_polyZSeries {m : ℕ} (hm : 1 ≤ m) :
    PolyZSeries (ManuscriptGroup m) (2 * m) := by
  convert semidirect_polyZSeries (manuscriptAction m) (integerVector_polyZSeries m)
    (coefficientGroup_polyZSeries hm) using 1
  omega

/-- A recursive representation of an actual subnormal subgroup series.
Each node names its normal subgroup and includes an explicit equivalence from
the actual subgroup quotient to the infinite cyclic group. Recursive nodes are
subgroups of the preceding subgroup, so this is a genuine nested series. -/
inductive InfiniteCyclicSubnormalSeries : (G : Type u) → [Group G] → ℕ → Prop
  | trivial {G : Type u} [Group G] (h : ∀ g : G, g = 1) :
      InfiniteCyclicSubnormalSeries G 0
  | step {G : Type u} [Group G] {n : ℕ} (N : Subgroup G) [N.Normal]
      (quotientEquiv : G ⧸ N ≃* Multiplicative ℤ)
      (subgroupSeries : InfiniteCyclicSubnormalSeries N n) :
      InfiniteCyclicSubnormalSeries G (n + 1)

/-- Every step of the kernel certificate supplies its actual quotient
isomorphism; no abstract extension-additivity hypothesis is assumed. -/
theorem PolyZSeries.to_subnormalSeries {G : Type u} [Group G] {n : ℕ}
    (h : PolyZSeries G n) : InfiniteCyclicSubnormalSeries G n := by
  induction h with
  | trivial h => exact InfiniteCyclicSubnormalSeries.trivial h
  | step f hf hs ih =>
    exact InfiniteCyclicSubnormalSeries.step f.ker (cyclicStepQuotientEquiv f hf) ih

/-- A direct series formulation of the manuscript's Hirsch-length claim:
exactly 2m successive actual subgroup quotients are explicitly infinite cyclic. -/
theorem manuscriptGroup_infiniteCyclicSubnormalSeries {m : ℕ} (hm : 1 ≤ m) :
    InfiniteCyclicSubnormalSeries (ManuscriptGroup m) (2 * m) :=
  (manuscriptGroup_polyZSeries hm).to_subnormalSeries

/-- The manuscript's full structural assertion, using its explicit integral
semidirect product and an actual series with 2m infinite cyclic quotients. -/
theorem manuscriptGroup_structure (m : ℕ) (hm : 4 ≤ m) :
    Group.FG (ManuscriptGroup m) ∧ IsMulTorsionFree (ManuscriptGroup m) ∧
      Group.IsNilpotent (ManuscriptGroup m) ∧
      Group.nilpotencyClass (ManuscriptGroup m) = m ∧
      InfiniteCyclicSubnormalSeries (ManuscriptGroup m) (2 * m) := by
  have : Fact (3 ≤ m) := ⟨by omega⟩
  exact ⟨inferInstance, inferInstance, inferInstance,
    manuscriptGroup_nilpotencyClass (by omega),
    manuscriptGroup_infiniteCyclicSubnormalSeries (by omega)⟩

end NilpotentConjugacy
