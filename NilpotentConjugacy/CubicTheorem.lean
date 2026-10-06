import NilpotentConjugacy.GroupClass
import NilpotentConjugacy.GroupSeries
import NilpotentConjugacy.GroupQuotientBound
import NilpotentConjugacy.PairNonconjugacy
import NilpotentConjugacy.PairFiniteQuotient
import NilpotentConjugacy.PairWordLength
import NilpotentConjugacy.ConjugacyGrowth
import NilpotentConjugacy.WordGeneration
import Mathlib.Data.Nat.Prime.Infinite

/-!
# The explicit cubic lower-bound family

The group is the manuscript's actual integral semidirect product. Every large
radius is witnessed by actual nonconjugate elements with finite separating
depth. The cyclic-series clause constructs the 8d infinite cyclic factors
that give the manuscript's Hirsch-length calculation. No quotient bound,
word-compression estimate, or group-structure assertion is assumed here.

The separate general theorem that all finitely generated nilpotent groups are
conjugacy separable, and the cited universal upper bound, are not formalized.
-/

namespace NilpotentConjugacy

/-- The actual separating depth of the chosen pair has the claimed bound. -/
theorem cubicFamily_depth_lower (p d s : ℕ) [Fact p.Prime]
    (hd : 2 ≤ d) (hp : 4*d < p) (hs : 0 < s) :
    (p^(s*d*(d+1)) : ℕ∞) ≤
      conjugacyDepth (specialPairLeft (4*d) (3*d) p s)
        (specialPairRight (4*d) (3*d) p s) := by
  apply le_conjugacyDepth
  intro q hq
  exact cubicFamily_finite_quotient_cardinality p d s hd hp hs q.hom hq

/-- In every finite word metric, each sufficiently large radius has an actual
pair of finite separating depth at least a fixed positive multiple of n^E,
where E=3d²(d+1). Finiteness of the witnesses is part of the conclusion. -/
theorem cubicFamily_finiteDepthPolynomialWitness (d : ℕ) (hd : 2 ≤ d)
    (S : WordGeneratingSet (ManuscriptGroup (4*d))) :
    FiniteDepthPolynomialWitness S (3*d^2*(d+1)) := by
  obtain ⟨p,hp,hprime⟩ := Nat.exists_infinite_primes (4*d+1)
  have : Fact p.Prime := ⟨hprime⟩
  have hpd : 4*d < p := by omega
  obtain ⟨C,hC,hwords⟩ := specialPair_wordLength_geometric (4*d) (3*d) p S
    (by omega) (by omega) (by omega) hprime.one_lt
  apply finiteDepthPolynomialWitness_of_geometric_pairs S (by omega : 0<C) hprime.one_lt
  intro k hk
  have hs : 0 < (3*d)*k := by nlinarith
  refine ⟨specialPairLeft (4*d) (3*d) p ((3*d)*k),
    specialPairRight (4*d) (3*d) p ((3*d)*k),
    (hwords k).1,(hwords k).2,?_,?_,?_⟩
  · exact specialPair_not_isConj p (4*d) (3*d) ((3*d)*k)
      (by omega) (by omega) (by omega) hpd hs
  · exact specialPair_conjugacyDepth_lt_top p (4*d) (3*d) ((3*d)*k)
      (by omega) (by omega) (by omega) hpd hs
  · have he : (3*d*k)*d*(d+1)=k*(3*d^2*(d+1)) := by ring
    simpa only [he] using cubicFamily_depth_lower p d ((3*d)*k) hd hpd hs

/-- The all-radius cubic-degree lower bound for the actual conjugacy growth
function, for every specified finite generating set. -/
theorem cubicFamily_polynomialConjugacyLower (d : ℕ) (hd : 2 ≤ d)
    (S : WordGeneratingSet (ManuscriptGroup (4*d))) :
    PolynomialConjugacyLower S (3*d^2*(d+1)) :=
  (cubicFamily_finiteDepthPolynomialWitness d hd S).lowerBound S _

/-- Main construction theorem: actual finite generation, torsion-freeness,
nilpotence of exact class 4d, an actual series of 8d infinite cyclic quotients,
and finite-depth polynomial witnesses in every finite word metric. -/
theorem cubicFamily_main (d : ℕ) (hd : 2 ≤ d) :
    Group.FG (ManuscriptGroup (4*d)) ∧
    IsMulTorsionFree (ManuscriptGroup (4*d)) ∧
    Group.IsNilpotent (ManuscriptGroup (4*d)) ∧
    Group.nilpotencyClass (ManuscriptGroup (4*d)) = 4*d ∧
    InfiniteCyclicSubnormalSeries (ManuscriptGroup (4*d)) (8*d) ∧
    Nonempty (WordGeneratingSet (ManuscriptGroup (4*d))) ∧
    ∀ S : WordGeneratingSet (ManuscriptGroup (4*d)),
      FiniteDepthPolynomialWitness S (3*d^2*(d+1)) ∧
      PolynomialConjugacyLower S (3*d^2*(d+1)) := by
  have : Fact (3 ≤ 4*d) := ⟨by omega⟩
  refine ⟨inferInstance,inferInstance,inferInstance,
    manuscriptGroup_nilpotencyClass (by omega),?_,?_,?_⟩
  · simpa only [show 2*(4*d)=8*d by omega] using
      manuscriptGroup_infiniteCyclicSubnormalSeries (m:=4*d) (by omega)
  · exact wordGeneratingSet_iff_finitelyGenerated.mpr inferInstance
  · intro S
    exact ⟨cubicFamily_finiteDepthPolynomialWitness d hd S,
      cubicFamily_polynomialConjugacyLower d hd S⟩

end NilpotentConjugacy
