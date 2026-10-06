import NilpotentConjugacy.WordLength
import Mathlib.GroupTheory.Finiteness

namespace NilpotentConjugacy
variable {G : Type*} [Group G]

/-- Generation by words is exactly generation as a subgroup. -/
theorem wordRep_exists_iff_mem_closure (S : Set G) (g : G) :
    (∃ n : ℕ, WordRep S n g) ↔ g ∈ Subgroup.closure S := by
  constructor
  · rintro ⟨n,w,hw,rfl,_⟩
    apply Subgroup.list_prod_mem
    intro x hx
    rcases hw x hx with h | h
    · exact Subgroup.subset_closure h
    · exact (Subgroup.inv_mem_iff _).mp (Subgroup.subset_closure h)
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact ⟨1, WordRep.generator hx⟩
    | one => exact ⟨0, WordRep.one S⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨n,hn⟩ := ihx
      obtain ⟨m,hm⟩ := ihy
      exact ⟨n+m,hn.mul hm⟩
    | inv x hx ih =>
      obtain ⟨n,hn⟩ := ih
      exact ⟨n,hn.inv⟩

theorem wordGeneratingSet_iff_finitelyGenerated :
    Nonempty (WordGeneratingSet G) ↔ Group.FG G := by
  constructor
  · rintro ⟨S⟩
    apply Group.fg_iff.mpr
    refine ⟨S.generators, ?_, S.finite⟩
    apply top_unique
    intro g _
    exact (wordRep_exists_iff_mem_closure S.generators g).mp (S.generates g)
  · intro hG
    obtain ⟨S,hS,hfin⟩ := Group.fg_iff.mp hG
    refine ⟨⟨S,hfin,fun g => ?_⟩⟩
    apply (wordRep_exists_iff_mem_closure S g).mpr
    rw [hS]
    trivial

end NilpotentConjugacy
