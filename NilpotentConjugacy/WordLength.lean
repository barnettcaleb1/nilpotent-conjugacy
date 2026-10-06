import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic

/-!
Actual word length in a finite generating set. A letter is a generator or the
inverse of one; `WordRep S n g` records a finite list of such letters whose
product is `g` and whose length is at most `n`. No coordinate size is used.
-/

namespace NilpotentConjugacy

variable {G H : Type*} [Group G] [Group H]

/-- A word of at most `n` letters from `S ∪ S⁻¹` representing `g`. -/
def WordRep (S : Set G) (n : ℕ) (g : G) : Prop :=
  ∃ w : List G, (∀ x ∈ w, x ∈ S ∨ x⁻¹ ∈ S) ∧ w.prod = g ∧ w.length ≤ n

namespace WordRep

variable {S T : Set G} {n m : ℕ} {g h : G}

theorem one (S : Set G) : WordRep S 0 1 := ⟨[], by simp⟩

theorem generator (hg : g ∈ S) : WordRep S 1 g :=
  ⟨[g], by simp [hg]⟩

theorem mono (h : WordRep S n g) (hn : n ≤ m) : WordRep S m g := by
  obtain ⟨w, hw, rfl, hlen⟩ := h
  exact ⟨w, hw, rfl, hlen.trans hn⟩

theorem mono_generators (h : WordRep S n g) (hST : S ⊆ T) : WordRep T n g := by
  obtain ⟨w, hw, rfl, hlen⟩ := h
  exact ⟨w, fun x hx => (hw x hx).imp (fun h => hST h) (fun h => hST h), rfl, hlen⟩

theorem mul (hg : WordRep S n g) (hh : WordRep S m h) : WordRep S (n + m) (g * h) := by
  obtain ⟨v, hv, rfl, hvl⟩ := hg
  obtain ⟨w, hw, rfl, hwl⟩ := hh
  refine ⟨v ++ w, ?_, by simp, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hv x hx
    · exact hw x hx
  · simp only [List.length_append]
    omega

theorem inv (hg : WordRep S n g) : WordRep S n g⁻¹ := by
  obtain ⟨w, hw, rfl, hlen⟩ := hg
  refine ⟨(w.map Inv.inv).reverse, ?_, ?_, by simpa using hlen⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hx)
    simpa only [inv_inv, or_comm] using hw y hy
  · exact (List.prod_inv_reverse w).symm

theorem inv_iff : WordRep S n g⁻¹ ↔ WordRep S n g :=
  ⟨fun h => by simpa using h.inv, fun h => h.inv⟩

theorem pow (hg : WordRep S n g) (k : ℕ) : WordRep S (k * n) (g ^ k) := by
  induction k with
  | zero => simpa using one S
  | succ k ih => simpa [pow_succ, Nat.succ_mul] using ih.mul hg

theorem zpow (hg : WordRep S n g) (k : ℤ) : WordRep S (k.natAbs * n) (g ^ k) := by
  cases k with
  | ofNat k => simpa using hg.pow k
  | negSucc k => simpa [zpow_negSucc] using (hg.pow (k + 1)).inv

theorem eq_one_of_zero (hg : WordRep S 0 g) : g = 1 := by
  obtain ⟨w, _, hprod, hlen⟩ := hg
  have : w = [] := List.length_eq_zero_iff.mp (by omega)
  simpa [this] using hprod.symm

theorem map (f : G →* H) (hg : WordRep S n g) : WordRep (f '' S) n (f g) := by
  obtain ⟨w, hw, rfl, hlen⟩ := hg
  refine ⟨w.map f, ?_, (map_list_prod f w).symm, by simpa using hlen⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  rcases hw y hy with hs | hs
  · exact Or.inl ⟨y, hs, rfl⟩
  · exact Or.inr ⟨y⁻¹, hs, by simp⟩

/-- Substituting words of length at most `C` for all generators. -/
theorem substitute (hST : ∀ s ∈ S, WordRep T m s) (hg : WordRep S n g) :
    WordRep T (m * n) g := by
  obtain ⟨w, hw, rfl, hlen⟩ := hg
  suffices h : WordRep T (m * w.length) w.prod from
    h.mono (Nat.mul_le_mul_left _ hlen)
  clear hlen
  induction w with
  | nil => simpa using one T
  | cons x xs ih =>
    have hx : WordRep T m x := by
      rcases hw x (by simp) with hx | hx
      · exact hST x hx
      · simpa using (hST x⁻¹ hx).inv
    have hxs := ih (fun y hy => hw y (by simp [hy]))
    simpa [Nat.mul_add, Nat.add_comm] using hx.mul hxs

theorem commutator (hg : WordRep S n g) (hh : WordRep S m h) :
    WordRep S (2 * (n + m)) (g * h * g⁻¹ * h⁻¹) := by
  simpa [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    ((hg.mul hh).mul hg.inv).mul hh.inv

end WordRep

/-- A finite generating set, with generation expressed by actual words. -/
structure WordGeneratingSet (G : Type*) [Group G] where
  generators : Set G
  finite : generators.Finite
  generates : ∀ g : G, ∃ n : ℕ, WordRep generators n g

/-- Minimum length of an actual word in the specified finite generating set. -/
noncomputable def wordLength (S : WordGeneratingSet G) (g : G) : ℕ :=
  by classical exact Nat.find (S.generates g)

theorem wordLength_rep (S : WordGeneratingSet G) (g : G) :
    WordRep S.generators (wordLength S g) g := by
  classical
  exact Nat.find_spec (S.generates g)

theorem wordLength_le_iff (S : WordGeneratingSet G) (g : G) (n : ℕ) :
    wordLength S g ≤ n ↔ WordRep S.generators n g := by
  classical
  constructor
  · exact fun h => (wordLength_rep S g).mono h
  · exact Nat.find_min' (S.generates g)

@[simp] theorem wordLength_one (S : WordGeneratingSet G) : wordLength S 1 = 0 := by
  exact Nat.eq_zero_of_le_zero ((wordLength_le_iff S 1 0).2 (WordRep.one _))

@[simp] theorem wordLength_eq_zero (S : WordGeneratingSet G) (g : G) :
    wordLength S g = 0 ↔ g = 1 := by
  constructor
  · intro h
    exact ((wordLength_le_iff S g 0).1 (by omega)).eq_one_of_zero
  · rintro rfl
    exact wordLength_one S

@[simp] theorem wordLength_inv (S : WordGeneratingSet G) (g : G) :
    wordLength S g⁻¹ = wordLength S g := by
  apply Nat.le_antisymm
  · exact (wordLength_le_iff _ _ _).2 (wordLength_rep S g).inv
  · simpa using (wordLength_le_iff S g (wordLength S g⁻¹)).2
      (by simpa using (wordLength_rep S g⁻¹).inv)

theorem wordLength_mul_le (S : WordGeneratingSet G) (g h : G) :
    wordLength S (g * h) ≤ wordLength S g + wordLength S h :=
  (wordLength_le_iff _ _ _).2 ((wordLength_rep S g).mul (wordLength_rep S h))

theorem wordLength_zpow_le (S : WordGeneratingSet G) (g : G) (k : ℤ) :
    wordLength S (g ^ k) ≤ k.natAbs * wordLength S g :=
  (wordLength_le_iff _ _ _).2 ((wordLength_rep S g).zpow k)

/-- Every two finite generating sets give linearly comparable word lengths. -/
theorem wordLength_compare (S T : WordGeneratingSet G) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ g, wordLength T g ≤ C * wordLength S g := by
  obtain ⟨C, hC⟩ := (S.finite.image (wordLength T)).bddAbove
  refine ⟨max 1 C, le_max_left _ _, fun g => ?_⟩
  apply (wordLength_le_iff _ _ _).2
  apply WordRep.substitute (m := max 1 C) (S := S.generators)
  · intro s hs
    apply (wordLength_le_iff _ _ _).1
    exact (hC ⟨s, hs, rfl⟩).trans (le_max_right _ _)
  · exact wordLength_rep S g

/-- Finiteness of a ball follows from finiteness of the alphabet of actual words. -/
theorem finite_wordRep_ball {S : Set G} (hS : S.Finite) (n : ℕ) :
    {g : G | WordRep S n g}.Finite := by
  let A : Set G := S ∪ Inv.inv '' S
  have hA : A.Finite := hS.union (hS.image Inv.inv)
  let : Finite A := hA.to_subtype
  have hf := (List.finite_length_le A n).image
    (fun w : List A => (List.map (fun a : A => a.val) w).prod)
  apply hf.subset
  intro g hg
  obtain ⟨w, hw, hprod, hlen⟩ := hg
  have hletters : ∀ x ∈ w, x ∈ A := by
    intro x hx
    rcases hw x hx with hs | hs
    · exact Or.inl hs
    · exact Or.inr ⟨x⁻¹, hs, inv_inv x⟩
  refine ⟨w.attach.map (fun x => (⟨x.val, hletters x.val x.property⟩ : A)), ?_, ?_⟩
  · simpa using hlen
  · change ((w.attach.map (fun x => (⟨x.val, hletters x.val x.property⟩ : A))).map
      (fun a : A => (a : G))).prod = g
    rw [List.map_map]
    change (w.attach.map (fun x : {x // x ∈ w} => x.val)).prod = g
    simpa only [List.map_subtype, List.unattach_attach, List.map_id_fun', id_eq] using hprod

theorem finite_wordLength_ball (S : WordGeneratingSet G) (n : ℕ) :
    {g : G | wordLength S g ≤ n}.Finite := by
  simpa only [wordLength_le_iff] using finite_wordRep_ball S.finite n

end NilpotentConjugacy
