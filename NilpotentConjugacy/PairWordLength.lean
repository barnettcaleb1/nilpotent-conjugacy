import NilpotentConjugacy.WeightedCompression
import NilpotentConjugacy.SpecialPairs

/-! Actual finite-generator word bounds for the manuscript's explicit pairs. -/
namespace NilpotentConjugacy
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem pairActor_split (m w : ℕ) (t : ℤ) :
    (SemidirectProduct.inr (pairActor m w t) : ManuscriptGroup m) =
      SemidirectProduct.inr (SemidirectProduct.inl
        (Multiplicative.ofAdd (t • coordinateVector ℤ (m - 1) (w - 1)))) *
      SemidirectProduct.inr (SemidirectProduct.inl
        (Multiplicative.ofAdd (coordinateVector ℤ (m - 1) w))) := by
  rw [← map_mul, ← map_mul]
  rfl

/-- Both members of the actual pair have linearly bounded word length whenever
their scalar coordinates fit the corresponding weight boxes. -/
theorem specialPair_wordLength_scale (m w p : ℕ)
    (S : WordGeneratingSet (ManuscriptGroup m)) (hm : 4 ≤ m) (hw : 1 ≤ w)
    (hwm : w ≤ m - 2) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ s B : ℕ, 1 ≤ B → p ^ s ≤ B ^ w →
      p ^ (s - 1) ≤ B ^ m →
      wordLength S (specialPairLeft m w p s) ≤ C * B ∧
      wordLength S (specialPairRight m w p s) ≤ C * B := by
  let iw : Fin (m - 1) := ⟨w - 1, by omega⟩
  let im : Fin m := ⟨m - 1, by omega⟩
  obtain ⟨Ca, hCa, hactor⟩ := coefficient_coordinate_wordLength m S iw
  obtain ⟨Cv, _, hvector⟩ := vector_coordinate_wordLength m S im
  let fixed : ManuscriptGroup m := SemidirectProduct.inr (SemidirectProduct.inl
    (Multiplicative.ofAdd (coordinateVector ℤ (m - 1) w)))
  let La := Ca + wordLength S fixed
  let K := m.factorial ^ (m - 1)
  let R := K + 1
  let Lc := Cv * R
  refine ⟨La + Lc, by dsimp [La, Lc]; omega, ?_⟩
  intro s B hB ha hc
  have hleft : wordLength S (specialPairLeft m w p s) ≤ La * B := by
    have hs : ((p : ℤ) ^ s).natAbs ≤ B ^ (iw.val + 1) := by
      simpa only [Int.natAbs_pow, Int.natAbs_natCast, iw, show w - 1 + 1 = w by omega] using ha
    have hact := hactor B hB ((p : ℤ) ^ s) hs
    unfold specialPairLeft
    rw [pairActor_split]
    apply (wordLength_mul_le _ _ _).trans
    calc
      wordLength S (SemidirectProduct.inr (SemidirectProduct.inl
          (Multiplicative.ofAdd ((p : ℤ) ^ s • coordinateVector ℤ (m - 1) (w - 1))))) +
          wordLength S fixed ≤ Ca * B + wordLength S fixed := Nat.add_le_add_right hact _
      _ ≤ Ca * B + wordLength S fixed * B := Nat.add_le_add_left
        (by simpa using Nat.mul_le_mul_left (wordLength S fixed) hB) _
      _ = La * B := by dsimp [La]; ring
  have hcentral : wordLength S (SemidirectProduct.inl
      (Multiplicative.ofAdd (pairCentralVector m p s))) ≤ Lc * B := by
    have hscalar : (((m.factorial : ℤ) ^ (m - 1) * (p : ℤ) ^ (s - 1))).natAbs ≤
        (R * B) ^ (im.val + 1) := by
      simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
      have hbound := fixed_coefficient_radius K B m m hB le_rfl (by omega)
      have hmul : K * p ^ (s - 1) ≤ K * B ^ m := Nat.mul_le_mul_left K hc
      simpa only [im, show m - 1 + 1 = m by omega] using hmul.trans hbound
    have hRB : 1 ≤ R * B := by dsimp [R]; nlinarith
    have hv := hvector (R * B) hRB
      ((m.factorial : ℤ) ^ (m - 1) * (p : ℤ) ^ (s - 1)) hscalar
    simpa only [pairCentralVector, im, Lc, Nat.mul_assoc] using hv
  constructor
  · exact hleft.trans (Nat.mul_le_mul_right B (Nat.le_add_right _ _))
  · unfold specialPairRight
    apply (wordLength_mul_le _ _ _).trans
    calc
      wordLength S (SemidirectProduct.inl (Multiplicative.ofAdd (pairCentralVector m p s))) +
          wordLength S (specialPairLeft m w p s) ≤ Lc * B + La * B :=
        Nat.add_le_add hcentral hleft
      _ = (La + Lc) * B := by ring

/-- Actual geometric pair-length bound used by the all-radius growth argument.
The estimate holds for every natural `k`, hence also for all `k ≥ 1`. -/
theorem specialPair_wordLength_geometric (m w p : ℕ)
    (S : WordGeneratingSet (ManuscriptGroup m)) (hm : 4 ≤ m) (hw : 1 ≤ w)
    (hwm : w ≤ m - 2) (hp : 1 < p) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ k : ℕ,
      wordLength S (specialPairLeft m w p (w * k)) ≤ C * p ^ k ∧
      wordLength S (specialPairRight m w p (w * k)) ≤ C * p ^ k := by
  obtain ⟨C, hC, hbound⟩ := specialPair_wordLength_scale m w p S hm hw hwm
  refine ⟨C, hC, fun k => hbound (w * k) (p ^ k) (Nat.one_le_pow k p (by omega)) ?_ ?_⟩
  · rw [← pow_mul, Nat.mul_comm k w]
  · have hwm' : w ≤ m := by omega
    have hexp : w * k - 1 ≤ k * m := by
      calc
        w * k - 1 ≤ w * k := Nat.sub_le _ _
        _ = k * w := Nat.mul_comm _ _
        _ ≤ k * m := Nat.mul_le_mul_left k hwm'
    simpa only [pow_mul] using Nat.pow_le_pow_right (by omega : 1 ≤ p) hexp

end
end NilpotentConjugacy
