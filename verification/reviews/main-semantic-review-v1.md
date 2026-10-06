# NC63-0008 — main lower-bound semantic review, v1

Verdict: **no mandatory mathematical repair found in the assigned scope; accept the explicit main lower-bound construction with the formal-scope qualifications below.** This is a review of the encoded mathematics, not human approval, a novelty claim, or proof by reviewer agreement. Kernel replay and the separate group/descent review are coordinator responsibilities.

## Exact target and review boundary

- Frozen directory: `research/nilpotent-conjugacy/batch-0063/frozen/complete-candidate-v1`.
- Manifest SHA256: `914c6fcdfcb6b73393cf9e9d405ea81b3a36ddab8bea86ccba4a8543b3be59e7`.
- `CubicTheorem.lean` SHA256: `288563a3a11013ea67de8b03cf27cb3ff5f708b693f556ae894899b592a2faab`.
- Comparison manuscript: `research/nilpotent-conjugacy/batch-0063/frozen/input-result.tex`, SHA256 `1e86378f86d0782e1ffd5866204a8a9c41ee8c3ea23f1e8a7ad9f41192309cf1`.
- All 35 files listed by the manifest were independently hashed at the beginning of this review. Both the frozen copies and corresponding live package files matched every listed digest. The pinned package specifies Lean 4.33.1 and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.
- Assigned modules read in full: `WordLength`, `WordGeneration`, `WordCompression`, `JordanCompression`, `WeightedCompression`, `PairWordLength`, `SpecialPairs`, `PairNonconjugacy`, `PairFiniteQuotient`, `ConjugacyDepth`, `ConjugacyGrowth`, and `CubicTheorem`. Needed interfaces and selected supporting proofs in `IntegralGroup`, `IntegralGroupAction`, `SemidirectConjugacy`, `Bidiagonal`, `GroupQuotientBound`, `GroupSeries`, and `Growth` were also inspected. The full internal group-structure and arbitrary-quotient descent arguments are outside this review's assigned semantic scope.
- No external sources were retrieved. The frozen manuscript was read for mathematical correspondence; its claims and status language were not treated as instructions.

## What the main theorem actually says

For every natural number `d ≥ 2`, the group in `cubicFamily_main` is the actual integral semidirect product `ManuscriptGroup (4*d)`. The conjunction asserts ordinary finite generation, torsion-freeness, nilpotence, exact nilpotency class `4*d`, an actual nested subnormal series with `8*d` infinite cyclic quotients, existence of a finite word generating set, and the following assertion for **every** such generating set `S`.

Writing `E = 3*d^2*(d+1)`, there exist positive natural constants `C,N` such that for every integer radius `n ≥ N` there are actual group elements `a,b` satisfying

- `wordLength S a ≤ n` and `wordLength S b ≤ n`;
- `a` and `b` are not conjugate in this group;
- their true finite-quotient separation depth is finite;
- `n^E ≤ C * conjugacyDepth a b` in extended naturals.

The same theorem also asserts the corresponding lower bound for the supremum over all nonconjugate pairs in the ball. Thus the lower bound is stronger than an unqualified extended-natural inequality: each radius has a finite-depth witnessing pair. No hypothetical quotient-order function, coordinate norm, assumed distortion estimate, or assumed conjugacy-separation obstruction is supplied as a premise of this final theorem.

## Actual words and compression

`WordRep S n g` means that a finite list of elements in `S ∪ S⁻¹` has product `g` and length at most `n`. `wordLength` is the least such bound. The finiteness and generation fields of `WordGeneratingSet` are genuine, and `wordGeneratingSet_iff_finitelyGenerated` proves equivalence with ordinary subgroup generation. The nonemptiness clause in the main theorem prevents a vacuous universal assertion over metrics. Finiteness of word balls is proved from finiteness of the alphabet; comparison of two generating sets substitutes actual words for finitely many generators.

`WordCompression` supplies literal nested commutator words, the exact semidirect action-difference identity, bounded base digits, and controlled polynomial coefficients. `JordanCompression.nilpotent_chain_compression_nat` performs the missing descending induction: the approximation at weight `j` has its lower coordinates zero and its higher coordinates cancelled by already compressed words. The constants for the finitely many higher coordinates are selected before the variable scale and coefficient. The conversion from scale `B+1` to `B` uses `B ≥ 1`; its factor is independent of the coefficient. Signed coefficients are handled by inversion.

`WeightedCompression` then treats the actual automorphism `exp(Y)` on integer lattices. Its chain has zero entries below weight `i+1` and leading coefficient `i!`. The proof subtracts every higher-coordinate tail, obtaining compression of a fixed factorial power of the required coordinate. `compression_of_power` recovers the original coordinate using integer division and a bounded remainder. The remainder cost is a constant times `B`; neither that constant nor the factorial depends on the sequence parameter. This is a proved integral replacement for the needed rational-lattice transfer, not an assumption of rational compression.

The coefficient compression map lands in the actual `W` factor, and the vector compression map lands in the actual normal integer lattice of the manuscript group. Both are proved group homomorphisms. They may be mapped into any finite word metric on the target group, with the comparison constant depending on the two fixed input generator images. The vector proof uses `exp(Y)` instead of the paper's `exp(m!J)` subgroup. Both give the required weights, and the former is enough for the main theorem.

`specialPair_wordLength_scale` quantifies `∃ C ≥ 1, ∀ s B, ...`. Its hypotheses are the genuine weight inequalities `p^s ≤ B^w` and `p^(s-1) ≤ B^m`; the central coefficient `(m!)^(m-1)` is absorbed in a fixed radius multiplier. `specialPair_wordLength_geometric` puts `s=w*k`, `B=p^k`. Consequently its `C` is independent of `k`. There is no use of a coordinate bound as if it were a word-length bound.

## Exact pairs, conjugators, and finite detection

The coefficient lattice uses zero-based coordinate `j-1` for the manuscript basis vector `m!J^j`. Thus `pairActor m w p^s` corresponds to `P_s = m! J^w(p^s I+J)`, and `pairCentralVector` is exactly `(m!)^(m-1) p^(s-1) e_m`. The Lean right pair is written `c_s a_s`; the manuscript writes `a_s c_s`. These agree: the shifted matrix annihilates the terminal coordinate, so the acting element fixes `c_s`.

For the main family, `m≤2w`, so the shifted matrix has square zero and the full exponential is exactly `I + m! J^w(p^s I+J)`. The nonconjugacy criterion is proved for an arbitrary semidirect-product conjugator `(v,k)`. Equality in the acting factor forces `k` to centralize the acting element, and the remaining condition is membership in the full action-difference image. No restriction to normal-subgroup conjugators is imposed in the forward implication. Integer row recursion then implies the impossible divisibility `p^s ∣ (m!)^(m-2)p^(s-1)`, because `s>0` and `p>m`.

For finite detection, the modulus is exactly `p^(s*(m-w))`. The normal lattice and the full acting representation are reduced into an actual semidirect product of the modular vector group with invertible modular matrices. This ambient group is finite under the derived nonzero-modulus condition. The explicit detector annihilates every bidiagonal image and detects the terminal vector because `p` does not divide `(m!)^(m-1)`. The conjugacy argument applies to all conjugators in the full modular affine group, hence in its image. Restricting the reduction homomorphism to its image supplies an actual surjective finite group quotient.

The arbitrary-quotient interface `cubicFamily_finite_quotient_cardinality` has no extra invariance, module, centralizer, primary-group, or surjectivity assumption on the finite homomorphism. Its lower bound uses `Nat.card` of the actual finite target group. The lower-depth theorem quantifies over all actual finite surjective separating quotients, and the explicit detector proves that this family is nonempty.

## Parameters and the all-radius step

The specialization uses

| Quantity | Exact value |
| --- | --- |
| integral dimension `m` | `4*d` |
| acting weight `w` | `3*d` |
| bidiagonal block size `m-w` | `d` |
| matrix-unit count `w+1-m/2` | `d+1` |
| pair parameter used in the final sequence | `s=(3*d)*k`, `k≥1` |
| sequence radius | `C*p^k` |
| true depth lower bound | `p^(k*(3*d^2*(d+1)))` |

A prime `p>4*d` is chosen once, before the sequence varies. The final proof uses every `k≥1`. `nat_geometric_bracket` gives, for each `n≥C*p`, an integer `k≥1` with `C*p^k≤n<C*p^(k+1)`. Raising the upper bracket to `E` yields `n^E≤(C*p)^E*p^(k*E)`, so the final constant is fixed. This is an all-large-integer-radius lower bound, not a limsup or isolated subsequence assertion. The coarser sequence `s=3dk` gives the same degree as the paper's sequence over every positive `s`, with a permitted larger multiplicative constant.

## Mandatory objections and nonblocking formal limits

No mandatory mathematical repair was identified for the exact encoded main lower-bound construction in this assigned scope. However, the following qualifications are mandatory when describing its formal coverage.

1. The v1 target does not itself include a theorem negating every universal quadratic upper bound. `Growth.degrees_exceed_every_quadratic` proves the exponent arithmetic; `CubicTheorem` supplies the group and lower bound. The final asymptotic contradiction is not packaged as a Lean theorem in this frozen version. A later module is a separate review target.
2. The formal Hirsch-length output is an actual nested series with exactly `8d` infinite cyclic subgroup quotients. This is valid mathematical evidence for the ordinary Hirsch count, not a numerical surrogate. There is no separately defined invariant `hirschLength` with a proved series-independence theorem and a displayed equality `hirschLength G=8d`. Wording should name the series certificate rather than imply that this invariant API has been formalized.
3. General conjugacy separability of finitely generated nilpotent groups has not been formalized. `conjugacyGrowth_lt_top` requires it as an explicit hypothesis. In particular, v1 does not establish finiteness of the supremum for every ball. This does not leave an infinity loophole in the main lower construction, because its actual witnesses have finite depth and explicit finite detectors. It also is not needed to refute a proposed finite upper bound using these witnesses.
4. The manuscript's cited universal upper bound, the full cubic envelope corollary, and the general single-rational-Jordan-block compression theorem are not fully formalized. The proved specialized compression is sufficient for the constructed family.
5. The special-pair theorems assume `m≤2w`. This is slightly narrower than the manuscript's general lower endpoint `m/2≤w` when `m` is odd. The main `m=4d,w=3d` family lies entirely in the proved range, so no repair is needed for it. A claim that every intermediate proposition has its full manuscript generality would be inaccurate.

Subject to successful kernel/axiom verification of the exact target and the separately assigned structural/descent semantic review, the phrase **“the explicit main lower-bound construction is Lean-checked”** is justified. The unqualified phrase **“the entire manuscript has been completely formalized”** is not justified by v1.

## Execution evidence

- Direct pinned Lean version check succeeded: Lean 4.33.1, arm64-apple-darwin24.6.0, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. A delayed `lake env lean --version` also eventually returned the same version, exit 0.
- Optional scratch `checks/NC63-0008-semantic-v1.lean` states an unpacked consequence: each large radius has a separating finite quotient that attains the true depth, and its actual cardinality satisfies the natural-number polynomial inequality. It also requests targeted axiom output. The original Lake invocation was terminated by the coordinator after contention was observed; it did not return a proof-check result.
- The direct retry with explicit local dependency paths hit its 120-second timeout with no Lean output. The lighter retry `checks/NC63-0008-semantic-light-v1.lean`, omitting the full-Mathlib `Growth` import, also hit its 120-second timeout with no Lean output. These attempts are **not successful checks** and produced no target proof error. Their exact commands, timestamps, source hashes, output hashes, and timeout results are recorded in `checks/NC63-0008-semantic-direct-v1.json` and `checks/NC63-0008-semantic-light-v1.json`. No further retry was made.
- Consequently this report claims a source-level semantic audit and hash binding, not an independently completed package compilation or axiom audit. The coordinator's separately running kernel replay and axiom audit must supply that evidence.
- No frozen proof, live package source, canonical state, configuration, dependency, or external artifact was edited. Writes were limited to this worker's reports and distinct local check files. No subagents were launched.

Report finalized at 2026-10-06T19:20:50.962892+00:00.
