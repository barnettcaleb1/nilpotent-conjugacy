# Verification scope

## What is formalized

[`cubicFamily_main`](NilpotentConjugacy/CubicTheorem.lean) proves the explicit cubic lower-bound construction. Its group is `ManuscriptGroup (4*d)`, the actual integral semidirect product from the paper, with its exponential action proved to exist. The statement assumes only the integer parameter restriction `2 ≤ d`.

It concludes finite generation, torsion-freeness, nilpotence, exact nilpotency class `4*d`, and an actual subnormal series with `8*d` infinite cyclic quotients. It also proves that finite word generating sets exist and that **every** such generating set has the stated polynomial lower bound.

More precisely, put $E=3d^2(d+1)$. For every finite generating set $S$, there are positive integers $C,N$ such that, for every integer $n\ge N$, there are actual elements $a,b$ with

$$
|a|_S,|b|_S\le n,\qquad a\not\sim b,\qquad
D_G(a,b)<\infty,\qquad n^E\le C D_G(a,b).
$$

Here $D_G(a,b)$ is the infimum of the orders of **actual finite separating group quotients**. Finite depth is part of the conclusion, so the lower estimate is not obtained from an infinite value. `conjugacyDepth_attained` proves that a finite depth is attained by an actual quotient. The resulting bound on the supremum of depths in the word ball is `cubicFamily_polynomialConjugacyLower`.

The manuscript remains a research draft pending independent review. No literature-priority claim follows from these checks, and the whole paper, including its cited external results, is not claimed to be formalized.

## Conventions and correspondence

### Group and structural invariants

`IntegralGroup.lean` constructs integer exponential matrices and their units. `IntegralGroupAction.lean` proves the full action law, including negative integer parameters, and defines

$$
G(m)=\mathbb Z^m\rtimes\bigl(\mathbb Z^{m-1}\rtimes\mathbb Z\bigr).
$$

The coefficient lattice is identified with $W=m!\mathbb ZJ+\cdots+m!\mathbb ZJ^{m-1}$ by an injective polynomial map. Its cyclic action is the paper’s $\exp(\operatorname{ad}Y)$. `GroupProperties.lean` proves the faithful representation and its equivalence with the generated matrix group. The affine embedding, explicit unitriangular central filtration, and nonzero final commutator establish torsion-freeness and exact class $m$.

`InfiniteCyclicSubnormalSeries` records genuine nested normal subgroups and explicit isomorphisms from their actual quotients to the infinite cyclic group. `manuscriptGroup_infiniteCyclicSubnormalSeries` constructs $2m$ such factors. This is the series certificate for Hirsch length $2m$. A separate canonical numeric Hirsch-length API and its general invariance theorem have not been introduced.

### Words and compression

`WordRep` is a list of generators or their inverses whose product equals the specified element. `wordLength` is the minimum such length. `wordGeneratingSet_iff_finitelyGenerated` proves equivalence with the usual subgroup-closure definition of finite generation, and `wordLength_compare` proves comparison between finite generating sets.

The compression proof constructs nested commutator words, assembles base digits, bounds every higher coefficient, and cancels the higher coordinates by descending induction. The actual weighted exponential actions are handled integrally: their cyclic-chain vectors have factorial leading coefficients, and a proved fixed-power transfer clears these factors. This supplies the needed coordinate bounds without assuming the paper’s general rational Jordan-block compression lemma.

The formal proof uses the subsequence $s=wk$ and radius proportional to $p^k$. This avoids real roots and preserves the exponent $w(m-w)(w+1-\lfloor m/2\rfloor)$. All constants may depend on the fixed group, prime, and generating set; none depends on $k$ or the radius.

### Arbitrary finite quotients

`SemidirectConjugacy.lean` proves the conjugacy criterion against every possible conjugator. `DescentGroupImage.lean` constructs the finite abelian normal image from an arbitrary homomorphism to a finite group. `DescentLocalization.lean` constructs its actual localization and relation kernel, proves finiteness and cardinality control, and preserves the detected obstruction.

`QuotientDescent.lean` recovers $J,Y$ from the integral exponential actions using nilpotent polynomial inversion over the actual ring $\mathbb Z_{(p)}$. No rational vector-space structure is imposed on a finite group. Matrix-unit interpolation and detecting characters then give the cardinality estimate.

`specialPair_finite_quotient_cardinality` applies this argument to every finite homomorphism separating the specified pair; surjectivity, a semidirect-product structure on the quotient, and a primary-group hypothesis are not assumed. The lower bound is $p^{s(m-w)(w+1-\lfloor m/2\rfloor)}$.

### Nonconjugacy and finite detection

`SpecialPairs.lean` defines the exact elements and their coordinate formulas. `PairNonconjugacy.lean` proves nonconjugacy in the original group by integral divisibility. `PairFiniteQuotient.lean` reduces the actual group modulo $p^{s(m-w)}$ into a finite affine group, proves separation there against all conjugators, and restricts the homomorphism to its range to obtain a surjective finite quotient. Thus each selected pair has finite separating depth independently of any general conjugacy-separability theorem.

### Depth and growth

`FiniteGroupQuotient` contains an actual finite group, its group instance, a homomorphism, and a surjectivity proof. Quotient order is `Nat.card` of that carrier. `conjugacyDepth` takes the infimum of those orders over separating quotients; the empty infimum is infinity. `conjugacyGrowth` takes the supremum over actual nonconjugate pairs in a finite word ball, with baseline value one.

The growth codomain is the extended naturals, allowing the definitions to precede a global conjugacy-separability theorem. `FiniteDepthPolynomialWitness`, used in the main theorem, explicitly rules out infinite depths as its witnesses. `conjugacyGrowth_lt_top` proves finiteness of growth under the usual conjugacy-separability hypothesis; that hypothesis is not used to obtain the lower-bound witnesses.

### No universal quadratic exponent

`NoQuadraticBound.lean` defines the manuscript's polynomial comparison, including its positive integer prefactor and radius rescaling. Its real-exponent upper predicate explicitly requires finite growth before applying `toNat`. `no_universal_quadratic_exponent` proves that for every real $A$, there is $d\ge2$ such that, in every finite word metric of the same constructed group, this comparison fails for exponent $A(8d)^2$. The parameter is chosen before the word metric. The actual cyclic-series certificate justifies the count $8d$.

The proof first shows that an actual lower bound of integer degree $E$ contradicts any upper comparison of smaller integer degree, with all constants and the radius threshold retained. It then majorizes $A$ by an integer and uses monotonicity of real powers. This is a consequence about the actual growth function, rather than only an inequality between candidate exponents.

## Remaining scope

- The cited general theorem that finitely generated nilpotent groups are conjugacy separable is not formalized here. In particular, this package does not prove that **every** nonconjugate pair in the constructed group has finite depth. It proves this for all pairs used in the lower bound.
- The cited universal upper bound and the paper’s full cubic-envelope corollary are not formalized.
- The concrete-pair theorem uses $m\le2w$. This includes $m=4d,w=3d$ and proves the main family, but omits the paper’s odd-dimensional boundary case $w=(m-1)/2$.
- The general rational single-Jordan-block compression statement is not formalized in its full generality. All coordinate compression needed for the constructed family is proved directly.
- The exact conjugacy growth of these groups, literature priority, and independent human review remain open questions or external tasks.

These limits do not supply assumptions to `cubicFamily_main`; they delimit which other assertions of the paper are included.

## Trust and reproducibility

The package pins Lean and Mathlib. `scripts/verify.py` imports every mathematical module, builds with warnings as errors, replays compiled declarations through Lean’s kernel, rejects admissions, custom axioms, unsafe declarations and `native_decide`, and checks transitive axioms of public and private package declarations. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.

The run record includes exact source hashes and command outcomes. The compiler, kernel, libraries, and build environment form the verification setting. A fresh-context AI-assisted semantic review can check correspondence but is not independent human review or a premise of any Lean proof.
