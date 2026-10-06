# Verification scope

## Status

This is a partial formalization accompanying an **unverified research draft**. Lean checking establishes the propositions expressed by the included Lean declarations, subject to their explicit hypotheses and the standard Lean axioms. It does not establish that the manuscript's main theorem has been formalized, that the paper is correct, or that its claims are new.

The paper's proposed main claim is the existence, for every integer $d\ge2$, of a torsion-free finitely generated nilpotent group of class $4d$, Hirsch length $8d$, and conjugacy-separation growth bounded below by a positive multiple of $n^{3d^2(d+1)}$ for all sufficiently large integer radii in every fixed finite word metric.

**No Lean declaration in this release states and proves that claim.**

## Correspondence with the paper

### Integral bidiagonal arithmetic and finite detection

`last_mem_bidiagonal_range_iff` proves that the final coordinate vector with coefficient $k$ lies in the image of the integral lower bidiagonal map $tI+J$, for $t\ne0$, exactly when $t\mid k$. Its dimension is `n + 1`, the paper's tail length $r$.

`bidiagonal_recurrence_exact_order` proves the exact order $p^{s(n+1)}$ from adjacent recurrence, terminal annihilation by $p^s$, and a detected multiple of the last term. The finite detector is an actual linear map on `ZMod (p^(s*(n+1)))` coordinates; its annihilation and nonzero value are proved for arbitrary permitted parameters. The formal detector codomain is this residue ring rather than $\mathbb Q/\mathbb Z$; identifying the two descriptions and embedding it in the manuscript's affine group quotient remain separate tasks.

### Matrix units

The indices in `MatrixUnits.lean` are zero based. A matrix's row is its output coordinate and its column is its input coordinate. Thus `shiftJ` and `shiftY` implement the paper's $Je_i=e_{i+1}$ and $Ye_i=i e_{i+1}$ after shifting the index by one.

`matrixUnit_mem_of_gap` proves the interpolation conclusion for a commutative ring with explicit unit hypotheses on every denominator. `matrixUnit_mem_primeLocal_adjoin` specializes to the localization at the prime ideal $(p)\subset\mathbb Z$, with $p>m$, and gaps at least `m / 2`. This is the paper's threshold $\lceil(m-1)/2\rceil$.

`matrixUnit_preserves_primeLocal` proves preservation of any submodule that is already invariant under both shifts. It does **not** prove that the kernel obtained from a finite quotient of the manuscript's group is invariant under those shifts. Recovering the shifts from the integral exponential actions is an additional obligation.

### Finite-character bound

`exists_detecting_character` constructs a character into `AddCircle (1 : ℚ)`, representing $\mathbb Q/\mathbb Z$, which vanishes on a specified subgroup and detects an element outside it.

`finite_cardinality_of_delta_characters` proves $N^q\le |A|$ by an explicit injection of the coefficient grid into a finite abelian group $A$. It uses delta evaluations with a common value of exact order $N$; the cardinality bound is a conclusion, not a hypothesis. This direct counting route avoids the paper's appeal to equality of the orders of a finite abelian group and its dual.

`finite_quotient_character_bound` proves $p^{srq}\le |A|$ from positive $s,r$, a subgroup $H\le A$, bidiagonal columns modulo $H$, a terminal annihilation relation, a terminal obstruction, and actual additive endomorphisms with the required delta values. `ambient_finite_quotient_character_bound` transfers the result through an explicit injection $A\to Q$ with $Q$ finite. The ambient $Q$ is just a finite type in this last lemma; no group construction or conjugacy assertion is silently attached to it.

### Actual finite module quotients

`QuotientModule.lean` joins the matrix and character arguments on the actual quotient $A=(R^m)/S$, where $R=\mathbb Z_{(p)}$. It defines the induced linear endomorphisms and derives their coordinate values.

`primeLocal_quotient_cardinality` assumes $p>m\ge4$, $\lfloor m/2\rfloor\le w\le m-2$, $s>0$, finiteness of this quotient, invariance of $S$ under both shifts, and nonmembership of $D p^{s-1}\overline e_m$ in the image of the actual induced operator $J^w(p^sI+J)$. It proves $p^{s(m-w)(w+1-\lfloor m/2\rfloor)}\le |A|$. The floor is Lean's natural-number division. The delta endomorphisms and bidiagonal columns are derived rather than assumed in this theorem. The multiplier $D$ is an arbitrary natural number; the obstruction hypothesis itself supplies the required nonvanishing.

The passage from a separating group quotient to such an invariant submodule and obstruction remains outside the formalization.

### Growth arithmetic

`specialized_exponent`, `specialized_parameters`, `cubic_degree_lower`, and `degrees_exceed_every_quadratic` verify the numerical specialization $m=4d,w=3d$, the proposed cubic degree, and its comparison with every fixed quadratic coefficient.

`geometric_polynomial_lower` proves an all-radius bound for a real-valued function from a hypothesis that supplies a lower bound at every sufficiently large radius above each geometric scale. This hypothesis must still be established for the manuscript's conjugacy-separation growth function. The lemma does not define that function or construct short words in a group.

## Obligations still outside Lean

1. Construct the integral groups $G(m)$, prove the action law and integrality of their exponential matrices, and establish finite generation, torsion-freeness, nilpotency class $m$, and Hirsch length $2m$.
2. Formalize word length for the specified generating sets and prove the constructive compression estimates, including the rational Jordan-block lattice reduction and constants uniform in the sequence parameter.
3. Construct the selected group elements, prove their nonconjugacy, and connect their word lengths to the geometric scales used in the growth argument.
4. Starting from **every** finite separating group quotient, obtain the finite abelian primary component and its localized module structure; prove the obstruction survives and that its kernel is invariant under $J,Y$. This includes the truncated logarithm argument and equality of the relevant operator images.
5. Apply the finite residue-ring detector inside the actual affine group quotient and prove that separation holds against every possible conjugator.
6. Define the conjugacy-separation depth and growth function, connect the formal algebra to those definitions, transfer between finite generating sets, and complete the all-radius main theorem and the comparison relation used in the paper.
7. Formalize the cited external upper bound and its application to the cubic envelope, if that corollary is to be included in a full formal verification.

These are substantive missing formal proofs. They are not discharged by compilation, arithmetic examples, source scans, or an AI-assisted correspondence review. The draft's independent mathematical verification and its literature priority remain pending.

## Trust and reproducibility

The package pins Lean and Mathlib. Its source check rejects admissions, user-declared axioms, unsafe declarations, and `native_decide` in mathematical modules. The axiom audit examines transitive dependencies, including imported declarations, and permits only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

The checker, elaborator, standard library, Mathlib, and build environment still form part of the verification setting. The axiom audit checks the formal dependency boundary; correspondence with the informal statement requires a separate mathematical review. No external human review is claimed.
