# NC63-0008 — no-quadratic comparison delta, source review v1

Verdict: **semantic correspondence accepted for the exact source below, conditional on its successful Lean compilation and axiom audit.** No mandatory mathematical repair was found. This report does not claim that those execution checks have completed.

Target: `research/nilpotent-conjugacy/batch-0063/checks/NoQuadraticBound.lean`.

SHA256: `c3c63fe9fcea0eec0e326dd1a3df39ceebdc4355d08972ba22b0828db7a12a88`.

Base reviewed target: `complete-candidate-v1`, manifest SHA256 `914c6fcdfcb6b73393cf9e9d405ea81b3a36ddab8bea86ccba4a8543b3be59e7`. A coordinator-authored future frozen version must be separately bound to this exact source digest. This delta is not yet part of that v1 manifest.

`GrowthLE` is the manuscript's comparison: a positive integer prefactor `C`, the same integer radius rescaling `C*n`, and a bound for every positive integer `n`. It is a statement about the actual `conjugacyGrowth`, not a supplied surrogate function.

`polynomialConjugacyLower_not_growthLE` correctly turns a lower degree `E` and any smaller natural degree `D` into failure of this comparison. It combines the lower constant `L` and comparison constant `C` into `K=L*C*C^D`, chooses `n=max N (K+1)`, and obtains both `n*n^D≤n^E` and `n^E≤K*n^D`. Cancellation is legitimate because `n≥1`, so `n^D>0`. The argument handles the finite lower-radius threshold and both upper-comparison constants explicitly.

`RealPolynomialGrowthUpper` uses the actual growth values and requires them to be finite at every positive integer radius before interpreting `toNat` in the reals. Thus `toNat(∞)=0` cannot give a spurious upper bound. Its exponent is an arbitrary real number and its prefactor and radius scaling follow the manuscript convention. The conversion to natural exponent `D≥e` uses a base `C*n≥1`, so monotonicity in the real exponent applies, including negative proposed exponents.

The final theorem quantifies over every real `A`. It chooses an integer `C≥A` and then one group parameter `d=64*C+2`, before quantifying over the finite generating set. For this parameter,

- `d≥2`;
- `A*(8d)^2≤C*(8d)^2`;
- `C*(8d)^2<3*d^2*(d+1)`.

The last inequality contradicts the actual lower bound supplied by `cubicFamily_polynomialConjugacyLower`, for every finite word generating set of the same `ManuscriptGroup (4*d)`. Nonemptiness of those metrics and the group's finite generation, torsion-freeness, nilpotence, exact class, and actual `8d` infinite-cyclic-factor series are already supplied by the reviewed `cubicFamily_main`. Those structural facts are not repeated inside the new theorem's conjunction; they are available for the exact same parameter and group.

This delta closes the v1 report's first scope limitation: the real-coefficient no-universal-quadratic consequence is now explicitly encoded. Subject to compilation, it proves failure of every proposed finite polynomial comparison with exponent `A*(8d)^2`. General conjugacy separability is not needed to derive this contradiction: the base construction supplies actual finite-depth witnesses, and any proposed upper comparison itself asserts finiteness.

The remaining limitations in the base report persist. In particular, the expression `8d` is justified by the actual cyclic-series certificate; no series-independent Hirsch-invariant API equality has been formalized. The universal upper theorem and full envelope corollary are not supplied by this module. Describing the result using the conventional Hirsch count is mathematically faithful if this certificate/interface distinction is disclosed.

No source edits, compilation, or axiom collection were performed by this delta review. Reviewed at 2026-10-06T19:20:50.971555+00:00.
