# Nilpotent conjugacy separation

**Caleb Barnett · Research draft · 6 October 2026**

This repository accompanies *Cubic lower bounds for conjugacy separation in nilpotent groups*. It contains the preprint, a graduate exposition, and a Lean formalization of the explicit lower-bound construction.

The main declaration is [`cubicFamily_main`](NilpotentConjugacy/CubicTheorem.lean). For every integer $d\ge2$, it constructs the manuscript’s actual group and proves:

- finite generation and torsion-freeness;
- nilpotence of exactly class $4d$;
- an actual nested subnormal series with $8d$ infinite cyclic quotients, giving the Hirsch-length calculation;
- in every finite word metric, a lower bound with exponent $3d^2(d+1)$ at every sufficiently large radius, witnessed by nonconjugate pairs whose actual separating depths are finite.

[`no_universal_quadratic_exponent`](NilpotentConjugacy/NoQuadraticBound.lean) also proves that every proposed real coefficient of the square of Hirsch length fails to give a universal polynomial upper comparison.

The paper remains a draft pending independent review. The formalization does not include the cited general upper bound or establish novelty. Its precise statement, conventions, and remaining scope are described in [VERIFICATION.md](VERIFICATION.md).

## Paper and proof

- [Preprint source](paper/preprint.tex)
- [Graduate exposition](paper/exposition.tex)
- [Website description](paper/website-notice.txt)
- [Combined main theorem](NilpotentConjugacy/CubicTheorem.lean)
- [Exact verification scope](VERIFICATION.md)

| Proof stage | Entry points |
| --- | --- |
| Integral group and action | [IntegralGroupAction](NilpotentConjugacy/IntegralGroupAction.lean) |
| Torsion-freeness, exact class, cyclic series | [GroupProperties](NilpotentConjugacy/GroupProperties.lean), [GroupClass](NilpotentConjugacy/GroupClass.lean), [GroupSeries](NilpotentConjugacy/GroupSeries.lean) |
| Actual word compression | [JordanCompression](NilpotentConjugacy/JordanCompression.lean), [WeightedCompression](NilpotentConjugacy/WeightedCompression.lean), [PairWordLength](NilpotentConjugacy/PairWordLength.lean) |
| Every finite separating quotient | [GroupQuotientBound](NilpotentConjugacy/GroupQuotientBound.lean) |
| Explicit finite separating quotients | [PairFiniteQuotient](NilpotentConjugacy/PairFiniteQuotient.lean) |
| Actual depth, growth, and main theorem | [ConjugacyDepth](NilpotentConjugacy/ConjugacyDepth.lean), [ConjugacyGrowth](NilpotentConjugacy/ConjugacyGrowth.lean), [CubicTheorem](NilpotentConjugacy/CubicTheorem.lean) |

## Reproduce the checks

The package pins **Lean 4.33.1** and Mathlib commit **0df444a360eaa60ab8c11dca51a86af692955474**. With elan and Python 3 installed, run:

~~~sh
lake exe cache get
python3 scripts/verify.py
~~~

The script builds every module with warnings treated as errors, replays compiled declarations through Lean’s kernel with `leanchecker`, rejects proof admissions and nonstandard shortcuts, and audits transitive axioms of public and private package declarations. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Kernel replay uses Lean’s own checker; it is not a separate proof assistant.

The [GitHub workflow](.github/workflows/lean.yml) runs the same checks. The [verification record](verification/checks.json) binds the local run to exact source hashes. Formal checking concerns the Lean statements; correspondence with the paper and literature priority require separate judgment.

Prepared with AI assistance. Comments and corrections are welcome through GitHub issues.
