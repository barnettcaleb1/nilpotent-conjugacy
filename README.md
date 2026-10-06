# Nilpotent conjugacy separation

**Caleb Barnett · Unverified draft · 6 October 2026**

This repository accompanies *Cubic lower bounds for conjugacy separation in nilpotent groups*. It contains the preprint, a graduate exposition, and a partial Lean formalization.

**The main theorem of the paper is not formally verified.** The Lean package checks selected algebraic arguments and growth calculations. It does not yet connect all of these arguments to the constructed groups and their word metrics. The paper was prepared with AI assistance and remains provisional, pending independent verification.

## Paper

- [Preprint source](paper/preprint.tex)
- [Expository source](paper/exposition.tex)
- [Short description for a website](paper/website-notice.txt)
- [Verification scope and remaining obligations](VERIFICATION.md)

The proposed construction has, for each integer $d\ge 2$, nilpotency class $4d$, Hirsch length $8d$, and a claimed conjugacy-separation lower exponent $3d^2(d+1)$. If correct, it would rule out a universal quadratic exponent bound in Hirsch length. Neither the main claim nor priority is certified by this repository.

## Lean package

The package uses **Lean 4.33.1** and Mathlib commit **0df444a360eaa60ab8c11dca51a86af692955474**. Dependencies are pinned in [lake-manifest.json](lake-manifest.json).

| Module | Formalized content |
| --- | --- |
| [Bidiagonal](NilpotentConjugacy/Bidiagonal.lean) | Integral image divisibility, signed recurrence, exact prime-power order, and a finite detector over a residue ring. |
| [FiniteCharacters](NilpotentConjugacy/FiniteCharacters.lean) | Detecting characters, an explicit injection giving a cardinality lower bound, and the bound $p^{srq}\le \lvert Q\rvert$ under stated algebraic hypotheses. |
| [MatrixUnits](NilpotentConjugacy/MatrixUnits.lean) | Matrix-unit interpolation over a general coefficient ring and over the actual localization $\mathbb Z_{(p)}$, including invariant-submodule preservation. |
| [Growth](NilpotentConjugacy/Growth.lean) | Parameter arithmetic, cubic degree comparisons, and passage from assumed bounds at geometric scales to an all-radius polynomial bound. |
| [QuotientModule](NilpotentConjugacy/QuotientModule.lean) | The bound $p^{s(m-w)(w+1-\lfloor m/2\rfloor)}$ for an actual finite quotient module, deriving the required matrix units and columns from shift invariance and the specified obstruction. |

Read each theorem's hypotheses. In particular, a checked implication with an obstruction or invariance hypothesis does not establish that every finite quotient of the manuscript's groups satisfies that hypothesis.

## Reproduce the checks

With [elan](https://github.com/leanprover/elan) and Python 3 installed, run from this directory:

~~~sh
lake exe cache get
python3 scripts/verify.py
~~~

The toolchain file selects Lean 4.33.1. The verification script builds the package with warnings treated as errors, replays its compiled declarations through Lean's kernel using `leanchecker`, rejects proof admissions and nonstandard proof shortcuts in its sources, and audits the transitive axioms of every declaration in the package namespace. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. Kernel replay uses Lean's own checker; it is not an independent proof assistant. The script records source hashes and command outcomes in `.verification-local/`.

The [GitHub workflow](.github/workflows/lean.yml) runs the same checks. Its status concerns this Lean package; it does not certify the unformalized parts of the paper. The checked-in [verification record](verification/checks.json) binds the local run to exact source hashes.

The two papers are standalone LaTeX files with embedded bibliographies. Their compilation checks concern typesetting. Comments and corrections are welcome through GitHub issues.
