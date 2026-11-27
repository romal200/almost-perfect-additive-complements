# van Doorn–Liu–Tang conjecture (almost perfect additive complements)

[![Lean 4 & Exact Verification](https://github.com/romal200/almost-perfect-additive-complements/actions/workflows/lean.yml/badge.svg)](https://github.com/romal200/almost-perfect-additive-complements/actions/workflows/lean.yml)

Complete, Lean 4–formalized proof of [Conjecture 1.3](https://arxiv.org/html/2610.35027v1#S1.Thmtheorem3) of Wouter van Doorn, Boning Liu, and Quanyu Tang (*On almost perfect additive complements*, [arXiv:2610.35027v1](https://arxiv.org/abs/2610.35027), 26 Oct 2026), together with an exact structural classification of all infinite almost perfect additive complements below the $`8/5`$ threshold.

- [Complete proof](PROOF.md)
- [Lean 4 formalization](lean/) and [Lean verification & review guide](LEAN-REVIEW.md)
- [Strict Lean verifier & axiom audit](scripts/verify-lean.py)
- [Exact rational & symbolic verifier](verify.py)
- [Internal mathematical and source audit](AUDIT.md)

## Main result

Let $`A, B \subseteq \mathbb{Z}_{\ge 0}`$ be infinite almost perfect additive complements ($`n \in A + B`$ for all sufficiently large $`n`$, and $`A(x)B(x) - x \not\to +\infty`$). If

```math
\limsup_{x \to \infty} \frac{A(x)B(x)}{x} < \frac{8}{5},
```

then there exist an integer $`D_0 \ge 1`$ and finite subsets $`A_0, B_0 \subseteq \{0, 1, \dots, D_0 - 1\}`$ such that $`(a, b) \mapsto a + b \bmod D_0`$ is a bijection $`A_0 \times B_0 \to \mathbb{Z}/D_0\mathbb{Z}`$, and (after swapping $`A`$ and $`B`$ if necessary)

```math
A = A_0 + D_0 \cdot A_{\mathrm{bin}}, \qquad B = B_0 + D_0 \cdot (2 A_{\mathrm{bin}}),
```

where $`A_{\mathrm{bin}} = \{\sum_{i \ge 0} \varepsilon_i 4^i : \varepsilon_i \in \{0, 1\},\ \text{finitely many } \varepsilon_i \ne 0\}`$.

In particular:
1. **Conjecture 1.3 holds:** $`\limsup_{x \to \infty} \frac{A(x)B(x)}{x} \in \bigl\{\frac{3}{2}\bigr\} \cup \bigl[\frac{8}{5}, 2\bigr]`$ for all infinite almost perfect additive complements $`A, B \subseteq \mathbb{Z}_{\ge 0}`$.
2. **No repeated sums below $`8/5`$:** whenever $`\limsup_{x\to\infty}\frac{A(x)B(x)}{x} < \frac{8}{5}`$, we have $`r_{A, B}(n) \le 1`$ for every $`n \in \mathbb{Z}_{\ge 0}`$ (resolving the remark in Section 5.1 of `arXiv:2610.35027v1`).

## Verification & status

### Lean 4 formalization (zero `sorry`, zero custom axioms)

The entire proof—including a self-contained formalization of the Gabardo–Lai convolution factorization theorem (2014, Thm. 2.2)—is formally verified end-to-end in **Lean `v4.35.0`** + **Mathlib `v4.35.0`** across 13 modules (13,750 lines, 1,909 owned declarations, 1,790 theorems) in [`lean/`](lean/).

To replay the full verification locally:

```bash
cd lean && lake exe cache get && cd ..
python3 scripts/verify-lean.py
```

`scripts/verify-lean.py` performs four checks (also run automatically on every push in [`.github/workflows/lean.yml`](.github/workflows/lean.yml)):
1. Source hygiene scan rejecting `sorry`, `admit`, custom `axiom`, `implemented_by`, `unsafe`, and linter/warning suppressions.
2. Fresh per-module compilation with `lake env lean -j1 -DwarningAsError=true` across all 13 modules (0 errors, 0 warnings).
3. Transitive `Lean.collectAxioms` audit across all 1,909 owned declarations (public and private), confirming zero project axioms and transitive axioms strictly within `{propext, Classical.choice, Quot.sound}`.
4. Independent stock kernel replay via `lake env leanchecker -v AlmostPerfect`.

See [`LEAN-REVIEW.md`](LEAN-REVIEW.md) for the exact specification definitions ([`lean/AlmostPerfect/Basic.lean`](lean/AlmostPerfect/Basic.lean), 71 lines), theorem signatures, and module-by-module mapping to [`PROOF.md`](PROOF.md).

### Exact rational & symbolic verifier

Run `python3 verify.py` with Python 3.12+ and SymPy installed. All five exact verification suites (Section 4 symbolic bounds, Section 5 rational $`\varepsilon`$-margins, Proposition 5.3 / Section 7 exact polynomial identities across 9 concrete families including shifted and swapped steps, Lemma 6.1 polynomial rigidity on profiles with $`r(n) \ge 2`$, and 4-step doubling induction) pass using exact `fractions.Fraction` and `sympy` arithmetic.

The formalization is machine-checked by Lean's kernel, while the written exposition and Lean specification definitions remain unrefereed; external review is welcome. Priority is not asserted. The proof builds on the Gabardo–Lai convolution factorization theorem (2014, Thm. 2.2, formally proved from scratch in `AlmostPerfect.GabardoLai`), the weak-limit framework of van Doorn–Liu–Tang (`arXiv:2610.35027v1`), and the discrete gap/reflected-convolution lemma of Z. Zhang (`arXiv:2610.29963v1`).
