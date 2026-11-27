# van Doorn–Liu–Tang conjecture (almost perfect additive complements)

Complete proposed proof of [Conjecture 1.3](https://arxiv.org/html/2610.35027v1#S1.Thmtheorem3) of Wouter van Doorn, Boning Liu, and Quanyu Tang (*On almost perfect additive complements*, [arXiv:2610.35027v1](https://arxiv.org/abs/2610.35027), 26 Oct 2026), together with an exact structural classification of all infinite almost perfect additive complements below the $`8/5`$ threshold.

- [Complete proof](PROOF.md)
- [Exact verifier](verify.py)
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

Run `python3 verify.py` with Python 3.12+ and SymPy 1.14.0 installed. All five exact verification suites (Section 4 symbolic bounds, Section 5 rational $`\varepsilon`$-margins, Proposition 5.3 / Section 7 exact polynomial identities across 9 concrete families including shifted and swapped steps, Lemma 6.1 polynomial rigidity on profiles with $`r(n) \ge 2`$, and 4-step doubling induction) pass using exact `fractions.Fraction` and `sympy` arithmetic.

The proof is internally audited but unrefereed, with no Lean 4 formalization yet; external mathematical review and formalization are welcome. Priority is not asserted. The proof builds on the Gabardo–Lai convolution factorization theorem (2014, Thm. 2.2), the weak-limit framework of van Doorn–Liu–Tang (`arXiv:2610.35027v1`), and the discrete gap/reflected-convolution lemma of Z. Zhang (`arXiv:2610.29963v1`).
