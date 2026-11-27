# Internal publication audit (2026-11-27)

**Disposition:** pass for both the written proof and the complete, zero-`sorry`, zero-custom-axiom Lean `v4.35.0` formalization of the exact original conjecture and accompanying structural classification below $`8/5`$. Unrefereed; external mathematical and specification review is welcome. No claim of external acceptance or exclusive priority.

## Source verification

- Read [van Doorn–Liu–Tang, *On almost perfect additive complements*, arXiv:2610.35027v1](https://arxiv.org/html/2610.35027v1#S1.Thmtheorem3) directly from primary HTML. Conjecture 1.3 states verbatim: if $`A, B \subseteq \mathbb{Z}_{\ge 0}`$ are infinite almost perfect additive complements ($`n \in A + B`$ for all sufficiently large $`n`$, and $`A(x)B(x) - x \not\to \infty`$), then $`\limsup_{x\to\infty} \frac{A(x)B(x)}{x} \in \{\frac{3}{2}\} \cup [\frac{8}{5}, 2]`$.
- Read [Z. Zhang, *A sharp bound for additive complements*, arXiv:2610.29963v1](https://arxiv.org/html/2610.29963v1) directly; the reflected-convolution gap lemmas (Lemmas 4.1–4.2) and base-$`4`$ sharpness calculation (Section 6) are reproduced self-containedly in Lemma 3.5 and Corollary 1.
- In the written proof (`PROOF.md`), the only external theorem quoted without proof is the single-step Gabardo–Lai convolution factorization theorem (Gabardo–Lai, *J. Fourier Anal. Appl.* **20** (2014), Thm. 2.2), quoted verbatim as Theorem 2.4 in `arXiv:2610.35027v1`. In the Lean 4 formalization (`AlmostPerfect.GabardoLaiBase` and `AlmostPerfect.GabardoLai`), this single-step theorem is proved completely from scratch over Mathlib with zero custom axioms.

## Mathematical audit

- **Section 3 (Invariants & difference density):** Verified $`r(a_{\min}+b_{\min}) = 1`$ unconditionally (so $`\widetilde{V}(0) = 1`$, $`\widetilde{V}`$ is primitive in $`\mathbb{Z}[z]`$, and $`|[z^d]\widetilde{V}(z)| \le E`$ for all $`d \ge 1`$, even when $`a_{\min}, b_{\min} > 0`$ or $`r(n) \ge 2`$ on $`[0, n_0-1]`$). Verified the pointwise identity $`\mathbf{1}_{d=0} \le (1-d) + d(d-1) = (d-1)^2`$ giving an explicit constant $`C_1(K) = E + S_2 + 2(1+E)(1+K)`$ for every bounded-crossing level $`N`$ with $`N \notin A \cup B`$.
- **Section 4 (Weak-limit uniqueness):** Verified that Proposition 4.3 works along *every* sequence $`N_j \to \infty`$ with $`T(N_j) \le K`$ (not merely minimal-excess subsequences). Checked scaling invariance (4.3)–(4.4), both Type I termination cases ($`\lambda \ge 2`$), the orientation-swap merge ($`M' = M_{2k+2}M_{2k+3} \ge 4 \implies \lambda \ge \frac{5}{3}`$), single-factor stripping for odd indices $`M_{2k+3} = 2`$, and the $`M_1 \ge 3`$ elimination via Zhang's gap lemma ($`\lambda \ge \frac{18}{11} > \frac{8}{5}`$). Verified uniform CDF convergence via Pólya's theorem since $`\nu_0, \mu_0`$ are atomless.
- **Section 5 (Forward doubling & quadratic recurrence):** Checked both cases of Lemma 5.1 ($`y_0 < 3x_0 + n_0`$ and $`y_0 \ge 3x_0 + n_0`$, using $`T(y_0 - 1) \le n_0 \le K`$). Checked Lemma 5.2 Step 2 ruling out $`w_0 \in (N, y_0 + n_0)`$ via the Cantor gap of $`\nu_0`$ on $`(\frac{1}{12}, \frac{1}{4})`$ and Step 3 pushing $`w_0 > y_0 + \frac{5}{8}N`$ via the two dyadic blocks $`[\frac{1}{16}, \frac{1}{12}]`$ and $`[\frac{5}{16}, \frac{1}{3}]`$. Checked the pigeonhole zero-run argument in Proposition 5.3 Step 1 without assuming $`r(0) = 1`$, and verified that shifting $`N_1'`$ by $`\max(a_{\min}, b_{\min})`$ yields exact truncations $`A \cap [0, N_1'] = A_0 \cup A_1'`$ and $`B \cap [0, N_1'] = B_0`$ with zero boundary-strip ambiguity.
- **Section 6–7 (Polynomial iteration rigidity & global structure):** Checked that $`k_0`$ and $`K_{\max} = 2^{k_0}(K_0 + E + 2n_0)`$ depend solely on $`(A, B)`$ prior to selecting $`N_0 \ge N_*(K_{\max}, \varepsilon)`$ (zero circularity). Verified UFD divisibility $`\widetilde{V} \mid \widetilde{W}_0`$ in $`\mathbb{Z}[z]`$, coefficient explosion $`|[z^d]\widetilde{W}_{k_0-1}| \ge M - E \ge 2`$ for any $`R \not\equiv 1`$, exact order comparison $`u_1^{(j)} = b_{\min}`$ giving $`A_j' = D_j + A^{(j)}`$, orientation flip at $`N_{j+1}`$, doubling $`D_{j+1} = 2 D_j`$, and modular bijection (7.3).

## Lean 4 formal verification & kernel audit

Replayed [`scripts/verify-lean.py`](scripts/verify-lean.py) against the pinned toolchain **`leanprover/lean4:v4.35.0`** and **Mathlib `v4.35.0`** (`rev 56a005855ea17e0b0958f73ec801ae140b0a1679`):
- **Source hygiene:** 0 occurrences of `sorry`, `admit`, custom `axiom`, `implemented_by`, `unsafe`, or linter/warning suppressions across all 13 project `.lean` files (13,750 lines total).
- **Strict compilation:** every module in topological order compiled cleanly with `lake env lean -j1 -DwarningAsError=true` (0 errors, 0 warnings).
- **All-owned declaration & transitive axiom audit:** all **1,909** owned declarations (**1,790** theorems, **110** definitions, **3** inductives/structures, **3** constructors, **3** recursors; **761** private declarations) across all 13 project modules audited via `Lean.collectAxioms`, with **0** project axioms and transitive axioms strictly within **`{propext, Classical.choice, Quot.sound}`**. All 14 required endpoint theorems—including `AlmostPerfect.main_classification`, `AlmostPerfect.conjecture_1_3`, `AlmostPerfect.no_repeated_sums_below_eight_fifths`, and `AlmostPerfect.gabardo_lai_single_step`—verified.
- **Stock kernel replay:** `lake env leanchecker -v AlmostPerfect` exited with status `0` across all 13 compiled modules.
- See [`LEAN-REVIEW.md`](LEAN-REVIEW.md) for full review instructions, exact definitions, and module mapping.

## Verifier replay

Replayed [`verify.py`](verify.py) using **Python 3.12.10** and **SymPy 1.14.0** (using exact `fractions.Fraction` and `sympy` arithmetic throughout):
- Section 4 symbolic Lemma 4.2 minimization, Type I ratios, and $`M_1 \ge 3`$ bounds passed.
- Section 5 exact rational margins for $`\varepsilon = 1/1000`$ and depth-6 dyadic masses of $`\nu_0`$ passed.
- Proposition 5.3 and Section 7 exact polynomial identities (5.6), (5.7), (5.8), (5.10), and (7.3) passed on 9 concrete families: perfect binary Cantor (at $`N = 4^4 - 1`$ and $`N = 4^4 - 3`$), shifted binary Cantor $`(3, 5)`$ and $`(7, 2)`$, Remark 5.1 $`C=\{0,2\}, D=\{0,3\}`$, shifted Remark 5.1 Steps 1 & 2 (swapped), and mod-6 $`C=\{0,1,5\}, D=\{0,3\}`$ Steps 1 & 2 (swapped).
- Lemma 6.1 coefficient-explosion bound passed on 5 representation profiles including $`r(n) \ge 2`$ and $`m_0 > 0`$.
- 4-step doubling induction and Zhang's base-$`4`$ bound $`v^2 \le 3 a_v`$ ($`0 \le v < 4096`$) passed.

## Bounded prior-resolution search (2026-11-27)

Checked the following sources on 2026-11-27 for any prior resolution of Conjecture 1.3 (`arXiv:2610.35027v1`):
- **arXiv API & web:** `2610.35027` remains at `v1` (26 Oct 2026); 0 subsequent papers citing or resolving Conjecture 1.3 across `math.NT` / `math.CO` and all 2026 submissions by van Doorn, Liu, Tang, and Zhang.
- **Google Scholar & Google Web Search:** 1 Scholar result (0 citations); 9 total indexed web pages for `"2610.35027"` / `"almost perfect additive complements"` (original preprint, arXiv bots, Wolfram MathWorld updated 25 Nov 2026, Valency Hub, MaRDI, ResearchGate).
- **GitHub Global Code, Repos, Issues & PRs:** 0 repos/PRs resolving Conjecture 1.3 across public conjecture collections and Lean formalization repositories.
- **Hexagon (`hexagonmath.org`), Zenodo, Crossref, `erdosproblems.com/785`, `erdosproblems.ai`, MathOverflow, X/Twitter:** 0 prior proofs or disproofs found (only the automated Oct 27 `@mathNTb` X bot post with 0 replies).

This is a bounded search as of 2026-11-27, not exhaustive coverage of private or unindexed archives.
