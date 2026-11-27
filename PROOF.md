# Proof of Conjecture 1.3 of van Doorn, Liu, and Tang (arXiv:2610.35027v1)

**Status (2026-11-27):** complete proof of [Conjecture 1.3](https://arxiv.org/html/2610.35027v1#S1.Thmtheorem3) and of the stronger exact classification theorem below 8/5, formally verified end-to-end in **Lean 4 (`v4.35.0`) + Mathlib (`v4.35.0`)** with zero `sorry`s, zero custom axioms (`{propext, Classical.choice, Quot.sound}` only), zero warnings under `-DwarningAsError=true`, and stock `leanchecker` kernel replay (see [`LEAN-REVIEW.md`](LEAN-REVIEW.md) and [`scripts/verify-lean.py`](scripts/verify-lean.py)). Exact symbolic and rational checks in [`verify.py`](verify.py) also pass. Internally audited ([`AUDIT.md`](AUDIT.md)); external peer and specification review is welcome. Priority is not asserted.

---

## 1. Statement of the Conjecture and Main Theorem

Let <i>A</i>, <i>B</i> ⊆ ℤ<sub>≥ 0</sub> be subsets of the non-negative integers, with counting functions

```math
A(x) := \#(A \cap [0, x]), \qquad B(x) := \#(B \cap [0, x]),
```

and representation function

```math
r(n) = r_{A, B}(n) := \#\{(a, b) \in A \times B : a + b = n\} \qquad (n \in \mathbb{Z}_{\ge 0}).
```

Following van Doorn, Liu, and Tang (*On almost perfect additive complements*, [arXiv:2610.35027v1](https://arxiv.org/abs/2610.35027), 26 Oct 2026), <i>A</i> and <i>B</i> are called **infinite almost perfect additive complements** if:
1. both <i>A</i> and <i>B</i> are infinite;
2. <i>r</i>(<i>n</i>) ≥ 1 for all sufficiently large integers <i>n</i>; and
3. $`A(x)B(x) - x \not\to +\infty`$ as $`x \to \infty`$.

In `arXiv:2610.35027v1`, van Doorn, Liu, and Tang confirmed Chen's conjecture that $`\limsup_{x\to\infty} \frac{A(x)B(x)}{x} \in [\frac{3}{2}, 2]`$ (see also Z. Zhang, [arXiv:2610.29963v1](https://arxiv.org/abs/2610.29963), 21 Oct 2026), and posed:

> **Conjecture 1.3 (van Doorn–Liu–Tang, 2026).** If <i>A</i>, <i>B</i> ⊆ ℤ<sub>≥ 0</sub> are infinite almost perfect additive complements, then
>
> ```math
> \limsup_{x \to \infty} \frac{A(x)B(x)}{x} \in \left\{\frac{3}{2}\right\} \cup \left[\frac{8}{5}, 2\right].
> ```

We prove Conjecture 1.3 in full by establishing the following sharper structural classification of all infinite almost perfect additive complements below the 8/5 threshold. Let

```math
A_{\mathrm{bin}} := \left\{\sum_{i \ge 0} \varepsilon_i 4^i \;\middle|\; \varepsilon_i \in \{0, 1\},\ \varepsilon_i = 0 \text{ for all but finitely many } i\right\}
```

be the base-4 binary Cantor set (so <i>A</i><sub>bin</sub> + 2 <i>A</i><sub>bin</sub> = ℤ<sub>≥ 0</sub> uniquely).

> **Main Theorem.** Let <i>A</i>, <i>B</i> ⊆ ℤ<sub>≥ 0</sub> be infinite almost perfect additive complements such that
>
> ```math
> \lambda := \limsup_{x \to \infty} \frac{A(x)B(x)}{x} < \frac{8}{5}.
> ```
>
> Then there exist an integer <i>D</i><sub>0</sub> ≥ 1 and finite subsets <i>A</i><sub>0</sub>, <i>B</i><sub>0</sub> ⊆ {0, 1, …, <i>D</i><sub>0</sub> − 1} such that $`(a, b) \mapsto a + b \bmod D_0`$ is a bijection <i>A</i><sub>0</sub> × <i>B</i><sub>0</sub> → ℤ/<i>D</i><sub>0</sub>ℤ, and (after swapping <i>A</i> and <i>B</i> if necessary)
>
> ```math
> A = A_0 + D_0 \cdot A_{\mathrm{bin}}, \qquad B = B_0 + D_0 \cdot (2 A_{\mathrm{bin}}).
> ```

> **Corollary 1 (Resolution of Conjecture 1.3).** For every pair of infinite almost perfect additive complements <i>A</i>, <i>B</i> ⊆ ℤ<sub>≥ 0</sub>,
>
> ```math
> \limsup_{x \to \infty} \frac{A(x)B(x)}{x} \in \left\{\frac{3}{2}\right\} \cup \left[\frac{8}{5}, 2\right].
> ```

> **Corollary 2 (Absence of repeated sums below 8/5 ).** Every pair of infinite almost perfect additive complements <i>A</i>, <i>B</i> ⊆ ℤ<sub>≥ 0</sub> with $`\limsup_{x\to\infty} \frac{A(x)B(x)}{x} < \frac{8}{5}`$ satisfies <i>r</i><sub><i>A</i>, <i>B</i></sub>(<i>n</i>) ≤ 1 for every <i>n</i> ∈ ℤ<sub>≥ 0</sub>. (In particular, any almost perfect additive complements with <i>r</i>(<i>n</i>) ≥ 2 for some <i>n</i> — whose existence was raised as an open remark in Section 5.1 of `arXiv:2610.35027v1` — must have $`\limsup \frac{A(x)B(x)}{x} \ge \frac{8}{5}`$.)

---

## 2. Proof Overview

The proof combines weak-limit analysis (using only the single-step Gabardo–Lai factorization theorem), discrete convolution identities, and a **polynomial iteration rigidity theorem**:

1. **Setup (Section 3).** Eventual uniqueness <i>r</i>(<i>n</i>) = 1 (<i>n</i> ≥ <i>n</i><sub>0</sub>) defines a fixed integer polynomial $`V(z) = 1 + (1-z)\sum_{n=0}^{n_0-1}(r(n)-1)z^n = z^{m_0}\widetilde{V}(z)`$ with <i>m</i><sub>0</sub> = <i>a</i><sub>min</sub> + <i>b</i><sub>min</sub> ≤ <i>n</i><sub>0</sub> and $`\widetilde{V}(0) = \widetilde{V}(1) = 1`$.
2. **Unique Weak Limit Along Every Bounded-Crossing Sequence (Section 4).** Under λ &lt; 8/5, along *every* sequence $`N_j \to \infty`$ with uniformly bounded crossing count <i>T</i>(<i>N</i><sub><i>j</i></sub>) ≤ <i>K</i>, the normalized counting measures $`(\mu_{N_j}, \nu_{N_j})`$ converge uniformly in CDF to the unique binary Cantor complementary pair (ν<sub>0</sub>, μ<sub>0</sub>) supported on [0, 1/3] and [0, 2/3] (up to swapping <i>A</i>, <i>B</i>). Both Type I limits and Type II limits with any <i>M</i><sub><i>k</i></sub> ≥ 3 (<i>k</i> ≥ 2) are excluded via scaling invariance of $`\frac{\mu([0, u])\nu([0, u])}{u}`$, while the boundary case <i>M</i><sub>1</sub> ≥ 3 (left open by Theorem 5.2 of `arXiv:2610.35027v1`) is eliminated via Zhang's gap lemma, yielding λ ≥ 18/11 &gt; 8/5.
3. **Exact Forward Doubling and Polynomial Recurrence (Section 5).** Starting from any sufficiently large <i>N</i> with <i>T</i>(<i>N</i>) ≤ <i>K</i> (wlog <i>A</i> on [0, 1/3], <i>B</i> on [0, 2/3]), we locate the next elements $`y_0 = \min(A \cap (N, \infty)) \in (N, (1 + 8\varepsilon)N]`$ and $`w_0 = \min(B \cap (N, \infty)) > y_0 + \frac{5}{8}N`$. The gap in <i>B</i> produces an exact polynomial identity $`P_{A_1'}(z)V(z) = P_{A_0}(z)U_1(z)`$, which multiplies by $`(1-z)P_{B_0}(z)`$ to produce a new level $`N_1' \approx 2N`$ where <i>A</i> ∩ [0, <i>N</i><sub>1</sub>′] = <i>A</i><sub>0</sub> ∪ <i>A</i><sub>1</sub>′, <i>B</i> ∩ [0, <i>N</i><sub>1</sub>′] = <i>B</i><sub>0</sub>, <i>T</i>(<i>N</i><sub>1</sub>′) ≤ 2T(<i>N</i>) + <i>E</i> + 2n<sub>0</sub>, and the stripped crossing polynomials satisfy the exact quadratic recurrence

```math
\widetilde{V}(z)\,\widetilde{W}_{N_1'}(z) = \widetilde{W}_N(z)^2.
```

4. **Polynomial Iteration Rigidity (Section 6).** Iterating the doubling step a *fixed* finite number <i>k</i><sub>0</sub> = <i>k</i><sub>0</sub>(<i>n</i><sub>0</sub>, <i>E</i>) of times from a sufficiently large <i>N</i><sub>0</sub> gives $`\widetilde{V}(z)^{M-1}\widetilde{W}_{N_{k_0-1}}(z) = \widetilde{W}_{N_0}(z)^M`$ with $`M = 2^{k_0-1} > \max(n_0, E+1)`$. Unique factorization in ℤ[<i>z</i>] forces $`\widetilde{V} \mid \widetilde{W}_{N_0}`$, and writing $`\widetilde{W}_{N_0} = \widetilde{V} R`$ yields $`\widetilde{W}_{N_{k_0-1}} = \widetilde{V} R^M`$. Because every coefficient of $`\widetilde{W}_{N_{k_0-1}}`$ lies in {−1, 0, +1}, the lowest nonconstant term of <i>R</i> would create a coefficient of magnitude ≥ <i>M</i> − <i>E</i> ≥ 2 unless <i>R</i>(<i>z</i>) ≡ 1. Hence $`\widetilde{W}_{N_0}(z) = \widetilde{V}(z)`$.
5. **Exact Global Structure and Corollaries (Section 7).** Once $`\widetilde{W}_{N_0} = \widetilde{V}`$, the crossing count freezes at <i>T</i>(<i>N</i><sub>1</sub>′) = −<i>c</i> − min(<i>a</i><sub>min</sub>, <i>b</i><sub>min</sub>) ≤ <i>E</i>, the next segment is an exact translate <i>A</i><sub>1</sub>′ = <i>D</i><sub>0</sub> + <i>A</i><sub>0</sub> (<i>D</i><sub>0</sub> = <i>y</i><sub>0</sub> − <i>a</i><sub>min</sub>), and induction over all doubling steps yields <i>D</i><sub><i>j</i></sub> = 2<sup><i>j</i></sup> <i>D</i><sub>0</sub> and <i>A</i> = <i>A</i><sub>0</sub> + <i>D</i><sub>0</sub> <i>A</i><sub>bin</sub>, <i>B</i> = <i>B</i><sub>0</sub> + <i>D</i><sub>0</sub>(2 <i>A</i><sub>bin</sub>). Both corollaries follow directly.

In the written proof below, the only external theorem quoted without proof is the single-step Gabardo–Lai convolution factorization theorem (Gabardo–Lai, *J. Fourier Anal. Appl.* 20 (2014), Thm. 2.2, cited verbatim as Theorem 2.4 in `arXiv:2610.35027v1`); in the accompanying Lean 4 formalization ([`lean/AlmostPerfect/GabardoLaiBase.lean`](lean/AlmostPerfect/GabardoLaiBase.lean) and [`lean/AlmostPerfect/GabardoLai.lean`](lean/AlmostPerfect/GabardoLai.lean)), this single-step theorem is also proved completely from scratch with zero custom axioms.

---

## 3. Preliminaries and Fundamental Identities

Throughout Sections 3–7, fix infinite almost perfect additive complements <i>A</i>, <i>B</i> ⊆ ℤ<sub>≥ 0</sub>. For any integer <i>N</i> ≥ 0, define the crossing count

```math
T(N) := \#\{(a, b) \in (A \cap [0, N]) \times (B \cap [0, N]) : a + b > N\}.
```

Splitting pairs (<i>a</i>, <i>b</i>) ∈ (<i>A</i> ∩ [0, <i>N</i>]) × (<i>B</i> ∩ [0, <i>N</i>]) according to whether <i>a</i> + <i>b</i> ≤ <i>N</i> or <i>a</i> + <i>b</i> &gt; <i>N</i> gives

```math
A(N)B(N) = \sum_{n=0}^{N} r(n) + T(N). \tag{3.1}
```

### Lemma 3.1 (Eventual uniqueness and basic invariants)
1. There exists an integer <i>n</i><sub>0</sub> ≥ 1 such that <i>r</i>(<i>n</i>) = 1 for all <i>n</i> ≥ <i>n</i><sub>0</sub>.
2. Setting δ(<i>n</i>) := <i>r</i>(<i>n</i>) − 1 for <i>n</i> ≥ 0 (supported on [0, <i>n</i><sub>0</sub> − 1]),

```math
E := \sum_{n=0}^{n_0 - 1} |\delta(n)|, \qquad c := \sum_{n=0}^{n_0 - 1} \delta(n) \quad (|c| \le E), \qquad S_2 := \sum_{n=0}^{n_0 - 1} r(n)(r(n) - 1),
```

we have for every integer <i>N</i> ≥ <i>n</i><sub>0</sub>:

```math
A(N)B(N) - N = 1 + c + T(N), \tag{3.2}
```

and $`T_{\min} := \liminf_{N \to \infty} T(N) < \infty`$.
3. For all <i>u</i>, <i>v</i> ∈ ℤ<sub>≥ 0</sub>, <i>A</i>(<i>u</i>)<i>B</i>(<i>v</i>) ≤ <i>u</i> + <i>v</i> + 1 + <i>E</i>.
4. Let <i>a</i><sub>min</sub> := min <i>A</i>, <i>b</i><sub>min</sub> := min <i>B</i>, and <i>m</i><sub>0</sub> := <i>a</i><sub>min</sub> + <i>b</i><sub>min</sub>. Then <i>m</i><sub>0</sub> ≤ <i>n</i><sub>0</sub> (hence <i>a</i><sub>min</sub>, <i>b</i><sub>min</sub> ≤ <i>n</i><sub>0</sub>), <i>r</i>(<i>n</i>) = 0 for 0 ≤ <i>n</i> &lt; <i>m</i><sub>0</sub>, and <i>r</i>(<i>m</i><sub>0</sub>) = 1.
5. Define the integer polynomial

```math
V(z) := 1 + (1 - z) \Delta(z) \in \mathbb{Z}[z], \qquad \Delta(z) := \sum_{n=0}^{n_0 - 1} \delta(n) z^n.
```

Then $`V(z) = \sum_{n=0}^{n_0} (r(n) - r(n-1)) z^n`$ (with <i>r</i>(−1) := 0), <i>V</i>(1) = 1, <i>V</i>′(1) = −<i>c</i>, ord<sub><i>z</i>=0</sub>(<i>V</i>) = <i>m</i><sub>0</sub>, and $`\widetilde{V}(z) := V(z) / z^{m_0} \in \mathbb{Z}[z]`$ satisfies

```math
\deg \widetilde{V} \le n_0 - m_0 \le n_0, \qquad \widetilde{V}(0) = 1, \qquad \widetilde{V}(1) = 1, \qquad \widetilde{V}'(1) = -c - m_0,
```

and $`|[z^d]\widetilde{V}(z)| \le E`$ for every integer <i>d</i> ≥ 1.

*Proof.*
(1)–(2) Choose <i>M</i><sub>0</sub> ≥ 1 with <i>r</i>(<i>n</i>) ≥ 1 for all <i>n</i> ≥ <i>M</i><sub>0</sub>. Since $`A(x)B(x) - x \not\to +\infty`$ and <i>A</i>, <i>B</i> are integer-supported, there exists a sequence of integers $`X_j \to \infty`$ with <i>A</i>(<i>X</i><sub><i>j</i></sub>)<i>B</i>(<i>X</i><sub><i>j</i></sub>) − <i>X</i><sub><i>j</i></sub> ≤ <i>L</i><sub>0</sub> for some constant <i>L</i><sub>0</sub>. By (3.1),

```math
L_0 \ge A(X_j)B(X_j) - X_j = 1 + \sum_{n=0}^{M_0 - 1}(r(n)-1) + \sum_{n=M_0}^{X_j}(r(n)-1) + T(X_j).
```

Since <i>T</i>(<i>X</i><sub><i>j</i></sub>) ≥ 0 and every term <i>r</i>(<i>n</i>) − 1 for <i>n</i> ≥ <i>M</i><sub>0</sub> is a non-negative integer, only finitely many terms can be nonzero. Thus <i>r</i>(<i>n</i>) = 1 for all <i>n</i> ≥ <i>n</i><sub>0</sub> for some <i>n</i><sub>0</sub> ≥ 1. Then $`\sum_{n=0}^N r(n) = N + 1 + c`$ for <i>N</i> ≥ <i>n</i><sub>0</sub>, giving (3.2) and <i>T</i>(<i>X</i><sub><i>j</i></sub>) ≤ <i>L</i><sub>0</sub> − 1 − <i>c</i>, so $`T_{\min} < \infty`$.

(3) Every pair (<i>a</i>, <i>b</i>) ∈ (<i>A</i> ∩ [0, <i>u</i>]) × (<i>B</i> ∩ [0, <i>v</i>]) has sum <i>a</i> + <i>b</i> ∈ [0, <i>u</i> + <i>v</i>], so

```math
A(u)B(v) \le \sum_{n=0}^{u+v} r(n) = u + v + 1 + \sum_{n=0}^{\min(u+v, n_0-1)} \delta(n) \le u + v + 1 + E.
```

(4) Since <i>r</i>(<i>n</i><sub>0</sub>) = 1, there is (<i>a</i>, <i>b</i>) ∈ <i>A</i> × <i>B</i> with <i>a</i> + <i>b</i> = <i>n</i><sub>0</sub>, so <i>m</i><sub>0</sub> = <i>a</i><sub>min</sub> + <i>b</i><sub>min</sub> ≤ <i>n</i><sub>0</sub>. Clearly <i>a</i> + <i>b</i> ≥ <i>m</i><sub>0</sub> for all (<i>a</i>, <i>b</i>) ∈ <i>A</i> × <i>B</i>, with equality if and only if (<i>a</i>, <i>b</i>) = (<i>a</i><sub>min</sub>, <i>b</i><sub>min</sub>), so <i>r</i>(<i>n</i>) = 0 for <i>n</i> &lt; <i>m</i><sub>0</sub> and <i>r</i>(<i>m</i><sub>0</sub>) = 1.

(5) Expanding $`1 + (1-z)\sum_{n=0}^{n_0-1} (r(n)-1)z^n`$ directly gives: for <i>n</i> = 0, 1 + (<i>r</i>(0)-1) = <i>r</i>(0); for 1 ≤ <i>n</i> ≤ <i>n</i><sub>0</sub> − 1, (<i>r</i>(<i>n</i>)-1) − (<i>r</i>(<i>n</i> − 1)-1) = <i>r</i>(<i>n</i>) − <i>r</i>(<i>n</i> − 1); for <i>n</i> = <i>n</i><sub>0</sub>, -(<i>r</i>(<i>n</i><sub>0</sub>-1)-1) = 1 − <i>r</i>(<i>n</i><sub>0</sub>-1) = <i>r</i>(<i>n</i><sub>0</sub>) − <i>r</i>(<i>n</i><sub>0</sub>-1). Clearly <i>V</i>(1) = 1 and <i>V</i>′(1) = -Δ(1) = −<i>c</i>. By (4), the smallest <i>n</i> with [<i>z</i><sup><i>n</i></sup>]<i>V</i>(<i>z</i>) ≠ 0 is <i>n</i> = <i>m</i><sub>0</sub>, with coefficient <i>r</i>(<i>m</i><sub>0</sub>) − <i>r</i>(<i>m</i><sub>0</sub> − 1) = 1. Thus ord<sub>0</sub>(<i>V</i>) = <i>m</i><sub>0</sub>, $`\widetilde{V}(0) = 1`$, $`\widetilde{V}(1) = 1`$, and $`V'(1) = m_0 \widetilde{V}(1) + \widetilde{V}'(1)`$ gives $`\widetilde{V}'(1) = -c - m_0`$. For every <i>d</i> ≥ 1,

```math
[z^d]\widetilde{V}(z) = r(m_0 + d) - r(m_0 + d - 1) = \delta(m_0 + d) - \delta(m_0 + d - 1),
```

so $`|[z^d]\widetilde{V}(z)| \le |\delta(m_0 + d)| + |\delta(m_0 + d - 1)| \le E`$. □

### Lemma 3.2 (Uniqueness of differences; Zhang Lemma 2.2)
If (<i>a</i>, <i>b</i>), (<i>a</i>′, <i>b</i>′) ∈ <i>A</i> × <i>B</i> are two distinct pairs satisfying <i>b</i> − <i>a</i> = <i>b</i>′ − <i>a</i>′, then <i>a</i>, <i>a</i>′, <i>b</i>, <i>b</i>′ &lt; <i>n</i><sub>0</sub>. In particular, for every integer <i>d</i> with |<i>d</i>| ≥ <i>n</i><sub>0</sub>, there is at most one pair (<i>a</i>, <i>b</i>) ∈ <i>A</i> × <i>B</i> with <i>b</i> − <i>a</i> = <i>d</i>.

*Proof.* From <i>b</i> − <i>a</i> = <i>b</i>′ − <i>a</i>′ we have <i>a</i> + <i>b</i>′ = <i>a</i>′ + <i>b</i>. Since (<i>a</i>, <i>b</i>) ≠ (<i>a</i>′, <i>b</i>′), we have <i>a</i> ≠ <i>a</i>′ and <i>b</i> ≠ <i>b</i>′, so (<i>a</i>, <i>b</i>′) and (<i>a</i>′, <i>b</i>) are two distinct representations of the sum <i>a</i> + <i>b</i>′. By Lemma 3.1(1), <i>a</i> + <i>b</i>′ = <i>a</i>′ + <i>b</i> &lt; <i>n</i><sub>0</sub>, and non-negativity gives <i>a</i>, <i>a</i>′, <i>b</i>, <i>b</i>′ &lt; <i>n</i><sub>0</sub>, hence |<i>b</i> − <i>a</i>| &lt; <i>n</i><sub>0</sub>. □

### Lemma 3.3 (Crossing-pair polynomial at level <i>N</i> )
For any integer <i>N</i> ≥ <i>n</i><sub>0</sub>, put <i>A</i><sub>0</sub> := <i>A</i> ∩ [0, <i>N</i>], <i>B</i><sub>0</sub> := <i>B</i> ∩ [0, <i>N</i>], $`P_{A_0}(z) := \sum_{a \in A_0} z^a`$, $`P_{B_0}(z) := \sum_{b \in B_0} z^b`$, and define the crossing-pair polynomial

```math
E_N(z) := \sum_{n \ge 0} e_N(n) z^n, \qquad e_N(n) := \#\{(a, b) \in A_0 \times B_0 : a + b = N + 1 + n\},
```

and <i>W</i><sub><i>N</i></sub>(<i>z</i>) := 1 − (1 − <i>z</i>) <i>E</i><sub><i>N</i></sub>(<i>z</i>) ∈ ℤ[<i>z</i>]. Then:
1. <i>e</i><sub><i>N</i></sub>(<i>n</i>) ∈ {0, 1} for all <i>n</i> ≥ 0, and <i>E</i><sub><i>N</i></sub>(1) = <i>T</i>(<i>N</i>);
2. $`(1 - z) P_{A_0}(z) P_{B_0}(z) = V(z) - z^{N+1} W_N(z)`$;
3. <i>W</i><sub><i>N</i></sub>(1) = 1, <i>W</i><sub><i>N</i></sub>′(1) = <i>T</i>(<i>N</i>), and every coefficient of <i>W</i><sub><i>N</i></sub>(<i>z</i>) lies in {−1, 0, +1};
4. writing <i>w</i><sub><i>N</i></sub> := ord<sub><i>z</i>=0</sub>(<i>W</i><sub><i>N</i></sub>) and $`\widetilde{W}_N(z) := W_N(z) / z^{w_N} \in \mathbb{Z}[z]`$, we have $`\widetilde{W}_N(0) = 1`$, $`\widetilde{W}_N(1) = 1`$, every coefficient of $`\widetilde{W}_N(z)`$ lies in {−1, 0, +1}, and $`\widetilde{W}_N(z) = 1 - (1 - z) \widetilde{E}_N(z)`$ where $`\widetilde{E}_N(n) = e_N(w_N + n) \in \{0, 1\}`$ with $`\widetilde{E}_N(0) = 0`$.

*Proof.*
(1) Since <i>N</i> + 1 + <i>n</i> &gt; <i>N</i> ≥ <i>n</i><sub>0</sub>, we have 0 ≤ <i>e</i><sub><i>N</i></sub>(<i>n</i>) ≤ <i>r</i>(<i>N</i> + 1 + <i>n</i>) = 1. Summing over <i>n</i> ≥ 0 counts all pairs in <i>A</i><sub>0</sub> × <i>B</i><sub>0</sub> with <i>a</i> + <i>b</i> &gt; <i>N</i>, which is <i>T</i>(<i>N</i>).
(2) Separating sums ≤ <i>N</i> and &gt; <i>N</i>,

```math
P_{A_0}(z) P_{B_0}(z) = \sum_{n=0}^{N} r(n) z^n + z^{N+1} E_N(z) = \frac{1 - z^{N+1}}{1 - z} + \Delta(z) + z^{N+1} E_N(z).
```

Multiplying by (1 − <i>z</i>) gives 1 − <i>z</i><sup><i>N</i>+1</sup> + (1 − <i>z</i>)Δ(<i>z</i>) + <i>z</i><sup><i>N</i>+1</sup>(1 − <i>z</i>)<i>E</i><sub><i>N</i></sub>(<i>z</i>) = <i>V</i>(<i>z</i>) − <i>z</i><sup><i>N</i>+1</sup> <i>W</i><sub><i>N</i></sub>(<i>z</i>).
(3) Directly <i>W</i><sub><i>N</i></sub>(1) = 1, <i>W</i><sub><i>N</i></sub>′(1) = <i>E</i><sub><i>N</i></sub>(1) = <i>T</i>(<i>N</i>), [<i>z</i><sup>0</sup>]<i>W</i><sub><i>N</i></sub> = 1 − <i>e</i><sub><i>N</i></sub>(0) ∈ {0, 1}, and [<i>z</i><sup><i>n</i></sup>]<i>W</i><sub><i>N</i></sub> = <i>e</i><sub><i>N</i></sub>(<i>n</i> − 1) − <i>e</i><sub><i>N</i></sub>(<i>n</i>) ∈ {−1, 0, +1} for <i>n</i> ≥ 1.
(4) Since <i>W</i><sub><i>N</i></sub>(1) = 1, $`W_N \not\equiv 0`$, so $`w_N < \infty`$. If <i>w</i><sub><i>N</i></sub> = 0, 1 − <i>e</i><sub><i>N</i></sub>(0) ≠ 0 ⇒ <i>e</i><sub><i>N</i></sub>(0) = 0 and [<i>z</i><sup>0</sup>]<i>W</i><sub><i>N</i></sub> = 1. If <i>w</i><sub><i>N</i></sub> ≥ 1, the vanishing of $`[z^0]W_N, \dots, [z^{w_N - 1}]W_N`$ inductively forces <i>e</i><sub><i>N</i></sub>(0) = <i>e</i><sub><i>N</i></sub>(1) = … = <i>e</i><sub><i>N</i></sub>(<i>w</i><sub><i>N</i></sub> − 1) = 1, and $`[z^{w_N}]W_N = 1 - e_N(w_N) \neq 0`$ forces <i>e</i><sub><i>N</i></sub>(<i>w</i><sub><i>N</i></sub>) = 0 and $`[z^{w_N}]W_N = 1`$. Hence $`E_N(z) = \frac{1 - z^{w_N}}{1 - z} + z^{w_N} \widetilde{E}_N(z)`$ and $`W_N(z) = z^{w_N}(1 - (1-z)\widetilde{E}_N(z))`$. □

### Lemma 3.4 (Quantitative modular difference density; cf. van Doorn–Liu–Tang Lemma 2.2)
Let <i>N</i> ≥ <i>n</i><sub>0</sub> be an integer with <i>N</i> ∉ <i>A</i> ∪ <i>B</i> and <i>T</i>(<i>N</i>) ≤ <i>K</i>. Put <i>A</i><sub>0</sub> := <i>A</i> ∩ [0, <i>N</i>), <i>B</i><sub>0</sub> := <i>B</i> ∩ [0, <i>N</i>), <i>x</i><sub>0</sub> := max <i>A</i><sub>0</sub>, <i>z</i><sub>0</sub> := max <i>B</i><sub>0</sub>, and

```math
C_1(K) := E + S_2 + 2(1 + E)(1 + K).
```

Then:
1. $`\#\bigl([0,\ N - 1 - x_0] \setminus (B_0 - A_0)\bigr) \le C_1(K)`$, and
2. $`\#\bigl([1,\ N - 1 - z_0] \setminus (A_0 - B_0)\bigr) \le C_1(K)`$.

*Proof.* For 0 ≤ <i>n</i> &lt; <i>N</i>, define

```math
R(n) := \#\{(a, b) \in A_0 \times B_0 : a + b \equiv n \pmod N\}, \qquad D(n) := \#\{(a, b) \in A_0 \times B_0 : b - a \equiv n \pmod N\}.
```

Counting pairs and quadruples (with $`a_1 + b_1 \equiv a_2 + b_2 \iff b_1 - a_2 \equiv b_2 - a_1 \pmod N`$) yields

```math
\sum_{n=0}^{N-1} R(n) = \sum_{n=0}^{N-1} D(n) = |A_0||B_0| = N + 1 + c + T(N), \qquad \sum_{n=0}^{N-1} R(n)^2 = \sum_{n=0}^{N-1} D(n)^2,
```

and therefore $`\sum_{n=0}^{N-1} D(n)(D(n)-1) = \sum_{n=0}^{N-1} R(n)(R(n)-1)`$. Let $`r_0(m) := \#\{(a, b) \in A_0 \times B_0 : a + b = m\}`$. For 0 ≤ <i>n</i> &lt; <i>N</i>, since <i>a</i> + <i>b</i> ≤ 2N − 2, we have <i>R</i>(<i>n</i>) = <i>r</i><sub>0</sub>(<i>n</i>) + <i>r</i><sub>0</sub>(<i>n</i> + <i>N</i>), where <i>r</i><sub>0</sub>(<i>n</i>) = <i>r</i>(<i>n</i>) ≤ 1 + <i>E</i> and <i>r</i><sub>0</sub>(<i>n</i> + <i>N</i>) ∈ {0, 1} (since <i>n</i> + <i>N</i> ≥ <i>N</i> ≥ <i>n</i><sub>0</sub>). Moreover $`\sum_{n=0}^{N-1} r_0(n + N) = r_0(N) + T(N) \le 1 + K`$. Thus

```math
\sum_{n=0}^{N-1} R(n)(R(n)-1) = \sum_{n=0}^{N-1} r(n)(r(n)-1) + 0 + 2\sum_{n=0}^{N-1} r(n) r_0(n + N) \le S_2 + 2(1 + E)(1 + K).
```

Using the pointwise inequality $`\mathbf{1}_{d = 0} \le (1 - d) + d(d - 1)`$ (valid for every integer <i>d</i> ≥ 0, since (1 − <i>d</i>) + <i>d</i>(<i>d</i> − 1) = (<i>d</i> − 1)<sup>2</sup>), we obtain

```math
\begin{aligned}
\#\{0 \le n < N : D(n) = 0\}
&\le \sum_{n=0}^{N-1} (1 - D(n)) + \sum_{n=0}^{N-1} D(n)(D(n)-1) \\
&= N - (N + 1 + c + T(N)) + \sum_{n=0}^{N-1} R(n)(R(n)-1) \\
&\le E + S_2 + 2(1 + E)(1 + K) = C_1(K).
\end{aligned}
```

Finally, for (<i>a</i>, <i>b</i>) ∈ <i>A</i><sub>0</sub> × <i>B</i><sub>0</sub>, we have −<i>x</i><sub>0</sub> ≤ <i>b</i> − <i>a</i> ≤ <i>z</i><sub>0</sub> &lt; <i>N</i>:
- If 0 ≤ <i>n</i> ≤ <i>N</i> − 1 − <i>x</i><sub>0</sub> and <i>D</i>(<i>n</i>) ≥ 1, then <i>n</i> − <i>N</i> &lt; −<i>x</i><sub>0</sub> and <i>n</i> + <i>N</i> ≥ <i>N</i> &gt; <i>z</i><sub>0</sub>, so $`b - a \equiv n \pmod N`$ forces <i>b</i> − <i>a</i> = <i>n</i> ∈ <i>B</i><sub>0</sub> − <i>A</i><sub>0</sub>.
- If 1 ≤ <i>m</i> ≤ <i>N</i> − 1 − <i>z</i><sub>0</sub> and <i>D</i>(<i>N</i> − <i>m</i>) ≥ 1, then <i>N</i> − <i>m</i> &gt; <i>z</i><sub>0</sub> and −<i>m</i> − <i>N</i> &lt; −<i>N</i> &lt; −<i>x</i><sub>0</sub>, so $`b - a \equiv N - m \pmod N`$ forces <i>b</i> − <i>a</i> = −<i>m</i>, i.e., <i>a</i> − <i>b</i> = <i>m</i> ∈ <i>A</i><sub>0</sub> − <i>B</i><sub>0</sub>.

Both (1) and (2) follow immediately. □

### Lemma 3.5 (Zhang's Gap Lemma; cf. Zhang Lemmas 4.1–4.2)
Let <i>C</i> := <i>E</i> + <i>n</i><sub>0</sub>. Suppose <i>x</i> &lt; <i>y</i> are consecutive elements of <i>A</i> with <i>x</i> ≥ 2n<sub>0</sub> and <i>y</i> ≥ 3x + <i>n</i><sub>0</sub>. Then:
1. $`B \cap [y - x + n_0,\ y + x + n_0 - 1] = \varnothing`$;
2. <i>T</i>(<i>y</i> − 1) ≤ <i>n</i><sub>0</sub>;
3. for every integer 0 ≤ <i>t</i> ≤ <i>x</i>,

```math
|A(y + t) - A(x) - A(t)| \le C, \qquad |A(x) B(y + t) - y| \le C.
```

*Proof.* All convolutions below are on ℤ<sub>≥ 0</sub>, with functions extended by 0 to negative integers; $`h := \mathbf{1}_{\mathbb{Z}_{\ge 0}}`$.
(1) Put $`f := \mathbf{1}_{A \cap [0, x]}`$, $`g := \mathbf{1}_B`$, $`\widetilde{f}(n) := f(x - n)`$, and $`D := h - \widetilde{f} * g`$. For <i>n</i> ≥ 0,

```math
(\widetilde{f} * g)(n) = \#\{(a, b) \in (A \cap [0, x]) \times B : b - a = n - x\}.
```

Since <i>A</i> ∩ (<i>x</i>, <i>y</i>) = ∅, we have <i>f</i> ∗ <i>g</i> = <i>h</i> + δ on [0, <i>y</i> − 1]. Convolving <i>D</i> with <i>f</i> yields

```math
(f * D)(n) = ((f - \widetilde{f}) * h)(n) - (\widetilde{f} * \delta)(n) \qquad (0 \le n < y).
```

For <i>n</i> ≥ <i>x</i>, $`(f * h)(n) = A(x) = (\widetilde{f} * h)(n)`$; for <i>n</i> ≥ <i>x</i> + <i>n</i><sub>0</sub>, $`(\widetilde{f} * \delta)(n) = 0`$. Hence (<i>f</i> ∗ <i>D</i>)(<i>n</i>) = 0 for <i>x</i> + <i>n</i><sub>0</sub> ≤ <i>n</i> &lt; <i>y</i>. By Lemma 3.2, <i>D</i>(<i>n</i>) ≥ 0 for all <i>n</i> ≥ <i>x</i> + <i>n</i><sub>0</sub>. For any $`u \in [x + n_0,\ 2x + n_0 - 1]`$, we have <i>u</i> + <i>x</i> ≤ 3x + <i>n</i><sub>0</sub> − 1 &lt; <i>y</i>, so

```math
0 = (f * D)(u + x) = \sum_{a \in A \cap [0, x]} D(u + x - a).
```

Every argument satisfies <i>u</i> + <i>x</i> − <i>a</i> ≥ <i>u</i> ≥ <i>x</i> + <i>n</i><sub>0</sub>, so every term is ≥ 0; the <i>a</i> = <i>x</i> term is <i>D</i>(<i>u</i>), forcing <i>D</i>(<i>u</i>) = 0 for all $`u \in [x + n_0,\ 2x + n_0 - 1]`$. If there were a largest $`d \in [n_0,\ x + n_0 - 1]`$ with <i>D</i>(<i>d</i>) ≠ 0, then <i>x</i> + <i>n</i><sub>0</sub> ≤ <i>x</i> + <i>d</i> ≤ 2x + <i>n</i><sub>0</sub> − 1 &lt; <i>y</i>, and in $`0 = (f * D)(x + d) = \sum_{a \in A \cap [0, x]} D(x + d - a)`$ every <i>a</i> &lt; <i>x</i> satisfies <i>d</i> &lt; <i>x</i> + <i>d</i> − <i>a</i> ≤ 2x + <i>n</i><sub>0</sub> − 1 so <i>D</i>(<i>x</i> + <i>d</i> − <i>a</i>) = 0, leaving <i>D</i>(<i>d</i>) = 0, contradiction. Hence <i>D</i>(<i>n</i>) = 0 for all $`n \in [n_0,\ 2x + n_0 - 1]`$, meaning every integer in $`[n_0 - x,\ x + n_0 - 1]`$ lies in <i>B</i> − (<i>A</i> ∩ [0, <i>x</i>]). If $`b \in B \cap [y - x + n_0,\ y + x + n_0 - 1]`$, then <i>b</i> − <i>y</i> = <i>b</i>′ − <i>a</i> for some <i>a</i> ∈ <i>A</i> ∩ [0, <i>x</i>] and <i>b</i>′ ∈ <i>B</i>, contradicting Lemma 3.2 since <i>y</i> &gt; <i>x</i> ≥ <i>n</i><sub>0</sub>.

(2) Since <i>x</i> ≥ 2n<sub>0</sub> and <i>n</i><sub>0</sub> ≥ 1, part (1) gives $`B \cap [y - x + n_0,\ y + x] = \varnothing`$, so <i>B</i>(<i>y</i> + <i>t</i>) = <i>B</i>(<i>y</i> − 1) for 0 ≤ <i>t</i> ≤ <i>x</i>, and every <i>b</i> ∈ <i>B</i> ∩ [0, <i>y</i> − 1] satisfies <i>b</i> ≤ <i>y</i> − <i>x</i> + <i>n</i><sub>0</sub> − 1. Thus every (<i>a</i>, <i>b</i>) ∈ (<i>A</i> ∩ [0, <i>x</i>]) × (<i>B</i> ∩ [0, <i>y</i> − 1]) has <i>a</i> + <i>b</i> ≤ <i>y</i> + <i>n</i><sub>0</sub> − 1, giving

```math
y + c + T(y - 1) = A(y - 1)B(y - 1) = A(x)B(y - 1) \le \sum_{n=0}^{y + n_0 - 1} r(n) = y + n_0 + c,
```

so <i>T</i>(<i>y</i> − 1) ≤ <i>n</i><sub>0</sub> and |<i>A</i>(<i>x</i>)<i>B</i>(<i>y</i> + <i>t</i>) − <i>y</i>| = |<i>A</i>(<i>x</i>)<i>B</i>(<i>y</i> − 1) − <i>y</i>| ≤ <i>n</i><sub>0</sub> + |<i>c</i>| ≤ <i>C</i>.

(3) Put $`f_y(n) := \mathbf{1}_A(y + n)`$ (<i>n</i> ≥ 0). For <i>n</i><sub>0</sub> ≤ <i>n</i> ≤ <i>x</i> + <i>n</i><sub>0</sub> − 1, the unique representation <i>y</i> + <i>n</i> = <i>a</i> + <i>b</i> cannot use <i>a</i> ≤ <i>x</i> (else $`b = y + n - a \in [y - x + n_0,\ y + x + n_0 - 1]`$, impossible by (1)), so it uses <i>a</i> ≥ <i>y</i>, giving (<i>f</i><sub><i>y</i></sub> ∗ <i>g</i>)(<i>n</i>) = 1. For 0 ≤ <i>n</i> &lt; <i>n</i><sub>0</sub>, (<i>f</i><sub><i>y</i></sub> ∗ <i>g</i>)(<i>n</i>) ∈ {0, 1}. Thus <i>f</i><sub><i>y</i></sub> ∗ <i>g</i> = <i>h</i> + δ<sub><i>y</i></sub> on [0, <i>x</i> + <i>n</i><sub>0</sub> − 1] with supp(δ<sub><i>y</i></sub>) ⊆ [0, <i>n</i><sub>0</sub> − 1] and δ<sub><i>y</i></sub> ∈ {−1, 0}. Substituting into <i>f</i><sub><i>y</i></sub> ∗ (<i>f</i> ∗ <i>g</i>) = <i>f</i> ∗ (<i>f</i><sub><i>y</i></sub> ∗ <i>g</i>) gives, for 0 ≤ <i>t</i> ≤ <i>x</i>,

```math
A(y + t) - A(x) - A(t) = ((f_y - f) * h)(t) = (f * \delta_y)(t) - (f_y * \delta)(t),
```

whose absolute value is at most <i>n</i><sub>0</sub> + <i>E</i> = <i>C</i>. □

---

## 4. Unique Weak Limit Along Every Bounded-Crossing Sequence

Define the binary Cantor probability measures on [0, 1]:

```math
\nu_0 := \ast_{i=1}^{\infty} \frac{1}{2}\left(\delta_0 + \delta_{4^{-i}}\right), \qquad \mu_0 := \ast_{i=1}^{\infty} \frac{1}{2}\left(\delta_0 + \delta_{2 \cdot 4^{-i}}\right).
```

Observe that $`\nu_0 * \mu_0 = \mathcal{L}_{[0, 1]}`$ (normalized Lebesgue measure on [0, 1]), supp(ν<sub>0</sub>) ⊆ [0, 1/12] ∪ [1/4, 1/3] with $`\max\mathrm{supp}(\nu_0) = \frac{1}{3}`$, supp(μ<sub>0</sub>) ⊆ [0, 1/6] ∪ [1/2, 2/3] with $`\max\mathrm{supp}(\mu_0) = \frac{2}{3}`$, and both ν<sub>0</sub> and μ<sub>0</sub> are atomless (for any <i>x</i> ∈ ℝ and <i>m</i> ≥ 1, the first <i>m</i> factors already bound the point mass at <i>x</i> by 2<sup>−<i>m</i></sup> → 0).

For any integer <i>N</i> ≥ 1 with <i>A</i>(<i>N</i>), <i>B</i>(<i>N</i>) ≥ 1, define the empirical probability measures on [0, 1]:

```math
\mu_N := \frac{1}{A(N)} \sum_{a \in A \cap [0, N]} \delta_{a/N}, \qquad \nu_N := \frac{1}{B(N)} \sum_{b \in B \cap [0, N]} \delta_{b/N}.
```

We rely on the following single-step convolution factorization theorem of Gabardo and Lai (*J. Fourier Anal. Appl.* **20** (2014), Thm. 2.2; quoted as Theorem 2.4 in `arXiv:2610.35027v1`).

> **Theorem 4.1 (Gabardo–Lai, 2014).** Let (μ, ν) be a pair of Borel probability measures supported on [0, 1] with $`\mu * \nu = \mathcal{L}_{[0, 1]}`$. If $`(\mu, \nu) \notin \{(\delta_0, \mathcal{L}_{[0, 1]}),\ (\mathcal{L}_{[0, 1]}, \delta_0)\}`$, then there exist integers <i>M</i><sub>1</sub>, <i>M</i><sub>2</sub> ≥ 2 and Borel probability measures μ′, ν′ supported in [0, (<i>M</i><sub>1</sub> <i>M</i><sub>2</sub>)<sup>−1</sup>] with $`\mu' * \nu' = \mathcal{L}_{[0, (M_1 M_2)^{-1}]}`$ such that either
>
> ```math
> \mu = \left(\frac{1}{M_1}\sum_{j=0}^{M_1 - 1} \delta_{\frac{j}{M_1}}\right) * \mu', \qquad \nu = \left(\frac{1}{M_2}\sum_{j=0}^{M_2 - 1} \delta_{\frac{j}{M_1 M_2}}\right) * \nu', \tag{4.1}
> ```
>
> or the same holds with μ and ν interchanged.

### Lemma 4.2 (Lower bound for a single Gabardo–Lai step; van Doorn–Liu–Tang Lemma 2.5)
If (μ, ν) satisfies (4.1) with integers <i>M</i><sub>1</sub>, <i>M</i><sub>2</sub> ≥ 2, then

```math
\sup_{u \in (0, 1)} \frac{\mu([0, u]) \nu([0, u])}{u} \ge \frac{2 M_2 + 2}{M_2 + 2}.
```

*Proof.* Let $`r_\sigma := \max \mathrm{supp}(\sigma)`$ for any compactly supported nonzero measure σ; note $`r_{\sigma_1 * \sigma_2} = r_{\sigma_1} + r_{\sigma_2}`$. From (4.1) and $`\mu * \nu = \mathcal{L}_{[0, 1]}`$, we have

```math
r_\mu = 1 - r_\nu, \qquad r_{\mu'} = \frac{1}{M_1} - r_\nu \ge 0, \qquad r_{\nu'} = r_\nu - \frac{1}{M_1} + \frac{1}{M_1 M_2} \ge 0,
```

so $`u_0 := M_1 r_\nu \in [1 - 1/M_2,\ 1]`$. Set $`t_1 := r_{\mu'} + \frac{1}{M_1} = \frac{2}{M_1} - r_\nu`$ and $`t_2 := r_{\nu'} + \frac{1}{M_1 M_2} = r_\nu - \frac{1}{M_1} + \frac{2}{M_1 M_2}`$.
- Since $`t_1 \ge r_\nu`$ (as <i>r</i><sub>μ′</sub> ≥ 0), we have ν([0, <i>t</i><sub>1</sub>]) = 1 and $`\mu([0, t_1]) \ge \frac{2}{M_1}`$ (covering the <i>j</i> = 0, 1 copies of μ′), giving

```math
\frac{\mu([0, t_1])\nu([0, t_1])}{t_1} \ge \frac{2}{2 - u_0}.
```

- Since $`t_2 - r_{\mu'} = 2(r_\nu - \frac{1}{M_1} + \frac{1}{M_1 M_2}) = 2 r_{\nu'} \ge 0`$, we have <i>r</i><sub>μ′</sub> ≤ <i>t</i><sub>2</sub>, so $`\mu([0, t_2]) \ge \frac{1}{M_1}`$ (covering the <i>j</i> = 0 copy of μ′) and $`\nu([0, t_2]) \ge \frac{2}{M_2}`$ (covering the <i>j</i> = 0, 1 copies of ν′), giving

```math
\frac{\mu([0, t_2])\nu([0, t_2])}{t_2} \ge \frac{2}{2 - M_2 + M_2 u_0}.
```

(Note that $`r_\nu \ge \frac{1}{M_1}(1 - \frac{1}{M_2})`$ gives $`t_1 = \frac{2}{M_1} - r_\nu \le \frac{1}{M_1}(1 + \frac{1}{M_2}) \le \frac{3}{4} < 1`$, and $`r_\nu \le \frac{1}{M_1}`$ gives $`t_2 \le \frac{2}{M_1 M_2} \le \frac{1}{2} < 1`$.) Since $`\frac{2}{2 - u_0}`$ increases in <i>u</i><sub>0</sub> and $`\frac{2}{2 - M_2 + M_2 u_0}`$ decreases in <i>u</i><sub>0</sub>, their maximum is minimized when 2 − <i>u</i><sub>0</sub> = 2 − <i>M</i><sub>2</sub> + <i>M</i><sub>2</sub> <i>u</i><sub>0</sub>, i.e. $`u_0 = \frac{M_2}{M_2 + 1}`$, yielding $`\frac{2 M_2 + 2}{M_2 + 2}`$. □

### Proposition 4.3 (Unique weak limit along every bounded-crossing sequence)
Assume $`\lambda := \limsup_{x \to \infty} \frac{A(x)B(x)}{x} < \frac{8}{5}`$. Fix any constant <i>K</i> ≥ <i>T</i><sub>min</sub> and any sequence of integers $`N_j \to \infty`$ with <i>T</i>(<i>N</i><sub><i>j</i></sub>) ≤ <i>K</i> for all <i>j</i>. If $`\mu_{N_j} \to \mu`$ and $`\nu_{N_j} \to \nu`$ weakly, then $`(\mu, \nu) \in \{(\nu_0, \mu_0),\ (\mu_0, \nu_0)\}`$.

*Proof.*
**Step 1: $`\mu * \nu = \mathcal{L}_{[0, 1]}`$ and lower bound on λ.**
For any continuous <i>f</i> : [0, 2] → ℝ, separating sums ≤ <i>N</i><sub><i>j</i></sub> and &gt; <i>N</i><sub><i>j</i></sub> gives

```math
\int f\,d(\mu_{N_j} * \nu_{N_j}) = \frac{1}{A(N_j)B(N_j)} \left(\sum_{n=0}^{n_0 - 1} \delta(n) f\!\left(\frac{n}{N_j}\right) + \sum_{n=0}^{N_j} f\!\left(\frac{n}{N_j}\right) + \sum_{\substack{a \in A_0, b \in B_0 \\ a+b > N_j}} f\!\left(\frac{a+b}{N_j}\right)\right).
```

Since <i>A</i>(<i>N</i><sub><i>j</i></sub>)<i>B</i>(<i>N</i><sub><i>j</i></sub>) = <i>N</i><sub><i>j</i></sub> + 1 + <i>c</i> + <i>T</i>(<i>N</i><sub><i>j</i></sub>) = <i>N</i><sub><i>j</i></sub> + <i>O</i><sub><i>K</i></sub>(1) and the first and third sums have at most <i>E</i> + <i>K</i> = <i>O</i><sub><i>K</i></sub>(1) terms, this converges to $`\int_0^1 f(t)\,dt`$. Hence $`\mu * \nu = \mathcal{L}_{[0, 1]}`$.

At every common continuity point <i>t</i> ∈ (0, 1) of μ and ν, $`\frac{A(t N_j)}{A(N_j)} \to \mu([0, t])`$ and $`\frac{B(t N_j)}{B(N_j)} \to \nu([0, t])`$, so

```math
\lambda \ge \lim_{j \to \infty} \frac{A(t N_j) B(t N_j)}{t N_j} = \frac{\mu([0, t]) \nu([0, t])}{t}.
```

Since discontinuities are countable, approximating any <i>t</i> ∈ (0, 1) from the right by common continuity points $`t_m \downarrow t`$ and using μ([0, <i>t</i><sub><i>m</i></sub>]) ≥ μ([0, <i>t</i>]), ν([0, <i>t</i><sub><i>m</i></sub>]) ≥ ν([0, <i>t</i>]) yields

```math
\lambda \ge \sup_{t \in (0, 1)} \frac{\mu([0, t]) \nu([0, t])}{t}. \tag{4.2}
```

**Step 2: Exclusion of the trivial limit $`(\delta_0, \mathcal{L}_{[0, 1]})`$ (cf. van Doorn–Liu–Tang Theorem 3.1).**
Suppose wlog $`(\mu, \nu) = (\delta_0, \mathcal{L}_{[0, 1]})`$. Since <i>A</i>, <i>B</i> are infinite and <i>T</i>(<i>N</i><sub><i>j</i></sub>) ≤ <i>K</i>, we have <i>N</i><sub><i>j</i></sub> ∉ <i>A</i> ∪ <i>B</i> for all large <i>j</i> (if <i>N</i><sub><i>j</i></sub> ∈ <i>A</i>, then $`T(N_j) \ge B(N_j) - 1 \to \infty`$, contradiction). Put <i>a</i><sub><i>j</i></sub> := max(<i>A</i> ∩ [0, <i>N</i><sub><i>j</i></sub>]) and $`g_j := \min(A \cap (N_j, \infty)) - 1`$. If <i>a</i><sub><i>j</i></sub> &gt; η <i>N</i><sub><i>j</i></sub> for some η &gt; 0 along a subsequence, then (<i>a</i><sub><i>j</i></sub>, <i>b</i>) is a crossing pair for every <i>b</i> ∈ <i>B</i> ∩ [(1 − η)<i>N</i><sub><i>j</i></sub>, <i>N</i><sub><i>j</i></sub>], giving $`T(N_j) \ge (\eta - o(1)) B(N_j) \to \infty`$, impossible; hence <i>a</i><sub><i>j</i></sub> = <i>o</i>(<i>N</i><sub><i>j</i></sub>). By (3.2) and Lemma 3.1(3),

```math
g_j + 1 + c + T(g_j) = A(g_j)B(g_j) = A(a_j)B(g_j) \le a_j + g_j + 1 + E,
```

so <i>T</i>(<i>g</i><sub><i>j</i></sub>) ≤ <i>a</i><sub><i>j</i></sub> + 2E = <i>O</i>(<i>a</i><sub><i>j</i></sub>) and <i>A</i>(<i>g</i><sub><i>j</i></sub>)<i>B</i>(<i>g</i><sub><i>j</i></sub>) = (1 + <i>o</i>(1))<i>g</i><sub><i>j</i></sub>. Set $`x_j := \lfloor \sqrt{(a_j + 1)N_j} \rfloor`$, so <i>a</i><sub><i>j</i></sub> = <i>o</i>(<i>x</i><sub><i>j</i></sub>) and <i>x</i><sub><i>j</i></sub> = <i>o</i>(<i>N</i><sub><i>j</i></sub>).
- For every $`b \in B \cap [g_j + 1,\ g_j + x_j]`$, 0 ≤ <i>b</i> − (<i>g</i><sub><i>j</i></sub> + 1) &lt; <i>x</i><sub><i>j</i></sub> &lt; <i>N</i><sub><i>j</i></sub> − 1 − <i>a</i><sub><i>j</i></sub>, and Lemma 3.2 forbids <i>b</i> − (<i>g</i><sub><i>j</i></sub> + 1) ∈ <i>B</i><sub>0</sub> − <i>A</i><sub>0</sub> (as <i>g</i><sub><i>j</i></sub> + 1 &gt; <i>N</i><sub><i>j</i></sub> ≥ <i>n</i><sub>0</sub>). By Lemma 3.4(1), <i>B</i>(<i>g</i><sub><i>j</i></sub> + <i>x</i><sub><i>j</i></sub>) − <i>B</i>(<i>g</i><sub><i>j</i></sub>) ≤ <i>C</i><sub>1</sub>(<i>K</i>) = <i>O</i>(1), so <i>B</i>(<i>g</i><sub><i>j</i></sub> + <i>x</i><sub><i>j</i></sub>) = (1 + <i>o</i>(1))<i>B</i>(<i>g</i><sub><i>j</i></sub>).
- Every integer $`n \in [g_j + 1,\ g_j + x_j]`$ has a representation <i>a</i> + <i>b</i> = <i>n</i> with either <i>a</i>, <i>b</i> ≤ <i>g</i><sub><i>j</i></sub> (at most <i>T</i>(<i>g</i><sub><i>j</i></sub>) = <i>o</i>(<i>x</i><sub><i>j</i></sub>) integers), or <i>g</i><sub><i>j</i></sub> + 1 ≤ <i>a</i> ≤ <i>g</i><sub><i>j</i></sub> + <i>x</i><sub><i>j</i></sub> and <i>b</i> ≤ <i>x</i><sub><i>j</i></sub>, or <i>g</i><sub><i>j</i></sub> + 1 ≤ <i>b</i> ≤ <i>g</i><sub><i>j</i></sub> + <i>x</i><sub><i>j</i></sub> and <i>a</i> ≤ <i>a</i><sub><i>j</i></sub> (at most <i>C</i><sub>1</sub>(<i>K</i>) <i>A</i>(<i>a</i><sub><i>j</i></sub>) = <i>O</i>(<i>A</i>(<i>g</i><sub><i>j</i></sub>)) = <i>o</i>(<i>x</i><sub><i>j</i></sub>), since <i>A</i>(<i>a</i><sub><i>j</i></sub>)<i>B</i>(<i>x</i><sub><i>j</i></sub>) ≤ <i>a</i><sub><i>j</i></sub> + <i>x</i><sub><i>j</i></sub> + <i>O</i>(1) = (1 + <i>o</i>(1))<i>x</i><sub><i>j</i></sub> and $`B(x_j) \to \infty`$). Thus

```math
(A(g_j + x_j) - A(g_j)) B(x_j) \ge (1 - o(1))x_j \ge (1 - o(1)) A(g_j) B(x_j),
```

giving <i>A</i>(<i>g</i><sub><i>j</i></sub> + <i>x</i><sub><i>j</i></sub>) ≥ (2 − <i>o</i>(1))<i>A</i>(<i>g</i><sub><i>j</i></sub>), hence $`\frac{A(g_j + x_j)B(g_j + x_j)}{g_j + x_j} \ge 2 - o(1)`$, contradicting λ &lt; 8/5.

**Step 3: Scaling invariance and exclusion of Type I and <i>M</i><sub><i>k</i></sub> ≥ 3 (<i>k</i> ≥ 2 ).**
Let (μ<sup>(0)</sup>, ν<sup>(0)</sup>) := (μ, ν). We iterate Theorem 4.1: if (μ<sup>(<i>k</i>)</sup>, ν<sup>(<i>k</i>)</sup>) is non-trivial, Theorem 4.1 yields integers <i>M</i><sub>2k+1</sub>, <i>M</i><sub>2k+2</sub> ≥ 2 and measures μ<sup>(<i>k</i>)′</sup>, ν<sup>(<i>k</i>)′</sup> supported in [0, (<i>M</i><sub>2k+1</sub><i>M</i><sub>2k+2</sub>)<sup>−1</sup>] satisfying (4.1) (up to swapping the two measures), and we define the rescaled complementary pair (μ<sup>(<i>k</i>+1)</sup>, ν<sup>(<i>k</i>+1)</sup>) on [0, 1] by pushing forward (μ<sup>(<i>k</i>)′</sup>, ν<sup>(<i>k</i>)′</sup>) under <i>x</i> ↦ <i>M</i><sub>2k+1</sub> <i>M</i><sub>2k+2</sub> <i>x</i>.

Observe two exact scaling-invariance identities for any pair (α ∗ σ′, β ∗ τ′) satisfying (4.1) with (<i>M</i><sub>1</sub>, <i>M</i><sub>2</sub>):
- *(Two-step rescaling)* For any <i>u</i> ∈ (0, 1), setting $`t := \frac{u}{M_1 M_2} < \frac{1}{M_1 M_2} < \frac{1}{M_1}`$, only the <i>j</i> = 0 copy of each factor meets [0, <i>t</i>], so

```math
\frac{(\alpha * \sigma')([0, t]) (\beta * \tau')([0, t])}{t} = \frac{\frac{1}{M_1}\widetilde{\sigma}([0, u]) \cdot \frac{1}{M_2}\widetilde{\tau}([0, u])}{u / (M_1 M_2)} = \frac{\widetilde{\sigma}([0, u]) \widetilde{\tau}([0, u])}{u}, \tag{4.3}
```

where $`\widetilde{\sigma} = (x \mapsto M_1 M_2 x)_* \sigma'`$ and $`\widetilde{\tau} = (x \mapsto M_1 M_2 x)_* \tau'`$.
- *(Single-factor stripping)* Since $`\sigma' * (\beta * \tau') = \beta * \mathcal{L}_{[0, (M_1 M_2)^{-1}]} = \mathcal{L}_{[0, M_1^{-1}]}`$, the measures $`\widehat{\sigma} := (x \mapsto M_1 x)_* \sigma'`$ and $`\widehat{\tau} := (x \mapsto M_1 x)_* (\beta * \tau')`$ satisfy $`\widehat{\sigma} * \widehat{\tau} = \mathcal{L}_{[0, 1]}`$ and, for any <i>u</i> ∈ (0, 1) with <i>t</i> := <i>u</i> / <i>M</i><sub>1</sub> &lt; 1 / <i>M</i><sub>1</sub>,

```math
\frac{(\alpha * \sigma')([0, t]) (\beta * \tau')([0, t])}{t} = \frac{\frac{1}{M_1}\widehat{\sigma}([0, u]) \cdot \widehat{\tau}([0, u])}{u / M_1} = \frac{\widehat{\sigma}([0, u]) \widehat{\tau}([0, u])}{u}. \tag{4.4}
```

By (4.2) and (4.3), $`\lambda \ge \sup_{u \in (0, 1)} \frac{\mu^{(k)}([0, u])\nu^{(k)}([0, u])}{u}`$ for every <i>k</i> ≥ 0 reached before termination.

*Claim 3a: (μ<sup>(<i>k</i>)</sup>, ν<sup>(<i>k</i>)</sup>) is non-trivial for every <i>k</i> ≥ 0.*
Step 2 rules out <i>k</i> = 0. Suppose <i>k</i> ≥ 1 is the smallest index where (μ<sup>(<i>k</i>)</sup>, ν<sup>(<i>k</i>)</sup>) is trivial. Write (μ<sup>(<i>k</i> − 1)</sup>, ν<sup>(<i>k</i> − 1)</sup>) in the form (4.1) with (<i>M</i><sub>1</sub>, <i>M</i><sub>2</sub>) = (<i>M</i><sub>2k − 1</sub>, <i>M</i><sub>2k</sub>) (wlog unswapped).
- If $`(\mu^{(k)}, \nu^{(k)}) = (\delta_0, \mathcal{L}_{[0, 1]})`$, then $`\mu^{(k-1)} = \frac{1}{M_1}\sum_{j=0}^{M_1 - 1} \delta_{j / M_1}`$ and $`\nu^{(k-1)} = \mathcal{L}_{[0, 1/M_1]}`$. Evaluating at $`u = \frac{1}{M_1} + \eta`$ ($`\eta \downarrow 0`$) gives $`\mu^{(k-1)}([0, u]) = \frac{2}{M_1}`$, ν<sup>(<i>k</i> − 1)</sup>([0, <i>u</i>]) = 1, so $`\lambda \ge \lim_{\eta \downarrow 0} \frac{2/M_1}{1/M_1 + \eta} = 2`$, contradiction.
- If $`(\mu^{(k)}, \nu^{(k)}) = (\mathcal{L}_{[0, 1]}, \delta_0)`$, then $`\mu^{(k-1)} = (\frac{1}{M_1}\sum_{j=0}^{M_1-1}\delta_{j/M_1}) * \mathcal{L}_{[0, 1/(M_1 M_2)]}`$ and $`\nu^{(k-1)} = \frac{1}{M_2}\sum_{j=0}^{M_2-1}\delta_{j/(M_1 M_2)}`$. Evaluating at $`u = \frac{1}{M_1 M_2} + \eta`$ ($`\eta \downarrow 0`$) gives $`\mu^{(k-1)}([0, u]) \ge \frac{1}{M_1}`$ and $`\nu^{(k-1)}([0, u]) = \frac{2}{M_2}`$, so $`\lambda \ge \lim_{\eta \downarrow 0} \frac{2/(M_1 M_2)}{1/(M_1 M_2) + \eta} = 2`$, contradiction.

Thus the iteration never terminates and yields an infinite sequence <i>M</i><sub>1</sub>, <i>M</i><sub>2</sub>, <i>M</i><sub>3</sub>, … ≥ 2.

*Claim 3b: At every <i>k</i> ≥ 0, <i>M</i><sub>2k+2</sub> = 2, <i>M</i><sub>2k+3</sub> = 2, and the orientation does not swap between step <i>k</i> and step <i>k</i> + 1.*
Write (μ<sup>(<i>k</i>)</sup>, ν<sup>(<i>k</i>)</sup>) in the form (4.1) with (<i>M</i><sub>1</sub>, <i>M</i><sub>2</sub>) = (<i>M</i><sub>2k+1</sub>, <i>M</i><sub>2k+2</sub>) (wlog with μ<sup>(<i>k</i>)</sup> carrying <i>M</i><sub>2k+1</sub> and ν<sup>(<i>k</i>)</sup> carrying <i>M</i><sub>2k+2</sub>).
- Lemma 4.2 gives $`\lambda \ge \frac{2 M_{2k+2} + 2}{M_{2k+2} + 2}`$. Since $`\lambda < \frac{8}{5} = \frac{2 \cdot 3 + 2}{3 + 2}`$, this forces <i>M</i><sub>2k+2</sub> = 2.
- At step <i>k</i> + 1, suppose the orientation swapped, so ν<sup>(<i>k</i>+1)</sup> carried <i>M</i><sub>2k+3</sub> and μ<sup>(<i>k</i>+1)</sup> carried <i>M</i><sub>2k+4</sub>:

```math
\nu^{(k+1)} = \left(\frac{1}{M_{2k+3}}\sum_{l=0}^{M_{2k+3}-1}\delta_{\frac{l}{M_{2k+3}}}\right) * \nu^{(k+1)'}, \qquad \mu^{(k+1)} = \left(\frac{1}{M_{2k+4}}\sum_{l=0}^{M_{2k+4}-1}\delta_{\frac{l}{M_{2k+3}M_{2k+4}}}\right) * \mu^{(k+1)'}.
```

Then supp(μ<sup>(<i>k</i>+1)</sup>) ⊆ [0, <i>M</i><sub>2k+3</sub><sup>−1</sup>] and $`\mu^{(k+1)} * \nu^{(k+1)'} = \mathcal{L}_{[0, M_{2k+3}^{-1}]}`$. Rescaling back by (<i>M</i><sub>2k+1</sub><i>M</i><sub>2k+2</sub>)<sup>−1</sup>, the two uniform discrete factors of ν<sup>(<i>k</i>)</sup> merge into a single factor of size <i>M</i>′ := <i>M</i><sub>2k+2</sub> <i>M</i><sub>2k+3</sub> ≥ 4:

```math
\mu^{(k)} = \left(\frac{1}{M_{2k+1}}\sum_{j=0}^{M_{2k+1}-1}\delta_{\frac{j}{M_{2k+1}}}\right) * \mu^{(k)'}, \qquad \nu^{(k)} = \left(\frac{1}{M'}\sum_{m=0}^{M'-1}\delta_{\frac{m}{M_{2k+1} M'}}\right) * \nu'',
```

where $`\mu^{(k)'} * \nu'' = \mathcal{L}_{[0, (M_{2k+1} M')^{-1}]}`$ and both have support in [0, (<i>M</i><sub>2k+1</sub><i>M</i>′)<sup>−1</sup>]. Lemma 4.2 then yields $`\lambda \ge \frac{2M'+2}{M'+2} \ge \frac{5}{3} > \frac{8}{5}`$, contradiction.
- Hence no swap occurs: μ<sup>(<i>k</i>+1)</sup> carries <i>M</i><sub>2k+3</sub> and ν<sup>(<i>k</i>+1)</sup> carries <i>M</i><sub>2k+4</sub>. In particular supp(ν<sup>(<i>k</i>+1)</sup>) ⊆ [0, <i>M</i><sub>2k+3</sub><sup>−1</sup>] and $`\mu^{(k+1)'} * \nu^{(k+1)} = \mathcal{L}_{[0, M_{2k+3}^{-1}]}`$. Applying single-factor stripping (4.4) to (μ<sup>(<i>k</i>)</sup>, ν<sup>(<i>k</i>)</sup>) gives $`(\widehat{\nu}, \widehat{\mu})`$ satisfying (4.1) with (<i>M</i><sub>2k+2</sub>, <i>M</i><sub>2k+3</sub>):

```math
\widehat{\nu} = \left(\frac{1}{M_{2k+2}}\sum_{j=0}^{M_{2k+2}-1}\delta_{\frac{j}{M_{2k+2}}}\right) * \widehat{\nu}_1, \qquad \widehat{\mu} = \left(\frac{1}{M_{2k+3}}\sum_{l=0}^{M_{2k+3}-1}\delta_{\frac{l}{M_{2k+2}M_{2k+3}}}\right) * \widehat{\mu}_1,
```

where $`\widehat{\nu}_1 = (x \mapsto x/M_{2k+2})_*\nu^{(k+1)}`$ and $`\widehat{\mu}_1 = (x \mapsto x/M_{2k+2})_*\mu^{(k+1)'}`$ are supported in [0, (<i>M</i><sub>2k+2</sub><i>M</i><sub>2k+3</sub>)<sup>−1</sup>] with $`\widehat{\nu}_1 * \widehat{\mu}_1 = \mathcal{L}_{[0, (M_{2k+2}M_{2k+3})^{-1}]}`$. By (4.4) and Lemma 4.2, $`\lambda \ge \frac{2 M_{2k+3} + 2}{M_{2k+3} + 2}`$, forcing <i>M</i><sub>2k+3</sub> = 2.

Consequently, <i>M</i><sub>2</sub> = <i>M</i><sub>3</sub> = <i>M</i><sub>4</sub> = … = 2 with strictly alternating factors. Since the remainder measures at step <i>k</i> have support in $`[0, \frac{2}{M_1 \cdot 4^k}]`$ and converge weakly to δ<sub>0</sub>, we obtain (up to swapping μ and ν):

```math
\mu = \left(\frac{1}{M_1}\sum_{j=0}^{M_1 - 1}\delta_{\frac{j}{M_1}}\right) * \ast_{i=1}^{\infty} \frac{1}{2}\left(\delta_0 + \delta_{\frac{1}{M_1 \cdot 4^i}}\right), \qquad \nu = \ast_{i=1}^{\infty} \frac{1}{2}\left(\delta_0 + \delta_{\frac{2}{M_1 \cdot 4^i}}\right).
```

Notice that both μ and ν are atomless, with $`\max\mathrm{supp}(\nu) = \frac{2}{3M_1}`$ and $`\max\mathrm{supp}(\mu) = 1 - \frac{2}{3M_1}`$.

**Step 4: Exclusion of <i>M</i><sub>1</sub> ≥ 3 via Zhang's Gap Lemma.**
Suppose for contradiction that <i>M</i><sub>1</sub> ≥ 3 (wlog with μ for <i>A</i> and ν for <i>B</i>). Fix η := 0.01. Since $`1 - \frac{2}{3M_1} = \max\mathrm{supp}(\mu)`$ and μ is atomless, $`\delta_\eta := \mu((1 - \frac{2}{3M_1} - \eta, 1]) > 0`$. By weak convergence, for all sufficiently large <i>j</i> we have

```math
\#\left(A \cap \left(\left(1 - \frac{2}{3M_1} - \eta\right)N_j,\ N_j\right]\right) \ge \frac{\delta_\eta}{2} A(N_j) \to \infty.
```

If there existed any $`b \in B \cap ((\frac{2}{3M_1} + \eta)N_j, N_j]`$, every such <i>a</i> would yield a crossing pair (<i>a</i>, <i>b</i>) with <i>a</i> + <i>b</i> &gt; <i>N</i><sub><i>j</i></sub>, contradicting <i>T</i>(<i>N</i><sub><i>j</i></sub>) ≤ <i>K</i>. Thus $`B \cap ((\frac{2}{3M_1} + \eta)N_j, N_j] = \varnothing`$ for all large <i>j</i>.

Set <i>x</i><sub><i>j</i></sub> := max(<i>B</i> ∩ [0, <i>N</i><sub><i>j</i></sub>]) and $`y_j := \min(B \cap (N_j, \infty))`$. Since <i>M</i><sub>1</sub> ≥ 3, we have $`\frac{2}{3M_1} + \eta \le \frac{2}{9} + 0.01 < \frac{1}{4}`$, so <i>x</i><sub><i>j</i></sub> ≤ (2/9 + η)<i>N</i><sub><i>j</i></sub> &lt; 1/4 <i>y</i><sub><i>j</i></sub>. For all large <i>j</i>, <i>x</i><sub><i>j</i></sub> ≥ 2n<sub>0</sub> and <i>y</i><sub><i>j</i></sub> ≥ 3x<sub><i>j</i></sub> + <i>n</i><sub>0</sub>, so Lemma 3.5 (with <i>A</i>, <i>B</i> swapped) applied at <i>t</i> = <i>x</i><sub><i>j</i></sub> gives

```math
B(y_j + x_j) \ge 2 B(x_j) - C, \qquad B(x_j) A(y_j + x_j) \ge y_j - C.
```

Therefore

```math
\lambda \ge \liminf_{j \to \infty} \frac{A(y_j + x_j)B(y_j + x_j)}{y_j + x_j} \ge \liminf_{j \to \infty} \left(2 - \frac{C}{B(x_j)}\right)\left(1 - \frac{C}{y_j}\right)\frac{y_j}{y_j + x_j} \ge \frac{2}{1 + \frac{2}{9} + \eta} = \frac{18}{11.09} > 1.62 > \frac{8}{5},
```

contradicting λ &lt; 8/5.

Thus <i>M</i><sub>1</sub> = 2, which gives μ = μ<sub>0</sub> and ν = ν<sub>0</sub> (or vice versa). □

### Corollary 4.4 (Uniform approximation at all bounded-crossing levels)
Assume λ &lt; 8/5. For every constant <i>K</i> ≥ <i>T</i><sub>min</sub> and every ε ∈ (0, 10<sup>−3</sup>], there exists an integer $`N_*(K, \varepsilon) \ge 10^4 (K + E + n_0 + 1)(E + n_0 + 1) / \varepsilon`$ such that for every integer $`N \ge N_*(K, \varepsilon)`$ with <i>T</i>(<i>N</i>) ≤ <i>K</i>:
1. <i>A</i>(<i>t</i>)<i>B</i>(<i>t</i>) ≤ 8/5 <i>t</i> for all real <i>t</i> ≥ <i>N</i>;
2. min(<i>A</i>(<i>N</i>), <i>B</i>(<i>N</i>)) ≥ 10<sup>4</sup> (<i>C</i><sub>1</sub>(<i>K</i>) + <i>K</i> + <i>E</i> + <i>n</i><sub>0</sub> + 1) / ε;
3. up to swapping the labels of <i>A</i> and <i>B</i>:

```math
\sup_{u \in [0, 1]} \left|\frac{A(uN)}{A(N)} - \nu_0([0, u])\right| < \varepsilon, \qquad \sup_{u \in [0, 1]} \left|\frac{B(uN)}{B(N)} - \mu_0([0, u])\right| < \varepsilon,
```

```math
x_0 := \max(A \cap [0, N]) \in \left[\left(\tfrac{1}{3} - \varepsilon\right)N,\ \left(\tfrac{1}{3} + \varepsilon\right)N\right], \qquad z_0 := \max(B \cap [0, N]) \in \left[\left(\tfrac{2}{3} - \varepsilon\right)N,\ \left(\tfrac{2}{3} + \varepsilon\right)N\right].
```

*Proof.* Properties (1) and (2) hold for all sufficiently large <i>N</i> since λ &lt; 8/5 and <i>A</i>, <i>B</i> are infinite. If (3) failed for arbitrarily large <i>N</i> with <i>T</i>(<i>N</i>) ≤ <i>K</i>, compactness of probability measures on [0, 1] (Prokhorov/Helly) would produce a sequence $`N_j \to \infty`$ with <i>T</i>(<i>N</i><sub><i>j</i></sub>) ≤ <i>K</i> along which $`(\mu_{N_j}, \nu_{N_j})`$ converges weakly to some (μ, ν) while violating (3). By Proposition 4.3, (μ, ν) ∈ {(ν<sub>0</sub>, μ<sub>0</sub>), (μ<sub>0</sub>, ν<sub>0</sub>)} (wlog (ν<sub>0</sub>, μ<sub>0</sub>)). Since ν<sub>0</sub> and μ<sub>0</sub> have continuous distribution functions on compact [0, 1], weak convergence implies uniform convergence of their cumulative distribution functions (Pólya's theorem). Moreover, ν<sub>0</sub>((1/3 − ε, 1/3]) &gt; 0 and μ<sub>0</sub>((2/3 − ε, 2/3]) &gt; 0 immediately force <i>x</i><sub>0</sub> &gt; (1/3 − ε)<i>N</i><sub><i>j</i></sub> and <i>z</i><sub>0</sub> &gt; (2/3 − ε)<i>N</i><sub><i>j</i></sub> for large <i>j</i>, while the crossing bound <i>T</i>(<i>N</i><sub><i>j</i></sub>) ≤ <i>K</i> (as in Step 4 of Proposition 4.3) forbids any element of <i>A</i> in ((1/3 + ε)<i>N</i><sub><i>j</i></sub>, <i>N</i><sub><i>j</i></sub>] or of <i>B</i> in ((2/3 + ε)<i>N</i><sub><i>j</i></sub>, <i>N</i><sub><i>j</i></sub>] for large <i>j</i>, contradicting the failure of (3). □

## 5. Exact Forward Doubling and Quadratic Polynomial Recurrence

Fix ε := 10<sup>−3</sup>. Throughout this section, assume λ &lt; 8/5, fix a constant <i>K</i> ≥ max(<i>T</i><sub>min</sub>, <i>n</i><sub>0</sub>), and let $`N \ge N_*(K, \varepsilon)`$ be an integer with <i>T</i>(<i>N</i>) ≤ <i>K</i>. By Corollary 4.4(3), assume without loss of generality that <i>A</i> approximates ν<sub>0</sub> (on [0, 1/3]) and <i>B</i> approximates μ<sub>0</sub> (on [0, 2/3]). Put:

```math
A_0 := A \cap [0, N], \quad B_0 := B \cap [0, N], \quad x_0 := \max A_0, \quad z_0 := \max B_0,
```

```math
y_0 := \min(A \cap (N, \infty)), \qquad w_0 := \min(B \cap (N, \infty)).
```

Note that <i>x</i><sub>0</sub> ∈ [(1/3 − ε)<i>N</i>, (1/3 + ε)<i>N</i>] and <i>z</i><sub>0</sub> ∈ [(2/3 − ε)<i>N</i>, (2/3 + ε)<i>N</i>], so <i>N</i> ∉ <i>A</i> ∪ <i>B</i>.

### Lemma 5.1 (Location of <i>y</i><sub>0</sub> )
We have <i>N</i> &lt; <i>y</i><sub>0</sub> ≤ (1 + 8ε)<i>N</i>.

*Proof.* If <i>y</i><sub>0</sub> &lt; 3 <i>x</i><sub>0</sub> + <i>n</i><sub>0</sub>, then $`y_0 < 3(\frac{1}{3} + \varepsilon)N + \varepsilon N = (1 + 4\varepsilon)N < (1 + 8\varepsilon)N`$. Otherwise <i>y</i><sub>0</sub> ≥ 3 <i>x</i><sub>0</sub> + <i>n</i><sub>0</sub>. Since <i>x</i><sub>0</sub> &lt; <i>y</i><sub>0</sub> are consecutive elements of <i>A</i> and <i>x</i><sub>0</sub> ≥ (1/3 − ε)<i>N</i> ≥ 2n<sub>0</sub>, Lemma 3.5(2) gives <i>T</i>(<i>y</i><sub>0</sub> − 1) ≤ <i>n</i><sub>0</sub> ≤ <i>K</i>. As $`y_0 - 1 \ge N \ge N_*(K, \varepsilon)`$, Corollary 4.4(3) applies at level <i>y</i><sub>0</sub> − 1, forcing <i>x</i><sub>0</sub> = max(<i>A</i> ∩ [0, <i>y</i><sub>0</sub> − 1]) to lie in [(1/3 − ε)(<i>y</i><sub>0</sub> − 1), (1/3 + ε)(<i>y</i><sub>0</sub> − 1)] or [(2/3 − ε)(<i>y</i><sub>0</sub> − 1), (2/3 + ε)(<i>y</i><sub>0</sub> − 1)]. Since <i>x</i><sub>0</sub> ≤ 1/3(<i>y</i><sub>0</sub> − <i>n</i><sub>0</sub>) ≤ 1/3(<i>y</i><sub>0</sub> − 1), the second interval is excluded, so <i>x</i><sub>0</sub> ≥ (1/3 − ε)(<i>y</i><sub>0</sub> − 1). Combining with <i>x</i><sub>0</sub> ≤ (1/3 + ε)<i>N</i> gives

```math
y_0 \le 1 + \frac{\frac{1}{3} + \varepsilon}{\frac{1}{3} - \varepsilon} N < (1 + 8\varepsilon) N. \qquad \square
```

### Lemma 5.2 (Location of <i>w</i><sub>0</sub> )
We have <i>w</i><sub>0</sub> &gt; <i>y</i><sub>0</sub> + 5/8 <i>N</i>.

*Proof.*
**Step 1: Exact difference interval in <i>B</i><sub>0</sub> − <i>A</i><sub>0</sub>.**
Set $`f_0 := \mathbf{1}_{A_0}`$, $`g_0 := \mathbf{1}_{B_0}`$, $`\widetilde{f}_0(n) := f_0(x_0 - n)`$, and $`D := h - \widetilde{f}_0 * g_0`$. Since <i>f</i><sub>0</sub> ∗ <i>g</i><sub>0</sub> = <i>h</i> + δ on [0, <i>N</i>], convolving <i>D</i> with <i>f</i><sub>0</sub> gives

```math
(f_0 * D)(n) = ((f_0 - \widetilde{f}_0) * h)(n) - (\widetilde{f}_0 * \delta)(n) = 0 \qquad (x_0 + n_0 \le n \le N).
```

By Lemma 3.2, <i>D</i>(<i>n</i>) ≥ 0 for all <i>n</i> ≥ <i>x</i><sub>0</sub> + <i>n</i><sub>0</sub>. For any integer $`u \in [x_0 + n_0,\ N - x_0]`$, we have <i>x</i><sub>0</sub> + <i>n</i><sub>0</sub> &lt; <i>u</i> + <i>x</i><sub>0</sub> ≤ <i>N</i>, so $`0 = (f_0 * D)(u + x_0) = \sum_{a \in A_0} D(u + x_0 - a)`$ is a sum of non-negative terms containing <i>D</i>(<i>u</i>) (at <i>a</i> = <i>x</i><sub>0</sub>). Thus <i>D</i>(<i>u</i>) = 0 for all $`u \in [x_0 + n_0,\ N - x_0]`$, which translates directly to

```math
[n_0,\ (\tfrac{1}{3} - 2\varepsilon)N] \subseteq [n_0,\ N - 2 x_0] \subseteq B_0 - A_0. \tag{5.1}
```

In particular, by Lemma 3.2, no pair $`(a, b) \in (A \cap (N, \infty)) \times (B \cap (N, \infty))`$ can satisfy <i>b</i> − <i>a</i> ∈ [<i>n</i><sub>0</sub>, (1/3 − 2ε)<i>N</i>]. Taking <i>a</i> = <i>y</i><sub>0</sub> yields

```math
B \cap \bigl[y_0 + n_0,\ y_0 + (\tfrac{1}{3} - 2\varepsilon)N\bigr] = \varnothing. \tag{5.2}
```

**Step 2: Ruling out $`w_0 \in (N,\ y_0 + n_0)`$.**
Suppose for contradiction that <i>N</i> &lt; <i>w</i><sub>0</sub> &lt; <i>y</i><sub>0</sub> + <i>n</i><sub>0</sub>. Put $`W := B \cap (N,\ y_0 + n_0)`$. Since <i>y</i><sub>0</sub> + <i>n</i><sub>0</sub> ≤ (1 + 9ε)<i>N</i>, by (5.2) we have $`B \cap (N,\ N + (\frac{1}{4} - 2\varepsilon)N] \subseteq W`$.

Next, consider $`A \cap (N,\ N + (\frac{1}{4} - 2\varepsilon)N]`$:
- <i>A</i> ∩ (<i>N</i>, <i>y</i><sub>0</sub>) = ∅;
- <i>A</i> ∩ [<i>y</i><sub>0</sub>, <i>w</i><sub>0</sub> + <i>n</i><sub>0</sub>) has at most 2n<sub>0</sub> elements (since <i>w</i><sub>0</sub> &lt; <i>y</i><sub>0</sub> + <i>n</i><sub>0</sub>).
- For every $`a \in A \cap [w_0 + n_0,\ N + (\frac{1}{4} - 2\varepsilon)N]`$, we have <i>n</i><sub>0</sub> ≤ <i>a</i> − <i>w</i><sub>0</sub> &lt; (1/4 − 2ε)<i>N</i> &lt; <i>N</i> − 1 − <i>z</i><sub>0</sub>, and Lemma 3.2 gives <i>a</i> − <i>w</i><sub>0</sub> ∉ <i>A</i><sub>0</sub> − <i>B</i><sub>0</sub>, so Lemma 3.4(2) bounds the number of such <i>a</i> by <i>C</i><sub>1</sub>(<i>K</i>).

Hence $`\#(A \cap (N,\ N + (\frac{1}{4} - 2\varepsilon)N]) \le 2n_0 + C_1(K)`$.

Also, by Corollary 4.4(1) at <i>t</i> = <i>y</i><sub>0</sub> + <i>n</i><sub>0</sub> ≥ <i>N</i>, <i>A</i>(<i>y</i><sub>0</sub> + <i>n</i><sub>0</sub>) <i>B</i>(<i>y</i><sub>0</sub> + <i>n</i><sub>0</sub>) ≤ 8/5(1 + 9ε)<i>N</i> &lt; 2N. Since <i>A</i>(<i>y</i><sub>0</sub> + <i>n</i><sub>0</sub>) ≥ <i>A</i>(<i>N</i>) and <i>A</i>(<i>N</i>)<i>B</i>(<i>N</i>) ≥ 1/2 <i>N</i>, we get <i>B</i>(<i>y</i><sub>0</sub> + <i>n</i><sub>0</sub>) ≤ 4 <i>B</i>(<i>N</i>), so |<i>W</i>| ≤ 3 <i>B</i>(<i>N</i>).

Now consider the interval $`I_{\mathrm{kill}} := [N + (\frac{1}{12} + 13\varepsilon)N,\ N + (\frac{1}{4} - 2\varepsilon)N]`$, whose integer cardinality is at least (1/6 − 15ε)<i>N</i> − 1 &gt; 0.15 <i>N</i>. Every $`n \in I_{\mathrm{kill}}`$ has a representation <i>n</i> = <i>a</i> + <i>b</i> falling into one of three cases (clearly <i>a</i>, <i>b</i> &gt; <i>N</i> is impossible since $`a + b \ge 2N + 2 > \max I_{\mathrm{kill}}`$):
1. <i>a</i> ≤ <i>N</i>, <i>b</i> ≤ <i>N</i>: at most <i>T</i>(<i>N</i>) ≤ <i>K</i> integers.
2. <i>a</i> &gt; <i>N</i>, <i>b</i> ≤ <i>N</i>: then $`a \in A \cap (N,\ N + (\frac{1}{4} - 2\varepsilon)N]`$, giving at most (2n<sub>0</sub> + <i>C</i><sub>1</sub>(<i>K</i>)) <i>B</i>(<i>N</i>) integers.
3. <i>b</i> &gt; <i>N</i>, <i>a</i> ≤ <i>N</i>: then $`b \in W \subseteq (N,\ (1 + 9\varepsilon)N]`$, so

```math
a = n - b \in \bigl[(\tfrac{1}{12} + 4\varepsilon)N,\ (\tfrac{1}{4} - 2\varepsilon)N\bigr].
```

Since supp(ν<sub>0</sub>) ⊆ [0, 1/12] ∪ [1/4, 1/3], we have $`\nu_0([0, \frac{1}{4} - 2\varepsilon]) = \nu_0([0, \frac{1}{12} + 3\varepsilon]) = \frac{1}{2}`$. By Corollary 4.4(3), the number of such <i>a</i> is at most $`A((\frac{1}{4} - 2\varepsilon)N) - A((\frac{1}{12} + 3\varepsilon)N) < 2\varepsilon A(N)`$. Thus case 3 covers at most |<i>W</i>| · 2ε <i>A</i>(<i>N</i>) ≤ 6ε <i>A</i>(<i>N</i>)<i>B</i>(<i>N</i>) &lt; 7ε <i>N</i> integers.

Since $`B(N) = \frac{A(N)B(N)}{A(N)} < \frac{2N}{A(N)}`$, Corollary 4.4(2) implies (2n<sub>0</sub> + <i>C</i><sub>1</sub>(<i>K</i>))<i>B</i>(<i>N</i>) + <i>K</i> &lt; ε <i>N</i>. Hence <i>A</i> + <i>B</i> covers fewer than $`8\varepsilon N = 0.008 N < 0.15 N < |I_{\mathrm{kill}}|`$ integers in $`I_{\mathrm{kill}}`$, a contradiction.

Thus <i>w</i><sub>0</sub> ≥ <i>y</i><sub>0</sub> + <i>n</i><sub>0</sub>, and by (5.2),

```math
w_0 > y_0 + (\tfrac{1}{3} - 2\varepsilon)N. \tag{5.3}
```

**Step 3: Pushing <i>w</i><sub>0</sub> past <i>y</i><sub>0</sub> + 5/8 <i>N</i>.**
Define $`f_1(n) := \mathbf{1}_A(y_0 + n)`$ and η<sub>1</sub>(<i>n</i>) := (<i>f</i><sub>0</sub> ∗ <i>g</i><sub>0</sub>)(<i>y</i><sub>0</sub> + <i>n</i>) for <i>n</i> ≥ 0. Note η<sub>1</sub>(<i>n</i>) ∈ {0, 1}, $`\sum_{n \ge 0} \eta_1(n) \le T(N) \le K`$, and $`\mathrm{supp}(\eta_1) \subseteq [0,\ x_0 + z_0 - y_0] \subseteq [0,\ 2\varepsilon N]`$. Since <i>B</i> ∩ (<i>N</i>, <i>w</i><sub>0</sub> − 1] = ∅, every representation of <i>y</i><sub>0</sub> + <i>n</i> for 0 ≤ <i>n</i> ≤ <i>w</i><sub>0</sub> − 1 − <i>y</i><sub>0</sub> uses <i>b</i> ∈ <i>B</i><sub>0</sub>, so

```math
(f_1 * g_0)(n) = 1 - \eta_1(n) = (h - \eta_1)(n) \qquad (0 \le n \le w_0 - 1 - y_0). \tag{5.4}
```

Convolving (5.4) with <i>f</i><sub>0</sub> and using <i>f</i><sub>0</sub> ∗ <i>g</i><sub>0</sub> = <i>h</i> + δ on [0, <i>N</i>] yields, for all $`0 \le t \le L_1 := \min(N,\ w_0 - 1 - y_0)`$,

```math
A(y_0 + t) - A(x_0) - A(t) = ((f_1 - f_0) * h)(t) = -(f_1 * \delta)(t) - (f_0 * \eta_1)(t) \in [-E - K,\ E]. \tag{5.5}
```

- *Substep 3a:* By (5.3), <i>L</i><sub>1</sub> &gt; (1/3 − 3ε)<i>N</i> &gt; (1/12 + ε)<i>N</i>. Since ν<sub>0</sub>([1/16, 1/12]) = 1/4 and ν<sub>0</sub>([0, 1/16 − ε]) = 1/4, Corollary 4.4(3) and (5.5) give

```math
A\bigl(y_0 + (\tfrac{1}{12} + \varepsilon)N\bigr) - A\bigl(y_0 + (\tfrac{1}{16} - \varepsilon)N\bigr) \ge (\tfrac{1}{4} - 2\varepsilon)A(N) - (2E + K) > 0,
```

so there exists $`a_1 \in A \cap [y_0 + (\frac{1}{16} - \varepsilon)N,\ y_0 + (\frac{1}{12} + \varepsilon)N]`$. If <i>w</i><sub>0</sub> ≤ <i>y</i><sub>0</sub> + 3/8N, then using (5.3) we get

```math
n_0 < (\tfrac{1}{4} - 3\varepsilon)N \le w_0 - a_1 \le (\tfrac{5}{16} + \varepsilon)N < (\tfrac{1}{3} - 2\varepsilon)N,
```

so <i>w</i><sub>0</sub> − <i>a</i><sub>1</sub> ∈ <i>B</i><sub>0</sub> − <i>A</i><sub>0</sub> by (5.1), contradicting Lemma 3.2. Hence <i>w</i><sub>0</sub> &gt; <i>y</i><sub>0</sub> + 3/8N.
- *Substep 3b:* Now <i>L</i><sub>1</sub> &gt; (3/8 − ε)<i>N</i> &gt; (1/3 + ε)<i>N</i>. Since ν<sub>0</sub>([5/16, 1/3]) = 1/4 and ν<sub>0</sub>([0, 5/16 − ε]) = 3/4, Corollary 4.4(3) and (5.5) give

```math
A\bigl(y_0 + (\tfrac{1}{3} + \varepsilon)N\bigr) - A\bigl(y_0 + (\tfrac{5}{16} - \varepsilon)N\bigr) \ge (\tfrac{1}{4} - 2\varepsilon)A(N) - (2E + K) > 0,
```

so there exists $`a_2 \in A \cap [y_0 + (\frac{5}{16} - \varepsilon)N,\ y_0 + (\frac{1}{3} + \varepsilon)N]`$. If <i>w</i><sub>0</sub> ≤ <i>y</i><sub>0</sub> + 5/8N, then using <i>w</i><sub>0</sub> &gt; <i>y</i><sub>0</sub> + 3/8N we get

```math
n_0 < (\tfrac{1}{24} - \varepsilon)N < w_0 - a_2 \le (\tfrac{5}{16} + \varepsilon)N < (\tfrac{1}{3} - 2\varepsilon)N,
```

again contradicting (5.1) and Lemma 3.2. Therefore <i>w</i><sub>0</sub> &gt; <i>y</i><sub>0</sub> + 5/8N. □

### Proposition 5.3 (Exact forward doubling step and quadratic recurrence)
Under the assumptions of this section, put $`U_1(z) := 1 - (1 - z)\sum_{n \ge 0} \eta_1(n) z^n \in \mathbb{Z}[z]`$, <i>u</i><sub>1</sub> := ord<sub><i>z</i>=0</sub>(<i>U</i><sub>1</sub>), and define

```math
N_1' := 2 y_0 + 2 u_1 - m_0 - 1 - \max(a_{\min}, b_{\min}).
```

Then:
1. $`N_1' \in [2N - 2n_0,\ (2 + 17\varepsilon)N]`$, and in particular <i>N</i><sub>1</sub>′ &gt; 3/2 <i>N</i>;
2. setting $`T_1 := x_0 + \lfloor 2\varepsilon N \rfloor + 1 + (E + 1)(n_0 + 1)`$ and $`A_1' := A \cap [y_0,\ y_0 + T_1]`$, we have $`P_{A_1'}(z) := \sum_{a \in A_1'} z^{a - y_0}`$ satisfying the exact polynomial identity

```math
P_{A_1'}(z)\, V(z) = P_{A_0}(z)\, U_1(z), \qquad W_N(z) = z^{y_0 - (N + 1)} U_1(z); \tag{5.6}
```

3. <i>A</i> ∩ [0, <i>N</i><sub>1</sub>′] = <i>A</i><sub>0</sub> ∪ <i>A</i><sub>1</sub>′ and <i>B</i> ∩ [0, <i>N</i><sub>1</sub>′] = <i>B</i><sub>0</sub> exactly;
4. the crossing-pair polynomials at <i>N</i> and <i>N</i><sub>1</sub>′ satisfy the exact identity

```math
z^{N_1' + 1}\, V(z)\, W_{N_1'}(z) = z^{2(N + 1)}\, W_N(z)^2, \tag{5.7}
```

with $`\mathrm{ord}_{z=0}(W_{N_1'}) = \max(a_{\min}, b_{\min})`$,

```math
\widetilde{V}(z)\, \widetilde{W}_{N_1'}(z) = \widetilde{W}_N(z)^2, \tag{5.8}
```

and <i>T</i>(<i>N</i><sub>1</sub>′) ≤ 2 <i>T</i>(<i>N</i>) + <i>E</i> + 2 <i>n</i><sub>0</sub>.

*Proof.*
**Step 1: Exact zero-interval of <i>f</i><sub>1</sub> and proof of (5.6).**
By Lemma 5.2, $`L_1 := \min(N,\ w_0 - 1 - y_0) > \frac{5}{8} N`$. Put $`T_0 := x_0 + \lfloor 2\varepsilon N \rfloor + 1 \le (\frac{1}{3} + 3\varepsilon)N + 1`$. For every <i>t</i> ∈ [<i>T</i><sub>0</sub>, <i>L</i><sub>1</sub>], we have <i>A</i>(<i>t</i>) = <i>A</i>(<i>x</i><sub>0</sub>) and (<i>f</i><sub>0</sub> ∗ η<sub>1</sub>)(<i>t</i>) = 0 (since supp(<i>f</i><sub>0</sub>) ⊆ [0, <i>x</i><sub>0</sub>] and supp(η<sub>1</sub>) ⊆ [0, 2ε <i>N</i>]). Thus (5.5) simplifies for all <i>t</i> ∈ [<i>T</i><sub>0</sub>, <i>L</i><sub>1</sub>] to

```math
S(t) := (f_1 * h)(t) = A(x_0) - (f_1 * \delta)(t) \in [A(x_0) - E,\ A(x_0) + E]. \tag{5.9}
```

Notice that <i>S</i>(<i>t</i>) is integer-valued and nondecreasing on [<i>T</i><sub>0</sub>, <i>L</i><sub>1</sub>]. Put <i>T</i><sub>1</sub> := <i>T</i><sub>0</sub> + (<i>E</i> + 1)(<i>n</i><sub>0</sub> + 1) and <i>T</i><sub>2</sub> := <i>L</i><sub>1</sub> − (<i>E</i> + 1)(<i>n</i><sub>0</sub> + 1); by Corollary 4.4, <i>T</i><sub>1</sub> + <i>n</i><sub>0</sub> &lt; 0.35 <i>N</i> &lt; 0.62 <i>N</i> &lt; <i>T</i><sub>2</sub>.
- If <i>S</i>(<i>t</i><sub><i>a</i></sub>) &lt; <i>A</i>(<i>x</i><sub>0</sub>) for some <i>t</i><sub><i>a</i></sub> ∈ [<i>T</i><sub>1</sub>, <i>L</i><sub>1</sub>], then since <i>S</i>(<i>T</i><sub>0</sub>) ≥ <i>A</i>(<i>x</i><sub>0</sub>) − <i>E</i>, <i>S</i> increases at most <i>E</i> times on [<i>T</i><sub>0</sub>, <i>t</i><sub><i>a</i></sub>], so [<i>T</i><sub>0</sub> + 1, <i>t</i><sub><i>a</i></sub>] contains at most <i>E</i> points with <i>f</i><sub>1</sub> = 1. Since <i>t</i><sub><i>a</i></sub> − <i>T</i><sub>0</sub> ≥ (<i>E</i> + 1)(<i>n</i><sub>0</sub> + 1), the pigeonhole principle yields a run of <i>n</i><sub>0</sub> consecutive zeros of <i>f</i><sub>1</sub> inside [<i>T</i><sub>0</sub> + 1, <i>t</i><sub><i>a</i></sub>]. At its right endpoint <i>u</i> ∈ [<i>T</i><sub>0</sub> + <i>n</i><sub>0</sub>, <i>t</i><sub><i>a</i></sub>], we have $`(f_1 * \delta)(u) = \sum_{j=0}^{n_0-1} \delta(j) f_1(u - j) = 0`$, so (5.9) gives <i>S</i>(<i>u</i>) = <i>A</i>(<i>x</i><sub>0</sub>), contradicting <i>S</i>(<i>u</i>) ≤ <i>S</i>(<i>t</i><sub><i>a</i></sub>) &lt; <i>A</i>(<i>x</i><sub>0</sub>).
- Symmetrically, if <i>S</i>(<i>t</i><sub><i>b</i></sub>) &gt; <i>A</i>(<i>x</i><sub>0</sub>) for some <i>t</i><sub><i>b</i></sub> ∈ [<i>T</i><sub>0</sub>, <i>T</i><sub>2</sub>], then since <i>S</i>(<i>L</i><sub>1</sub>) ≤ <i>A</i>(<i>x</i><sub>0</sub>) + <i>E</i>, [<i>t</i><sub><i>b</i></sub> + 1, <i>L</i><sub>1</sub>] contains at most <i>E</i> − 1 points with <i>f</i><sub>1</sub> = 1. Since <i>L</i><sub>1</sub> − <i>t</i><sub><i>b</i></sub> ≥ (<i>E</i> + 1)(<i>n</i><sub>0</sub> + 1), there is a run of <i>n</i><sub>0</sub> consecutive zeros of <i>f</i><sub>1</sub> inside [<i>t</i><sub><i>b</i></sub> + 1, <i>L</i><sub>1</sub>]; at its right endpoint <i>v</i>, (<i>f</i><sub>1</sub> ∗ δ)(<i>v</i>) = 0 gives <i>S</i>(<i>v</i>) = <i>A</i>(<i>x</i><sub>0</sub>), contradicting <i>S</i>(<i>v</i>) ≥ <i>S</i>(<i>t</i><sub><i>b</i></sub>) &gt; <i>A</i>(<i>x</i><sub>0</sub>).

Hence <i>S</i>(<i>t</i>) = <i>A</i>(<i>x</i><sub>0</sub>) for all <i>t</i> ∈ [<i>T</i><sub>1</sub>, <i>T</i><sub>2</sub>], and <i>f</i><sub>1</sub>(<i>t</i>) = 0 for all <i>t</i> ∈ [<i>T</i><sub>1</sub> + 1, <i>T</i><sub>2</sub>].

Let $`A_1' := A \cap [y_0,\ y_0 + T_1]`$ and $`f_1' := \mathbf{1}_{A_1' - y_0}`$. Then |<i>A</i><sub>1</sub>′| = <i>S</i>(<i>T</i><sub>1</sub>) = <i>A</i>(<i>x</i><sub>0</sub>), and <i>f</i><sub>1</sub>′ agrees with <i>f</i><sub>1</sub> on [0, <i>T</i><sub>2</sub>]. Consequently the identity ((<i>f</i><sub>1</sub>′ − <i>f</i><sub>0</sub>) ∗ <i>h</i>)(<i>t</i>) = -(<i>f</i><sub>1</sub>′ ∗ δ)(<i>t</i>) − (<i>f</i><sub>0</sub> ∗ η<sub>1</sub>)(<i>t</i>) holds for all 0 ≤ <i>t</i> ≤ <i>T</i><sub>2</sub> by (5.5), and holds trivially (0 = 0) for all <i>t</i> &gt; <i>T</i><sub>1</sub> + <i>n</i><sub>0</sub> (since <i>T</i><sub>1</sub> + <i>n</i><sub>0</sub> &lt; <i>T</i><sub>2</sub> and every term vanishes beyond <i>T</i><sub>1</sub> + <i>n</i><sub>0</sub>). Passing to generating functions in ℤ[<i>z</i>]:

```math
\frac{P_{A_1'}(z) - P_{A_0}(z)}{1 - z} = -P_{A_1'}(z)\Delta(z) - P_{A_0}(z) H_{\eta_1}(z) \iff P_{A_1'}(z)\, V(z) = P_{A_0}(z)\, U_1(z),
```

where $`H_{\eta_1}(z) := \sum_{n \ge 0} \eta_1(n) z^n`$.

Moreover, put <i>s</i> := <i>y</i><sub>0</sub> − (<i>N</i> + 1) ≥ 0. Since $`y_0 = \min(A \cap (N, \infty))`$ and <i>w</i><sub>0</sub> &gt; <i>y</i><sub>0</sub>, every integer <i>m</i> ∈ [<i>N</i> + 1, <i>y</i><sub>0</sub> − 1] is uniquely represented by <i>A</i><sub>0</sub> + <i>B</i><sub>0</sub>, so <i>e</i><sub><i>N</i></sub>(<i>j</i>) = 1 for 0 ≤ <i>j</i> &lt; <i>s</i> and <i>e</i><sub><i>N</i></sub>(<i>s</i> + <i>n</i>) = η<sub>1</sub>(<i>n</i>) for <i>n</i> ≥ 0. Thus $`E_N(z) = \frac{1 - z^s}{1 - z} + z^s H_{\eta_1}(z)`$ and <i>W</i><sub><i>N</i></sub>(<i>z</i>) = 1 − (1 − <i>z</i>)<i>E</i><sub><i>N</i></sub>(<i>z</i>) = <i>z</i><sup><i>s</i></sup> <i>U</i><sub>1</sub>(<i>z</i>), proving (5.6).

**Step 2: Exact determination of <i>A</i> ∩ [0, <i>N</i><sub>1</sub>′] and <i>B</i> ∩ [0, <i>N</i><sub>1</sub>′].**
Multiply $`P_{A_1'} V = P_{A_0} U_1`$ by $`(1 - z) P_{B_0}(z)`$ and substitute Lemma 3.3(2) together with $`z^{N+1} W_N(z) = z^{y_0} U_1(z)`$:

```math
V(z) \cdot (1 - z) P_{A_1'}(z) P_{B_0}(z) = U_1(z) \bigl(V(z) - z^{y_0} U_1(z)\bigr).
```

Rearranging gives

```math
V(z)\, F(z) = z^{y_0} U_1(z)^2, \qquad F(z) := U_1(z) - (1 - z) P_{A_1'}(z) P_{B_0}(z). \tag{5.10}
```

Write $`P_{A_1'}(z) P_{B_0}(z) = \sum_{n \ge 0} c_1(n) z^n`$, where $`c_1(n) := \#\{(a, b) \in A_1' \times B_0 : a + b = y_0 + n\}`$. Since <i>y</i><sub>0</sub> + <i>n</i> &gt; <i>N</i> ≥ <i>n</i><sub>0</sub>, we have

```math
e(n) := \eta_1(n) + c_1(n) = \#\{(a, b) \in (A_0 \cup A_1') \times B_0 : a + b = y_0 + n\} \le r(y_0 + n) = 1,
```

so <i>e</i>(<i>n</i>) ∈ {0, 1} for all <i>n</i> ≥ 0, and $`F(z) = 1 - (1 - z)\sum_{n \ge 0} e(n) z^n`$.

Taking ord<sub><i>z</i>=0</sub> of both sides of (5.10) gives ord<sub>0</sub>(<i>F</i>) = <i>y</i><sub>0</sub> + 2 <i>u</i><sub>1</sub> − <i>m</i><sub>0</sub> =: <i>M</i><sub>1</sub>. Since [<i>z</i><sup>0</sup>]<i>F</i> = 1 − <i>e</i>(0) and [<i>z</i><sup><i>n</i></sup>]<i>F</i> = <i>e</i>(<i>n</i> − 1) − <i>e</i>(<i>n</i>) for <i>n</i> ≥ 1, the vanishing of $`[z^0]F, \dots, [z^{M_1 - 1}]F`$ forces

```math
e(n) = 1 \qquad \text{for every } 0 \le n \le M_1 - 1.
```

That is, every integer in $`[y_0,\ N_1]`$ (where <i>N</i><sub>1</sub> := <i>y</i><sub>0</sub> + <i>M</i><sub>1</sub> − 1 = 2 <i>y</i><sub>0</sub> + 2 <i>u</i><sub>1</sub> − <i>m</i><sub>0</sub> − 1) is already uniquely represented by (<i>A</i><sub>0</sub> ∪ <i>A</i><sub>1</sub>′) + <i>B</i><sub>0</sub>.

Now examine any element outside (<i>A</i><sub>0</sub> ∪ <i>A</i><sub>1</sub>′) or <i>B</i><sub>0</sub>:
- Since $`A \cap (y_0 + T_1,\ y_0 + T_2] = \varnothing`$, any <i>a</i> ∈ <i>A</i> ∖ (<i>A</i><sub>0</sub> ∪ <i>A</i><sub>1</sub>′) satisfies <i>a</i> &gt; <i>y</i><sub>0</sub> + <i>T</i><sub>2</sub> &gt; <i>y</i><sub>0</sub>. Since <i>b</i><sub>min</sub> ∈ <i>B</i><sub>0</sub>, the sum <i>a</i> + <i>b</i><sub>min</sub> &gt; <i>y</i><sub>0</sub> cannot equal a sum already represented in (<i>A</i><sub>0</sub> ∪ <i>A</i><sub>1</sub>′) + <i>B</i><sub>0</sub> (as <i>r</i>(<i>m</i>) = 1 for <i>m</i> &gt; <i>N</i>), forcing <i>a</i> + <i>b</i><sub>min</sub> ≥ <i>N</i><sub>1</sub> + 1, i.e., <i>a</i> ≥ <i>N</i><sub>1</sub> + 1 − <i>b</i><sub>min</sub> &gt; <i>N</i><sub>1</sub>′.
- Any <i>b</i> ∈ <i>B</i> ∖ <i>B</i><sub>0</sub> satisfies <i>b</i> ≥ <i>w</i><sub>0</sub> &gt; <i>y</i><sub>0</sub>, so with <i>a</i><sub>min</sub> ∈ <i>A</i><sub>0</sub> ⊆ <i>A</i><sub>0</sub> ∪ <i>A</i><sub>1</sub>′, the sum <i>a</i><sub>min</sub> + <i>b</i> &gt; <i>y</i><sub>0</sub> cannot lie in [<i>y</i><sub>0</sub>, <i>N</i><sub>1</sub>], forcing <i>b</i> ≥ <i>N</i><sub>1</sub> + 1 − <i>a</i><sub>min</sub> &gt; <i>N</i><sub>1</sub>′.

Meanwhile, since $`0 \le u_1 \le H_{\eta_1}(1) \le K`$ and <i>N</i> &lt; <i>y</i><sub>0</sub> ≤ (1 + 8ε)<i>N</i>, we have

```math
N_1' = 2 y_0 + 2 u_1 - m_0 - 1 - \max(a_{\min}, b_{\min}) \in [2N - 2n_0,\ (2 + 17\varepsilon)N],
```

which exceeds max(<i>y</i><sub>0</sub> + <i>T</i><sub>1</sub>, <i>z</i><sub>0</sub>) &lt; 1.36 <i>N</i>. Thus <i>A</i> ∩ [0, <i>N</i><sub>1</sub>′] = <i>A</i><sub>0</sub> ∪ <i>A</i><sub>1</sub>′ and <i>B</i> ∩ [0, <i>N</i><sub>1</sub>′] = <i>B</i><sub>0</sub>, proving (1) and (3).

**Step 3: Proof of (5.7), (5.8), and the crossing bound.**
Using (3), Lemma 3.3(2), (5.6), and (5.10):

```math
\begin{aligned}
(1 - z) P_{A \cap [0, N_1']}(z) P_{B \cap [0, N_1']}(z)
&= (1 - z) P_{A_0}(z) P_{B_0}(z) + z^{y_0} (1 - z) P_{A_1'}(z) P_{B_0}(z) \\
&= \bigl(V(z) - z^{y_0} U_1(z)\bigr) + z^{y_0} \bigl(U_1(z) - F(z)\bigr) = V(z) - z^{y_0} F(z).
\end{aligned}
```

Comparing with Lemma 3.3(2) at level <i>N</i><sub>1</sub>′ yields $`z^{N_1' + 1} W_{N_1'}(z) = z^{y_0} F(z)`$. Multiplying by <i>V</i>(<i>z</i>) and substituting (5.10) together with $`z^{y_0} U_1(z) = z^{N + 1} W_N(z)`$ yields

```math
z^{N_1' + 1}\, V(z)\, W_{N_1'}(z) = z^{2 y_0} U_1(z)^2 = z^{2(N + 1)} W_N(z)^2,
```

which is (5.7). Furthermore,

```math
\mathrm{ord}_0(W_{N_1'}) = y_0 + \mathrm{ord}_0(F) - (N_1' + 1) = (N_1 + 1) - (N_1 + 1 - \max(a_{\min}, b_{\min})) = \max(a_{\min}, b_{\min}).
```

Stripping all factors of <i>z</i> from (5.7) gives $`\widetilde{V}(z)\widetilde{W}_{N_1'}(z) = \widetilde{W}_N(z)^2`$, which is (5.8). Finally, differentiating (5.7) at <i>z</i> = 1 (using $`V(1) = W_N(1) = W_{N_1'}(1) = 1`$, <i>V</i>′(1) = −<i>c</i>, <i>W</i><sub><i>N</i></sub>′(1) = <i>T</i>(<i>N</i>), $`W_{N_1'}'(1) = T(N_1')`$) gives

```math
(N_1' + 1) - c + T(N_1') = 2(N + 1) + 2 T(N),
```

whence

```math
T(N_1') = 2 T(N) + c + 2(N + 1) - (N_1' + 1) = 2 T(N) + c - 2 s - 2 u_1 + m_0 + \max(a_{\min}, b_{\min}) \le 2 T(N) + E + 2 n_0. \qquad \square
```

---

## 6. Polynomial Iteration Rigidity

We now prove that the quadratic recurrence (5.8) forces $`\widetilde{W}_N(z) = \widetilde{V}(z)`$ after a fixed finite number of doubling steps.

### Lemma 6.1 (Polynomial Iteration Rigidity Lemma)
Let <i>k</i><sub>0</sub> ≥ 2 be the smallest integer such that $`M := 2^{k_0 - 1} > \max(n_0,\ E + 1)`$. Suppose $`\widetilde{W}_0, \widetilde{W}_1, \dots, \widetilde{W}_{k_0 - 1} \in \mathbb{Z}[z]`$ satisfy:
1. $`\widetilde{W}_0(0) = 1`$,
2. every coefficient of $`\widetilde{W}_{k_0 - 1}(z)`$ lies in {−1, 0, +1}, and
3. $`\widetilde{V}(z) \widetilde{W}_{j+1}(z) = \widetilde{W}_j(z)^2`$ for every 0 ≤ <i>j</i> ≤ <i>k</i><sub>0</sub> − 2.

Then $`\widetilde{W}_j(z) = \widetilde{V}(z)`$ for every 0 ≤ <i>j</i> ≤ <i>k</i><sub>0</sub> − 1.

*Proof.* By induction on <i>j</i>, condition (3) gives

```math
\widetilde{V}(z)^{2^j - 1} \widetilde{W}_j(z) = \widetilde{W}_0(z)^{2^j} \qquad (0 \le j \le k_0 - 1).
```

Setting <i>j</i> = <i>k</i><sub>0</sub> − 1 gives $`\widetilde{V}(z)^{M - 1} \widetilde{W}_{k_0 - 1}(z) = \widetilde{W}_0(z)^M`$ in ℤ[<i>z</i>]. Since $`\widetilde{V}(0) = 1`$, $`\widetilde{V}`$ is primitive in the UFD ℤ[<i>z</i>]. For any irreducible polynomial <i>p</i>(<i>z</i>) ∈ ℤ[<i>z</i>] dividing $`\widetilde{V}(z)`$, let $`a := v_p(\widetilde{V}) \ge 1`$ and $`b := v_p(\widetilde{W}_0) \ge 0`$. From $`\widetilde{V}^{M-1} \mid \widetilde{W}_0^M`$ we have (<i>M</i> − 1)<i>a</i> ≤ <i>M</i> <i>b</i>, i.e.

```math
a - b \le \frac{a}{M} \le \frac{\deg \widetilde{V}}{M} \le \frac{n_0}{M} < 1.
```

Since <i>a</i> − <i>b</i> ∈ ℤ, we obtain <i>a</i> ≤ <i>b</i>. Hence $`\widetilde{V}(z) \mid \widetilde{W}_0(z)`$ in ℤ[<i>z</i>].

Write $`\widetilde{W}_0(z) = \widetilde{V}(z) R(z)`$ with <i>R</i>(<i>z</i>) ∈ ℤ[<i>z</i>]. Since $`\widetilde{W}_0(0) = \widetilde{V}(0) = 1`$, we have <i>R</i>(0) = 1. Cancelling $`\widetilde{V}^{M-1} \neq 0`$ from $`\widetilde{V}^{M-1}\widetilde{W}_{k_0 - 1} = \widetilde{V}^M R^M`$ yields

```math
\widetilde{W}_{k_0 - 1}(z) = \widetilde{V}(z)\, R(z)^M.
```

Suppose for contradiction that $`R(z) \not\equiv 1`$, and let <i>c</i><sub><i>d</i></sub> <i>z</i><sup><i>d</i></sup> (<i>d</i> ≥ 1, <i>c</i><sub><i>d</i></sub> ∈ ℤ ∖ {0}) be the lowest-degree nonconstant term of <i>R</i>(<i>z</i>), so <i>R</i>(<i>z</i>) = 1 + <i>c</i><sub><i>d</i></sub> <i>z</i><sup><i>d</i></sup> + <i>O</i>(<i>z</i><sup><i>d</i>+1</sup>). Then <i>R</i>(<i>z</i>)<sup><i>M</i></sup> = 1 + <i>M</i> <i>c</i><sub><i>d</i></sub> <i>z</i><sup><i>d</i></sup> + <i>O</i>(<i>z</i><sup><i>d</i>+1</sup>), and therefore

```math
[z^d]\widetilde{W}_{k_0 - 1}(z) = [z^d]\widetilde{V}(z) + M c_d.
```

By Lemma 3.1(5), $`|[z^d]\widetilde{V}(z)| \le E`$. Since |<i>c</i><sub><i>d</i></sub>| ≥ 1 and <i>M</i> &gt; <i>E</i> + 1,

```math
\bigl|[z^d]\widetilde{W}_{k_0 - 1}(z)\bigr| \ge M |c_d| - |[z^d]\widetilde{V}(z)| \ge M - E \ge 2,
```

contradicting condition (2). Hence <i>R</i>(<i>z</i>) ≡ 1, i.e., $`\widetilde{W}_0(z) = \widetilde{V}(z)`$, and condition (3) inductively gives $`\widetilde{W}_j(z) = \widetilde{V}(z)`$ for all 0 ≤ <i>j</i> ≤ <i>k</i><sub>0</sub> − 1. □

---

## 7. Proof of the Main Theorem and Corollaries

*Proof of the Main Theorem.*
Assume λ &lt; 8/5. Fix ε := 10<sup>−3</sup> and the constants (depending solely on <i>A</i>, <i>B</i>):

```math
K_0 := \max(T_{\min},\ n_0,\ E), \qquad k_0 \text{ as in Lemma 6.1}, \qquad K_{\max} := 2^{k_0}(K_0 + E + 2 n_0).
```

Apply Corollary 4.4 with (<i>K</i><sub>max</sub>, ε) to obtain the threshold $`N_* := N_*(K_{\max}, \varepsilon)`$. Since <i>T</i><sub>min</sub> ≤ <i>K</i><sub>0</sub>, there exists an integer $`N_0 \ge N_*`$ with <i>T</i>(<i>N</i><sub>0</sub>) ≤ <i>K</i><sub>0</sub>.

**Step 1: Rigidity at any $`N \ge N_*`$ with <i>T</i>(<i>N</i>) ≤ <i>K</i><sub>0</sub>.**
Start at any integer $`N^{(0)} \ge N_*`$ with <i>T</i>(<i>N</i><sup>(0)</sup>) ≤ <i>K</i><sub>0</sub>. For <i>j</i> = 0, 1, …, <i>k</i><sub>0</sub> − 2, we inductively apply Proposition 5.3 (swapping <i>A</i> and <i>B</i> whenever Corollary 4.4 assigns ν<sub>0</sub> to <i>B</i>; note that <i>V</i>(<i>z</i>), <i>m</i><sub>0</sub>, max(<i>a</i><sub>min</sub>, <i>b</i><sub>min</sub>), <i>n</i><sub>0</sub>, <i>E</i>, <i>c</i> are all symmetric in <i>A</i> and <i>B</i>) to construct $`N^{(0)} < N^{(1)} < \dots < N^{(k_0 - 1)}`$ satisfying

```math
N^{(j)} \ge N_*, \qquad T(N^{(j)}) \le 2^j(K_0 + E + 2n_0) - (E + 2n_0) < K_{\max}, \qquad \widetilde{V}(z)\widetilde{W}_{N^{(j+1)}}(z) = \widetilde{W}_{N^{(j)}}(z)^2.
```

By Lemma 3.3(4), $`\widetilde{W}_{N^{(0)}}(0) = 1`$ and every coefficient of $`\widetilde{W}_{N^{(k_0 - 1)}}(z)`$ lies in {−1, 0, +1}. Lemma 6.1 therefore forces

```math
\widetilde{W}_{N^{(0)}}(z) = \widetilde{W}_{N^{(1)}}(z) = \widetilde{V}(z). \tag{7.1}
```

**Step 2: Exact translation and doubling induction.**
Starting at $`N_0 \ge N_*`$ with <i>T</i>(<i>N</i><sub>0</sub>) ≤ <i>K</i><sub>0</sub>, assume without loss of generality (swapping <i>A</i> and <i>B</i> once and for all if needed) that Corollary 4.4 assigns ν<sub>0</sub> to <i>A</i> and μ<sub>0</sub> to <i>B</i> at level <i>N</i><sub>0</sub>. Put <i>A</i><sub>0</sub> := <i>A</i> ∩ [0, <i>N</i><sub>0</sub>], <i>B</i><sub>0</sub> := <i>B</i> ∩ [0, <i>N</i><sub>0</sub>], $`y_0 := \min(A \cap (N_0, \infty))`$, and <i>D</i><sub>0</sub> := <i>y</i><sub>0</sub> − <i>a</i><sub>min</sub>. Note that

```math
\max A_0 \le (\tfrac{1}{3} + \varepsilon)N_0 < N_0 - n_0 < D_0, \qquad \max B_0 \le (\tfrac{2}{3} + \varepsilon)N_0 < N_0 - n_0 < D_0,
```

so <i>A</i><sub>0</sub>, <i>B</i><sub>0</sub> ⊆ {0, 1, …, <i>D</i><sub>0</sub> − 1}.

We construct an infinite sequence <i>N</i><sub>0</sub> &lt; <i>N</i><sub>1</sub> &lt; <i>N</i><sub>2</sub> &lt; ⋯ by repeatedly applying Proposition 5.3, and prove by induction on <i>j</i> ≥ 0 that:
- $`N_j \ge N_*`$, <i>T</i>(<i>N</i><sub><i>j</i></sub>) ≤ <i>K</i><sub>0</sub>, and $`\widetilde{W}_{N_j}(z) = \widetilde{V}(z)`$;
- for <i>j</i> ≥ 1, <i>N</i><sub><i>j</i></sub> = 2<sup><i>j</i></sup> <i>D</i><sub>0</sub> + min(<i>a</i><sub>min</sub>, <i>b</i><sub>min</sub>) − 1 and $`W_{N_j}(z) = z^{\max(a_{\min}, b_{\min})} \widetilde{V}(z)`$;
- if <i>j</i> = 2i is even, then <i>A</i> ∩ [0, <i>N</i><sub><i>j</i></sub>] = <i>A</i><sub>0</sub> + <i>D</i><sub>0</sub> · <i>A</i><sub>bin</sub><sup>(<i>i</i>)</sup> and <i>B</i> ∩ [0, <i>N</i><sub><i>j</i></sub>] = <i>B</i><sub>0</sub> + <i>D</i><sub>0</sub> · (2 <i>A</i><sub>bin</sub><sup>(<i>i</i>)</sup>), with ν<sub>0</sub> assigned to <i>A</i> and μ<sub>0</sub> to <i>B</i> at <i>N</i><sub><i>j</i></sub>, and $`\min(A \cap (N_j, \infty)) = 2^j D_0 + a_{\min}`$;
- if <i>j</i> = 2i + 1 is odd, then <i>A</i> ∩ [0, <i>N</i><sub><i>j</i></sub>] = <i>A</i><sub>0</sub> + <i>D</i><sub>0</sub> · <i>A</i><sub>bin</sub><sup>(<i>i</i>+1)</sup> and <i>B</i> ∩ [0, <i>N</i><sub><i>j</i></sub>] = <i>B</i><sub>0</sub> + <i>D</i><sub>0</sub> · (2 <i>A</i><sub>bin</sub><sup>(<i>i</i>)</sup>), with ν<sub>0</sub> assigned to <i>B</i> and μ<sub>0</sub> to <i>A</i> at <i>N</i><sub><i>j</i></sub>, and $`\min(B \cap (N_j, \infty)) = 2^j D_0 + b_{\min}`$;

where $`A_{\mathrm{bin}}^{(i)} := \{\sum_{r=0}^{i-1} \varepsilon_r 4^r : \varepsilon_r \in \{0, 1\}\}`$ (<i>A</i><sub>bin</sub><sup>(0)</sup> := {0}).

*Base case <i>j</i> = 0:* Already established ($`N_0 \ge N_*`$, <i>T</i>(<i>N</i><sub>0</sub>) ≤ <i>K</i><sub>0</sub>, $`\widetilde{W}_{N_0} = \widetilde{V}`$ by Step 1, <i>y</i><sub>0</sub> = <i>D</i><sub>0</sub> + <i>a</i><sub>min</sub>).

*Inductive step <i>j</i> → <i>j</i> + 1:* Suppose the statement holds at <i>j</i>. For clarity, treat <i>j</i> = 2i even (the odd case <i>j</i> = 2i + 1 is identical with <i>A</i> and <i>B</i> interchanged). Put <i>A</i><sup>(<i>j</i>)</sup> := <i>A</i> ∩ [0, <i>N</i><sub><i>j</i></sub>], <i>B</i><sup>(<i>j</i>)</sup> := <i>B</i> ∩ [0, <i>N</i><sub><i>j</i></sub>], $`y_j := \min(A \cap (N_j, \infty)) = 2^j D_0 + a_{\min}`$, and <i>D</i><sub><i>j</i></sub> := <i>y</i><sub><i>j</i></sub> − <i>a</i><sub>min</sub> = 2<sup><i>j</i></sup> <i>D</i><sub>0</sub>.

Apply Proposition 5.3 at <i>N</i><sub><i>j</i></sub> to obtain <i>N</i><sub><i>j</i>+1</sub> and <i>A</i><sub><i>j</i></sub>′ := <i>A</i> ∩ [<i>y</i><sub><i>j</i></sub>, <i>y</i><sub><i>j</i></sub> + <i>T</i><sub>1</sub><sup>(<i>j</i>)</sup>]. By (5.6) and $`\widetilde{W}_{N_j} = \widetilde{V}`$, we have $`\widetilde{U}_1^{(j)}(z) = \widetilde{V}(z)`$, so $`U_1^{(j)}(z) = z^{u_1^{(j)}} \widetilde{V}(z)`$. Substituting $`V(z) = z^{m_0}\widetilde{V}(z)`$ and $`U_1^{(j)}(z) = z^{u_1^{(j)}}\widetilde{V}(z)`$ into $`P_{A_j'}(z)V(z) = P_{A^{(j)}}(z)U_1^{(j)}(z)`$ and cancelling $`\widetilde{V}(z) \neq 0`$ yields

```math
z^{m_0} P_{A_j'}(z) = z^{u_1^{(j)}} P_{A^{(j)}}(z).
```

Since min <i>A</i><sub><i>j</i></sub>′ = <i>y</i><sub><i>j</i></sub> and min <i>A</i><sup>(<i>j</i>)</sup> = <i>a</i><sub>min</sub>, we have $`\mathrm{ord}_0(P_{A_j'}) = 0`$ and $`\mathrm{ord}_0(P_{A^{(j)}}) = a_{\min}`$. Comparing orders at <i>z</i> = 0 gives

```math
u_1^{(j)} = m_0 - a_{\min} = b_{\min},
```

and hence $`z^{y_j} P_{A_j'}(z) = z^{y_j - a_{\min}} P_{A^{(j)}}(z) = z^{D_j} P_{A^{(j)}}(z)`$, i.e. <i>A</i><sub><i>j</i></sub>′ = <i>D</i><sub><i>j</i></sub> + <i>A</i><sup>(<i>j</i>)</sup>.

By Proposition 5.3(3), <i>B</i> ∩ [0, <i>N</i><sub><i>j</i>+1</sub>] = <i>B</i><sup>(<i>j</i>)</sup> and

```math
A \cap [0, N_{j+1}] = A^{(j)} \cup (D_j + A^{(j)}) = A_0 + D_0 \cdot (A_{\mathrm{bin}}^{(i)} \cup (4^i + A_{\mathrm{bin}}^{(i)})) = A_0 + D_0 \cdot A_{\mathrm{bin}}^{(i+1)}.
```

Moreover, substituting <i>y</i><sub><i>j</i></sub> = <i>D</i><sub><i>j</i></sub> + <i>a</i><sub>min</sub> and <i>u</i><sub>1</sub><sup>(<i>j</i>)</sup> = <i>b</i><sub>min</sub> into the formula for <i>N</i><sub><i>j</i>+1</sub> gives

```math
N_{j+1} = 2(D_j + a_{\min}) + 2 b_{\min} - (a_{\min} + b_{\min}) - 1 - \max(a_{\min}, b_{\min}) = 2 D_j + \min(a_{\min}, b_{\min}) - 1 = 2^{j+1} D_0 + \min(a_{\min}, b_{\min}) - 1.
```

By Proposition 5.3(4) and the induction hypothesis $`\widetilde{W}_{N_j} = \widetilde{V}`$, we have $`\widetilde{W}_{N_{j+1}}(z) = \widetilde{V}(z)`$ and $`\mathrm{ord}_0(W_{N_{j+1}}) = \max(a_{\min}, b_{\min})`$, so

```math
W_{N_{j+1}}(z) = z^{\max(a_{\min}, b_{\min})} \widetilde{V}(z). \tag{7.2}
```

Differentiating (7.2) at <i>z</i> = 1 using Lemma 3.1(5) yields

```math
T(N_{j+1}) = W_{N_{j+1}}'(1) = \max(a_{\min}, b_{\min}) + (-c - a_{\min} - b_{\min}) = -c - \min(a_{\min}, b_{\min}) \le E \le K_0.
```

Next, check the orientation at <i>N</i><sub><i>j</i>+1</sub>: $`\max(B \cap [0, N_{j+1}]) = \max B^{(j)} \le (\frac{2}{3} + \varepsilon)N_j < 0.45 N_{j+1}`$ while $`\max(A \cap [0, N_{j+1}]) = D_j + \max A^{(j)} \ge (1 - \varepsilon)N_j + (\frac{1}{3} - \varepsilon)N_j > 0.6 N_{j+1}`$, so Corollary 4.4(3) assigns ν<sub>0</sub> to <i>B</i> and μ<sub>0</sub> to <i>A</i> at <i>N</i><sub><i>j</i>+1</sub>.

Finally, let $`w_j := \min(B \cap (N_{j+1}, \infty))`$. Applying Proposition 5.3 at <i>N</i><sub><i>j</i>+1</sub> (with <i>B</i> playing the role of <i>A</i>) gives $`W_{N_{j+1}}(z) = z^{w_j - (N_{j+1} + 1)} U_1^{(j+1)}(z)`$ and (by the exact same order comparison as above, with <i>a</i><sub>min</sub>, <i>b</i><sub>min</sub> swapped) ord<sub>0</sub>(<i>U</i><sub>1</sub><sup>(<i>j</i>+1)</sup>) = <i>a</i><sub>min</sub>. Comparing $`\mathrm{ord}_0(W_{N_{j+1}})`$ with (7.2) gives

```math
\max(a_{\min}, b_{\min}) = w_j - (N_{j+1} + 1) + a_{\min},
```

whence

```math
w_j = (2^{j+1} D_0 + \min(a_{\min}, b_{\min})) + \max(a_{\min}, b_{\min}) - a_{\min} = 2^{j+1} D_0 + b_{\min}.
```

This completes the induction.

**Step 3: Bijection modulo <i>D</i><sub>0</sub> and global identity.**
Taking the union over all <i>j</i> ≥ 0 (as $`N_j \to \infty`$) immediately gives

```math
A = A_0 + D_0 \cdot A_{\mathrm{bin}}, \qquad B = B_0 + D_0 \cdot (2 A_{\mathrm{bin}}).
```

Moreover, at <i>j</i> = 0, we found $`W_{N_0}(z) = z^{y_0 - (N_0 + 1)} U_1^{(0)}(z) = z^{y_0 - N_0 - 1 + b_{\min}} \widetilde{V}(z)`$. Substituting into Lemma 3.3(2) gives

```math
(1 - z) P_{A_0}(z) P_{B_0}(z) = V(z) - z^{N_0 + 1} W_{N_0}(z) = z^{m_0}\widetilde{V}(z) - z^{y_0 + b_{\min}}\widetilde{V}(z) = V(z)(1 - z^{D_0}),
```

since <i>y</i><sub>0</sub> + <i>b</i><sub>min</sub> − <i>m</i><sub>0</sub> = <i>y</i><sub>0</sub> − <i>a</i><sub>min</sub> = <i>D</i><sub>0</sub>. Dividing by (1 − <i>z</i>) in ℤ[<i>z</i>] gives

```math
P_{A_0}(z) P_{B_0}(z) = V(z)\frac{1 - z^{D_0}}{1 - z} = \frac{1 - z^{D_0}}{1 - z} + (1 - z^{D_0})\Delta(z) \equiv 1 + z + \dots + z^{D_0 - 1} \pmod{z^{D_0} - 1}. \tag{7.3}
```

Reading off coefficients modulo $`z^{D_0} - 1`$, every residue class <i>r</i> ∈ ℤ/<i>D</i><sub>0</sub>ℤ has $`\#\{(a, b) \in A_0 \times B_0 : a + b \equiv r \pmod{D_0}\} = 1`$. Hence $`(a, b) \mapsto a + b \bmod D_0`$ is a bijection <i>A</i><sub>0</sub> × <i>B</i><sub>0</sub> → ℤ/<i>D</i><sub>0</sub>ℤ (and in particular |<i>A</i><sub>0</sub>||<i>B</i><sub>0</sub>| = <i>D</i><sub>0</sub>). This completes the proof of the Main Theorem. □

---

*Proof of Corollary 1 (Conjecture 1.3).*
By Theorem 1.1 of `arXiv:2610.35027v1` (or Proposition 4.3 + Lemma 4.2 with <i>M</i><sub>2</sub> = 2, which already gives λ ≥ 3/2), we have λ ∈ [3/2, 2]. Suppose λ &lt; 8/5. By the Main Theorem, <i>A</i> = <i>A</i><sub>0</sub> + <i>D</i><sub>0</sub> <i>A</i><sub>bin</sub> and <i>B</i> = <i>B</i><sub>0</sub> + <i>D</i><sub>0</sub> (2 <i>A</i><sub>bin</sub>) with <i>A</i><sub>0</sub>, <i>B</i><sub>0</sub> ⊆ {0, 1, …, <i>D</i><sub>0</sub> − 1} and |<i>A</i><sub>0</sub>||<i>B</i><sub>0</sub>| = <i>D</i><sub>0</sub>.

For any real <i>x</i> &gt; 0, every <i>a</i> = <i>a</i><sub>0</sub> + <i>D</i><sub>0</sub> <i>a</i>′ ∈ <i>A</i> ∩ [0, <i>x</i>] satisfies <i>a</i>′ ≤ <i>x</i> / <i>D</i><sub>0</sub>, so $`A(x) \le |A_0|\, A_{\mathrm{bin}}(x / D_0)`$; likewise $`B(x) \le |B_0|\, B_{\mathrm{bin}}(x / D_0)`$ where <i>B</i><sub>bin</sub> := 2 <i>A</i><sub>bin</sub>. Multiplying gives

```math
\frac{A(x) B(x)}{x} \le \frac{|A_0||B_0|\, A_{\mathrm{bin}}(x / D_0) B_{\mathrm{bin}}(x / D_0)}{x} = \frac{A_{\mathrm{bin}}(x / D_0) B_{\mathrm{bin}}(x / D_0)}{x / D_0}.
```

We recall the elementary verification that $`\limsup_{y\to\infty} \frac{A_{\mathrm{bin}}(y)B_{\mathrm{bin}}(y)}{y} \le \frac{3}{2}`$ (Zhang, Section 6): list <i>A</i><sub>bin</sub> in increasing order as $`a_v := \sum_i \varepsilon_i 4^i`$ for $`v = \sum_i \varepsilon_i 2^i \ge 0`$; then

```math
v^2 = \sum_i \varepsilon_i 4^i + 2\sum_i \varepsilon_i 2^i \sum_{j < i} \varepsilon_j 2^j \le \sum_i \varepsilon_i 4^i + 2\sum_i \varepsilon_i 2^i (2^i - 1) \le 3 a_v.
```

On [4<sup><i>k</i></sup>, 4<sup><i>k</i>+1</sup>) with <i>H</i> := 2<sup><i>k</i></sup>, elements of <i>A</i><sub>bin</sub> are 4<sup><i>k</i></sup> + <i>a</i><sub><i>v</i></sub> (0 ≤ <i>v</i> &lt; <i>H</i>) and elements of <i>B</i><sub>bin</sub> are 2(4<sup><i>k</i></sup> + <i>a</i><sub><i>v</i></sub>) (0 ≤ <i>v</i> &lt; <i>H</i>), with the <i>A</i><sub>bin</sub>-block ending at $`4^k + \frac{4^k-1}{3} < 2 \cdot 4^k`$. At either <i>y</i> = 4<sup><i>k</i></sup> + <i>a</i><sub><i>v</i></sub> or <i>y</i> = 2(4<sup><i>k</i></sup> + <i>a</i><sub><i>v</i></sub>),

```math
\frac{A_{\mathrm{bin}}(y)B_{\mathrm{bin}}(y)}{y} = \frac{H(H + v + 1)}{H^2 + a_v} \le \frac{H(H + v)}{H^2 + v^2 / 3} + \frac{1}{H} \le \frac{3}{2} + \frac{1}{H},
```

since $`\frac{3}{2}(H^2 + \frac{v^2}{3}) - H(H + v) = \frac{1}{2}(H - v)^2 \ge 0`$. Between consecutive elements of <i>A</i><sub>bin</sub> ∪ <i>B</i><sub>bin</sub> the numerator is constant while <i>y</i> increases, so $`\limsup_{y\to\infty} \frac{A_{\mathrm{bin}}(y)B_{\mathrm{bin}}(y)}{y} \le \frac{3}{2}`$. Thus λ ≤ 3/2, and hence λ = 3/2. □

---

*Proof of Corollary 2.*
Under λ &lt; 8/5, write <i>A</i> = <i>A</i><sub>0</sub> + <i>D</i><sub>0</sub> <i>A</i><sub>bin</sub> and <i>B</i> = <i>B</i><sub>0</sub> + <i>D</i><sub>0</sub>(2 <i>A</i><sub>bin</sub>) as in the Main Theorem. For any <i>n</i> ∈ ℤ<sub>≥ 0</sub>, if <i>n</i> = (<i>a</i><sub>0</sub> + <i>D</i><sub>0</sub> <i>a</i>′) + (<i>b</i><sub>0</sub> + <i>D</i><sub>0</sub> <i>b</i>′) with <i>a</i><sub>0</sub> ∈ <i>A</i><sub>0</sub>, <i>b</i><sub>0</sub> ∈ <i>B</i><sub>0</sub>, <i>a</i>′ ∈ <i>A</i><sub>bin</sub>, <i>b</i>′ ∈ 2 <i>A</i><sub>bin</sub>, then $`a_0 + b_0 \equiv n \pmod{D_0}`$ uniquely determines (<i>a</i><sub>0</sub>, <i>b</i><sub>0</sub>) ∈ <i>A</i><sub>0</sub> × <i>B</i><sub>0</sub> by the bijection property, and then $`a' + b' = \frac{n - (a_0 + b_0)}{D_0} \in \mathbb{Z}_{\ge 0}`$ uniquely determines (<i>a</i>′, <i>b</i>′) ∈ <i>A</i><sub>bin</sub> × (2 <i>A</i><sub>bin</sub>). Hence <i>r</i><sub><i>A</i>, <i>B</i></sub>(<i>n</i>) ≤ 1 for every <i>n</i> ∈ ℤ<sub>≥ 0</sub>. □
