# Lean 4 Formalization & Review Guide

This document summarizes the complete, end-to-end **Lean 4** formalization of the proof of [Conjecture 1.3](https://arxiv.org/html/2610.35027v1#S1.Thmtheorem3) of van Doorn, Liu, and Tang (*On almost perfect additive complements*, [arXiv:2610.35027v1](https://arxiv.org/abs/2610.35027)) and the sharper structural classification below $`8/5`$.

## Verification summary

- **Toolchain:** `leanprover/lean4:v4.35.0` (pinned in [`lean/lean-toolchain`](lean/lean-toolchain))
- **Mathlib:** `v4.35.0`, commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (pinned in [`lean/lake-manifest.json`](lean/lake-manifest.json))
- **Project size:** 13 Lean modules (12 proof modules + umbrella [`lean/AlmostPerfect.lean`](lean/AlmostPerfect.lean)), 13,750 lines total
- **Owned declaration inventory:** 1,909 declarations across all 13 project modules (1,790 theorems, 110 definitions, 3 inductives/structures, 3 constructors, 3 recursors; 761 private declarations)
- **Strict compilation:** every module compiles freshly in topological import order with `lake env lean -j1 -DwarningAsError=true` with **0 errors and 0 warnings**
- **Sorry & custom-axiom count:** **0 `sorry`s**, **0 `admit`s**, **0 custom axioms**, **0 `native_decide` / `Lean.ofReduceBool` uses**
- **Transitive axiom footprint across all 1,909 owned declarations:** strictly `{Classical.choice, Quot.sound, propext}`
- **Stock kernel replay:** `lake env leanchecker -v AlmostPerfect` exits with status `0` across all 13 compiled modules
- **External theorem coverage:** the single-step Gabardo–Lai convolution factorization theorem (Gabardo–Lai, *J. Fourier Anal. Appl.* **20** (2014), Thm. 2.2) is **not** assumed as an axiom; it is formally proved from scratch over Mathlib in `AlmostPerfect.GabardoLaiBase` and `AlmostPerfect.GabardoLai`.

## What a reviewer needs to trust (specification audit)

Because Lean's kernel checks every proof step and `scripts/verify-lean.py` verifies zero custom axioms across all 1,909 declarations plus full `leanchecker` kernel replay, verifying that the formalized theorems match the mathematical statements in `arXiv:2610.35027v1` reduces to inspecting the **71-line definitions file** [`lean/AlmostPerfect/Basic.lean`](lean/AlmostPerfect/Basic.lean) and the three endpoint theorem signatures in [`lean/AlmostPerfect/Main.lean`](lean/AlmostPerfect/Main.lean):

### Core definitions ([`lean/AlmostPerfect/Basic.lean`](lean/AlmostPerfect/Basic.lean))

```lean
def countNat (S : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred (· ∈ S)
  ((Finset.range (n + 1)).filter (· ∈ S)).card

def countReal (S : Set ℕ) (x : ℝ) : ℕ :=
  if x < 0 then 0 else countNat S ⌊x⌋₊

def repCount (A B : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred (· ∈ A)
  letI := Classical.decPred (· ∈ B)
  ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ B)).card

def IsAlmostPerfect (A B : Set ℕ) : Prop :=
  A.Infinite ∧
  B.Infinite ∧
  (∀ᶠ n : ℕ in atTop, 1 ≤ repCount A B n) ∧
  ¬ Tendsto (fun x : ℝ => (countReal A x : ℝ) * (countReal B x : ℝ) - x) atTop atTop

def ABin : Set ℕ :=
  {m : ℕ | ∀ i : ℕ, (m / 4 ^ i) % 4 ≤ 1}

def ratioEReal (A B : Set ℕ) (x : ℝ) : EReal :=
  (((countReal A x : ℝ) * (countReal B x : ℝ)) / x : ℝ)

def IsModularLift (A B : Set ℕ) : Prop :=
  ∃ (D₀ : ℕ) (A₀ B₀ : Finset ℕ),
    1 ≤ D₀ ∧
    (∀ a ∈ A₀, a < D₀) ∧
    (∀ b ∈ B₀, b < D₀) ∧
    (∀ r < D₀, ∃! p : ℕ × ℕ, p.1 ∈ A₀ ∧ p.2 ∈ B₀ ∧ (p.1 + p.2) % D₀ = r) ∧
    ((A = {n : ℕ | ∃ a₀ ∈ A₀, ∃ m ∈ ABin, n = a₀ + D₀ * m} ∧
      B = {n : ℕ | ∃ b₀ ∈ B₀, ∃ m ∈ ABin, n = b₀ + D₀ * (2 * m)}) ∨
     (B = {n : ℕ | ∃ a₀ ∈ A₀, ∃ m ∈ ABin, n = a₀ + D₀ * m} ∧
      A = {n : ℕ | ∃ b₀ ∈ B₀, ∃ m ∈ ABin, n = b₀ + D₀ * (2 * m)}))
```

Note on `EReal`: using `Filter.limsup (ratioEReal A B) Filter.atTop` in `EReal` (rather than `ℝ`, where `Filter.limsup` defaults to `0` if unbounded) eliminates any possibility of truncation artifacts; `almostPerfect_limsup_le_two` explicitly proves the `EReal` limsup is bounded above by `(2 : EReal)`.

### Endpoint theorem signatures ([`lean/AlmostPerfect/Main.lean`](lean/AlmostPerfect/Main.lean))

```lean
/-- Main Theorem (Exact Classification below 8/5) -/
theorem main_classification {A B : Set ℕ} (hAP : IsAlmostPerfect A B)
    (hlim : Filter.limsup (ratioEReal A B) Filter.atTop < ((8 / 5 : ℝ) : EReal)) :
    IsModularLift A B

/-- Corollary 1 (Resolution of Conjecture 1.3 of van Doorn–Liu–Tang, arXiv:2610.35027v1) -/
theorem conjecture_1_3 {A B : Set ℕ} (hAP : IsAlmostPerfect A B) :
    Filter.limsup (ratioEReal A B) Filter.atTop = (3 / 2 : EReal) ∨
      (((8 / 5 : ℝ) : EReal) ≤ Filter.limsup (ratioEReal A B) Filter.atTop ∧
       Filter.limsup (ratioEReal A B) Filter.atTop ≤ (2 : EReal))

/-- Corollary 2 (No Repeated Sums below 8/5) -/
theorem no_repeated_sums_below_eight_fifths {A B : Set ℕ} (hAP : IsAlmostPerfect A B)
    (hlim : Filter.limsup (ratioEReal A B) Filter.atTop < ((8 / 5 : ℝ) : EReal)) :
    ∀ n : ℕ, repCount A B n ≤ 1
```

## Module-by-module mapping to `PROOF.md`

| Compile order | Module | Lines | Owned decls | Corresponding section in [`PROOF.md`](PROOF.md) |
|---:|---|---:|---:|---|
| 1 | [`AlmostPerfect.Basic`](lean/AlmostPerfect/Basic.lean) | 71 | 7 | Section 1: `countNat`, `countReal`, `repCount`, `IsAlmostPerfect`, `ABin`, `ratioEReal`, `IsModularLift` |
| 2 | [`AlmostPerfect.ModularLift`](lean/AlmostPerfect/ModularLift.lean) | 262 | 74 | Section 1 & Corollary 2: base-4 bijection `binElem`/`binIndex`, `sq_add_two_mul_le_three_mul_binElem`, `modularLift_repCount_le_one` |
| 3 | [`AlmostPerfect.PolynomialInvariants`](lean/AlmostPerfect/PolynomialInvariants.lean) | 451 | 81 | Section 3 (Lemmas 3.1, 3.3): `truncPoly`, `crossExcess`, `VPoly`, `WPoly`, `exists_repCount_eq_one_eventually`, `truncPoly_exact_identity`, `WPoly_coeff_abs_le_one` |
| 4 | [`AlmostPerfect.LimsupBounds`](lean/AlmostPerfect/LimsupBounds.lean) | 798 | 124 | Section 1 & Corollary 1: `ABin_count_prod_le`, `almostPerfect_limsup_le_two`, `modularLift_limsup_eq_three_halves` |
| 5 | [`AlmostPerfect.ZhangGap`](lean/AlmostPerfect/ZhangGap.lean) | 660 | 103 | Section 3 (Lemma 3.5): discrete reflected convolution `dconv` and `zhang_gap_lemma` |
| 6 | [`AlmostPerfect.DifferenceDensity`](lean/AlmostPerfect/DifferenceDensity.lean) | 979 | 128 | Section 3 (Lemmas 3.1, 3.2, 3.4): `minElem`, `mZero`, `errSum`, `errSigned`, `stripPoly`, `VPoly_strip_properties`, `WPoly_deriv_eval_one`, difference-density bound |
| 7 | [`AlmostPerfect.ForwardDoubling`](lean/AlmostPerfect/ForwardDoubling.lean) | 1,889 | 422 | Section 5 (Lemmas 5.1–5.2, Prop. 5.3): `LevelApprox`, `lemma_5_1`, `lemma_5_2`, `DoublingStepResult`, `forward_doubling_step` |
| 8 | [`AlmostPerfect.PolynomialRigidity`](lean/AlmostPerfect/PolynomialRigidity.lean) | 313 | 26 | Section 6 (Lemma 6.1): UFD divisibility in $`\mathbb{Z}[X]`$ and `polynomial_iteration_rigidity` |
| 9 | [`AlmostPerfect.GabardoLaiBase`](lean/AlmostPerfect/GabardoLaiBase.lean) | 1,646 | 191 | Section 4 foundation: Lebesgue/discrete measures on $`\mathbb{R}`$, Fourier transforms, support endpoints, periodic tile helpers |
| 10 | [`AlmostPerfect.GabardoLai`](lean/AlmostPerfect/GabardoLai.lean) | 1,898 | 130 | Section 4 (Theorem 4.1): self-contained zero-axiom proof of Gabardo–Lai (2014, Thm. 2.2) (`gabardo_lai_single_step`) |
| 11 | [`AlmostPerfect.WeakLimit`](lean/AlmostPerfect/WeakLimit.lean) | 3,590 | 427 | Section 4 (Lemma 4.2, Prop. 4.3, Cor. 4.4): binary Cantor measures `cantorNu`/`cantorMu`, Prokhorov compactness, scaling invariance, $`M_1 \ge 3`$ elimination via `zhang_gap_lemma`, `weak_limit_unique`, `exists_levelApprox` |
| 12 | [`AlmostPerfect.Main`](lean/AlmostPerfect/Main.lean) | 1,181 | 196 | Section 7: polynomial rigidity at bounded-crossing levels, exact doubling tower, modular bijection (7.3), `main_classification`, `conjecture_1_3`, `no_repeated_sums_below_eight_fifths` |
| 13 | [`AlmostPerfect`](lean/AlmostPerfect.lean) | 12 | 0 | Umbrella library root importing all 12 modules |
| **Total** | **13 modules** | **13,750** | **1,909** | **1,790 theorems, 110 defs, 3 inductives, 3 constructors, 3 recursors** |

## Local replay commands

With `elan` and Python 3.12+ installed:

```bash
# 1. Fetch precompiled Mathlib v4.35.0 cache
cd lean
lake exe cache get
cd ..

# 2. Run the full 4-stage strict verification script:
#    (1) source hygiene, (2) fresh per-module -j1 -DwarningAsError=true compile,
#    (3) all-owned transitive Lean.collectAxioms audit, (4) leanchecker kernel replay
python3 scripts/verify-lean.py

# 3. Optionally also run the standalone exact rational & symbolic check suite
python3 verify.py
```

## Audited required endpoint theorems

Every one of the 14 required endpoint declarations below was verified by `scripts/verify-lean.py` to exist in the audited project closure and depend transitively on strictly `{Classical.choice, Quot.sound, propext}`:

- `AlmostPerfect.main_classification`
- `AlmostPerfect.conjecture_1_3`
- `AlmostPerfect.no_repeated_sums_below_eight_fifths`
- `AlmostPerfect.gabardo_lai_single_step`
- `AlmostPerfect.weak_limit_unique`
- `AlmostPerfect.exists_levelApprox`
- `AlmostPerfect.forward_doubling_step`
- `AlmostPerfect.polynomial_iteration_rigidity`
- `AlmostPerfect.zhang_gap_lemma`
- `AlmostPerfect.modularLift_limsup_eq_three_halves`
- `AlmostPerfect.modularLift_repCount_le_one`
- `AlmostPerfect.almostPerfect_limsup_le_two`
- `AlmostPerfect.truncPoly_exact_identity`
- `AlmostPerfect.exists_repCount_eq_one_eventually`
