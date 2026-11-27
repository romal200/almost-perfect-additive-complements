import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

/-!
# Core Definitions for Almost Perfect Additive Complements

Defines counting functions `countNat` and `countReal`, representation multiplicity `repCount`,
almost perfect additive complements (`IsAlmostPerfect`), the base-4 binary Cantor set `ABin`,
and the modular-lift structural form `IsModularLift` appearing in the Main Theorem and
Conjecture 1.3 of van Doorn–Liu–Tang (arXiv:2610.35027v1).
-/

namespace AlmostPerfect

open Filter

noncomputable section

/-- Discrete counting function `S(n) = #(S ∩ [0, n])`. -/
def countNat (S : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred (· ∈ S)
  ((Finset.range (n + 1)).filter (· ∈ S)).card

/-- Real-variable counting function `S(x) = #(S ∩ [0, x])`. -/
def countReal (S : Set ℕ) (x : ℝ) : ℕ :=
  if x < 0 then 0 else countNat S ⌊x⌋₊

/-- Representation function `r_{A, B}(n) = #{(a, b) ∈ A × B : a + b = n}`. -/
def repCount (A B : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred (· ∈ A)
  letI := Classical.decPred (· ∈ B)
  ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ B)).card

/-- Two subsets `A, B ⊆ ℕ` are infinite almost perfect additive complements
(van Doorn–Liu–Tang, arXiv:2610.35027v1). -/
def IsAlmostPerfect (A B : Set ℕ) : Prop :=
  A.Infinite ∧
  B.Infinite ∧
  (∀ᶠ n : ℕ in atTop, 1 ≤ repCount A B n) ∧
  ¬ Tendsto (fun x : ℝ => (countReal A x : ℝ) * (countReal B x : ℝ) - x) atTop atTop

/-- The base-4 binary Cantor set `A_bin = {∑ ε_i 4^i : ε_i ∈ {0, 1}}`. -/
def ABin : Set ℕ :=
  {m : ℕ | ∀ i : ℕ, (m / 4 ^ i) % 4 ≤ 1}

/-- The scaled ratio `A(x)B(x)/x` viewed in `EReal` so `limsup` has no truncation artifacts. -/
def ratioEReal (A B : Set ℕ) (x : ℝ) : EReal :=
  (((countReal A x : ℝ) * (countReal B x : ℝ)) / x : ℝ)

/-- Modular-lift form `A = A₀ + D₀ · A_bin`, `B = B₀ + D₀ · (2 A_bin)` (up to swapping `A, B`),
where `(a, b) ↦ a + b mod D₀` is a bijection `A₀ × B₀ → ℤ/D₀ℤ`. -/
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

end

end AlmostPerfect
