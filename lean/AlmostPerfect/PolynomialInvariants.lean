import AlmostPerfect.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Section 3: Polynomial Invariants, Exact Truncation Identity, and Difference Density

Formalizes Section 3 of `PROOF.md`:
- Lemma 3.1: Stabilization `r(n) = 1` for all `n ≥ n₀`, minimal sum `r(a_min + b_min) = 1`,
  and invariants `V(z)`, `Ṽ(z)` with `Ṽ(0) = Ṽ(1) = 1` and `|coeff_d(Ṽ)| ≤ E`.
- Lemma 3.3: Exact generating-function identity
  `(1 - X) * P_{A₀}(X) * P_{B₀}(X) = V(X) - X^(N+1) * W_N(X)`
  and `{-1, 0, +1}` coefficient bound for `W_N(X)`.
- Lemma 3.4: Pointwise bound `1_{d=0} ≤ (1 - d) + d(d - 1)`.
-/

namespace AlmostPerfect

open Polynomial BigOperators Filter

noncomputable section

/-- Truncated generating polynomial `P_{S ∩ [0, N]}(X) = ∑_{a ∈ S ∩ [0, N]} X^a ∈ ℤ[X]`. -/
def truncPoly (S : Set ℕ) (N : ℕ) : ℤ[X] :=
  letI := Classical.decPred (· ∈ S)
  ∑ a ∈ (Finset.range (N + 1)).filter (· ∈ S), (X : ℤ[X]) ^ a

/-- Number of pairs `(a, b) ∈ (A ∩ [0, N]) × (B ∩ [0, N])` with `a + b = n`. -/
def repTrunc (A B : Set ℕ) (N n : ℕ) : ℕ :=
  letI := Classical.decPred (· ∈ A)
  letI := Classical.decPred (· ∈ B)
  ((Finset.range (N + 1)).filter (fun a => a ∈ A ∧ a ≤ n ∧ n - a ≤ N ∧ n - a ∈ B)).card

/-- Crossing excess `T(N) = #{(a, b) ∈ (A ∩ [0, N]) × (B ∩ [0, N]) : a + b > N}`. -/
def crossExcess (A B : Set ℕ) (N : ℕ) : ℕ :=
  ∑ m ∈ Finset.range N, repTrunc A B N (N + 1 + m)

lemma truncPoly_coeff (S : Set ℕ) (N n : ℕ) :
    letI := Classical.decPred (· ∈ S)
    (truncPoly S N).coeff n = if n ≤ N ∧ n ∈ S then 1 else 0 := by
  classical
  unfold truncPoly
  rw [finsetSum_coeff]
  simp only [coeff_X_pow]
  by_cases h : n ≤ N ∧ n ∈ S
  · have hmem : n ∈ (Finset.range (N + 1)).filter (· ∈ S) := by
      simp [Finset.mem_filter, Finset.mem_range, h.1, h.2]
    rw [Finset.sum_eq_single n]
    · simp [h]
    · intro b _ hbn; simp [hbn.symm]
    · intro hnot; exact absurd hmem hnot
  · rw [ite_eq_right_iff.mpr (fun hh => absurd hh h)]
    apply Finset.sum_eq_zero
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hb
    have hbn : n ≠ b := by intro heq; subst heq; exact h hb
    simp [hbn]

lemma truncPoly_eval_one (S : Set ℕ) (N : ℕ) :
    (truncPoly S N).eval 1 = (countNat S N : ℤ) := by
  classical
  unfold truncPoly countNat
  simp [eval_finsetSum]

lemma repTrunc_eq_repCount {A B : Set ℕ} {N n : ℕ} (hn : n ≤ N) :
    repTrunc A B N n = repCount A B n := by
  classical
  unfold repTrunc repCount
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, haA, hale, _, hbB⟩
    exact ⟨by omega, haA, hbB⟩
  · rintro ⟨hale, haA, hbB⟩
    exact ⟨by omega, haA, by omega, by omega, hbB⟩

lemma repTrunc_le_repCount (A B : Set ℕ) (N n : ℕ) :
    repTrunc A B N n ≤ repCount A B n := by
  classical
  unfold repTrunc repCount
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
  exact ⟨by omega, ha.2.1, ha.2.2.2.2⟩

lemma repTrunc_eq_zero_of_gt (A B : Set ℕ) {N n : ℕ} (hn : 2 * N < n) :
    repTrunc A B N n = 0 := by
  classical
  unfold repTrunc
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a ha
  simp only [Finset.mem_range] at ha
  omega

lemma truncPoly_mul_coeff (A B : Set ℕ) (N n : ℕ) :
    (truncPoly A N * truncPoly B N).coeff n = (repTrunc A B N n : ℤ) := by
  classical
  rw [coeff_mul]
  have h1 :
      ∑ p ∈ Finset.antidiagonal n, (truncPoly A N).coeff p.1 * (truncPoly B N).coeff p.2 =
        ∑ a ∈ Finset.range (n + 1),
          (if a ≤ N ∧ a ∈ A then (1 : ℤ) else 0) * (if n - a ≤ N ∧ n - a ∈ B then 1 else 0) := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun x y => (truncPoly A N).coeff x * (truncPoly B N).coeff y)]
    apply Finset.sum_congr rfl
    intro a _
    rw [truncPoly_coeff, truncPoly_coeff]
  rw [h1]
  have h2 :
      ∑ a ∈ Finset.range (n + 1),
        (if a ≤ N ∧ a ∈ A then (1 : ℤ) else 0) * (if n - a ≤ N ∧ n - a ∈ B then 1 else 0) =
      ∑ a ∈ Finset.range (n + 1),
        if a ≤ N ∧ a ∈ A ∧ a ≤ n ∧ n - a ≤ N ∧ n - a ∈ B then (1 : ℤ) else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    have hle : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    by_cases h1a : a ≤ N
    · by_cases h2a : a ∈ A
      · by_cases h3a : n - a ≤ N
        · by_cases h4a : n - a ∈ B
          · simp [h1a, h2a, hle, h3a, h4a]
          · simp [h1a, h2a, hle, h3a, h4a]
        · simp [h1a, h2a, h3a]
      · simp [h1a, h2a]
    · simp [h1a]
  rw [h2, ← Finset.sum_filter]
  have hfilt :
      (Finset.range (n + 1)).filter (fun a => a ≤ N ∧ a ∈ A ∧ a ≤ n ∧ n - a ≤ N ∧ n - a ∈ B) =
      (Finset.range (N + 1)).filter (fun a => a ∈ A ∧ a ≤ n ∧ n - a ≤ N ∧ n - a ∈ B) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, h1a, h2a, h3a, h4a, h5a⟩
      exact ⟨by omega, h2a, h3a, h4a, h5a⟩
    · rintro ⟨h1a, h2a, h3a, h4a, h5a⟩
      exact ⟨by omega, by omega, h2a, h3a, h4a, h5a⟩
  rw [hfilt, Finset.sum_const, nsmul_eq_mul, mul_one]
  rfl

/-- Exact product decomposition: `A(N) * B(N) = ∑_{n=0}^N r(n) + T(N)`. -/
lemma countNat_mul_eq_sum_repCount_add_crossExcess (A B : Set ℕ) (N : ℕ) :
    countNat A N * countNat B N =
      (∑ n ∈ Finset.range (N + 1), repCount A B n) + crossExcess A B N := by
  have hcast : ((countNat A N * countNat B N : ℕ) : ℤ) =
      (((∑ n ∈ Finset.range (N + 1), repCount A B n) + crossExcess A B N : ℕ) : ℤ) := by
    have heval : (truncPoly A N * truncPoly B N).eval 1 = (countNat A N : ℤ) * (countNat B N : ℤ) := by
      rw [eval_mul, truncPoly_eval_one, truncPoly_eval_one]
    have hsum : (truncPoly A N * truncPoly B N).eval 1 =
        ∑ n ∈ Finset.range (2 * N + 1), (truncPoly A N * truncPoly B N).coeff n := by
      by_cases h0 : truncPoly A N * truncPoly B N = 0
      · rw [h0]; simp
      · have hdegA : (truncPoly A N).natDegree ≤ N := by
          unfold truncPoly
          refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun a ha => ?_)
          simp only [Finset.mem_filter, Finset.mem_range] at ha
          rw [Polynomial.natDegree_X_pow]
          omega
        have hdegB : (truncPoly B N).natDegree ≤ N := by
          unfold truncPoly
          refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun b hb => ?_)
          simp only [Finset.mem_filter, Finset.mem_range] at hb
          rw [Polynomial.natDegree_X_pow]
          omega
        have hdegMul : (truncPoly A N * truncPoly B N).natDegree < 2 * N + 1 := by
          have := natDegree_mul_le (p := truncPoly A N) (q := truncPoly B N)
          omega
        rw [eval_eq_sum_range' hdegMul]
        simp
    rw [Nat.cast_mul, ← heval, hsum]
    have hsplit : 2 * N + 1 = (N + 1) + N := by omega
    rw [hsplit, Finset.sum_range_add]
    push_cast
    congr 1
    · apply Finset.sum_congr rfl
      intro n hn
      rw [truncPoly_mul_coeff, repTrunc_eq_repCount (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))]
    · unfold crossExcess
      push_cast
      apply Finset.sum_congr rfl
      intro m _
      rw [truncPoly_mul_coeff]
  exact_mod_cast hcast

/-- **Lemma 3.1(1) (Stabilization):**
For any almost perfect additive complements `A, B`, there exists `n₀ ≥ 1` such that
`repCount A B n = 1` for every `n ≥ n₀`. -/
theorem exists_repCount_eq_one_eventually {A B : Set ℕ} (hAP : IsAlmostPerfect A B) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n ≥ n₀, repCount A B n = 1 := by
  rcases hAP with ⟨_, _, hcov, hnot⟩
  rw [Filter.eventually_atTop] at hcov
  rcases hcov with ⟨N₁, hN₁⟩
  have hfreq : ∃ K : ℕ, ∀ M : ℕ, ∃ N ≥ M, countNat A N * countNat B N ≤ N + K := by
    rw [Filter.tendsto_atTop_atTop] at hnot
    push Not at hnot
    rcases hnot with ⟨C, hC⟩
    obtain ⟨K, hK⟩ := exists_nat_gt (max C 0 + 2)
    refine ⟨K, fun M => ?_⟩
    rcases hC (max (M : ℝ) 1) with ⟨x, hx_ge, hx_lt⟩
    have hx_nonneg : 0 ≤ x := by linarith [le_max_right (M : ℝ) 1]
    set N := ⌊x⌋₊
    have hN_ge : M ≤ N := Nat.le_floor (le_trans (le_max_left (M : ℝ) 1) hx_ge)
    have hcrA : countReal A x = countNat A N := by
      unfold countReal; exact ite_eq_right_iff.mpr (fun hlt => absurd hlt (not_lt.mpr hx_nonneg))
    have hcrB : countReal B x = countNat B N := by
      unfold countReal; exact ite_eq_right_iff.mpr (fun hlt => absurd hlt (not_lt.mpr hx_nonneg))
    rw [hcrA, hcrB] at hx_lt
    have hx_lt_succ : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
    have hbound_real : ((countNat A N * countNat B N : ℕ) : ℝ) < (N : ℝ) + (K : ℝ) := by
      push_cast
      have hC_le : C ≤ max C 0 := le_max_left C 0
      linarith
    exact ⟨N, hN_ge, Nat.le_of_lt (by exact_mod_cast hbound_real)⟩
  rcases hfreq with ⟨K, hK⟩
  have hexcess_bound : ∀ M ≥ N₁, ∑ n ∈ Finset.Ico N₁ (M + 1), (repCount A B n - 1) ≤ K + N₁ := by
    intro M hM
    rcases hK M with ⟨N, hNM, hNbound⟩
    have hprod := countNat_mul_eq_sum_repCount_add_crossExcess A B N
    have hN1_le_N : N₁ ≤ N := le_trans hM hNM
    have hsub : Finset.Ico N₁ (M + 1) ⊆ Finset.Ico N₁ (N + 1) :=
      Finset.Ico_subset_Ico_right (Nat.succ_le_succ hNM)
    have h1 : ∑ n ∈ Finset.Ico N₁ (M + 1), (repCount A B n - 1) ≤
        ∑ n ∈ Finset.Ico N₁ (N + 1), (repCount A B n - 1) :=
      Finset.sum_le_sum_of_subset hsub
    have h2 : ∑ n ∈ Finset.Ico N₁ (N + 1), (repCount A B n - 1) + (N + 1 - N₁) =
        ∑ n ∈ Finset.Ico N₁ (N + 1), repCount A B n := by
      have hcard : (Finset.Ico N₁ (N + 1)).card = N + 1 - N₁ := Nat.card_Ico N₁ (N + 1)
      rw [← hcard, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      have hn_ge : N₁ ≤ n := (Finset.mem_Ico.mp hn).1
      have hr : 1 ≤ repCount A B n := hN₁ n hn_ge
      omega
    have h3 : ∑ n ∈ Finset.Ico N₁ (N + 1), repCount A B n ≤
        ∑ n ∈ Finset.range (N + 1), repCount A B n := by
      apply Finset.sum_le_sum_of_subset
      intro n hn
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2
    omega
  have hfin : {n : ℕ | N₁ ≤ n ∧ 2 ≤ repCount A B n}.Finite := by
    by_contra hinf
    have hinf' : {n : ℕ | N₁ ≤ n ∧ 2 ≤ repCount A B n}.Infinite := hinf
    obtain ⟨S, hS_sub, hS_card⟩ := hinf'.exists_subset_card_eq (K + N₁ + 1)
    let M := max N₁ (S.sup id)
    have hM_ge : N₁ ≤ M := le_max_left _ _
    have hS_in : S ⊆ Finset.Ico N₁ (M + 1) := by
      intro n hn
      have hmem := hS_sub hn
      rw [Finset.mem_Ico]
      refine ⟨hmem.1, ?_⟩
      have hle : n ≤ S.sup id := Finset.le_sup (f := id) hn
      have : n ≤ M := le_trans hle (le_max_right _ _)
      omega
    have hsum_ge : S.card ≤ ∑ n ∈ Finset.Ico N₁ (M + 1), (repCount A B n - 1) := by
      calc
        S.card = ∑ _n ∈ S, 1 := by simp
        _ ≤ ∑ n ∈ S, (repCount A B n - 1) := by
          apply Finset.sum_le_sum
          intro n hn
          have := (hS_sub hn).2
          omega
        _ ≤ ∑ n ∈ Finset.Ico N₁ (M + 1), (repCount A B n - 1) :=
          Finset.sum_le_sum_of_subset hS_in
    have hbd := hexcess_bound M hM_ge
    omega
  rcases hfin.bddAbove with ⟨B_max, hB_max⟩
  refine ⟨max (max N₁ 1) (B_max + 1), le_trans (le_max_right N₁ 1) (le_max_left _ _), ?_⟩
  intro n hn
  have hn_N1 : N₁ ≤ n := le_trans (le_trans (le_max_left N₁ 1) (le_max_left _ _)) hn
  have hge1 : 1 ≤ repCount A B n := hN₁ n hn_N1
  have hlt2 : repCount A B n < 2 := by
    by_contra hge2
    push Not at hge2
    have hle : n ≤ B_max := hB_max ⟨hn_N1, hge2⟩
    have hgt : B_max + 1 ≤ n := le_trans (le_max_right _ _) hn
    omega
  omega

/-- The representation invariant polynomial
`V(X) = 1 + (1 - X) * ∑_{n=0}^{n₀-1} (r(n) - 1) X^n ∈ ℤ[X]`. -/
def VPoly (A B : Set ℕ) (n₀ : ℕ) : ℤ[X] :=
  1 + (1 - X) * ∑ n ∈ Finset.range n₀, C ((repCount A B n : ℤ) - 1) * (X : ℤ[X]) ^ n

/-- The boundary crossing polynomial
`W_N(X) = 1 - (1 - X) * ∑_{m=0}^{N-1} e_N(m) X^m ∈ ℤ[X]`. -/
def WPoly (A B : Set ℕ) (N : ℕ) : ℤ[X] :=
  1 - (1 - X) * ∑ m ∈ Finset.range N, C (repTrunc A B N (N + 1 + m) : ℤ) * (X : ℤ[X]) ^ m

lemma VPoly_eval_one (A B : Set ℕ) (n₀ : ℕ) : (VPoly A B n₀).eval 1 = 1 := by
  simp [VPoly]

lemma WPoly_eval_one (A B : Set ℕ) (N : ℕ) : (WPoly A B N).eval 1 = 1 := by
  simp [WPoly]

lemma coeff_one_sub_X_mul (P : ℤ[X]) (n : ℕ) :
    ((1 - X) * P).coeff n = if n = 0 then P.coeff 0 else P.coeff n - P.coeff (n - 1) := by
  rw [sub_mul, one_mul, coeff_sub]
  cases n with
  | zero => simp
  | succ m => simp [coeff_X_mul]

lemma VPoly_coeff {A B : Set ℕ} {n₀ : ℕ} (hstab : ∀ n ≥ n₀, repCount A B n = 1) (n : ℕ) :
    (VPoly A B n₀).coeff n =
      if n = 0 then (repCount A B 0 : ℤ)
      else (repCount A B n : ℤ) - (repCount A B (n - 1) : ℤ) := by
  have hS : ∀ k,
      (∑ j ∈ Finset.range n₀, C ((repCount A B j : ℤ) - 1) * (X : ℤ[X]) ^ j).coeff k =
        (repCount A B k : ℤ) - 1 := by
    intro k
    rw [finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow]
    by_cases hk : k < n₀
    · rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hbk; simp [hbk.symm]
      · intro hnot; exact absurd (Finset.mem_range.mpr hk) hnot
    · have h0 : ∑ x ∈ Finset.range n₀, ((repCount A B x : ℤ) - 1) * (if k = x then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        have hbk : k ≠ b := by intro h; subst h; exact hk (Finset.mem_range.mp hb)
        simp [hbk]
      rw [h0]
      have := hstab k (Nat.le_of_not_lt hk)
      simp [this]
  unfold VPoly
  rw [coeff_add, coeff_one_sub_X_mul]
  cases n with
  | zero =>
    simp only [Polynomial.coeff_one_zero, ↓reduceIte]
    rw [hS 0]
    ring
  | succ m =>
    simp only [Polynomial.coeff_one, Nat.succ_ne_zero, ↓reduceIte, zero_add, Nat.add_sub_cancel]
    rw [hS (m + 1), hS m]
    ring

lemma WPoly_coeff (A B : Set ℕ) (N m : ℕ) :
    (WPoly A B N).coeff m =
      if m = 0 then 1 - (repTrunc A B N (N + 1) : ℤ)
      else (repTrunc A B N (N + m) : ℤ) - (repTrunc A B N (N + 1 + m) : ℤ) := by
  have hS : ∀ k,
      (∑ j ∈ Finset.range N, C (repTrunc A B N (N + 1 + j) : ℤ) * (X : ℤ[X]) ^ j).coeff k =
        (repTrunc A B N (N + 1 + k) : ℤ) := by
    intro k
    rw [finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow]
    by_cases hk : k < N
    · rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hbk; simp [hbk.symm]
      · intro hnot; exact absurd (Finset.mem_range.mpr hk) hnot
    · have hgt : 2 * N < N + 1 + k := by omega
      rw [repTrunc_eq_zero_of_gt A B hgt]
      simp only [Nat.cast_zero]
      apply Finset.sum_eq_zero
      intro b hb
      have hbk : k ≠ b := by intro h; subst h; exact hk (Finset.mem_range.mp hb)
      simp [hbk]
  unfold WPoly
  rw [coeff_sub, coeff_one_sub_X_mul]
  cases m with
  | zero =>
    simp only [Polynomial.coeff_one_zero, ↓reduceIte, hS 0, add_zero]
  | succ j =>
    simp only [Polynomial.coeff_one, Nat.succ_ne_zero, ↓reduceIte, zero_sub, Nat.add_sub_cancel]
    rw [hS (j + 1), hS j]
    have heq : N + 1 + j = N + (j + 1) := by omega
    rw [heq]
    ring

/-- **Lemma 3.3(1) (Exact Generating-Function Identity):**
For all `N ≥ n₀` (where `r(n) = 1` for all `n ≥ n₀`),
`(1 - X) * P_{A ∩ [0, N]}(X) * P_{B ∩ [0, N]}(X) = V(X) - X^(N + 1) * W_N(X)`. -/
theorem truncPoly_exact_identity {A B : Set ℕ} {n₀ N : ℕ}
    (hstab : ∀ n ≥ n₀, repCount A B n = 1) (hN : n₀ ≤ N) :
    (1 - X) * (truncPoly A N * truncPoly B N) =
      VPoly A B n₀ - X ^ (N + 1) * WPoly A B N := by
  ext n
  rw [coeff_one_sub_X_mul, coeff_sub, VPoly_coeff hstab, coeff_X_pow_mul']
  cases n with
  | zero =>
    have hnot0 : ¬ (N + 1 ≤ 0) := by omega
    simp only [↓reduceIte, hnot0, sub_zero]
    rw [truncPoly_mul_coeff, repTrunc_eq_repCount (Nat.zero_le N)]
  | succ m =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [truncPoly_mul_coeff, truncPoly_mul_coeff]
    by_cases hle : m + 1 ≤ N
    · have hnot : ¬ (N + 1 ≤ m + 1) := by omega
      simp only [hnot, ↓reduceIte, sub_zero]
      rw [repTrunc_eq_repCount hle, repTrunc_eq_repCount (by omega : m ≤ N)]
    · have hge : N + 1 ≤ m + 1 := by omega
      simp only [hge, ↓reduceIte]
      rw [WPoly_coeff]
      by_cases heq : m + 1 = N + 1
      · have hm : m = N := by omega
        have hsub0 : m + 1 - (N + 1) = 0 := by omega
        have hrN : repCount A B m = 1 := hstab m (by omega)
        have hrN1 : repCount A B (m + 1) = 1 := hstab (m + 1) (by omega)
        simp only [hsub0, ↓reduceIte, hrN, hrN1, sub_self, zero_sub]
        rw [repTrunc_eq_repCount (by omega : m ≤ N), hrN, heq]
        ring
      · have hpos : m + 1 - (N + 1) ≠ 0 := by omega
        have hr1 : repCount A B (m + 1) = 1 := hstab (m + 1) (by omega)
        have hr2 : repCount A B m = 1 := hstab m (by omega)
        have hidx1 : N + (m + 1 - (N + 1)) = m := by omega
        have hidx2 : N + 1 + (m + 1 - (N + 1)) = m + 1 := by omega
        simp only [hpos, ↓reduceIte, hr1, hr2, sub_self, zero_sub, hidx1, hidx2]
        ring

/-- **Lemma 3.3(2):** Every coefficient of `W_N(X)` lies in `{-1, 0, +1}` when `N ≥ n₀`. -/
lemma WPoly_coeff_abs_le_one {A B : Set ℕ} {n₀ N : ℕ}
    (hstab : ∀ n ≥ n₀, repCount A B n = 1) (hN : n₀ ≤ N) (m : ℕ) :
    |(WPoly A B N).coeff m| ≤ 1 := by
  rw [WPoly_coeff]
  have hle1 : ∀ k ≥ N + 1, repTrunc A B N k ≤ 1 := fun k hk => by
    calc
      repTrunc A B N k ≤ repCount A B k := repTrunc_le_repCount A B N k
      _ = 1 := hstab k (by omega)
  cases m with
  | zero =>
    have h0 := hle1 (N + 1) le_rfl
    simp only [↓reduceIte]
    rw [abs_le]
    omega
  | succ j =>
    have h1 := hle1 (N + (j + 1)) (by omega)
    have h2 := hle1 (N + 1 + (j + 1)) (by omega)
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    rw [abs_le]
    omega

/-- **Lemma 3.4 pointwise helper:** `1_{d=0} ≤ (1 - d) + d(d - 1)` for every `d : ℕ`. -/
lemma indicator_zero_le_quad (d : ℕ) :
    (if d = 0 then (1 : ℤ) else 0) ≤ (1 - (d : ℤ)) + (d : ℤ) * ((d : ℤ) - 1) := by
  cases d with
  | zero => norm_num
  | succ m =>
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    have h : (1 - ((m + 1 : ℕ) : ℤ)) + ((m + 1 : ℕ) : ℤ) * (((m + 1 : ℕ) : ℤ) - 1) =
        ((m : ℤ)) ^ 2 := by push_cast; ring
    rw [h]
    exact sq_nonneg (m : ℤ)

end

end AlmostPerfect
