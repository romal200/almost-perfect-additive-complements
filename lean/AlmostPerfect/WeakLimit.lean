import AlmostPerfect.Basic
import AlmostPerfect.PolynomialInvariants
import AlmostPerfect.ZhangGap
import AlmostPerfect.DifferenceDensity
import AlmostPerfect.ForwardDoubling
import AlmostPerfect.GabardoLaiBase
import AlmostPerfect.GabardoLai
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Section 4: Binary Cantor Measures, Weak-Limit Uniqueness, and Level Approximation

Formalizes Section 4 of `PROOF.md`:
1. Binary Cantor probability measures `cantorNu` (`ν₀`) and `cantorMu` (`μ₀`) via pushforward of
   `Measure.infinitePi` of fair Bernoulli coin flips on `ℕ → Bool`: support, atomlessness,
   Fourier transform limit, and exact CDF values on the six checkpoint intervals of `LevelApprox`.
2. **Lemma 4.2** (`lemma_4_2`): single Gabardo–Lai step lower bound `(2 M₂ + 2) / (M₂ + 2)`.
3. Scaling invariance `(4.3)`–`(4.4)`, exclusion of Type I factors, orientation-swap merging
   (`≥ 5/3`), and induction forcing `M₂ = M₃ = ... = 2` (`classify_subcritical_pair`).
4. **Proposition 4.3** (`weak_limit_unique`): along any filter `L ≤ atTop` with `T(N_j) ≤ K` and
   `limsup A(x)B(x)/x < 8/5`, any weak cluster point `(μ, ν)` of `(empMeas A N_j, empMeas B N_j)`
   equals `(cantorNu, cantorMu)` or `(cantorMu, cantorNu)` (ruling out `(δ₀, leb01)` via
   `modular_difference_density` and `M₁ ≥ 3` via `zhang_gap_lemma`).
5. **Corollary 4.4** (`exists_levelApprox`): uniform `LevelApprox` at all `N ≥ N_*(K)` with
   `T(N) ≤ K`, proved via compactness of `ProbabilityMeasure (Set.Icc (0 : ℝ) 1)` (`Prokhorov`)
   and `Portmanteau`.
-/

namespace AlmostPerfect

open MeasureTheory Filter Topology Real Complex BigOperators
open scoped ENNReal MeasureTheory

noncomputable section

/-! ### Part 0: Local Elementary Helpers -/

private lemma norm_exp_ofReal_mul_I_sub_one_le (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ≤ |x| := by
  have hsq : ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ^ 2 = (2 * Real.sin (x / 2)) ^ 2 := by
    rw [Complex.exp_ofReal_mul_I]
    have hsub : (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I - 1 =
        ((Real.cos x - 1 : ℝ) : ℂ) + ((Real.sin x : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hsub, Complex.sq_norm, Complex.normSq_add_mul_I]
    have hcos : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
      have := Real.cos_two_mul' (x / 2)
      rw [show 2 * (x / 2) = x by ring, Real.cos_sq'] at this; linarith
    have hsin : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
      have := Real.sin_two_mul (x / 2)
      rw [show 2 * (x / 2) = x by ring] at this; exact this
    have hpyth := Real.sin_sq_add_cos_sq (x / 2)
    rw [hcos, hsin]
    calc (1 - 2 * Real.sin (x / 2) ^ 2 - 1) ^ 2 + (2 * Real.sin (x / 2) * Real.cos (x / 2)) ^ 2
        = 4 * Real.sin (x / 2) ^ 2 * (Real.sin (x / 2) ^ 2 + Real.cos (x / 2) ^ 2) := by ring
      _ = (2 * Real.sin (x / 2)) ^ 2 := by rw [hpyth]; ring
  have h1 : ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ = |2 * Real.sin (x / 2)| := by
    have h2 := congrArg Real.sqrt hsq
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq_eq_abs] at h2
    exact h2
  rw [h1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hsin_le : |Real.sin (x / 2)| ≤ |x / 2| := Real.abs_sin_le_abs
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hsin_le
  linarith

private lemma repCount_comm (A B : Set ℕ) (n : ℕ) : repCount A B n = repCount B A n := by
  classical
  unfold repCount
  apply Finset.card_bij (fun a _ => n - a)
  · intro a ha; simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    refine ⟨by omega, ha.2.2, ?_⟩
    have : n - (n - a) = a := by omega
    rw [this]; exact ha.2.1
  · intro a₁ h₁ a₂ h₂ heq
    simp only [Finset.mem_filter, Finset.mem_range] at h₁ h₂
    omega
  · intro b hb; simp only [Finset.mem_filter, Finset.mem_range] at hb
    refine ⟨n - b, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, hb.2.2, ?_⟩
    have : n - (n - b) = b := by omega
    rw [this]; exact hb.2.1

private lemma repTrunc_comm (A B : Set ℕ) (N n : ℕ) : repTrunc A B N n = repTrunc B A N n := by
  classical
  unfold repTrunc
  apply Finset.card_bij (fun a _ => n - a)
  · intro a ha; simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    refine ⟨by omega, ha.2.2.2.2, by omega, by omega, ?_⟩
    have : n - (n - a) = a := by omega
    rw [this]; exact ha.2.1
  · intro a₁ h₁ a₂ h₂ heq
    simp only [Finset.mem_filter, Finset.mem_range] at h₁ h₂
    omega
  · intro b hb; simp only [Finset.mem_filter, Finset.mem_range] at hb
    refine ⟨n - b, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, hb.2.2.2.2, by omega, by omega, ?_⟩
    have : n - (n - b) = b := by omega
    rw [this]; exact hb.2.1

private lemma crossExcess_comm (A B : Set ℕ) (N : ℕ) : crossExcess A B N = crossExcess B A N := by
  unfold crossExcess
  apply Finset.sum_congr rfl; intro m _; exact repTrunc_comm A B N _

private lemma repPairSum_comm (A B : Set ℕ) (n₀ : ℕ) : repPairSum A B n₀ = repPairSum B A n₀ := by
  unfold repPairSum
  apply Finset.sum_congr rfl; intro n _; rw [repCount_comm]

/-! ### Part 1: Binary Cantor Measures `cantorNu` (`ν₀`) and `cantorMu` (`μ₀`) -/

/-- Fair Bernoulli probability measure `(1/2)(δ_false + δ_true)` on `Bool`. -/
def fairCoin : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac false + (1 / 2 : ℝ≥0∞) • Measure.dirac true

instance instIsProbabilityMeasure_fairCoin : IsProbabilityMeasure fairCoin := by
  constructor
  simp only [fairCoin, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply, mul_one]
  exact ENNReal.add_halves 1

/-- Infinite product of fair coin flips on `ℕ → Bool`. -/
def coinSpace : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => fairCoin)

instance instIsProbabilityMeasure_coinSpace : IsProbabilityMeasure coinSpace := by
  unfold coinSpace; infer_instance

/-- Base-4 Cantor map `ω ↦ ∑_{i=0}^∞ (ω i) · 4^{-(i+1)}`. -/
def base4Sum (ω : ℕ → Bool) : ℝ :=
  ∑' i : ℕ, if ω i then (1 / 4 : ℝ) ^ (i + 1) else 0

/-- Binary Cantor measure `ν₀` supported in `[0, 1/3]`. -/
def cantorNu : Measure ℝ := coinSpace.map base4Sum

/-- Binary Cantor measure `μ₀ = (2 * ·)_* ν₀` supported in `[0, 2/3]`. -/
def cantorMu : Measure ℝ := coinSpace.map (fun ω => 2 * base4Sum ω)

lemma summable_base4_term (ω : ℕ → Bool) :
    Summable (fun i : ℕ => if ω i then (1 / 4 : ℝ) ^ (i + 1) else 0) := by
  have hgeom : Summable (fun i : ℕ => (1 / 4 : ℝ) ^ (i + 1)) := by
    have h1 : Summable (fun i : ℕ => (1 / 4 : ℝ) ^ i) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    simpa [pow_succ'] using h1.mul_left (1 / 4 : ℝ)
  refine Summable.of_nonneg_of_le (fun i => by split_ifs <;> positivity) (fun i => ?_) hgeom
  split_ifs <;> [exact le_rfl; positivity]

lemma tsum_inv_four_pow_succ : (∑' i : ℕ, (1 / 4 : ℝ) ^ (i + 1)) = 1 / 3 := by
  have h1 : (∑' i : ℕ, (1 / 4 : ℝ) ^ (i + 1)) = (1 / 4 : ℝ) * ∑' i : ℕ, (1 / 4 : ℝ) ^ i := by
    rw [← tsum_mul_left]; congr 1; ext i; rw [pow_succ']
  rw [h1, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

lemma tsum_inv_four_tail (k : ℕ) :
    (∑' i : ℕ, (1 / 4 : ℝ) ^ (i + k + 1)) = (1 / 3 : ℝ) * (1 / 4 : ℝ) ^ k := by
  have h1 : (∑' i : ℕ, (1 / 4 : ℝ) ^ (i + k + 1)) =
      (1 / 4 : ℝ) ^ k * ∑' i : ℕ, (1 / 4 : ℝ) ^ (i + 1) := by
    rw [← tsum_mul_left]; congr 1; ext i
    rw [show i + k + 1 = k + (i + 1) by omega, pow_add]
  rw [h1, tsum_inv_four_pow_succ]; ring

lemma base4Sum_split (ω : ℕ → Bool) (k : ℕ) :
    base4Sum ω = (∑ i ∈ Finset.range k, if ω i then (1 / 4 : ℝ) ^ (i + 1) else 0) +
      (1 / 4 : ℝ) ^ k * base4Sum (fun i => ω (i + k)) := by
  unfold base4Sum
  rw [← (summable_base4_term ω).sum_add_tsum_nat_add k]
  congr 1
  rw [← tsum_mul_left]
  congr 1; ext i
  split_ifs <;> [rw [show i + k + 1 = k + (i + 1) by omega, pow_add]; rw [mul_zero]]

lemma base4Sum_nonneg (ω : ℕ → Bool) : 0 ≤ base4Sum ω :=
  tsum_nonneg (fun _ => by split_ifs <;> positivity)

lemma base4Sum_le_third (ω : ℕ → Bool) : base4Sum ω ≤ 1 / 3 := by
  rw [← tsum_inv_four_pow_succ]
  have hgeom : Summable (fun i : ℕ => (1 / 4 : ℝ) ^ (i + 1)) := by
    simpa [pow_succ'] using (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)).mul_left (1 / 4 : ℝ)
  exact (summable_base4_term ω).tsum_le_tsum (fun i => by split_ifs <;> [exact le_rfl; positivity]) hgeom

lemma continuous_base4Sum : Continuous base4Sum := by
  unfold base4Sum
  apply continuous_tsum (u := fun i : ℕ => (1 / 4 : ℝ) ^ (i + 1))
  · intro i
    exact (continuous_of_discreteTopology (f := fun b : Bool => if b then (1 / 4 : ℝ) ^ (i + 1) else 0)).comp
      (continuous_apply i)
  · simpa [pow_succ'] using (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)).mul_left (1 / 4 : ℝ)
  · intro i ω
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · simp only [norm_zero]; positivity

lemma measurable_base4Sum : Measurable base4Sum := continuous_base4Sum.measurable

lemma base4Sum_injective : Function.Injective base4Sum := by
  classical
  intro ω₁ ω₂ heq
  by_contra hne
  have hex : ∃ i : ℕ, ω₁ i ≠ ω₂ i := by
    by_contra hall; push Not at hall; exact hne (funext hall)
  let k := Nat.find hex
  have hk_ne : ω₁ k ≠ ω₂ k := Nat.find_spec hex
  have hk_eq : ∀ i < k, ω₁ i = ω₂ i := fun i hi => by
    by_contra h; exact Nat.find_min hex hi h
  have hpref : (∑ i ∈ Finset.range k, if ω₁ i then (1 / 4 : ℝ) ^ (i + 1) else 0) =
      (∑ i ∈ Finset.range k, if ω₂ i then (1 / 4 : ℝ) ^ (i + 1) else 0) :=
    Finset.sum_congr rfl (fun i hi => by rw [hk_eq i (Finset.mem_range.mp hi)])
  have htail_eq : base4Sum (fun i => ω₁ (i + k)) = base4Sum (fun i => ω₂ (i + k)) := by
    have h1 := base4Sum_split ω₁ k
    have h2 := base4Sum_split ω₂ k
    rw [heq, hpref] at h1
    have hpos : (1 / 4 : ℝ) ^ k ≠ 0 := by positivity
    exact mul_left_cancel₀ hpos (by linarith)
  have h1 := base4Sum_split (fun i => ω₁ (i + k)) 1
  have h2 := base4Sum_split (fun i => ω₂ (i + k)) 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one] at h1 h2
  have hlo1 := base4Sum_nonneg (fun i => ω₁ (i + 1 + k))
  have hhi1 := base4Sum_le_third (fun i => ω₁ (i + 1 + k))
  have hlo2 := base4Sum_nonneg (fun i => ω₂ (i + 1 + k))
  have hhi2 := base4Sum_le_third (fun i => ω₂ (i + 1 + k))
  cases hω1 : ω₁ k <;> cases hω2 : ω₂ k
  · exact hk_ne (by rw [hω1, hω2])
  · rw [hω1] at h1; rw [hω2] at h2; simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at h1 h2
    linarith
  · rw [hω1] at h1; rw [hω2] at h2; simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at h1 h2
    linarith
  · exact hk_ne (by rw [hω1, hω2])

instance instIsProbabilityMeasure_cantorNu : IsProbabilityMeasure cantorNu := by
  constructor
  rw [cantorNu, Measure.map_apply measurable_base4Sum MeasurableSet.univ, Set.preimage_univ, measure_univ]

instance instIsProbabilityMeasure_cantorMu : IsProbabilityMeasure cantorMu := by
  constructor
  rw [cantorMu, Measure.map_apply (measurable_base4Sum.const_mul 2) MeasurableSet.univ, Set.preimage_univ, measure_univ]

lemma cantorNu_supported_third : IsSupportedIn cantorNu (Set.Icc 0 (1 / 3)) := by
  unfold IsSupportedIn cantorNu
  rw [Measure.map_apply measurable_base4Sum measurableSet_Icc.compl]
  have hemp : base4Sum ⁻¹' (Set.Icc 0 (1 / 3))ᶜ = ∅ := by
    ext ω; simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc, Set.mem_empty_iff_false, iff_false, not_not]
    exact ⟨base4Sum_nonneg ω, base4Sum_le_third ω⟩
  rw [hemp, measure_empty]

lemma cantorMu_supported_two_thirds : IsSupportedIn cantorMu (Set.Icc 0 (2 / 3)) := by
  unfold IsSupportedIn cantorMu
  rw [Measure.map_apply (measurable_base4Sum.const_mul 2) measurableSet_Icc.compl]
  have hemp : (fun ω => 2 * base4Sum ω) ⁻¹' (Set.Icc 0 (2 / 3))ᶜ = ∅ := by
    ext ω; simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc, Set.mem_empty_iff_false, iff_false, not_not]
    exact ⟨by linarith [base4Sum_nonneg ω], by linarith [base4Sum_le_third ω]⟩
  rw [hemp, measure_empty]

lemma cantorNu_singleton_zero (x : ℝ) : cantorNu {x} = 0 := by
  unfold cantorNu
  rw [Measure.map_apply measurable_base4Sum (measurableSet_singleton x)]
  by_cases hx : ∃ ω, base4Sum ω = x
  · rcases hx with ⟨ω₀, rfl⟩
    have hpre : base4Sum ⁻¹' {base4Sum ω₀} = {ω₀} := by
      ext ω; simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => base4Sum_injective h, fun h => h ▸ rfl⟩
    rw [hpre]
    have hle_pow : ∀ k : ℕ, coinSpace {ω₀} ≤ (1 / 2 : ℝ≥0∞) ^ k := by
      intro k
      have hsub : ({ω₀} : Set (ℕ → Bool)) ⊆ (Finset.range k : Set ℕ).pi (fun i => {ω₀ i}) := by
        intro ω hω i _
        rw [Set.mem_singleton_iff] at hω; subst hω; exact Set.mem_singleton _
      calc coinSpace {ω₀}
          ≤ coinSpace ((Finset.range k : Set ℕ).pi (fun i => {ω₀ i})) := measure_mono hsub
        _ = ∏ i ∈ Finset.range k, fairCoin {ω₀ i} :=
              Measure.infinitePi_pi (fun _ => fairCoin) (fun _ _ => measurableSet_singleton _)
        _ = ∏ _i ∈ Finset.range k, (1 / 2 : ℝ≥0∞) := by
              apply Finset.prod_congr rfl; intro i _
              cases ω₀ i <;> simp [fairCoin, Measure.dirac_apply' _ (measurableSet_singleton _)]
        _ = (1 / 2 : ℝ≥0∞) ^ k := by simp
    by_contra hne
    have hpos : 0 < (coinSpace {ω₀}).toReal :=
      ENNReal.toReal_pos hne (measure_ne_top _ _)
    have htend : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    obtain ⟨k, hk⟩ := (htend.eventually (gt_mem_nhds hpos)).exists
    have hle_r : (coinSpace {ω₀}).toReal ≤ (1 / 2 : ℝ) ^ k := by
      have h1 := ENNReal.toReal_mono (ENNReal.pow_ne_top (by norm_num)) (hle_pow k)
      have h2 : ((1 / 2 : ℝ≥0∞) ^ k).toReal = (1 / 2 : ℝ) ^ k := by
        rw [ENNReal.toReal_pow]; simp
      linarith
    linarith
  · push Not at hx
    have hemp : base4Sum ⁻¹' {x} = ∅ := by
      ext ω; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact hx ω
    rw [hemp, measure_empty]

lemma cantorMu_eq_map_two : cantorMu = cantorNu.map ((2 : ℝ) * ·) := by
  unfold cantorMu cantorNu
  rw [Measure.map_map (measurable_const_mul 2) measurable_base4Sum]
  rfl

lemma cantorMu_singleton_zero (x : ℝ) : cantorMu {x} = 0 := by
  rw [cantorMu_eq_map_two, Measure.map_apply (measurable_const_mul 2) (measurableSet_singleton x)]
  have hpre : ((2 : ℝ) * ·) ⁻¹' {x} = {x / 2} := by
    ext y; simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor <;> intro h <;> linarith
  rw [hpre]; exact cantorNu_singleton_zero (x / 2)

/-- Exact cylinder measure for the first `k` bits of `coinSpace`. -/
lemma coinSpace_prefix_measure (k : ℕ) (b : Fin k → Bool) :
    coinSpace {ω | ∀ i : Fin k, ω i.1 = b i} = (1 / 2 : ℝ≥0∞) ^ k := by
  have heq : {ω : ℕ → Bool | ∀ i : Fin k, ω i.1 = b i} =
      (Finset.range k : Set ℕ).pi (fun i => if h : i < k then {b ⟨i, h⟩} else Set.univ) := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_range]
    constructor
    · intro h i hi; simp only [hi, ↓reduceDIte, Set.mem_singleton_iff]; exact h ⟨i, hi⟩
    · intro h ⟨i, hi⟩; have := h i hi; simpa [hi] using this
  rw [heq, coinSpace, Measure.infinitePi_pi _ (fun i _ => by split_ifs <;> [exact measurableSet_singleton _; exact MeasurableSet.univ])]
  have hterm : ∀ i ∈ Finset.range k,
      fairCoin (if h : i < k then {b ⟨i, h⟩} else Set.univ) = (1 / 2 : ℝ≥0∞) := by
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    simp only [hik, ↓reduceDIte]
    cases b ⟨i, hik⟩ <;> simp [fairCoin, Measure.dirac_apply' _ (measurableSet_singleton _)]
  rw [Finset.prod_congr rfl hterm, Finset.prod_const, Finset.card_range]

/-- Exact checkpoint values of `cantorNu` and `cantorMu` needed by Corollary 4.4 (`LevelApprox`). -/
lemma cantorNu_checkpoints :
    cantorNu (Set.Ioc (1 / 12 + 3 / 1000) (1 / 4 - 2 / 1000)) = 0 ∧
    cantorNu (Set.Ioc (1 / 16 - 1 / 1000) (1 / 12 + 1 / 1000)) = (1 / 4 : ℝ≥0∞) ∧
    cantorNu (Set.Ioc (5 / 16 - 1 / 1000) (1 / 3 + 1 / 1000)) = (1 / 4 : ℝ≥0∞) ∧
    (1 / 64 : ℝ≥0∞) ≤ cantorNu (Set.Ioo (1 / 3 - 1 / 1000) 1) ∧
    (1 / 64 : ℝ≥0∞) ≤ cantorMu (Set.Ioo (2 / 3 - 1 / 1000) 1) := by
  have hval2 : ∀ ω : ℕ → Bool,
      base4Sum ω = (if ω 0 then (1 / 4 : ℝ) else 0) + (if ω 1 then (1 / 16 : ℝ) else 0) +
        (1 / 16 : ℝ) * base4Sum (fun i => ω (i + 2)) := by
    intro ω
    have h := base4Sum_split ω 2
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at h
    norm_num at h
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Gap (1/12 + 3/1000, 1/4 - 2/1000] has measure 0
    unfold cantorNu
    rw [Measure.map_apply measurable_base4Sum measurableSet_Ioc]
    have hemp : base4Sum ⁻¹' Set.Ioc (1 / 12 + 3 / 1000) (1 / 4 - 2 / 1000) = ∅ := by
      ext ω; simp only [Set.mem_preimage, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false, not_and, not_le]
      intro hgt
      have h1 := base4Sum_split ω 1
      simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one] at h1
      have hlo := base4Sum_nonneg (fun i => ω (i + 1))
      have hhi := base4Sum_le_third (fun i => ω (i + 1))
      cases h0 : ω 0
      · rw [h0] at h1; simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at h1; linarith
      · rw [h0] at h1; simp only [↓reduceIte] at h1; linarith
    rw [hemp, measure_empty]
  · -- Block 1: (1/16 - 1/1000, 1/12 + 1/1000] corresponds exactly to ω 0 = false ∧ ω 1 = true
    unfold cantorNu
    rw [Measure.map_apply measurable_base4Sum measurableSet_Ioc]
    have hpre : base4Sum ⁻¹' Set.Ioc (1 / 16 - 1 / 1000) (1 / 12 + 1 / 1000) =
        {ω : ℕ → Bool | ∀ i : Fin 2, ω i.1 = (if i.1 = 0 then false else true)} := by
      ext ω; simp only [Set.mem_preimage, Set.mem_Ioc, Set.mem_ofPred_eq]
      have hv := hval2 ω
      have hlo := base4Sum_nonneg (fun i => ω (i + 2))
      have hhi := base4Sum_le_third (fun i => ω (i + 2))
      constructor
      · intro ⟨h1, h2⟩ ⟨i, hi⟩
        have h01 : i = 0 ∨ i = 1 := by omega
        cases hw0 : ω 0 <;> cases hw1 : ω 1
        · rw [hw0, hw1] at hv; simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at hv; linarith
        · rcases h01 with rfl | rfl <;> simp [hw0, hw1]
        · rw [hw0, hw1] at hv; simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hv; linarith
        · rw [hw0, hw1] at hv; simp only [↓reduceIte] at hv; linarith
      · intro h
        have hw0 : ω 0 = false := by simpa using h ⟨0, by omega⟩
        have hw1 : ω 1 = true := by simpa using h ⟨1, by omega⟩
        rw [hw0, hw1] at hv; simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at hv
        constructor <;> linarith
    rw [hpre, coinSpace_prefix_measure 2, one_div, one_div, ← ENNReal.inv_pow]; congr 1; norm_num
  · -- Block 2: (5/16 - 1/1000, 1/3 + 1/1000] corresponds exactly to ω 0 = true ∧ ω 1 = true
    unfold cantorNu
    rw [Measure.map_apply measurable_base4Sum measurableSet_Ioc]
    have hpre : base4Sum ⁻¹' Set.Ioc (5 / 16 - 1 / 1000) (1 / 3 + 1 / 1000) =
        {ω : ℕ → Bool | ∀ i : Fin 2, ω i.1 = true} := by
      ext ω; simp only [Set.mem_preimage, Set.mem_Ioc, Set.mem_ofPred_eq]
      have hv := hval2 ω
      have hlo := base4Sum_nonneg (fun i => ω (i + 2))
      have hhi := base4Sum_le_third (fun i => ω (i + 2))
      constructor
      · intro ⟨h1, h2⟩ ⟨i, hi⟩
        have h01 : i = 0 ∨ i = 1 := by omega
        cases hw0 : ω 0 <;> cases hw1 : ω 1
        · rw [hw0, hw1] at hv; simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at hv; linarith
        · rw [hw0, hw1] at hv; simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at hv; linarith
        · rw [hw0, hw1] at hv; simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hv; linarith
        · rcases h01 with rfl | rfl <;> simp [hw0, hw1]
      · intro h
        have hw0 : ω 0 = true := h ⟨0, by omega⟩
        have hw1 : ω 1 = true := h ⟨1, by omega⟩
        rw [hw0, hw1] at hv; simp only [↓reduceIte] at hv
        constructor <;> linarith
    rw [hpre, coinSpace_prefix_measure 2, one_div, one_div, ← ENNReal.inv_pow]; congr 1; norm_num
  · -- Tail mass of cantorNu near 1/3: all-true 6-bit prefix has base4Sum > 1/3 - 1/1000
    unfold cantorNu
    rw [Measure.map_apply measurable_base4Sum measurableSet_Ioo]
    have hsub : {ω : ℕ → Bool | ∀ i : Fin 6, ω i.1 = true} ⊆ base4Sum ⁻¹' Set.Ioo (1 / 3 - 1 / 1000) 1 := by
      intro ω hω
      simp only [Set.mem_preimage, Set.mem_Ioo]
      have hs := base4Sum_split ω 6
      have hpref : (∑ i ∈ Finset.range 6, if ω i then (1 / 4 : ℝ) ^ (i + 1) else 0) =
          ∑ i ∈ Finset.range 6, (1 / 4 : ℝ) ^ (i + 1) :=
        Finset.sum_congr rfl (fun i hi => by rw [hω ⟨i, Finset.mem_range.mp hi⟩]; simp)
      rw [hpref] at hs
      have hval : (∑ i ∈ Finset.range 6, (1 / 4 : ℝ) ^ (i + 1)) = 1365 / 4096 := by
        simp [Finset.sum_range_succ]; norm_num
      have hlo := base4Sum_nonneg (fun i => ω (i + 6))
      have hhi := base4Sum_le_third ω
      constructor <;> linarith
    have h64 : (1 / 64 : ℝ≥0∞) = (1 / 2 : ℝ≥0∞) ^ 6 := by
      rw [one_div, one_div, ← ENNReal.inv_pow]; congr 1; norm_num
    calc (1 / 64 : ℝ≥0∞) = (1 / 2 : ℝ≥0∞) ^ 6 := h64
      _ = coinSpace {ω | ∀ i : Fin 6, ω i.1 = true} := (coinSpace_prefix_measure 6 _).symm
      _ ≤ coinSpace (base4Sum ⁻¹' Set.Ioo (1 / 3 - 1 / 1000) 1) := measure_mono hsub
  · -- Tail mass of cantorMu near 2/3
    rw [cantorMu_eq_map_two, Measure.map_apply (measurable_const_mul 2) measurableSet_Ioo]
    have hsub2 : {ω : ℕ → Bool | ∀ i : Fin 6, ω i.1 = true} ⊆
        (fun ω => 2 * base4Sum ω) ⁻¹' Set.Ioo (2 / 3 - 1 / 1000) 1 := by
      intro ω hω
      simp only [Set.mem_preimage, Set.mem_Ioo]
      have hs := base4Sum_split ω 6
      have hpref : (∑ i ∈ Finset.range 6, if ω i then (1 / 4 : ℝ) ^ (i + 1) else 0) = 1365 / 4096 := by
        calc (∑ i ∈ Finset.range 6, if ω i then (1 / 4 : ℝ) ^ (i + 1) else 0)
            = ∑ i ∈ Finset.range 6, (1 / 4 : ℝ) ^ (i + 1) :=
              Finset.sum_congr rfl (fun i hi => by rw [hω ⟨i, Finset.mem_range.mp hi⟩]; simp)
          _ = 1365 / 4096 := by simp [Finset.sum_range_succ]; norm_num
      rw [hpref] at hs
      have hlo := base4Sum_nonneg (fun i => ω (i + 6))
      have hhi := base4Sum_le_third ω
      constructor <;> linarith
    have heq_m : cantorNu (((2 : ℝ) * ·) ⁻¹' Set.Ioo (2 / 3 - 1 / 1000) 1) =
        coinSpace ((fun ω => 2 * base4Sum ω) ⁻¹' Set.Ioo (2 / 3 - 1 / 1000) 1) := by
      unfold cantorNu; rw [Measure.map_apply measurable_base4Sum ((measurable_const_mul 2) measurableSet_Ioo)]
      rfl
    rw [heq_m]
    have h64 : (1 / 64 : ℝ≥0∞) = (1 / 2 : ℝ≥0∞) ^ 6 := by
      rw [one_div, one_div, ← ENNReal.inv_pow]; congr 1; norm_num
    calc (1 / 64 : ℝ≥0∞) = (1 / 2 : ℝ≥0∞) ^ 6 := h64
      _ = coinSpace {ω | ∀ i : Fin 6, ω i.1 = true} := (coinSpace_prefix_measure 6 _).symm
      _ ≤ coinSpace ((fun ω => 2 * base4Sum ω) ⁻¹' Set.Ioo (2 / 3 - 1 / 1000) 1) := measure_mono hsub2

/-- Finite binary convolution approximations `convBinNu k M` and `convBinMu k M`. -/
def convBinNu (k : ℕ) (M : ℝ) : Measure ℝ :=
  match k with
  | 0 => Measure.dirac 0
  | k + 1 => convBinNu k M ∗ unifDiscrete 2 (1 / (M * (4 : ℝ) ^ (k + 1)))

def convBinMu (k : ℕ) (M : ℝ) : Measure ℝ :=
  match k with
  | 0 => Measure.dirac 0
  | k + 1 => convBinMu k M ∗ unifDiscrete 2 (2 / (M * (4 : ℝ) ^ (k + 1)))

lemma isProbabilityMeasure_convBinNu (k : ℕ) (M : ℝ) : IsProbabilityMeasure (convBinNu k M) := by
  induction k with
  | zero => exact Measure.dirac.isProbabilityMeasure
  | succ k ih =>
    have : IsProbabilityMeasure (convBinNu k M) := ih
    have : IsProbabilityMeasure (unifDiscrete 2 (1 / (M * (4 : ℝ) ^ (k + 1)))) :=
      isProbabilityMeasure_unifDiscrete (by norm_num : 0 < 2) (1 / (M * (4 : ℝ) ^ (k + 1)))
    unfold convBinNu; infer_instance

lemma isProbabilityMeasure_convBinMu (k : ℕ) (M : ℝ) : IsProbabilityMeasure (convBinMu k M) := by
  induction k with
  | zero => exact Measure.dirac.isProbabilityMeasure
  | succ k ih =>
    have : IsProbabilityMeasure (convBinMu k M) := ih
    have : IsProbabilityMeasure (unifDiscrete 2 (2 / (M * (4 : ℝ) ^ (k + 1)))) :=
      isProbabilityMeasure_unifDiscrete (by norm_num : 0 < 2) (2 / (M * (4 : ℝ) ^ (k + 1)))
    unfold convBinMu; infer_instance

lemma ft_convBinNu (k : ℕ) (M ξ : ℝ) :
    ft (convBinNu k M) ξ =
      ∏ i ∈ Finset.range k,
        (1 + Complex.exp (-2 * Real.pi * ξ * (1 / (M * (4 : ℝ) ^ (i + 1))) * Complex.I)) / 2 := by
  induction k with
  | zero => simp [convBinNu, ft_dirac]
  | succ k ih =>
    have := isProbabilityMeasure_convBinNu k M
    have := isProbabilityMeasure_unifDiscrete (by norm_num : 0 < 2) (1 / (M * (4 : ℝ) ^ (k + 1)))
    rw [convBinNu, ft_conv, ih, Finset.prod_range_succ, ft_unifDiscrete (by norm_num)]
    congr 1
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, Complex.ofReal_zero, zero_mul, mul_zero,
      Complex.exp_zero, Complex.ofReal_one, one_mul]
    push_cast; ring

lemma ft_convBinMu (k : ℕ) (M ξ : ℝ) :
    ft (convBinMu k M) ξ =
      ∏ i ∈ Finset.range k,
        (1 + Complex.exp (-2 * Real.pi * ξ * (2 / (M * (4 : ℝ) ^ (i + 1))) * Complex.I)) / 2 := by
  induction k with
  | zero => simp [convBinMu, ft_dirac]
  | succ k ih =>
    have := isProbabilityMeasure_convBinMu k M
    have := isProbabilityMeasure_unifDiscrete (by norm_num : 0 < 2) (2 / (M * (4 : ℝ) ^ (k + 1)))
    rw [convBinMu, ft_conv, ih, Finset.prod_range_succ, ft_unifDiscrete (by norm_num)]
    congr 1
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, Complex.ofReal_zero, zero_mul, mul_zero,
      Complex.exp_zero, Complex.ofReal_one, one_mul]
    push_cast; ring

lemma tendsto_ft_convBinNu_one (ξ : ℝ) :
    Tendsto (fun k : ℕ => ft (convBinNu k 1) ξ) atTop (𝓝 (ft cantorNu ξ)) := by
  -- Express ft (convBinNu k 1) ξ as integral of prefix_k over coinSpace
  have hpref_int : ∀ k : ℕ, ft (convBinNu k 1) ξ =
      ∫ ω, Complex.exp (-2 * Real.pi * ξ *
        (∑ i ∈ Finset.range k, if ω i then (1 / 4 : ℝ) ^ (i + 1) else 0) * Complex.I) ∂coinSpace := by
    intro k
    rw [ft_convBinNu]
    -- Push forward coinSpace to Finset.range k → Bool
    set f : (ℕ → Bool) → ℂ := fun ω =>
      ∏ i ∈ Finset.range k, Complex.exp (-2 * Real.pi * ξ * (if ω i then (1 / 4 : ℝ) ^ (i + 1) else 0) * Complex.I)
    let S : (ℕ → Bool) → ℝ := fun ω => ∑ i ∈ Finset.range k, if ω i then (1 / 4 : ℝ) ^ (i + 1) else 0
    have hf_eq : ∀ ω, Complex.exp (-2 * Real.pi * ξ * (S ω : ℂ) * Complex.I) = f ω := by
      intro ω
      simp only [f, S, ← Complex.exp_sum]
      congr 1
      rw [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
    change _ = ∫ ω, Complex.exp (-2 * Real.pi * ξ * (S ω : ℂ) * Complex.I) ∂coinSpace
    rw [show (fun ω => Complex.exp (-2 * Real.pi * ξ * (S ω : ℂ) * Complex.I)) = f from funext hf_eq]
    -- Integrate finite product over Measure.pi via infinitePi_map_restrict
    let g : (↥(Finset.range k) → Bool) → ℂ := fun y =>
      ∏ i : Finset.range k, Complex.exp (-2 * Real.pi * ξ * (if y i then (1 / 4 : ℝ) ^ (i.1 + 1) else 0) * Complex.I)
    have hcomp : f = g ∘ (Finset.range k).restrict := by
      ext ω; simp only [f, g, Function.comp_apply]
      exact (Finset.prod_attach (Finset.range k) _).symm
    have hg_int : ∫ ω, f ω ∂coinSpace = ∫ y, g y ∂(Measure.pi fun _ : Finset.range k => fairCoin) := by
      rw [hcomp]
      simp only [Function.comp_apply]
      rw [← integral_map (Finset.measurable_restrict _).aemeasurable
          (Continuous.aestronglyMeasurable (continuous_of_discreteTopology (f := g))),
          coinSpace, Measure.infinitePi_map_restrict]
    rw [hg_int]
    -- Evaluate integral of product over Fintype Measure.pi via integral_fintype_prod_eq_prod
    have hprod_int := integral_fintype_prod_eq_prod (μ := fun _ : Finset.range k => fairCoin)
      (f := fun (i : Finset.range k) (b : Bool) =>
        Complex.exp (-2 * Real.pi * ξ * (if b then (1 / 4 : ℝ) ^ (i.1 + 1) else 0) * Complex.I))
    simp only [g]
    rw [hprod_int]
    have hterm : ∀ i : Finset.range k,
        (∫ b : Bool, Complex.exp (-2 * Real.pi * ξ * (if b then (1 / 4 : ℝ) ^ (i.1 + 1) else 0) * Complex.I) ∂fairCoin) =
        (1 + Complex.exp (-2 * Real.pi * ξ * (1 / (1 * (4 : ℝ) ^ (i.1 + 1))) * Complex.I)) / 2 := by
      intro i
      have hfin_f : IsFiniteMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac false) := by constructor; simp
      have hfin_t : IsFiniteMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac true) := by constructor; simp
      rw [fairCoin, integral_add_measure (Integrable.of_finite) (Integrable.of_finite),
          integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
      simp only [Bool.false_eq_true, ↓reduceIte, Complex.ofReal_zero, mul_zero, zero_mul,
        Complex.exp_zero, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat,
        Complex.real_smul]
      have hpow : (((1 / 4 : ℝ) ^ (i.1 + 1) : ℝ) : ℂ) = 1 / ((1 : ℂ) * (4 : ℂ) ^ (i.1 + 1)) := by
        push_cast; rw [one_mul, one_div_pow]
      have hhalf : (((1 / 2 : ℝ) : ℂ)) = (1 : ℂ) / 2 := by push_cast; rfl
      rw [hpow, hhalf]; push_cast; ring
    simp_rw [hterm]
    exact (Finset.prod_attach (Finset.range k) _).symm
  -- Now compare with ft cantorNu ξ = ∫ exp(-2πi ξ base4Sum ω) ∂coinSpace via norm bound
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hpow : Tendsto (fun k : ℕ => (2 * Real.pi * |ξ| / 3 + 1) * (1 / 4 : ℝ) ^ k) atTop (𝓝 0) := by
    have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
    simpa using h1.const_mul (2 * Real.pi * |ξ| / 3 + 1)
  obtain ⟨K, hK⟩ := (hpow.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  refine ⟨K, fun k hk => ?_⟩
  rw [dist_eq_norm, hpref_int k, ft_apply, cantorNu,
      integral_map measurable_base4Sum.aemeasurable (by fun_prop : Continuous fun x : ℝ => Complex.exp (-2 * Real.pi * ξ * x * Complex.I)).aestronglyMeasurable]
  set F₁ : (ℕ → Bool) → ℂ := fun ω =>
    Complex.exp (-2 * Real.pi * ξ * (∑ i ∈ Finset.range k, if ω i then (1 / 4 : ℝ) ^ (i + 1) else 0) * Complex.I)
  set F₂ : (ℕ → Bool) → ℂ := fun ω => Complex.exp (-2 * Real.pi * ξ * base4Sum ω * Complex.I)
  have hF1_cont : Continuous F₁ :=
    Complex.continuous_exp.comp
      ((continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_finsetSum _ fun i _ =>
          (continuous_of_discreteTopology (f := fun b : Bool => if b then (1 / 4 : ℝ) ^ (i + 1) else 0)).comp
            (continuous_apply i)))).mul continuous_const)
  have hF1_int : Integrable F₁ coinSpace :=
    (integrable_const (1 : ℝ)).mono' hF1_cont.aestronglyMeasurable (ae_of_all _ fun ω => by
      have : (-2 * Real.pi * ξ * (∑ i ∈ Finset.range k, if ω i then (1 / 4 : ℝ) ^ (i + 1) else 0) * Complex.I : ℂ) =
          ((-2 * Real.pi * ξ * (∑ i ∈ Finset.range k, if ω i then (1 / 4 : ℝ) ^ (i + 1) else 0) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      simp only [F₁, this, Complex.norm_exp_ofReal_mul_I]; exact le_rfl)
  have hF2_int : Integrable F₂ coinSpace :=
    (integrable_const (1 : ℝ)).mono' (Continuous.aestronglyMeasurable (by
      exact Complex.continuous_exp.comp (((continuous_const.mul (Complex.continuous_ofReal.comp continuous_base4Sum)).mul continuous_const))))
      (ae_of_all _ fun ω => by
        have : (-2 * Real.pi * ξ * base4Sum ω * Complex.I : ℂ) = ((-2 * Real.pi * ξ * base4Sum ω : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        simp only [F₂, this, Complex.norm_exp_ofReal_mul_I]; exact le_rfl)
  rw [← integral_sub hF1_int hF2_int]
  have hbound : ∀ ω, ‖F₁ ω - F₂ ω‖ ≤ (2 * Real.pi * |ξ| / 3) * (1 / 4 : ℝ) ^ k := by
    intro ω
    have hsplit := base4Sum_split ω k
    set s := ∑ i ∈ Finset.range k, if ω i then (1 / 4 : ℝ) ^ (i + 1) else 0
    set t := (1 / 4 : ℝ) ^ k * base4Sum (fun i => ω (i + k))
    have ht_le : |t| ≤ (1 / 3 : ℝ) * (1 / 4 : ℝ) ^ k := by
      rw [abs_of_nonneg (mul_nonneg (by positivity) (base4Sum_nonneg _))]
      have := base4Sum_le_third (fun i => ω (i + k))
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) k]
    have hdiff : ‖F₁ ω - F₂ ω‖ = ‖Complex.exp (((-2 * Real.pi * ξ * t : ℝ) : ℂ) * Complex.I) - 1‖ := by
      have h1 : F₂ ω = F₁ ω * Complex.exp (((-2 * Real.pi * ξ * t : ℝ) : ℂ) * Complex.I) := by
        show Complex.exp (-2 * Real.pi * ξ * (base4Sum ω : ℂ) * Complex.I) =
            Complex.exp (-2 * Real.pi * ξ * (s : ℂ) * Complex.I) * Complex.exp (((-2 * Real.pi * ξ * t : ℝ) : ℂ) * Complex.I)
        rw [hsplit, ← Complex.exp_add]; congr 1; push_cast; ring
      rw [h1, show F₁ ω - F₁ ω * Complex.exp (((-2 * Real.pi * ξ * t : ℝ) : ℂ) * Complex.I) =
          -(F₁ ω * (Complex.exp (((-2 * Real.pi * ξ * t : ℝ) : ℂ) * Complex.I) - 1)) by ring,
          norm_neg, norm_mul]
      have hF1n : ‖F₁ ω‖ = 1 := by
        have : (-2 * Real.pi * ξ * (s : ℂ) * Complex.I : ℂ) = ((-2 * Real.pi * ξ * s : ℝ) : ℂ) * Complex.I := by push_cast; ring
        change ‖Complex.exp (-2 * Real.pi * ξ * (s : ℂ) * Complex.I)‖ = 1
        rw [this, Complex.norm_exp_ofReal_mul_I]
      rw [hF1n, one_mul]
    rw [hdiff]
    have hlip := norm_exp_ofReal_mul_I_sub_one_le (-2 * Real.pi * ξ * t)
    calc ‖Complex.exp (((-2 * Real.pi * ξ * t : ℝ) : ℂ) * Complex.I) - 1‖
        ≤ |-2 * Real.pi * ξ * t| := hlip
      _ = 2 * Real.pi * |ξ| * |t| := by
          rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]
      _ ≤ 2 * Real.pi * |ξ| * ((1 / 3 : ℝ) * (1 / 4 : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left ht_le (by positivity)
      _ = (2 * Real.pi * |ξ| / 3) * (1 / 4 : ℝ) ^ k := by ring
  calc ‖∫ ω, (F₁ ω - F₂ ω) ∂coinSpace‖
      ≤ ∫ ω, ‖F₁ ω - F₂ ω‖ ∂coinSpace := norm_integral_le_integral_norm _
    _ ≤ ∫ _ω, (2 * Real.pi * |ξ| / 3) * (1 / 4 : ℝ) ^ k ∂coinSpace :=
          integral_mono (hF1_int.sub hF2_int).norm (integrable_const _) hbound
    _ = (2 * Real.pi * |ξ| / 3) * (1 / 4 : ℝ) ^ k := by simp
    _ < (2 * Real.pi * |ξ| / 3 + 1) * (1 / 4 : ℝ) ^ k := by
          have : (0 : ℝ) < (1 / 4 : ℝ) ^ k := by positivity
          nlinarith
    _ < ε := hK k hk

lemma tendsto_ft_convBinMu_one (ξ : ℝ) :
    Tendsto (fun k : ℕ => ft (convBinMu k 1) ξ) atTop (𝓝 (ft cantorMu ξ)) := by
  have heq : ∀ k, ft (convBinMu k 1) ξ = ft (convBinNu k 1) (2 * ξ) := by
    intro k; rw [ft_convBinMu, ft_convBinNu]
    apply Finset.prod_congr rfl; intro i _; congr 3; push_cast; ring
  simp_rw [heq]
  rw [cantorMu_eq_map_two, ft_map_mul]
  exact tendsto_ft_convBinNu_one (2 * ξ)

/-! ### Part 2: Lemma 4.2, Scaling Invariance, and Classification of Subcritical Pairs -/

/-- Subcriticality property for a complementary pair `(μ, ν)` on `[0, 1]`. -/
def IsSubcriticalPair (μ ν : Measure ℝ) (lam : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
  IsSupportedIn μ (Set.Icc 0 1) ∧ IsSupportedIn ν (Set.Icc 0 1) ∧
  μ ∗ ν = leb01 ∧
  ∀ u : ℝ, 0 < u → u < 1 → (μ (Set.Icc 0 u)).toReal * (ν (Set.Icc 0 u)).toReal ≤ lam * u

/-- Helper: lower bound on `(unifDiscrete M step ∗ σ) [0, t]` from the first `j` atoms. -/
private lemma unifDiscrete_conv_Icc_ge {M : ℕ} (hM : 1 ≤ M) {step : ℝ} (hstep : 0 ≤ step)
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {r : ℝ} (hr : IsSupportedIn σ (Set.Icc 0 r))
    {j : ℕ} (hj : j ≤ M) {t : ℝ} (ht : ((j : ℝ) - 1) * step + r ≤ t) (_ht0 : 0 ≤ t) :
    ((j : ℝ) / (M : ℝ)) ≤ ((unifDiscrete M step ∗ σ) (Set.Icc 0 t)).toReal := by
  have h1 : (unifDiscrete M step ∗ σ) (Set.Icc 0 t) =
      ((M : ℝ≥0∞))⁻¹ * ∑ i ∈ Finset.range M, σ ((fun y => (i : ℝ) * step + y) ⁻¹' Set.Icc 0 t) := by
    unfold unifDiscrete
    rw [Measure.conv_smul_left, Measure.smul_apply, smul_eq_mul]
    have hsum : (∑ i ∈ Finset.range M, Measure.dirac ((i : ℝ) * step)) ∗ σ =
        ∑ i ∈ Finset.range M, Measure.dirac ((i : ℝ) * step) ∗ σ := by
      clear hM hj ht
      induction Finset.range M using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.add_conv, ih]
    rw [hsum, Measure.finsetSum_apply]
    congr 1; apply Finset.sum_congr rfl; intro i _
    rw [Measure.dirac_conv, Measure.map_apply (measurable_const_add _) measurableSet_Icc]
  have hge_en : ((j : ℝ≥0∞) / (M : ℝ≥0∞)) ≤ (unifDiscrete M step ∗ σ) (Set.Icc 0 t) := by
    rw [h1, div_eq_mul_inv, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    calc (j : ℝ≥0∞) = ∑ _i ∈ Finset.range j, (1 : ℝ≥0∞) := by simp
      _ ≤ ∑ i ∈ Finset.range j, σ ((fun y => (i : ℝ) * step + y) ⁻¹' Set.Icc 0 t) := by
            apply Finset.sum_le_sum; intro i hi
            have hi_lt : i < j := Finset.mem_range.mp hi
            have hsub : Set.Icc (0 : ℝ) r ⊆ (fun y => (i : ℝ) * step + y) ⁻¹' Set.Icc 0 t := by
              intro y hy; simp only [Set.mem_preimage, Set.mem_Icc]
              have hi_le : (i : ℝ) ≤ (j : ℝ) - 1 := by
                have : i + 1 ≤ j := by omega
                have : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast this
                linarith
              exact ⟨add_nonneg (mul_nonneg (Nat.cast_nonneg i) hstep) hy.1, by nlinarith [hy.2]⟩
            have h1_eq : σ (Set.Icc 0 r) = 1 := by
              have hsp := measure_add_measure_compl (s := Set.Icc (0 : ℝ) r) (μ := σ) measurableSet_Icc
              rw [hr, add_zero, measure_univ] at hsp; exact hsp
            rw [← h1_eq]; exact measure_mono hsub
      _ ≤ ∑ i ∈ Finset.range M, σ ((fun y => (i : ℝ) * step + y) ⁻¹' Set.Icc 0 t) :=
            Finset.sum_le_sum_of_subset (Finset.range_mono hj)
  have := isProbabilityMeasure_unifDiscrete (by omega : 0 < M) step
  have hne_top : (unifDiscrete M step ∗ σ) (Set.Icc 0 t) ≠ ⊤ := measure_ne_top _ _
  have hto := ENNReal.toReal_mono hne_top hge_en
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at hto
  exact hto

/-- Helper: `j = 0` lower bound on `(unifDiscrete M step ∗ σ) [0, t]`. -/
private lemma unifDiscrete_conv_Icc_ge_zero {M : ℕ} (hM : 1 ≤ M) (step : ℝ)
    {σ : Measure ℝ} [IsProbabilityMeasure σ] (t : ℝ) :
    ((σ (Set.Icc 0 t)).toReal / (M : ℝ)) ≤ ((unifDiscrete M step ∗ σ) (Set.Icc 0 t)).toReal := by
  have h1 : (unifDiscrete M step ∗ σ) (Set.Icc 0 t) =
      ((M : ℝ≥0∞))⁻¹ * ∑ i ∈ Finset.range M, σ ((fun y => (i : ℝ) * step + y) ⁻¹' Set.Icc 0 t) := by
    unfold unifDiscrete
    rw [Measure.conv_smul_left, Measure.smul_apply, smul_eq_mul]
    have hsum : (∑ i ∈ Finset.range M, Measure.dirac ((i : ℝ) * step)) ∗ σ =
        ∑ i ∈ Finset.range M, Measure.dirac ((i : ℝ) * step) ∗ σ := by
      clear hM
      induction Finset.range M using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.add_conv, ih]
    rw [hsum, Measure.finsetSum_apply]
    congr 1; apply Finset.sum_congr rfl; intro i _
    rw [Measure.dirac_conv, Measure.map_apply (measurable_const_add _) measurableSet_Icc]
  have hge_en : σ (Set.Icc 0 t) / (M : ℝ≥0∞) ≤ (unifDiscrete M step ∗ σ) (Set.Icc 0 t) := by
    rw [h1, div_eq_mul_inv, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    have h0mem : 0 ∈ Finset.range M := Finset.mem_range.mpr (by omega)
    have hle : σ ((fun y => ((0 : ℕ) : ℝ) * step + y) ⁻¹' Set.Icc 0 t) ≤
        ∑ i ∈ Finset.range M, σ ((fun y => (i : ℝ) * step + y) ⁻¹' Set.Icc 0 t) :=
      Finset.single_le_sum (f := fun i : ℕ => σ ((fun y => (i : ℝ) * step + y) ⁻¹' Set.Icc 0 t))
        (by intro _ _; exact zero_le) h0mem
    simpa using hle
  have := isProbabilityMeasure_unifDiscrete (by omega : 0 < M) step
  have hto := ENNReal.toReal_mono (measure_ne_top _ _) hge_en
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast] at hto
  exact hto

/-- **Lemma 4.2 (van Doorn–Liu–Tang Lemma 2.5):**
If `(μ, ν)` is a subcritical pair with bound `lam` satisfying a Gabardo–Lai step `(4.1)` with
`M₁, M₂ ≥ 2`, then `(2 M₂ + 2) / (M₂ + 2) ≤ lam`. -/
theorem lemma_4_2 {μ ν μ' ν' : Measure ℝ} {lam : ℝ} {M₁ M₂ : ℕ}
    (hsub : IsSubcriticalPair μ ν lam) (hM1 : 2 ≤ M₁) (hM2 : 2 ≤ M₂)
    [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν']
    (hμ'_supp : IsSupportedIn μ' (Set.Icc 0 (1 / ((M₁ : ℝ) * (M₂ : ℝ)))))
    (hν'_supp : IsSupportedIn ν' (Set.Icc 0 (1 / ((M₁ : ℝ) * (M₂ : ℝ)))))
    (hconv' : μ' ∗ ν' = lebScaled (1 / ((M₁ : ℝ) * (M₂ : ℝ))))
    (hμ_eq : μ = unifDiscrete M₁ (1 / (M₁ : ℝ)) ∗ μ')
    (hν_eq : ν = unifDiscrete M₂ (1 / ((M₁ : ℝ) * (M₂ : ℝ))) ∗ ν') :
    (2 * (M₂ : ℝ) + 2) / ((M₂ : ℝ) + 2) ≤ lam := by
  have : IsProbabilityMeasure μ := hsub.1
  have : IsProbabilityMeasure ν := hsub.2.1
  have hM1p : (0 : ℝ) < (M₁ : ℝ) := Nat.cast_pos.mpr (by omega)
  have hM2p : (0 : ℝ) < (M₂ : ℝ) := Nat.cast_pos.mpr (by omega)
  have hM12p : (0 : ℝ) < (M₁ : ℝ) * (M₂ : ℝ) := mul_pos hM1p hM2p
  -- Rescale μ', ν' by M₁ * M₂ to compute their exact support endpoints r_μ', r_ν'
  let μs := μ'.map (((M₁ : ℝ) * (M₂ : ℝ)) * ·)
  let νs := ν'.map (((M₁ : ℝ) * (M₂ : ℝ)) * ·)
  have : IsProbabilityMeasure μs := isProbabilityMeasure_map_measurable (measurable_const_mul _)
  have : IsProbabilityMeasure νs := isProbabilityMeasure_map_measurable (measurable_const_mul _)
  have hconvs : μs ∗ νs = leb01 := by
    rw [← map_conv_mul_left, hconv', lebScaled_map_mul (div_pos one_pos hM12p) hM12p]
    have : (M₁ : ℝ) * (M₂ : ℝ) * (1 / ((M₁ : ℝ) * (M₂ : ℝ))) = 1 := by field_simp
    rw [this, lebScaled_one]
  have hmap_supp : ∀ (ρ : Measure ℝ), IsSupportedIn ρ (Set.Icc 0 (1 / ((M₁ : ℝ) * (M₂ : ℝ)))) →
      IsSupportedIn (ρ.map (((M₁ : ℝ) * (M₂ : ℝ)) * ·)) (Set.Icc 0 1) := by
    intro ρ hρ; unfold IsSupportedIn
    rw [Measure.map_apply (measurable_const_mul _) measurableSet_Icc.compl]
    have hsub_s : (((M₁ : ℝ) * (M₂ : ℝ)) * ·) ⁻¹' (Set.Icc 0 1)ᶜ ⊆ (Set.Icc 0 (1 / ((M₁ : ℝ) * (M₂ : ℝ))))ᶜ := by
      intro x hx hmem; apply hx; refine ⟨mul_nonneg (le_of_lt hM12p) hmem.1, ?_⟩
      have := mul_le_mul_of_nonneg_left hmem.2 (le_of_lt hM12p)
      have h1 : (M₁ : ℝ) * (M₂ : ℝ) * (1 / ((M₁ : ℝ) * (M₂ : ℝ))) = 1 := by field_simp
      linarith
    exact measure_mono_null hsub_s hρ
  rcases support_endpoints_of_conv_leb01 hconvs (hmap_supp μ' hμ'_supp) (hmap_supp ν' hν'_supp) with
    ⟨hμs_bb, hμs_ba, hνs_bb, hνs_ba, hinf_μs, hinf_νs, hsup_sum_s⟩
  set r₁ := sSup μs.support / ((M₁ : ℝ) * (M₂ : ℝ))
  set r₂ := sSup νs.support / ((M₁ : ℝ) * (M₂ : ℝ))
  have hr₁_nn : 0 ≤ r₁ := by
    rcases Measure.nonempty_support (IsProbabilityMeasure.ne_zero μs) with ⟨x, hx⟩
    have h0 : 0 ≤ sSup μs.support := by
      rw [← hinf_μs]; exact le_trans (csInf_le hμs_bb hx) (le_csSup hμs_ba hx)
    exact div_nonneg h0 (le_of_lt hM12p)
  have hr₂_nn : 0 ≤ r₂ := by
    rcases Measure.nonempty_support (IsProbabilityMeasure.ne_zero νs) with ⟨x, hx⟩
    have h0 : 0 ≤ sSup νs.support := by
      rw [← hinf_νs]; exact le_trans (csInf_le hνs_bb hx) (le_csSup hνs_ba hx)
    exact div_nonneg h0 (le_of_lt hM12p)
  have hr_sum : r₁ + r₂ = 1 / ((M₁ : ℝ) * (M₂ : ℝ)) := by
    simp only [r₁, r₂, ← add_div, hsup_sum_s]
  have hμ'_r1 : IsSupportedIn μ' (Set.Icc 0 r₁) := by
    have hback : μ' = μs.map (((M₁ : ℝ) * (M₂ : ℝ))⁻¹ * ·) := by
      simp only [μs, Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
      have : (((M₁ : ℝ) * (M₂ : ℝ))⁻¹ * ·) ∘ (((M₁ : ℝ) * (M₂ : ℝ)) * ·) = id := by ext x; simp; field_simp
      rw [this, Measure.map_id]
    rw [hback]; unfold IsSupportedIn
    rw [Measure.map_apply (measurable_const_mul _) measurableSet_Icc.compl]
    have hsub_r : (((M₁ : ℝ) * (M₂ : ℝ))⁻¹ * ·) ⁻¹' (Set.Icc 0 r₁)ᶜ ⊆ μs.supportᶜ := by
      intro x hx hmem; apply hx
      have hx1 : 0 ≤ x := hinf_μs ▸ csInf_le hμs_bb hmem
      have hx2 : x ≤ sSup μs.support := le_csSup hμs_ba hmem
      exact ⟨by positivity, by simp only [r₁, div_eq_inv_mul]; exact mul_le_mul_of_nonneg_left hx2 (inv_nonneg.mpr (le_of_lt hM12p))⟩
    exact measure_mono_null hsub_r Measure.measure_compl_support
  have hν'_r2 : IsSupportedIn ν' (Set.Icc 0 r₂) := by
    have hback : ν' = νs.map (((M₁ : ℝ) * (M₂ : ℝ))⁻¹ * ·) := by
      simp only [νs, Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
      have : (((M₁ : ℝ) * (M₂ : ℝ))⁻¹ * ·) ∘ (((M₁ : ℝ) * (M₂ : ℝ)) * ·) = id := by ext x; simp; field_simp
      rw [this, Measure.map_id]
    rw [hback]; unfold IsSupportedIn
    rw [Measure.map_apply (measurable_const_mul _) measurableSet_Icc.compl]
    have hsub_r : (((M₁ : ℝ) * (M₂ : ℝ))⁻¹ * ·) ⁻¹' (Set.Icc 0 r₂)ᶜ ⊆ νs.supportᶜ := by
      intro x hx hmem; apply hx
      have hx1 : 0 ≤ x := hinf_νs ▸ csInf_le hνs_bb hmem
      have hx2 : x ≤ sSup νs.support := le_csSup hνs_ba hmem
      exact ⟨by positivity, by simp only [r₂, div_eq_inv_mul]; exact mul_le_mul_of_nonneg_left hx2 (inv_nonneg.mpr (le_of_lt hM12p))⟩
    exact measure_mono_null hsub_r Measure.measure_compl_support
  set t₁ := 1 / (M₁ : ℝ) + r₁
  set t₂ := 1 / ((M₁ : ℝ) * (M₂ : ℝ)) + r₂
  have ht1_pos : 0 < t₁ := by simp only [t₁]; positivity
  have ht2_pos : 0 < t₂ := by simp only [t₂]; positivity
  have ht1_lt1 : t₁ < 1 := by
    have h1 : (2 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hM1
    have h2 : (2 : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hM2
    have hr1_le : r₁ ≤ 1 / ((M₁ : ℝ) * (M₂ : ℝ)) := by linarith
    have hinv1 : 1 / (M₁ : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ hM1p (by norm_num)]; linarith
    have hinv12 : 1 / ((M₁ : ℝ) * (M₂ : ℝ)) ≤ 1 / 4 := by rw [div_le_div_iff₀ hM12p (by norm_num)]; nlinarith
    simp only [t₁]; linarith
  have ht2_lt1 : t₂ < 1 := by
    have h1 : (2 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hM1
    have h2 : (2 : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hM2
    have hr2_le : r₂ ≤ 1 / ((M₁ : ℝ) * (M₂ : ℝ)) := by linarith
    have hinv12 : 1 / ((M₁ : ℝ) * (M₂ : ℝ)) ≤ 1 / 4 := by rw [div_le_div_iff₀ hM12p (by norm_num)]; nlinarith
    simp only [t₂]; linarith
  -- Bound 1 at t₁: μ([0, t₁]) ≥ 2/M₁ and ν([0, t₁]) = 1
  have hbd1 : (2 / (M₁ : ℝ)) ≤ lam * t₁ := by
    have hμt1 : (2 : ℝ) / (M₁ : ℝ) ≤ (μ (Set.Icc 0 t₁)).toReal := by
      rw [hμ_eq]
      have h2 := unifDiscrete_conv_Icc_ge (M := M₁) (by omega) (step := 1 / (M₁ : ℝ)) (by positivity) hμ'_r1 hM1
        (t := t₁) (by simp only [t₁]; norm_num) (le_of_lt ht1_pos)
      simpa using h2
    have hνt1 : (1 : ℝ) ≤ (ν (Set.Icc 0 t₁)).toReal := by
      rw [hν_eq]
      have h2 := unifDiscrete_conv_Icc_ge (M := M₂) (by omega) (step := 1 / ((M₁ : ℝ) * (M₂ : ℝ))) (by positivity) hν'_r2 le_rfl
        (t := t₁) (by
          have hcalc : ((M₂ : ℝ) - 1) * (1 / ((M₁ : ℝ) * (M₂ : ℝ))) + r₂ = 1 / (M₁ : ℝ) - r₁ := by
            have : ((M₂ : ℝ) - 1) * (1 / ((M₁ : ℝ) * (M₂ : ℝ))) = 1 / (M₁ : ℝ) - 1 / ((M₁ : ℝ) * (M₂ : ℝ)) := by
              field_simp
            linarith
          simp only [t₁]; linarith) (le_of_lt ht1_pos)
      rw [div_self hM2p.ne'] at h2; exact h2
    have hsub1 := hsub.2.2.2.2.2 t₁ ht1_pos ht1_lt1
    have hmul : (2 / (M₁ : ℝ)) * 1 ≤ (μ (Set.Icc 0 t₁)).toReal * (ν (Set.Icc 0 t₁)).toReal :=
      mul_le_mul hμt1 hνt1 zero_le_one (by positivity)
    linarith
  -- Bound 2 at t₂: μ([0, t₂]) ≥ 1/M₁ (since r₁ ≤ t₂!) and ν([0, t₂]) ≥ 2/M₂
  have hbd2 : (2 / ((M₁ : ℝ) * (M₂ : ℝ))) ≤ lam * t₂ := by
    have hμt2 : (1 : ℝ) / (M₁ : ℝ) ≤ (μ (Set.Icc 0 t₂)).toReal := by
      rw [hμ_eq]
      have h2 := unifDiscrete_conv_Icc_ge (M := M₁) (by omega) (step := 1 / (M₁ : ℝ)) (by positivity) hμ'_r1 (by omega : 1 ≤ M₁)
        (t := t₂) (by simp only [t₂, Nat.cast_one, sub_self, zero_mul, zero_add]; linarith) (le_of_lt ht2_pos)
      simpa using h2
    have hνt2 : (2 : ℝ) / (M₂ : ℝ) ≤ (ν (Set.Icc 0 t₂)).toReal := by
      rw [hν_eq]
      have h2 := unifDiscrete_conv_Icc_ge (M := M₂) (by omega) (step := 1 / ((M₁ : ℝ) * (M₂ : ℝ))) (by positivity) hν'_r2 hM2
        (t := t₂) (by simp only [t₂]; norm_num) (le_of_lt ht2_pos)
      simpa using h2
    have hsub2 := hsub.2.2.2.2.2 t₂ ht2_pos ht2_lt1
    have hmul : (1 / (M₁ : ℝ)) * (2 / (M₂ : ℝ)) ≤ (μ (Set.Icc 0 t₂)).toReal * (ν (Set.Icc 0 t₂)).toReal :=
      mul_le_mul hμt2 hνt2 (by positivity) (by positivity)
    have hprod_eq : (1 / (M₁ : ℝ)) * (2 / (M₂ : ℝ)) = 2 / ((M₁ : ℝ) * (M₂ : ℝ)) := by ring
    linarith
  -- Combine hbd1 and hbd2: t₁ + t₂ = (M₂ + 2) / (M₁ M₂) eliminates r₁, r₂
  have hsum_t : t₁ + t₂ = ((M₂ : ℝ) + 2) / ((M₁ : ℝ) * (M₂ : ℝ)) := by
    simp only [t₁, t₂]
    have : 1 / (M₁ : ℝ) + r₁ + (1 / ((M₁ : ℝ) * (M₂ : ℝ)) + r₂) =
        1 / (M₁ : ℝ) + 2 * (1 / ((M₁ : ℝ) * (M₂ : ℝ))) := by linarith
    rw [this]; field_simp
  have hsum_lhs : 2 / (M₁ : ℝ) + 2 / ((M₁ : ℝ) * (M₂ : ℝ)) = (2 * (M₂ : ℝ) + 2) / ((M₁ : ℝ) * (M₂ : ℝ)) := by
    field_simp
  have hadd : (2 * (M₂ : ℝ) + 2) / ((M₁ : ℝ) * (M₂ : ℝ)) ≤ lam * (((M₂ : ℝ) + 2) / ((M₁ : ℝ) * (M₂ : ℝ))) := by
    have hsum_ineq : 2 / (M₁ : ℝ) + 2 / ((M₁ : ℝ) * (M₂ : ℝ)) ≤ lam * (t₁ + t₂) := by linarith
    rw [hsum_lhs, hsum_t] at hsum_ineq
    exact hsum_ineq
  have hmul_pos := mul_le_mul_of_nonneg_left hadd (le_of_lt hM12p)
  have h1 : (M₁ : ℝ) * (M₂ : ℝ) * ((2 * (M₂ : ℝ) + 2) / ((M₁ : ℝ) * (M₂ : ℝ))) = 2 * (M₂ : ℝ) + 2 := by field_simp
  have h2 : (M₁ : ℝ) * (M₂ : ℝ) * (lam * (((M₂ : ℝ) + 2) / ((M₁ : ℝ) * (M₂ : ℝ)))) = lam * ((M₂ : ℝ) + 2) := by field_simp
  rw [h1, h2] at hmul_pos
  rw [div_le_iff₀ (by positivity)]
  exact hmul_pos

/-- Scaling invariance `(4.3)`: two-step rescaling preserves `IsSubcriticalPair _ _ lam`. -/
lemma scaling_invariance_two_step {μ ν μ' ν' : Measure ℝ} {lam : ℝ} {M₁ M₂ : ℕ}
    (hsub : IsSubcriticalPair μ ν lam) (hM1 : 2 ≤ M₁) (hM2 : 2 ≤ M₂)
    [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν']
    (hμ'_supp : IsSupportedIn μ' (Set.Icc 0 (1 / ((M₁ : ℝ) * (M₂ : ℝ)))))
    (hν'_supp : IsSupportedIn ν' (Set.Icc 0 (1 / ((M₁ : ℝ) * (M₂ : ℝ)))))
    (hconv' : μ' ∗ ν' = lebScaled (1 / ((M₁ : ℝ) * (M₂ : ℝ))))
    (hμ_eq : μ = unifDiscrete M₁ (1 / (M₁ : ℝ)) ∗ μ')
    (hν_eq : ν = unifDiscrete M₂ (1 / ((M₁ : ℝ) * (M₂ : ℝ))) ∗ ν') :
    IsSubcriticalPair (μ'.map (((M₁ : ℝ) * (M₂ : ℝ)) * ·)) (ν'.map (((M₁ : ℝ) * (M₂ : ℝ)) * ·)) lam := by
  have hM12p : (0 : ℝ) < (M₁ : ℝ) * (M₂ : ℝ) := by positivity
  have hmap_supp : ∀ (ρ : Measure ℝ), IsSupportedIn ρ (Set.Icc 0 (1 / ((M₁ : ℝ) * (M₂ : ℝ)))) →
      IsSupportedIn (ρ.map (((M₁ : ℝ) * (M₂ : ℝ)) * ·)) (Set.Icc 0 1) := by
    intro ρ hρ; unfold IsSupportedIn
    rw [Measure.map_apply (measurable_const_mul _) measurableSet_Icc.compl]
    have hsub_s : (((M₁ : ℝ) * (M₂ : ℝ)) * ·) ⁻¹' (Set.Icc 0 1)ᶜ ⊆ (Set.Icc 0 (1 / ((M₁ : ℝ) * (M₂ : ℝ))))ᶜ := by
      intro x hx hmem; apply hx; refine ⟨mul_nonneg (le_of_lt hM12p) hmem.1, ?_⟩
      have := mul_le_mul_of_nonneg_left hmem.2 (le_of_lt hM12p)
      have h1 : (M₁ : ℝ) * (M₂ : ℝ) * (1 / ((M₁ : ℝ) * (M₂ : ℝ))) = 1 := by field_simp
      linarith
    exact measure_mono_null hsub_s hρ
  refine ⟨isProbabilityMeasure_map_measurable (measurable_const_mul _),
    isProbabilityMeasure_map_measurable (measurable_const_mul _),
    hmap_supp μ' hμ'_supp, hmap_supp ν' hν'_supp, ?_, ?_⟩
  · rw [← map_conv_mul_left, hconv', lebScaled_map_mul (div_pos one_pos hM12p) hM12p]
    have : (M₁ : ℝ) * (M₂ : ℝ) * (1 / ((M₁ : ℝ) * (M₂ : ℝ))) = 1 := by field_simp
    rw [this, lebScaled_one]
  · intro u hu0 hu1
    set t := u / ((M₁ : ℝ) * (M₂ : ℝ))
    have ht0 : 0 < t := div_pos hu0 hM12p
    have ht1 : t < 1 := by
      have : (4 : ℝ) ≤ (M₁ : ℝ) * (M₂ : ℝ) := by
        have h1 : (2 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hM1
        have h2 : (2 : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hM2
        nlinarith
      rw [div_lt_one hM12p]; linarith
    have hpre : (((M₁ : ℝ) * (M₂ : ℝ)) * ·) ⁻¹' Set.Icc 0 u = Set.Icc 0 t := by
      ext x; simp only [Set.mem_preimage, Set.mem_Icc, t, le_div_iff₀ hM12p]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨by positivity, by linarith⟩
    have hμt : (μ'.map (((M₁ : ℝ) * (M₂ : ℝ)) * ·) (Set.Icc 0 u)).toReal / (M₁ : ℝ) ≤ (μ (Set.Icc 0 t)).toReal := by
      rw [Measure.map_apply (measurable_const_mul _) measurableSet_Icc, hpre, hμ_eq]
      exact unifDiscrete_conv_Icc_ge_zero (by omega) _ t
    have hνt : (ν'.map (((M₁ : ℝ) * (M₂ : ℝ)) * ·) (Set.Icc 0 u)).toReal / (M₂ : ℝ) ≤ (ν (Set.Icc 0 t)).toReal := by
      rw [Measure.map_apply (measurable_const_mul _) measurableSet_Icc, hpre, hν_eq]
      exact unifDiscrete_conv_Icc_ge_zero (by omega) _ t
    have hprod := mul_le_mul hμt hνt (by positivity) (ENNReal.toReal_nonneg)
    have hbd := hsub.2.2.2.2.2 t ht0 ht1
    have hcomb : ((μ'.map (((M₁ : ℝ) * (M₂ : ℝ)) * ·) (Set.Icc 0 u)).toReal *
        (ν'.map (((M₁ : ℝ) * (M₂ : ℝ)) * ·) (Set.Icc 0 u)).toReal) / ((M₁ : ℝ) * (M₂ : ℝ)) ≤
        lam * u / ((M₁ : ℝ) * (M₂ : ℝ)) := by
      calc _ = ((μ'.map (((M₁ : ℝ) * (M₂ : ℝ)) * ·) (Set.Icc 0 u)).toReal / (M₁ : ℝ)) *
               ((ν'.map (((M₁ : ℝ) * (M₂ : ℝ)) * ·) (Set.Icc 0 u)).toReal / (M₂ : ℝ)) := by ring
        _ ≤ (μ (Set.Icc 0 t)).toReal * (ν (Set.Icc 0 t)).toReal := hprod
        _ ≤ lam * t := hbd
        _ = lam * u / ((M₁ : ℝ) * (M₂ : ℝ)) := by simp only [t]; ring
    exact (div_le_div_iff_of_pos_right hM12p).mp hcomb

/-- Scaling invariance `(4.4)`: single-factor stripping preserves `IsSubcriticalPair _ _ lam`. -/
lemma scaling_invariance_one_step {μ ν μ' : Measure ℝ} {lam : ℝ} {M₁ : ℕ}
    (hsub : IsSubcriticalPair μ ν lam) (hM1 : 2 ≤ M₁)
    [IsProbabilityMeasure μ']
    (hμ'_supp : IsSupportedIn μ' (Set.Icc 0 (1 / (M₁ : ℝ))))
    (hν_supp_M1 : IsSupportedIn ν (Set.Icc 0 (1 / (M₁ : ℝ))))
    (hconv' : μ' ∗ ν = lebScaled (1 / (M₁ : ℝ)))
    (hμ_eq : μ = unifDiscrete M₁ (1 / (M₁ : ℝ)) ∗ μ') :
    IsSubcriticalPair (ν.map ((M₁ : ℝ) * ·)) (μ'.map ((M₁ : ℝ) * ·)) lam := by
  have : IsProbabilityMeasure ν := hsub.2.1
  have hM1p : (0 : ℝ) < (M₁ : ℝ) := by positivity
  have hmap_supp : ∀ (ρ : Measure ℝ), IsSupportedIn ρ (Set.Icc 0 (1 / (M₁ : ℝ))) →
      IsSupportedIn (ρ.map ((M₁ : ℝ) * ·)) (Set.Icc 0 1) := by
    intro ρ hρ; unfold IsSupportedIn
    rw [Measure.map_apply (measurable_const_mul _) measurableSet_Icc.compl]
    have hsub_s : ((M₁ : ℝ) * ·) ⁻¹' (Set.Icc 0 1)ᶜ ⊆ (Set.Icc 0 (1 / (M₁ : ℝ)))ᶜ := by
      intro x hx hmem; apply hx; refine ⟨mul_nonneg (le_of_lt hM1p) hmem.1, ?_⟩
      have := mul_le_mul_of_nonneg_left hmem.2 (le_of_lt hM1p)
      have h1 : (M₁ : ℝ) * (1 / (M₁ : ℝ)) = 1 := by field_simp
      linarith
    exact measure_mono_null hsub_s hρ
  refine ⟨isProbabilityMeasure_map_measurable (measurable_const_mul _),
    isProbabilityMeasure_map_measurable (measurable_const_mul _),
    hmap_supp ν hν_supp_M1, hmap_supp μ' hμ'_supp, ?_, ?_⟩
  · rw [Measure.conv_comm, ← map_conv_mul_left, hconv', lebScaled_map_mul (div_pos one_pos hM1p) hM1p]
    have : (M₁ : ℝ) * (1 / (M₁ : ℝ)) = 1 := by field_simp
    rw [this, lebScaled_one]
  · intro u hu0 hu1
    set t := u / (M₁ : ℝ)
    have ht0 : 0 < t := div_pos hu0 hM1p
    have ht1 : t < 1 := by
      have : (2 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hM1
      rw [div_lt_one hM1p]; linarith
    have hpre : ((M₁ : ℝ) * ·) ⁻¹' Set.Icc 0 u = Set.Icc 0 t := by
      ext x; simp only [Set.mem_preimage, Set.mem_Icc, t, le_div_iff₀ hM1p]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨by positivity, by linarith⟩
    have hμt : (μ'.map ((M₁ : ℝ) * ·) (Set.Icc 0 u)).toReal / (M₁ : ℝ) ≤ (μ (Set.Icc 0 t)).toReal := by
      rw [Measure.map_apply (measurable_const_mul _) measurableSet_Icc, hpre, hμ_eq]
      exact unifDiscrete_conv_Icc_ge_zero (by omega) _ t
    have hνt : (ν.map ((M₁ : ℝ) * ·) (Set.Icc 0 u)).toReal = (ν (Set.Icc 0 t)).toReal := by
      rw [Measure.map_apply (measurable_const_mul _) measurableSet_Icc, hpre]
    have hbd := hsub.2.2.2.2.2 t ht0 ht1
    have hcomb : ((ν.map ((M₁ : ℝ) * ·) (Set.Icc 0 u)).toReal *
        (μ'.map ((M₁ : ℝ) * ·) (Set.Icc 0 u)).toReal) / (M₁ : ℝ) ≤ lam * u / (M₁ : ℝ) := by
      calc _ = ((μ'.map ((M₁ : ℝ) * ·) (Set.Icc 0 u)).toReal / (M₁ : ℝ)) *
               (ν.map ((M₁ : ℝ) * ·) (Set.Icc 0 u)).toReal := by ring
        _ ≤ (μ (Set.Icc 0 t)).toReal * (ν (Set.Icc 0 t)).toReal := by
              rw [hνt]; exact mul_le_mul_of_nonneg_right hμt ENNReal.toReal_nonneg
        _ ≤ lam * t := hbd
        _ = lam * u / (M₁ : ℝ) := by simp only [t]; ring
    exact (div_le_div_iff_of_pos_right hM1p).mp hcomb

/-- Helper: merging two consecutive discrete uniform factors `unifDiscrete M₁ c ∗ unifDiscrete M₂ (c / M₂) = unifDiscrete (M₁ * M₂) (c / M₂)`. -/
private lemma unifDiscrete_merge {M₁ M₂ : ℕ} (hM1 : 1 ≤ M₁) (hM2 : 1 ≤ M₂) (c : ℝ) :
    unifDiscrete M₁ c ∗ unifDiscrete M₂ (c / (M₂ : ℝ)) =
      unifDiscrete (M₁ * M₂) (c / (M₂ : ℝ)) := by
  have := isProbabilityMeasure_unifDiscrete (by omega : 0 < M₁) c
  have := isProbabilityMeasure_unifDiscrete (by omega : 0 < M₂) (c / (M₂ : ℝ))
  have := isProbabilityMeasure_unifDiscrete (by positivity : 0 < M₁ * M₂) (c / (M₂ : ℝ))
  apply ext_of_ft
  intro ξ
  rw [ft_conv, ft_unifDiscrete (by omega), ft_unifDiscrete (by omega), ft_unifDiscrete (by positivity)]
  have hM2ne : (M₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmul_inv : ((M₁ : ℂ))⁻¹ * ((M₂ : ℂ))⁻¹ = (((M₁ * M₂ : ℕ) : ℂ))⁻¹ := by
    push_cast; rw [mul_inv]
  rw [mul_mul_mul_comm, hmul_inv]; congr 1
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  apply Finset.sum_bij (fun m _ => (m / M₂, m % M₂))
  · intro m hm
    have hm_lt := Finset.mem_range.mp hm
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.div_lt_of_lt_mul (by rwa [mul_comm])),
      Finset.mem_range.mpr (Nat.mod_lt m (by omega))⟩
  · intro m₁ _ m₂ _ heq
    have h1 := congrArg Prod.fst heq; have h2 := congrArg Prod.snd heq
    dsimp only at h1 h2
    have hd1 := Nat.div_add_mod m₁ M₂
    have hd2 := Nat.div_add_mod m₂ M₂
    rw [h1, h2] at hd1; linarith
  · rintro ⟨j, l⟩ hjl
    rcases Finset.mem_product.mp hjl with ⟨hj, hl⟩
    have hj_lt := Finset.mem_range.mp hj
    have hl_lt := Finset.mem_range.mp hl
    refine ⟨j * M₂ + l, Finset.mem_range.mpr ?_, ?_⟩
    · have : j + 1 ≤ M₁ := by omega
      calc j * M₂ + l < j * M₂ + M₂ := by omega
        _ = (j + 1) * M₂ := by ring
        _ ≤ M₁ * M₂ := Nat.mul_le_mul_right M₂ this
    · ext
      · dsimp only
        rw [mul_comm j M₂, Nat.mul_add_div (by omega : 0 < M₂), Nat.div_eq_of_lt hl_lt, add_zero]
      · dsimp only
        rw [Nat.mul_add_mod_of_lt hl_lt]
  · intro m _
    rw [← Complex.exp_add]
    congr 1
    have hdm : ((m : ℝ)) = ((m / M₂ : ℕ) : ℝ) * (M₂ : ℝ) + ((m % M₂ : ℕ) : ℝ) := by
      have hdiv := Nat.div_add_mod m M₂
      exact_mod_cast (show m = m / M₂ * M₂ + m % M₂ by rw [mul_comm]; exact hdiv.symm)
    have harg : (m : ℝ) * (c / (M₂ : ℝ)) = ((m / M₂ : ℕ) : ℝ) * c + ((m % M₂ : ℕ) : ℝ) * (c / (M₂ : ℝ)) := by
      rw [hdm]; field_simp
    have hargC : ((m : ℝ) : ℂ) * ((c / (M₂ : ℝ) : ℝ) : ℂ) =
        (((m / M₂ : ℕ) : ℝ) : ℂ) * (c : ℂ) + (((m % M₂ : ℕ) : ℝ) : ℂ) * ((c / (M₂ : ℝ) : ℝ) : ℂ) := by
      exact_mod_cast harg
    dsimp only
    rw [hargC]; ring

/-- Exclusion of Type I factors under `lam < 8/5`. -/
private lemma subcritical_no_dirac_remainder {μ ν μ' ν' : Measure ℝ} {lam : ℝ} {M₁ M₂ : ℕ}
    (hsub : IsSubcriticalPair μ ν lam) (hlam : lam < 8 / 5) (hM1 : 2 ≤ M₁) (hM2 : 2 ≤ M₂)
    [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν']
    (hμ'_supp : IsSupportedIn μ' (Set.Icc 0 (1 / ((M₁ : ℝ) * (M₂ : ℝ)))))
    (_hν'_supp : IsSupportedIn ν' (Set.Icc 0 (1 / ((M₁ : ℝ) * (M₂ : ℝ)))))
    (hconv' : μ' ∗ ν' = lebScaled (1 / ((M₁ : ℝ) * (M₂ : ℝ))))
    (hμ_eq : μ = unifDiscrete M₁ (1 / (M₁ : ℝ)) ∗ μ')
    (hν_eq : ν = unifDiscrete M₂ (1 / ((M₁ : ℝ) * (M₂ : ℝ))) ∗ ν') :
    μ' ≠ Measure.dirac 0 ∧ ν' ≠ Measure.dirac 0 := by
  have hM1p : (0 : ℝ) < (M₁ : ℝ) := by positivity
  have hM2p : (0 : ℝ) < (M₂ : ℝ) := by positivity
  have hM12p : (0 : ℝ) < (M₁ : ℝ) * (M₂ : ℝ) := mul_pos hM1p hM2p
  constructor
  · intro hμ0
    -- μ' = δ₀ implies ν' = lebScaled (1/(M₁ M₂)), hence ν = lebScaled (1/M₁), μ = unifDiscrete M₁ (1/M₁)
    -- At u = 1 / M₁ ∈ (0, 1): μ([0, 1/M₁]) ≥ 2 / M₁, ν([0, 1/M₁]) = 1, giving 2 ≤ lam!
    have hν' : ν' = lebScaled (1 / ((M₁ : ℝ) * (M₂ : ℝ))) := by
      rw [hμ0, Measure.dirac_conv] at hconv'; simpa using hconv'
    have hν_leb : ν = lebScaled (1 / (M₁ : ℝ)) := by
      rw [hν_eq, hν', unifDiscrete_conv_lebScaled (by omega) (div_pos one_pos hM12p)]
      congr 1; field_simp
    have hu0 : (0 : ℝ) < 1 / (M₁ : ℝ) := div_pos one_pos hM1p
    have hu1 : (1 : ℝ) / (M₁ : ℝ) < 1 := by
      rw [div_lt_one hM1p]; exact_mod_cast (show 1 < M₁ by omega)
    have hμu : (2 : ℝ) / (M₁ : ℝ) ≤ (μ (Set.Icc 0 (1 / (M₁ : ℝ)))).toReal := by
      rw [hμ_eq, hμ0]
      have hdir : IsSupportedIn (Measure.dirac (0 : ℝ)) (Set.Icc 0 0) := by
        unfold IsSupportedIn
        have h0in : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 0 := ⟨le_rfl, le_rfl⟩
        rw [Measure.dirac_apply' _ measurableSet_Icc.compl,
          Set.indicator_of_notMem (Set.notMem_compl_iff.mpr h0in)]
      have := unifDiscrete_conv_Icc_ge (M := M₁) (by omega) (step := 1 / (M₁ : ℝ)) (by positivity) hdir hM1
        (t := 1 / (M₁ : ℝ)) (by norm_num) (le_of_lt hu0)
      simpa using this
    have hνu : (ν (Set.Icc 0 (1 / (M₁ : ℝ)))).toReal = 1 := by
      have h1 : ν (Set.Icc 0 (1 / (M₁ : ℝ))) = 1 := by
        have := isProbabilityMeasure_lebScaled hu0
        have hsp := measure_add_measure_compl (s := Set.Icc (0 : ℝ) (1 / (M₁ : ℝ)))
          (μ := lebScaled (1 / (M₁ : ℝ))) measurableSet_Icc
        rw [lebScaled_supported, add_zero, measure_univ] at hsp
        rwa [hν_leb]
      rw [h1, ENNReal.toReal_one]
    have hbd := hsub.2.2.2.2.2 (1 / (M₁ : ℝ)) hu0 hu1
    rw [hνu, mul_one] at hbd
    have : (2 : ℝ) ≤ lam := by
      have h1 := mul_le_mul_of_nonneg_left hbd (le_of_lt hM1p)
      have h2 : (M₁ : ℝ) * (2 / (M₁ : ℝ)) = 2 := by field_simp
      have h3 : (M₁ : ℝ) * (lam * (1 / (M₁ : ℝ))) = lam := by field_simp
      nlinarith
    linarith
  · intro hν0
    -- ν' = δ₀ implies μ' = lebScaled (1/(M₁ M₂)), at u = 1/(M₁ M₂) ∈ (0, 1):
    -- μ([0, u]) ≥ 1/M₁, ν([0, u]) ≥ 2/M₂, giving 2 ≤ lam!
    have hu0 : (0 : ℝ) < 1 / ((M₁ : ℝ) * (M₂ : ℝ)) := div_pos one_pos hM12p
    have hu1 : (1 : ℝ) / ((M₁ : ℝ) * (M₂ : ℝ)) < 1 := by
      rw [div_lt_one hM12p]
      have h1 : (2 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hM1
      have h2 : (2 : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hM2
      nlinarith
    have hμu : (1 : ℝ) / (M₁ : ℝ) ≤ (μ (Set.Icc 0 (1 / ((M₁ : ℝ) * (M₂ : ℝ))))).toReal := by
      rw [hμ_eq]
      have := unifDiscrete_conv_Icc_ge (M := M₁) (by omega) (step := 1 / (M₁ : ℝ)) (by positivity) hμ'_supp (by omega : 1 ≤ M₁)
        (t := 1 / ((M₁ : ℝ) * (M₂ : ℝ))) (by norm_num) (le_of_lt hu0)
      simpa using this
    have hνu : (2 : ℝ) / (M₂ : ℝ) ≤ (ν (Set.Icc 0 (1 / ((M₁ : ℝ) * (M₂ : ℝ))))).toReal := by
      rw [hν_eq, hν0]
      have hdir : IsSupportedIn (Measure.dirac (0 : ℝ)) (Set.Icc 0 0) := by
        unfold IsSupportedIn
        have h0in : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 0 := ⟨le_rfl, le_rfl⟩
        rw [Measure.dirac_apply' _ measurableSet_Icc.compl,
          Set.indicator_of_notMem (Set.notMem_compl_iff.mpr h0in)]
      have := unifDiscrete_conv_Icc_ge (M := M₂) (by omega) (step := 1 / ((M₁ : ℝ) * (M₂ : ℝ))) (by positivity) hdir hM2
        (t := 1 / ((M₁ : ℝ) * (M₂ : ℝ))) (by norm_num) (le_of_lt hu0)
      simpa using this
    have hbd := hsub.2.2.2.2.2 (1 / ((M₁ : ℝ) * (M₂ : ℝ))) hu0 hu1
    have hmul := mul_le_mul hμu hνu (by positivity) (by positivity)
    have h1 : (1 / (M₁ : ℝ)) * (2 / (M₂ : ℝ)) = 2 / ((M₁ : ℝ) * (M₂ : ℝ)) := by ring
    have h2 : 2 / ((M₁ : ℝ) * (M₂ : ℝ)) ≤ lam * (1 / ((M₁ : ℝ) * (M₂ : ℝ))) := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt hM12p)
    have h4 : (M₁ : ℝ) * (M₂ : ℝ) * (2 / ((M₁ : ℝ) * (M₂ : ℝ))) = 2 := by field_simp
    have h5 : (M₁ : ℝ) * (M₂ : ℝ) * (lam * (1 / ((M₁ : ℝ) * (M₂ : ℝ)))) = lam := by field_simp
    linarith

/-- One locked binary step of Claim 3b: given a subcritical pair `(μ, ν)` with `lam < 8/5` in the
form `(4.1)` with `(M₁, 2)`, the next rescaled pair `(μ_next, ν_next)` AGAIN factors WITHOUT swapping
orientation and with `(2, 2)`! -/
private lemma subcritical_next_binary_step {μ ν μ' ν' : Measure ℝ} {lam : ℝ} {M₁ : ℕ}
    (hsub : IsSubcriticalPair μ ν lam) (hlam : lam < 8 / 5) (hM1 : 2 ≤ M₁)
    [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν']
    (hμ'_supp : IsSupportedIn μ' (Set.Icc 0 (1 / ((M₁ : ℝ) * (2 : ℕ)))))
    (hν'_supp : IsSupportedIn ν' (Set.Icc 0 (1 / ((M₁ : ℝ) * (2 : ℕ)))))
    (hconv' : μ' ∗ ν' = lebScaled (1 / ((M₁ : ℝ) * (2 : ℕ))))
    (hμ_eq : μ = unifDiscrete M₁ (1 / (M₁ : ℝ)) ∗ μ')
    (hν_eq : ν = unifDiscrete 2 (1 / ((M₁ : ℝ) * (2 : ℕ))) ∗ ν') :
    let μ_next := μ'.map (((M₁ : ℝ) * (2 : ℕ)) * ·)
    let ν_next := ν'.map (((M₁ : ℝ) * (2 : ℕ)) * ·)
    IsSubcriticalPair μ_next ν_next lam ∧
    ∃ (μ'' ν'' : Measure ℝ), IsProbabilityMeasure μ'' ∧ IsProbabilityMeasure ν'' ∧
      IsSupportedIn μ'' (Set.Icc 0 (1 / ((2 : ℕ) * (2 : ℕ) : ℝ))) ∧
      IsSupportedIn ν'' (Set.Icc 0 (1 / ((2 : ℕ) * (2 : ℕ) : ℝ))) ∧
      μ'' ∗ ν'' = lebScaled (1 / ((2 : ℕ) * (2 : ℕ) : ℝ)) ∧
      μ_next = unifDiscrete 2 (1 / (2 : ℝ)) ∗ μ'' ∧
      ν_next = unifDiscrete 2 (1 / ((2 : ℕ) * (2 : ℕ) : ℝ)) ∗ ν'' := by
  intro μ_next ν_next
  have hsub_next : IsSubcriticalPair μ_next ν_next lam :=
    scaling_invariance_two_step hsub hM1 le_rfl hμ'_supp hν'_supp hconv' hμ_eq hν_eq
  have hM1p : (0 : ℝ) < (M₁ : ℝ) := by positivity
  have hM12p : (0 : ℝ) < (M₁ : ℝ) * (2 : ℕ) := by positivity
  have hnodir := subcritical_no_dirac_remainder hsub hlam hM1 le_rfl hμ'_supp hν'_supp hconv' hμ_eq hν_eq
  have hdir0 : Measure.map (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·) (Measure.dirac (0 : ℝ)) = Measure.dirac 0 := by
    ext s hs
    rw [Measure.map_apply (measurable_const_mul _) hs,
        Measure.dirac_apply' _ ((measurable_const_mul _) hs), Measure.dirac_apply' _ hs]
    by_cases h0 : (0 : ℝ) ∈ s
    · have h0' : (0 : ℝ) ∈ (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·) ⁻¹' s := by simpa [Set.mem_preimage] using h0
      rw [Set.indicator_of_mem h0', Set.indicator_of_mem h0]
    · have h0' : (0 : ℝ) ∉ (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·) ⁻¹' s := by simpa [Set.mem_preimage] using h0
      rw [Set.indicator_of_notMem h0', Set.indicator_of_notMem h0]
  have hμn_ne : μ_next ≠ Measure.dirac 0 := by
    intro h0; apply hnodir.1
    have hback : μ' = μ_next.map (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·) := by
      simp only [μ_next, Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
      have : (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·) ∘ (((M₁ : ℝ) * (2 : ℕ)) * ·) = id := by ext x; simp; field_simp
      rw [this, Measure.map_id]
    rw [h0, hdir0] at hback; exact hback
  have hνn_ne : ν_next ≠ Measure.dirac 0 := by
    intro h0; apply hnodir.2
    have hback : ν' = ν_next.map (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·) := by
      simp only [ν_next, Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
      have : (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·) ∘ (((M₁ : ℝ) * (2 : ℕ)) * ·) = id := by ext x; simp; field_simp
      rw [this, Measure.map_id]
    rw [h0, hdir0] at hback; exact hback
  have : IsProbabilityMeasure μ_next := hsub_next.1
  have : IsProbabilityMeasure ν_next := hsub_next.2.1
  obtain ⟨M₃, M₄, α, β, hM3, hM4, hαp, hβp, hαs, hβs, hcv, hor⟩ :=
    gabardo_lai_single_step hsub_next.2.2.2.2.1 hsub_next.2.2.1 hsub_next.2.2.2.1 hμn_ne hνn_ne
  -- Force M₄ = 2 by Lemma 4.2 on (μ_next, ν_next) (or swapped)
  have hM4_eq2 : M₄ = 2 := by
    have hbd : (2 * (M₄ : ℝ) + 2) / ((M₄ : ℝ) + 2) ≤ lam := by
      rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact lemma_4_2 hsub_next hM3 hM4 hαs hβs hcv h1 h2
      · have hswap : IsSubcriticalPair ν_next μ_next lam :=
          ⟨hsub_next.2.1, hsub_next.1, hsub_next.2.2.2.1, hsub_next.2.2.1,
           by rw [Measure.conv_comm]; exact hsub_next.2.2.2.2.1,
           fun u hu0 hu1 => by rw [mul_comm]; exact hsub_next.2.2.2.2.2 u hu0 hu1⟩
        exact lemma_4_2 hswap hM3 hM4 hαs hβs hcv h1 h2
    by_contra hne
    have hM4_3 : (3 : ℝ) ≤ (M₄ : ℝ) := by exact_mod_cast (show 3 ≤ M₄ by omega)
    have hge85 : (8 / 5 : ℝ) ≤ (2 * (M₄ : ℝ) + 2) / ((M₄ : ℝ) + 2) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
    linarith
  subst hM4_eq2
  -- Rule out orientation swap (Or.inr) by merging unifDiscrete 2 and unifDiscrete M₃ into M' = 2 * M₃ ≥ 4
  rcases hor with ⟨hμn_eq, hνn_eq⟩ | ⟨hνn_eq, hμn_eq⟩
  · -- No swap: prove M₃ = 2 via single-factor stripping (4.4)
    have hM3_eq2 : M₃ = 2 := by
      -- Pull back β? No: apply scaling_invariance_one_step to (μ, ν)!
      -- ν.map (M₁ * ·) and μ'.map (M₁ * ·) satisfy IsSubcriticalPair with factor (2, M₃)!
      have hM3p : (0 : ℝ) < (M₃ : ℝ) := by positivity
      have hμ'_supp_M1 : IsSupportedIn μ' (Set.Icc 0 (1 / (M₁ : ℝ))) := by
        unfold IsSupportedIn
        have hsub_s : (Set.Icc (0 : ℝ) (1 / (M₁ : ℝ)))ᶜ ⊆ (Set.Icc 0 (1 / ((M₁ : ℝ) * (2 : ℕ))))ᶜ :=
          Set.compl_subset_compl.mpr (fun x hx => ⟨hx.1, le_trans hx.2 (by
            rw [div_le_div_iff₀ hM12p hM1p]; norm_num; linarith)⟩)
        exact measure_mono_null hsub_s hμ'_supp
      have hν_supp_M1 : IsSupportedIn ν (Set.Icc 0 (1 / (M₁ : ℝ))) := by
        rw [hν_eq]
        have hunif_s : IsSupportedIn (unifDiscrete 2 (1 / ((M₁ : ℝ) * (2 : ℕ)))) (Set.Icc 0 (1 / ((M₁ : ℝ) * (2 : ℕ)))) := by
          unfold IsSupportedIn unifDiscrete
          rw [Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
          have hz : ∑ j ∈ Finset.range 2, Measure.dirac ((j : ℝ) * (1 / ((M₁ : ℝ) * (2 : ℕ))))
              (Set.Icc 0 (1 / ((M₁ : ℝ) * (2 : ℕ))))ᶜ = 0 := by
            apply Finset.sum_eq_zero; intro j hj
            rw [Measure.dirac_apply' _ measurableSet_Icc.compl, Set.indicator_of_notMem]
            rw [Set.notMem_compl_iff]
            have hj_le : (j : ℝ) ≤ 1 := by exact_mod_cast (show j ≤ 1 by have := Finset.mem_range.mp hj; omega)
            exact ⟨by positivity, by nlinarith [div_pos one_pos hM12p]⟩
          rw [hz, mul_zero]
        have : IsProbabilityMeasure (unifDiscrete 2 (1 / ((M₁ : ℝ) * (2 : ℕ)))) :=
          isProbabilityMeasure_unifDiscrete (by norm_num : 0 < 2) _
        have h1 := conv_supported_Icc hunif_s hν'_supp
        have heq : 1 / ((M₁ : ℝ) * (2 : ℕ)) + 1 / ((M₁ : ℝ) * (2 : ℕ)) = 1 / (M₁ : ℝ) := by push_cast; field_simp; ring
        rwa [zero_add, heq] at h1
      have hconv_M1 : μ' ∗ ν = lebScaled (1 / (M₁ : ℝ)) := by
        have := isProbabilityMeasure_unifDiscrete (by norm_num : 0 < 2) (1 / ((M₁ : ℝ) * (2 : ℕ)))
        rw [hν_eq, Measure.conv_comm μ', Measure.conv_assoc, Measure.conv_comm ν' μ',
            hconv', unifDiscrete_conv_lebScaled (by norm_num) (div_pos one_pos hM12p)]
        congr 1; push_cast; field_simp
      have hsub_1 := scaling_invariance_one_step hsub hM1 hμ'_supp_M1 hν_supp_M1 hconv_M1 hμ_eq
      -- Express ν_hat := ν.map (M₁ * ·) and μ_hat := μ'.map (M₁ * ·) via (2, M₃)
      let ν_hat1 := ν_next.map ((1 / 2 : ℝ) * ·)
      let μ_hat1 := α.map ((1 / 2 : ℝ) * ·)
      have : IsProbabilityMeasure ν_hat1 := isProbabilityMeasure_map_measurable (measurable_const_mul _)
      have : IsProbabilityMeasure μ_hat1 := isProbabilityMeasure_map_measurable (measurable_const_mul _)
      have hν_hat_eq : ν.map ((M₁ : ℝ) * ·) = unifDiscrete 2 (1 / (2 : ℝ)) ∗ ν_hat1 := by
        have := isProbabilityMeasure_unifDiscrete (by norm_num : 0 < 2) (1 / ((M₁ : ℝ) * (2 : ℕ)))
        rw [hν_eq, map_conv_mul_left, unifDiscrete_map_mul]
        congr 1
        · congr 1; push_cast; field_simp
        · simp only [ν_hat1, ν_next, Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
          congr 1; ext x; simp only [Function.comp_apply]; push_cast; ring
      have hμ_hat_eq : μ'.map ((M₁ : ℝ) * ·) = unifDiscrete M₃ (1 / ((2 : ℕ) * (M₃ : ℝ))) ∗ μ_hat1 := by
        have := isProbabilityMeasure_unifDiscrete (by omega : 0 < M₃) (1 / (M₃ : ℝ))
        have hback : μ'.map ((M₁ : ℝ) * ·) = μ_next.map ((1 / 2 : ℝ) * ·) := by
          simp only [μ_next, Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
          congr 1; ext x; simp only [Function.comp_apply]; push_cast; ring
        rw [hback, hμn_eq, map_conv_mul_left, unifDiscrete_map_mul]
        congr 1; congr 1; push_cast; field_simp
      have hconv_hat : ν_hat1 ∗ μ_hat1 = lebScaled (1 / ((2 : ℕ) * (M₃ : ℝ))) := by
        have hαν : α ∗ ν_next = lebScaled (1 / (M₃ : ℝ)) := by
          have := isProbabilityMeasure_unifDiscrete (by omega : 0 < M₃) (1 / (M₃ : ℝ))
          have := isProbabilityMeasure_unifDiscrete (by norm_num : 0 < 2) (1 / ((M₃ : ℝ) * (2 : ℕ)))
          rw [hνn_eq, Measure.conv_comm α, Measure.conv_assoc, Measure.conv_comm β α,
              hcv, unifDiscrete_conv_lebScaled (by norm_num) (div_pos one_pos (by positivity))]
          congr 1; push_cast; field_simp
        rw [Measure.conv_comm, ← map_conv_mul_left, hαν, lebScaled_map_mul (div_pos one_pos hM3p) (by norm_num)]
        congr 1; push_cast; field_simp
      have hpull_half : ∀ (ρ : Measure ℝ), IsSupportedIn ρ (Set.Icc 0 (1 / (M₃ : ℝ))) →
          IsSupportedIn (ρ.map ((1 / 2 : ℝ) * ·)) (Set.Icc 0 (1 / ((2 : ℕ) * (M₃ : ℝ)))) := by
        intro ρ hρ; unfold IsSupportedIn
        rw [Measure.map_apply (measurable_const_mul _) measurableSet_Icc.compl]
        have hsub_s : ((1 / 2 : ℝ) * ·) ⁻¹' (Set.Icc 0 (1 / ((2 : ℕ) * (M₃ : ℝ))))ᶜ ⊆ (Set.Icc 0 (1 / (M₃ : ℝ)))ᶜ := by
          intro x hx hmem; apply hx; refine ⟨mul_nonneg (by norm_num) hmem.1, ?_⟩
          have : (1 / 2 : ℝ) * (1 / (M₃ : ℝ)) = 1 / ((2 : ℕ) * (M₃ : ℝ)) := by push_cast; field_simp
          linarith [mul_le_mul_of_nonneg_left hmem.2 (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        exact measure_mono_null hsub_s hρ
      have hα_supp_M3 : IsSupportedIn α (Set.Icc 0 (1 / (M₃ : ℝ))) := by
        unfold IsSupportedIn
        have hsub_s : (Set.Icc (0 : ℝ) (1 / (M₃ : ℝ)))ᶜ ⊆ (Set.Icc 0 (1 / ((M₃ : ℝ) * (2 : ℕ))))ᶜ :=
          Set.compl_subset_compl.mpr (fun x hx => ⟨hx.1, le_trans hx.2 (by
            rw [div_le_div_iff₀ (by positivity) hM3p]; norm_num; linarith)⟩)
        exact measure_mono_null hsub_s hαs
      have hνn_supp_M3 : IsSupportedIn ν_next (Set.Icc 0 (1 / (M₃ : ℝ))) := by
        rw [hνn_eq]
        have hunif_s : IsSupportedIn (unifDiscrete 2 (1 / ((M₃ : ℝ) * (2 : ℕ)))) (Set.Icc 0 (1 / ((M₃ : ℝ) * (2 : ℕ)))) := by
          unfold IsSupportedIn unifDiscrete
          rw [Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
          have hz : ∑ j ∈ Finset.range 2, Measure.dirac ((j : ℝ) * (1 / ((M₃ : ℝ) * (2 : ℕ))))
              (Set.Icc 0 (1 / ((M₃ : ℝ) * (2 : ℕ))))ᶜ = 0 := by
            apply Finset.sum_eq_zero; intro j hj
            rw [Measure.dirac_apply' _ measurableSet_Icc.compl, Set.indicator_of_notMem]
            rw [Set.notMem_compl_iff]
            have hj_le : (j : ℝ) ≤ 1 := by exact_mod_cast (show j ≤ 1 by have := Finset.mem_range.mp hj; omega)
            exact ⟨by positivity, by nlinarith [div_pos one_pos (show (0 : ℝ) < (M₃ : ℝ) * (2 : ℕ) by positivity)]⟩
          rw [hz, mul_zero]
        have : IsProbabilityMeasure (unifDiscrete 2 (1 / ((M₃ : ℝ) * (2 : ℕ)))) :=
          isProbabilityMeasure_unifDiscrete (by norm_num : 0 < 2) _
        have h1 := conv_supported_Icc hunif_s hβs
        have heq : 1 / ((M₃ : ℝ) * (2 : ℕ)) + 1 / ((M₃ : ℝ) * (2 : ℕ)) = 1 / (M₃ : ℝ) := by push_cast; field_simp; ring
        rwa [zero_add, heq] at h1
      have hbd := lemma_4_2 hsub_1 le_rfl hM3 (hpull_half ν_next hνn_supp_M3) (hpull_half α hα_supp_M3)
        hconv_hat hν_hat_eq hμ_hat_eq
      by_contra hne
      have hM3_3 : (3 : ℝ) ≤ (M₃ : ℝ) := by exact_mod_cast (show 3 ≤ M₃ by omega)
      have hge85 : (8 / 5 : ℝ) ≤ (2 * (M₃ : ℝ) + 2) / ((M₃ : ℝ) + 2) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
      linarith
    subst hM3_eq2
    refine ⟨hsub_next, α, β, hαp, hβp, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hαs
    · simpa using hβs
    · simpa using hcv
    · simpa using hμn_eq
    · simpa using hνn_eq
  · -- Swap case: merge unifDiscrete 2 and unifDiscrete M₃ into unifDiscrete (2 * M₃), violating lam < 8/5!
    exfalso
    set M' := 2 * M₃
    have hM'4 : 4 ≤ M' := by omega
    have hM3p : (0 : ℝ) < (M₃ : ℝ) := by positivity
    let ν'' := α.map (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·)
    have : IsProbabilityMeasure ν'' := isProbabilityMeasure_map_measurable (measurable_const_mul _)
    have hμ'_back : μ' = μ_next.map (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·) := by
      simp only [μ_next, Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
      have : (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·) ∘ (((M₁ : ℝ) * (2 : ℕ)) * ·) = id := by ext x; simp; field_simp
      rw [this, Measure.map_id]
    have hν'_back : ν' = ν_next.map (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·) := by
      simp only [ν_next, Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
      have : (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·) ∘ (((M₁ : ℝ) * (2 : ℕ)) * ·) = id := by ext x; simp; field_simp
      rw [this, Measure.map_id]
    have hν_merged : ν = unifDiscrete M' (1 / ((M₁ : ℝ) * (M' : ℝ))) ∗ ν'' := by
      have := isProbabilityMeasure_unifDiscrete (by norm_num : 0 < 2) (1 / ((M₁ : ℝ) * (2 : ℕ)))
      have := isProbabilityMeasure_unifDiscrete (by omega : 0 < M₃) (1 / (M₃ : ℝ))
      have := isProbabilityMeasure_unifDiscrete (by omega : 0 < M₃) (((M₁ : ℝ) * (2 : ℕ))⁻¹ * (1 / (M₃ : ℝ)))
      rw [hν_eq, hν'_back, hνn_eq, map_conv_mul_left, unifDiscrete_map_mul, ← Measure.conv_assoc]
      have hstep_eq : ((M₁ : ℝ) * (2 : ℕ))⁻¹ * (1 / (M₃ : ℝ)) = (1 / ((M₁ : ℝ) * (2 : ℕ))) / (M₃ : ℝ) := by field_simp
      rw [hstep_eq, unifDiscrete_merge (by norm_num) (by omega)]
      congr 2; simp only [M']; push_cast; field_simp
    have hμ'_conv_ν'' : μ' ∗ ν'' = lebScaled (1 / ((M₁ : ℝ) * (M' : ℝ))) := by
      have hαμ : α ∗ μ_next = lebScaled (1 / (M₃ : ℝ)) := by
        have := isProbabilityMeasure_unifDiscrete (by norm_num : 0 < 2) (1 / ((M₃ : ℝ) * (2 : ℕ)))
        rw [hμn_eq, Measure.conv_comm α, Measure.conv_assoc, Measure.conv_comm β α,
            hcv, unifDiscrete_conv_lebScaled (by norm_num) (div_pos one_pos (by positivity))]
        congr 1; push_cast; field_simp
      rw [hμ'_back, Measure.conv_comm, ← map_conv_mul_left, hαμ,
          lebScaled_map_mul (div_pos one_pos hM3p) (inv_pos.mpr hM12p)]
      congr 1; simp only [M']; push_cast; field_simp
    have hpull : ∀ (ρ : Measure ℝ), IsSupportedIn ρ (Set.Icc 0 (1 / (M₃ : ℝ))) →
        IsSupportedIn (ρ.map (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·)) (Set.Icc 0 (1 / ((M₁ : ℝ) * (M' : ℝ)))) := by
      intro ρ hρ; unfold IsSupportedIn
      rw [Measure.map_apply (measurable_const_mul _) measurableSet_Icc.compl]
      have hsub_s : (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·) ⁻¹' (Set.Icc 0 (1 / ((M₁ : ℝ) * (M' : ℝ))))ᶜ ⊆ (Set.Icc 0 (1 / (M₃ : ℝ)))ᶜ := by
        intro x hx hmem; apply hx; refine ⟨mul_nonneg (inv_nonneg.mpr (le_of_lt hM12p)) hmem.1, ?_⟩
        have : ((M₁ : ℝ) * (2 : ℕ))⁻¹ * (1 / (M₃ : ℝ)) = 1 / ((M₁ : ℝ) * (M' : ℝ)) := by
          simp only [M']; push_cast; field_simp
        linarith [mul_le_mul_of_nonneg_left hmem.2 (inv_nonneg.mpr (le_of_lt hM12p))]
      exact measure_mono_null hsub_s hρ
    have hα_s3 : IsSupportedIn α (Set.Icc 0 (1 / (M₃ : ℝ))) := by
      unfold IsSupportedIn
      exact measure_mono_null (Set.compl_subset_compl.mpr (fun x hx => ⟨hx.1, le_trans hx.2 (by
        rw [div_le_div_iff₀ (by positivity) hM3p]; norm_num; linarith)⟩)) hαs
    have hμn_s3 : IsSupportedIn μ_next (Set.Icc 0 (1 / (M₃ : ℝ))) := by
      rw [hμn_eq]
      have hunif_s : IsSupportedIn (unifDiscrete 2 (1 / ((M₃ : ℝ) * (2 : ℕ)))) (Set.Icc 0 (1 / ((M₃ : ℝ) * (2 : ℕ)))) := by
        unfold IsSupportedIn unifDiscrete; rw [Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
        have hz : ∑ j ∈ Finset.range 2, Measure.dirac ((j : ℝ) * (1 / ((M₃ : ℝ) * (2 : ℕ))))
            (Set.Icc 0 (1 / ((M₃ : ℝ) * (2 : ℕ))))ᶜ = 0 := by
          apply Finset.sum_eq_zero; intro j hj
          rw [Measure.dirac_apply' _ measurableSet_Icc.compl, Set.indicator_of_notMem]
          rw [Set.notMem_compl_iff]
          have hj_le : (j : ℝ) ≤ 1 := by exact_mod_cast (show j ≤ 1 by have := Finset.mem_range.mp hj; omega)
          exact ⟨by positivity, by nlinarith [div_pos one_pos (show (0 : ℝ) < (M₃ : ℝ) * (2 : ℕ) by positivity)]⟩
        rw [hz, mul_zero]
      have : IsProbabilityMeasure (unifDiscrete 2 (1 / ((M₃ : ℝ) * (2 : ℕ)))) :=
        isProbabilityMeasure_unifDiscrete (by norm_num : 0 < 2) _
      have h1 := conv_supported_Icc hunif_s hβs
      have heq : 1 / ((M₃ : ℝ) * (2 : ℕ)) + 1 / ((M₃ : ℝ) * (2 : ℕ)) = 1 / (M₃ : ℝ) := by push_cast; field_simp; ring
      rwa [zero_add, heq] at h1
    have hμ'_s' : IsSupportedIn μ' (Set.Icc 0 (1 / ((M₁ : ℝ) * (M' : ℝ)))) := by
      rw [hμ'_back]; exact hpull μ_next hμn_s3
    have hbd := lemma_4_2 hsub hM1 (by omega : 2 ≤ M') hμ'_s' (hpull α hα_s3) hμ'_conv_ν'' hμ_eq hν_merged
    have hM'r : (4 : ℝ) ≤ (M' : ℝ) := by exact_mod_cast hM'4
    have hge53 : (5 / 3 : ℝ) ≤ (2 * (M' : ℝ) + 2) / ((M' : ℝ) + 2) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
    linarith

/-- Self-similarity of `cantorNu`: `unifDiscrete 2 (1/4) ∗ cantorNu.map ((1/4) * ·) = cantorNu`. -/
lemma cantorNu_self_similar :
    unifDiscrete 2 (1 / 4 : ℝ) ∗ cantorNu.map ((1 / 4 : ℝ) * ·) = cantorNu := by
  have := isProbabilityMeasure_unifDiscrete (by norm_num : 0 < 2) (1 / 4 : ℝ)
  have := isProbabilityMeasure_map_measurable (μ := cantorNu) (measurable_const_mul (1 / 4 : ℝ))
  apply ext_of_ft
  intro ξ
  rw [ft_conv, ft_map_mul]
  -- Compare with limit of convBinNu (k + 1) 1
  have hlim1 := tendsto_ft_convBinNu_one ξ
  have hlim2 := (tendsto_ft_convBinNu_one ((1 / 4 : ℝ) * ξ)).const_mul (ft (unifDiscrete 2 (1 / 4 : ℝ)) ξ)
  have hshift : ∀ k : ℕ, ft (unifDiscrete 2 (1 / 4 : ℝ)) ξ * ft (convBinNu k 1) ((1 / 4 : ℝ) * ξ) =
      ft (convBinNu (k + 1) 1) ξ := by
    intro k
    rw [ft_unifDiscrete (by norm_num), ft_convBinNu, ft_convBinNu, Finset.prod_range_succ']
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, pow_one, Complex.ofReal_zero, zero_mul,
      mul_zero, Complex.exp_zero, Complex.ofReal_one, one_mul]
    rw [mul_comm (∏ i ∈ Finset.range k, _)]
    have hfirst : (2 : ℂ)⁻¹ * (1 + Complex.exp (-2 * Real.pi * ξ * ((1 / 4 : ℝ) : ℂ) * Complex.I)) =
        (1 + Complex.exp (-2 * Real.pi * ξ * (1 / ((4 : ℝ) : ℂ)) * Complex.I)) / 2 := by
      push_cast; ring
    rw [hfirst]; congr 1
    apply Finset.prod_congr rfl; intro i _
    congr 3; push_cast; rw [pow_succ']; ring_nf
  have hlim3 : Tendsto (fun k : ℕ => ft (convBinNu (k + 1) 1) ξ) atTop (𝓝 (ft cantorNu ξ)) :=
    hlim1.comp (tendsto_add_atTop_nat 1)
  simp_rw [hshift] at hlim2
  exact tendsto_nhds_unique hlim2 hlim3

/-- Self-similarity of `cantorMu`: `unifDiscrete 2 (1/2) ∗ cantorMu.map ((1/4) * ·) = cantorMu`. -/
lemma cantorMu_self_similar :
    unifDiscrete 2 (1 / 2 : ℝ) ∗ cantorMu.map ((1 / 4 : ℝ) * ·) = cantorMu := by
  have h := congrArg (Measure.map ((2 : ℝ) * ·)) cantorNu_self_similar
  have := isProbabilityMeasure_unifDiscrete (by norm_num : 0 < 2) (1 / 4 : ℝ)
  have := isProbabilityMeasure_map_measurable (μ := cantorNu) (measurable_const_mul (1 / 4 : ℝ))
  rw [map_conv_mul_left, unifDiscrete_map_mul, ← cantorMu_eq_map_two] at h
  have h1 : (2 : ℝ) * (1 / 4 : ℝ) = 1 / 2 := by norm_num
  have h2 : (cantorNu.map ((1 / 4 : ℝ) * ·)).map ((2 : ℝ) * ·) = cantorMu.map ((1 / 4 : ℝ) * ·) := by
    rw [cantorMu_eq_map_two, Measure.map_map (measurable_const_mul _) (measurable_const_mul _),
        Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
    congr 1; ext x; simp only [Function.comp_apply]; ring
  rwa [h1, h2] at h

/-- A subcritical `(2, 2)` pair equals `(cantorMu, cantorNu)`. -/
private lemma eq_cantor_of_binary_step {μ ν : Measure ℝ} {lam : ℝ}
    (hsub : IsSubcriticalPair μ ν lam) (hlam : lam < 8 / 5)
    {α₀ β₀ : Measure ℝ} [IsProbabilityMeasure α₀] [IsProbabilityMeasure β₀]
    (hα0s : IsSupportedIn α₀ (Set.Icc 0 (1 / ((2 : ℕ) * (2 : ℕ) : ℝ))))
    (hβ0s : IsSupportedIn β₀ (Set.Icc 0 (1 / ((2 : ℕ) * (2 : ℕ) : ℝ))))
    (hcv0 : α₀ ∗ β₀ = lebScaled (1 / ((2 : ℕ) * (2 : ℕ) : ℝ)))
    (hμ_eq : μ = unifDiscrete 2 (1 / (2 : ℝ)) ∗ α₀)
    (hν_eq : ν = unifDiscrete 2 (1 / ((2 : ℕ) * (2 : ℕ) : ℝ)) ∗ β₀) :
    μ = cantorMu ∧ ν = cantorNu := by
  have : IsProbabilityMeasure μ := hsub.1
  have : IsProbabilityMeasure ν := hsub.2.1
  -- Inductive tower for all k : ℕ
  have htower : ∀ k : ℕ, ∃ (σ_k τ_k : Measure ℝ),
      IsProbabilityMeasure σ_k ∧ IsProbabilityMeasure τ_k ∧
      IsSupportedIn σ_k (Set.Icc 0 (1 / (4 : ℝ) ^ (k + 1))) ∧
      IsSupportedIn τ_k (Set.Icc 0 (1 / (4 : ℝ) ^ (k + 1))) ∧
      σ_k ∗ τ_k = lebScaled (1 / (4 : ℝ) ^ (k + 1)) ∧
      μ = convBinMu (k + 1) 1 ∗ σ_k ∧
      ν = convBinNu (k + 1) 1 ∗ τ_k ∧
      (∃ (α_k β_k : Measure ℝ), IsProbabilityMeasure α_k ∧ IsProbabilityMeasure β_k ∧
        IsSupportedIn α_k (Set.Icc 0 (1 / ((2 : ℕ) * (2 : ℕ) : ℝ))) ∧
        IsSupportedIn β_k (Set.Icc 0 (1 / ((2 : ℕ) * (2 : ℕ) : ℝ))) ∧
        α_k ∗ β_k = lebScaled (1 / ((2 : ℕ) * (2 : ℕ) : ℝ)) ∧
        IsSubcriticalPair (σ_k.map ((4 : ℝ) ^ (k + 1) * ·)) (τ_k.map ((4 : ℝ) ^ (k + 1) * ·)) lam ∧
        σ_k.map ((4 : ℝ) ^ (k + 1) * ·) = unifDiscrete 2 (1 / (2 : ℝ)) ∗ α_k ∧
        τ_k.map ((4 : ℝ) ^ (k + 1) * ·) = unifDiscrete 2 (1 / ((2 : ℕ) * (2 : ℕ) : ℝ)) ∗ β_k) := by
    intro k
    induction k with
    | zero =>
      have hstep := subcritical_next_binary_step hsub hlam le_rfl hα0s hβ0s hcv0 hμ_eq hν_eq
      rcases hstep with ⟨hsub1, α₁, β₁, hα1p, hβ1p, hα1s, hβ1s, hcv1, hμ1, hν1⟩
      refine ⟨α₀, β₀, inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_,
        α₁, β₁, hα1p, hβ1p, hα1s, hβ1s, hcv1, ?_, ?_, ?_⟩
      · convert hα0s using 2; norm_num
      · convert hβ0s using 2; norm_num
      · convert hcv0 using 2; norm_num
      · have hdir_id : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ], Measure.dirac (0 : ℝ) ∗ ρ = ρ := fun ρ _ => by
          rw [Measure.dirac_conv]; simp
        have := isProbabilityMeasure_unifDiscrete (by norm_num : 0 < 2) (2 / (1 * (4 : ℝ) ^ (0 + 1)))
        simp only [convBinMu, hdir_id]
        convert hμ_eq using 2; norm_num
      · have hdir_id : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ], Measure.dirac (0 : ℝ) ∗ ρ = ρ := fun ρ _ => by
          rw [Measure.dirac_conv]; simp
        have := isProbabilityMeasure_unifDiscrete (by norm_num : 0 < 2) (1 / (1 * (4 : ℝ) ^ (0 + 1)))
        simp only [convBinNu, hdir_id]
        convert hν_eq using 2; norm_num
      · convert hsub1 using 2 <;> (ext x; norm_num)
      · convert hμ1 using 2; ext x; norm_num
      · convert hν1 using 2; ext x; norm_num
    | succ k ih =>
      rcases ih with ⟨σ_k, τ_k, hσkp, hτkp, hσks, hτks, hcvk, hμk, hνk,
        α_k, β_k, hαkp, hβkp, hαks, hβks, hcv_ab, hsub_ab, hσs_eq, hτs_eq⟩
      have : IsProbabilityMeasure σ_k := hσkp
      have : IsProbabilityMeasure τ_k := hτkp
      have : IsProbabilityMeasure α_k := hαkp
      have : IsProbabilityMeasure β_k := hβkp
      set S : ℝ := (4 : ℝ) ^ (k + 1)
      have hSp : 0 < S := by simp only [S]; positivity
      have hstep := subcritical_next_binary_step hsub_ab hlam le_rfl hαks hβks hcv_ab hσs_eq hτs_eq
      rcases hstep with ⟨hsub_next, α_n, β_n, hαnp, hβnp, hαns, hβns, hcv_n, hμn, hνn⟩
      let σ_n := α_k.map (S⁻¹ * ·)
      let τ_n := β_k.map (S⁻¹ * ·)
      have : IsProbabilityMeasure σ_n := isProbabilityMeasure_map_measurable (measurable_const_mul _)
      have : IsProbabilityMeasure τ_n := isProbabilityMeasure_map_measurable (measurable_const_mul _)
      have hpull : ∀ (ρ : Measure ℝ), IsSupportedIn ρ (Set.Icc 0 (1 / ((2 : ℕ) * (2 : ℕ) : ℝ))) →
          IsSupportedIn (ρ.map (S⁻¹ * ·)) (Set.Icc 0 (1 / (4 : ℝ) ^ (k + 2))) := by
        intro ρ hρ; unfold IsSupportedIn
        rw [Measure.map_apply (measurable_const_mul _) measurableSet_Icc.compl]
        have hsub_s : (S⁻¹ * ·) ⁻¹' (Set.Icc 0 (1 / (4 : ℝ) ^ (k + 2)))ᶜ ⊆
            (Set.Icc 0 (1 / ((2 : ℕ) * (2 : ℕ) : ℝ)))ᶜ := by
          intro x hx hmem; apply hx; refine ⟨mul_nonneg (inv_nonneg.mpr (le_of_lt hSp)) hmem.1, ?_⟩
          have : S⁻¹ * (1 / ((2 : ℕ) * (2 : ℕ) : ℝ)) = 1 / (4 : ℝ) ^ (k + 2) := by
            simp only [S, pow_succ]; norm_num; field_simp
          linarith [mul_le_mul_of_nonneg_left hmem.2 (inv_nonneg.mpr (le_of_lt hSp))]
        exact measure_mono_null hsub_s hρ
      have hσ_back : σ_k = unifDiscrete 2 (2 / (1 * (4 : ℝ) ^ (k + 2))) ∗ σ_n := by
        have := isProbabilityMeasure_unifDiscrete (by norm_num : 0 < 2) (1 / (2 : ℝ))
        have h1 : σ_k = (σ_k.map (S * ·)).map (S⁻¹ * ·) := by
          rw [Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
          have : (S⁻¹ * ·) ∘ (S * ·) = id := by ext x; simp; field_simp
          rw [this, Measure.map_id]
        rw [h1, hσs_eq, map_conv_mul_left, unifDiscrete_map_mul]
        congr 2; simp only [S, pow_succ]; field_simp; ring
      have hτ_back : τ_k = unifDiscrete 2 (1 / (1 * (4 : ℝ) ^ (k + 2))) ∗ τ_n := by
        have := isProbabilityMeasure_unifDiscrete (by norm_num : 0 < 2) (1 / ((2 : ℕ) * (2 : ℕ) : ℝ))
        have h1 : τ_k = (τ_k.map (S * ·)).map (S⁻¹ * ·) := by
          rw [Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
          have : (S⁻¹ * ·) ∘ (S * ·) = id := by ext x; simp; field_simp
          rw [this, Measure.map_id]
        rw [h1, hτs_eq, map_conv_mul_left, unifDiscrete_map_mul]
        congr 2; simp only [S, pow_succ]; norm_num; field_simp
      have hmap4_σ : σ_n.map ((4 : ℝ) ^ (k + 2) * ·) = α_k.map (((2 : ℕ) * (2 : ℕ) : ℝ) * ·) := by
        simp only [σ_n, Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
        congr 1; ext x; simp only [S, Function.comp_apply, pow_succ]; norm_num; field_simp
      have hmap4_τ : τ_n.map ((4 : ℝ) ^ (k + 2) * ·) = β_k.map (((2 : ℕ) * (2 : ℕ) : ℝ) * ·) := by
        simp only [τ_n, Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
        congr 1; ext x; simp only [S, Function.comp_apply, pow_succ]; norm_num; field_simp
      refine ⟨σ_n, τ_n, inferInstance, inferInstance, hpull α_k hαks, hpull β_k hβks, ?_, ?_, ?_,
        α_n, β_n, hαnp, hβnp, hαns, hβns, hcv_n, ?_, ?_, ?_⟩
      · rw [← map_conv_mul_left, hcv_ab, lebScaled_map_mul (by norm_num) (inv_pos.mpr hSp)]
        congr 1; simp only [S, pow_succ]; norm_num; field_simp
      · have := isProbabilityMeasure_convBinMu (k + 1) 1
        have := isProbabilityMeasure_unifDiscrete (by norm_num : 0 < 2) (2 / (1 * (4 : ℝ) ^ (k + 2)))
        rw [hμk, hσ_back, ← Measure.conv_assoc]; rfl
      · have := isProbabilityMeasure_convBinNu (k + 1) 1
        have := isProbabilityMeasure_unifDiscrete (by norm_num : 0 < 2) (1 / (1 * (4 : ℝ) ^ (k + 2)))
        rw [hνk, hτ_back, ← Measure.conv_assoc]; rfl
      · rw [hmap4_σ, hmap4_τ]; exact hsub_next
      · rw [hmap4_σ]; exact hμn
      · rw [hmap4_τ]; exact hνn
  -- Helper: if ρ_k is supported in [0, 1/4^(k+1)], then ft ρ_k ξ → 1
  have hft_rem_one : ∀ (ρ : ℕ → Measure ℝ), (∀ k, IsProbabilityMeasure (ρ k)) →
      (∀ k, IsSupportedIn (ρ k) (Set.Icc 0 (1 / (4 : ℝ) ^ (k + 1)))) →
      ∀ ξ : ℝ, Tendsto (fun k => ft (ρ k) ξ) atTop (𝓝 1) := by
    intro ρ hρp hρs ξ
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hpow : Tendsto (fun k : ℕ => (2 * Real.pi * |ξ| + 1) * (1 / 4 : ℝ) ^ (k + 1)) atTop (𝓝 0) := by
      have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)).comp
        (tendsto_add_atTop_nat 1)
      simpa using h1.const_mul (2 * Real.pi * |ξ| + 1)
    obtain ⟨K, hK⟩ := (hpow.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
    refine ⟨K, fun k hk => ?_⟩
    have : IsProbabilityMeasure (ρ k) := hρp k
    rw [dist_eq_norm, ft_apply]
    have h1_int : (1 : ℂ) = ∫ _x : ℝ, (1 : ℂ) ∂(ρ k) := by
      rw [integral_const]
      change (1 : ℂ) = ((ρ k) (Set.univ : Set ℝ)).toReal • (1 : ℂ)
      rw [measure_univ, ENNReal.toReal_one, one_smul]
    rw [h1_int, ← integral_sub]
    · have hae : ∀ᵐ (x : ℝ) ∂(ρ k), ‖Complex.exp (-2 * Real.pi * ξ * x * Complex.I) - 1‖ ≤
          (2 * Real.pi * |ξ|) * (1 / 4 : ℝ) ^ (k + 1) := by
        have hmem : ∀ᵐ x ∂(ρ k), x ∈ Set.Icc (0 : ℝ) (1 / (4 : ℝ) ^ (k + 1)) := by rw [ae_iff]; exact hρs k
        filter_upwards [hmem] with x hx
        have harg : (-2 * Real.pi * ξ * x * Complex.I : ℂ) = ((-2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [harg]
        have hlip := norm_exp_ofReal_mul_I_sub_one_le (-2 * Real.pi * ξ * x)
        calc ‖Complex.exp (((-2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I) - 1‖
            ≤ |-2 * Real.pi * ξ * x| := hlip
          _ = 2 * Real.pi * |ξ| * |x| := by
              rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]
          _ ≤ 2 * Real.pi * |ξ| * (1 / 4 : ℝ) ^ (k + 1) := by
              rw [abs_of_nonneg hx.1, one_div_pow]
              exact mul_le_mul_of_nonneg_left hx.2 (by positivity)
      calc ‖∫ x, (Complex.exp (-2 * Real.pi * ξ * x * Complex.I) - 1) ∂(ρ k)‖
          ≤ ∫ x, ‖Complex.exp (-2 * Real.pi * ξ * x * Complex.I) - 1‖ ∂(ρ k) := norm_integral_le_integral_norm _
        _ ≤ ∫ _x, (2 * Real.pi * |ξ|) * (1 / 4 : ℝ) ^ (k + 1) ∂(ρ k) := by
              apply integral_mono_ae _ (integrable_const _) hae
              exact ((integrable_const (2 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun x => by
                have harg : (-2 * Real.pi * ξ * x * Complex.I : ℂ) = ((-2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I := by
                  push_cast; ring
                have hnorm : ‖Complex.exp (-2 * Real.pi * ξ * x * Complex.I)‖ = 1 := by
                  rw [harg, Complex.norm_exp_ofReal_mul_I]
                rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
                calc ‖Complex.exp (-2 * Real.pi * ξ * x * Complex.I) - 1‖
                    ≤ ‖Complex.exp (-2 * Real.pi * ξ * x * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
                  _ = 2 := by rw [hnorm, norm_one]; norm_num))
        _ = (2 * Real.pi * |ξ|) * (1 / 4 : ℝ) ^ (k + 1) := by simp
        _ < (2 * Real.pi * |ξ| + 1) * (1 / 4 : ℝ) ^ (k + 1) := by
              have : (0 : ℝ) < (1 / 4 : ℝ) ^ (k + 1) := by positivity
              nlinarith
        _ < ε := hK k hk
    · exact (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun x => by
        have harg : (-2 * Real.pi * ξ * x * Complex.I : ℂ) = ((-2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [harg, Complex.norm_exp_ofReal_mul_I])
    · exact integrable_const 1
  choose σ_seq τ_seq hσp hτp hσs hτs _ hμ_seq hν_seq _ using htower
  constructor
  · apply ext_of_ft; intro ξ
    have hconst : Tendsto (fun _ : ℕ => ft μ ξ) atTop (𝓝 (ft μ ξ)) := tendsto_const_nhds
    have hprod : Tendsto (fun k => ft (convBinMu (k + 1) 1) ξ * ft (σ_seq k) ξ) atTop (𝓝 (ft cantorMu ξ * 1)) :=
      ((tendsto_ft_convBinMu_one ξ).comp (tendsto_add_atTop_nat 1)).mul (hft_rem_one σ_seq hσp hσs ξ)
    have heq : (fun k => ft (convBinMu (k + 1) 1) ξ * ft (σ_seq k) ξ) = fun _ => ft μ ξ := by
      ext k
      have : IsProbabilityMeasure (convBinMu (k + 1) 1) := isProbabilityMeasure_convBinMu (k + 1) 1
      have : IsProbabilityMeasure (σ_seq k) := hσp k
      rw [← ft_conv, ← hμ_seq k]
    rw [heq, mul_one] at hprod
    exact tendsto_nhds_unique hconst hprod
  · apply ext_of_ft; intro ξ
    have hconst : Tendsto (fun _ : ℕ => ft ν ξ) atTop (𝓝 (ft ν ξ)) := tendsto_const_nhds
    have hprod : Tendsto (fun k => ft (convBinNu (k + 1) 1) ξ * ft (τ_seq k) ξ) atTop (𝓝 (ft cantorNu ξ * 1)) :=
      ((tendsto_ft_convBinNu_one ξ).comp (tendsto_add_atTop_nat 1)).mul (hft_rem_one τ_seq hτp hτs ξ)
    have heq : (fun k => ft (convBinNu (k + 1) 1) ξ * ft (τ_seq k) ξ) = fun _ => ft ν ξ := by
      ext k
      have : IsProbabilityMeasure (convBinNu (k + 1) 1) := isProbabilityMeasure_convBinNu (k + 1) 1
      have : IsProbabilityMeasure (τ_seq k) := hτp k
      rw [← ft_conv, ← hν_seq k]
    rw [heq, mul_one] at hprod
    exact tendsto_nhds_unique hconst hprod

/-- **Full Step 3 Classification (`classify_subcritical_pair`):**
Every nontrivial subcritical pair `(μ, ν)` with `lam < 8/5` either equals `(cantorNu, cantorMu)` or
`(cantorMu, cantorNu)`, or has `M₁ ≥ 3` with (up to swap) `IsSupportedIn ν (Set.Icc 0 (2 / (3 M₁)))`
and `1 / (64 M₁) ≤ μ (Set.Ioo (1 - 2 / (3 M₁) - 1 / 100) 2)`. -/
theorem classify_subcritical_pair {μ ν : Measure ℝ} {lam : ℝ}
    (hsub : IsSubcriticalPair μ ν lam) (hlam : lam < 8 / 5)
    (hμ_ne : μ ≠ Measure.dirac 0) (hν_ne : ν ≠ Measure.dirac 0) :
    (μ = cantorNu ∧ ν = cantorMu) ∨ (μ = cantorMu ∧ ν = cantorNu) ∨
    (∃ M₁ : ℕ, 3 ≤ M₁ ∧
      ((IsSupportedIn ν (Set.Icc 0 (2 / (3 * (M₁ : ℝ)))) ∧
        (1 / (64 * (M₁ : ℝ≥0∞))) ≤ μ (Set.Ioo (1 - 2 / (3 * (M₁ : ℝ)) - 1 / 100) 2)) ∨
       (IsSupportedIn μ (Set.Icc 0 (2 / (3 * (M₁ : ℝ)))) ∧
        (1 / (64 * (M₁ : ℝ≥0∞))) ≤ ν (Set.Ioo (1 - 2 / (3 * (M₁ : ℝ)) - 1 / 100) 2)))) := by
  have horient : ∀ (σ τ : Measure ℝ) (M₁ : ℕ) (σ₀ τ₀ : Measure ℝ),
      IsSubcriticalPair σ τ lam → 2 ≤ M₁ →
      IsProbabilityMeasure σ₀ → IsProbabilityMeasure τ₀ →
      IsSupportedIn σ₀ (Set.Icc 0 (1 / ((M₁ : ℝ) * (2 : ℕ)))) →
      IsSupportedIn τ₀ (Set.Icc 0 (1 / ((M₁ : ℝ) * (2 : ℕ)))) →
      σ₀ ∗ τ₀ = lebScaled (1 / ((M₁ : ℝ) * (2 : ℕ))) →
      σ = unifDiscrete M₁ (1 / (M₁ : ℝ)) ∗ σ₀ →
      τ = unifDiscrete 2 (1 / ((M₁ : ℝ) * (2 : ℕ))) ∗ τ₀ →
      (σ = cantorMu ∧ τ = cantorNu) ∨
      (3 ≤ M₁ ∧ IsSupportedIn τ (Set.Icc 0 (2 / (3 * (M₁ : ℝ)))) ∧
        (1 / (64 * (M₁ : ℝ≥0∞))) ≤ σ (Set.Ioo (1 - 2 / (3 * (M₁ : ℝ)) - 1 / 100) 2)) := by
    intro σ τ M₁ σ₀ τ₀ hst hM1 hσ0p hτ0p hσ0s hτ0s hcv0 hσ_eq hτ_eq
    have : IsProbabilityMeasure σ := hst.1
    have : IsProbabilityMeasure τ := hst.2.1
    have : IsProbabilityMeasure σ₀ := hσ0p
    have : IsProbabilityMeasure τ₀ := hτ0p
    have hM12p : (0 : ℝ) < (M₁ : ℝ) * (2 : ℕ) := by positivity
    -- Step 1: rescaled pair (σ₀.map (2 M₁ ·), τ₀.map (2 M₁ ·)) is (cantorMu, cantorNu)!
    obtain ⟨hsub1, α₁, β₁, hα1p, hβ1p, hα1s, hβ1s, hcv1, hσ1, hτ1⟩ :=
      subcritical_next_binary_step hst hlam hM1 hσ0s hτ0s hcv0 hσ_eq hτ_eq
    have hcantor := eq_cantor_of_binary_step hsub1 hlam hα1s hβ1s hcv1 hσ1 hτ1
    have hσ0_eq : σ₀ = cantorMu.map (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·) := by
      have hback : σ₀ = (σ₀.map (((M₁ : ℝ) * (2 : ℕ)) * ·)).map (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·) := by
        rw [Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
        have : (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·) ∘ (((M₁ : ℝ) * (2 : ℕ)) * ·) = id := by ext x; simp; field_simp
        rw [this, Measure.map_id]
      rw [hback, hcantor.1]
    have hτ0_eq : τ₀ = cantorNu.map (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·) := by
      have hback : τ₀ = (τ₀.map (((M₁ : ℝ) * (2 : ℕ)) * ·)).map (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·) := by
        rw [Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
        have : (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·) ∘ (((M₁ : ℝ) * (2 : ℕ)) * ·) = id := by ext x; simp; field_simp
        rw [this, Measure.map_id]
      rw [hback, hcantor.2]
    by_cases hM1_2 : M₁ = 2
    · left
      subst hM1_2
      constructor
      · rw [hσ_eq, hσ0_eq]
        have h1 : (((2 : ℕ) : ℝ) * (2 : ℕ))⁻¹ = (1 / 4 : ℝ) := by norm_num
        have h2 : (1 / ((2 : ℕ) : ℝ)) = (1 / 2 : ℝ) := by norm_num
        rw [h1, h2]; exact cantorMu_self_similar
      · rw [hτ_eq, hτ0_eq]
        have h1 : (((2 : ℕ) : ℝ) * (2 : ℕ))⁻¹ = (1 / 4 : ℝ) := by norm_num
        have h2 : (1 / (((2 : ℕ) : ℝ) * (2 : ℕ))) = (1 / 4 : ℝ) := by norm_num
        rw [h1, h2]; exact cantorNu_self_similar
    · right
      have hM1_3 : 3 ≤ M₁ := by omega
      refine ⟨hM1_3, ?_, ?_⟩
      · -- τ = unifDiscrete 2 (1/(2 M₁)) ∗ cantorNu.map ((2 M₁)⁻¹ * ·) is supported in [0, 2/(3 M₁)]
        have hτ0_s : IsSupportedIn τ₀ (Set.Icc 0 (1 / (6 * (M₁ : ℝ)))) := by
          rw [hτ0_eq]; unfold IsSupportedIn
          rw [Measure.map_apply (measurable_const_mul _) measurableSet_Icc.compl]
          have hsub_s : (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·) ⁻¹' (Set.Icc 0 (1 / (6 * (M₁ : ℝ))))ᶜ ⊆ (Set.Icc 0 (1 / 3))ᶜ := by
            intro x hx hmem; apply hx; refine ⟨mul_nonneg (inv_nonneg.mpr (le_of_lt hM12p)) hmem.1, ?_⟩
            have : ((M₁ : ℝ) * (2 : ℕ))⁻¹ * (1 / 3) = 1 / (6 * (M₁ : ℝ)) := by push_cast; field_simp; ring
            linarith [mul_le_mul_of_nonneg_left hmem.2 (inv_nonneg.mpr (le_of_lt hM12p))]
          exact measure_mono_null hsub_s cantorNu_supported_third
        have hunif_s : IsSupportedIn (unifDiscrete 2 (1 / ((M₁ : ℝ) * (2 : ℕ)))) (Set.Icc 0 (1 / ((M₁ : ℝ) * (2 : ℕ)))) := by
          unfold IsSupportedIn unifDiscrete; rw [Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
          have hz : ∑ j ∈ Finset.range 2, Measure.dirac ((j : ℝ) * (1 / ((M₁ : ℝ) * (2 : ℕ))))
              (Set.Icc 0 (1 / ((M₁ : ℝ) * (2 : ℕ))))ᶜ = 0 := by
            apply Finset.sum_eq_zero; intro j hj
            rw [Measure.dirac_apply' _ measurableSet_Icc.compl, Set.indicator_of_notMem]
            rw [Set.notMem_compl_iff]
            have hj_le : (j : ℝ) ≤ 1 := by exact_mod_cast (show j ≤ 1 by have := Finset.mem_range.mp hj; omega)
            exact ⟨by positivity, by nlinarith [div_pos one_pos hM12p]⟩
          rw [hz, mul_zero]
        have := isProbabilityMeasure_unifDiscrete (by norm_num : 0 < 2) (1 / ((M₁ : ℝ) * (2 : ℕ)))
        have hconv_s := conv_supported_Icc hunif_s hτ0_s
        have hsum_end : 1 / ((M₁ : ℝ) * (2 : ℕ)) + 1 / (6 * (M₁ : ℝ)) = 2 / (3 * (M₁ : ℝ)) := by
          push_cast; field_simp; ring
        rw [hτ_eq, ← zero_add (0 : ℝ), ← hsum_end]; exact hconv_s
      · -- Top atom j = M₁ - 1 of unifDiscrete M₁ (1/M₁) shifts cantorMu (2/3 - 1/1000, 1) inside (1 - 2/(3 M₁) - 1/100, 2)
        rw [hσ_eq]
        set G := Set.Ioo (1 - 2 / (3 * (M₁ : ℝ)) - 1 / 100) (2 : ℝ)
        have hσG : (unifDiscrete M₁ (1 / (M₁ : ℝ)) ∗ σ₀) G =
            ((M₁ : ℝ≥0∞))⁻¹ * ∑ j ∈ Finset.range M₁, σ₀ ((fun y => (j : ℝ) * (1 / (M₁ : ℝ)) + y) ⁻¹' G) := by
          unfold unifDiscrete
          rw [Measure.conv_smul_left, Measure.smul_apply, smul_eq_mul]
          have hsum : (∑ j ∈ Finset.range M₁, Measure.dirac ((j : ℝ) * (1 / (M₁ : ℝ)))) ∗ σ₀ =
              ∑ j ∈ Finset.range M₁, Measure.dirac ((j : ℝ) * (1 / (M₁ : ℝ))) ∗ σ₀ := by
            clear hM1 hM1_2 hM1_3
            induction Finset.range M₁ using Finset.induction_on with
            | empty => simp
            | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.add_conv, ih]
          rw [hsum, Measure.finsetSum_apply]
          congr 1; apply Finset.sum_congr rfl; intro j _
          rw [Measure.dirac_conv, Measure.map_apply (measurable_const_add _) measurableSet_Ioo]
        rw [hσG]
        have htop_mem : M₁ - 1 ∈ Finset.range M₁ := Finset.mem_range.mpr (by omega)
        have hsingle : σ₀ ((fun y => ((M₁ - 1 : ℕ) : ℝ) * (1 / (M₁ : ℝ)) + y) ⁻¹' G) ≤
            ∑ j ∈ Finset.range M₁, σ₀ ((fun y => (j : ℝ) * (1 / (M₁ : ℝ)) + y) ⁻¹' G) :=
          Finset.single_le_sum (f := fun j : ℕ => σ₀ ((fun y => (j : ℝ) * (1 / (M₁ : ℝ)) + y) ⁻¹' G))
            (by intro _ _; exact zero_le) htop_mem
        have htail_le : (1 / 64 : ℝ≥0∞) ≤ σ₀ ((fun y => ((M₁ - 1 : ℕ) : ℝ) * (1 / (M₁ : ℝ)) + y) ⁻¹' G) := by
          rw [hσ0_eq, Measure.map_apply (measurable_const_mul _) ((measurable_const_add _) measurableSet_Ioo)]
          have hsub_t : Set.Ioo (2 / 3 - 1 / 1000 : ℝ) 1 ⊆
              (((M₁ : ℝ) * (2 : ℕ))⁻¹ * ·) ⁻¹' ((fun y => ((M₁ - 1 : ℕ) : ℝ) * (1 / (M₁ : ℝ)) + y) ⁻¹' G) := by
            intro x hx
            simp only [Set.mem_preimage, G, Set.mem_Ioo]
            have hM1r : (3 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hM1_3
            have hshift : ((M₁ - 1 : ℕ) : ℝ) * (1 / (M₁ : ℝ)) = 1 - 1 / (M₁ : ℝ) := by
              rw [Nat.cast_sub (by omega : 1 ≤ M₁), Nat.cast_one]; field_simp
            rw [hshift]
            have hinv : (2 / 3 - 1 / 1000 : ℝ) / (2 * (M₁ : ℝ)) < ((M₁ : ℝ) * (2 : ℕ))⁻¹ * x := by
              have : ((M₁ : ℝ) * (2 : ℕ))⁻¹ * x = x / (2 * (M₁ : ℝ)) := by push_cast; field_simp
              rw [this]; exact div_lt_div_of_pos_right hx.1 (by positivity)
            have hinv2 : ((M₁ : ℝ) * (2 : ℕ))⁻¹ * x < 1 / (2 * (M₁ : ℝ)) := by
              have : ((M₁ : ℝ) * (2 : ℕ))⁻¹ * x = x / (2 * (M₁ : ℝ)) := by push_cast; field_simp
              rw [this]; exact div_lt_div_of_pos_right hx.2 (by positivity)
            have hgap : (1 : ℝ) / (2000 * (M₁ : ℝ)) < 1 / 100 := by
              rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
            have halg : 1 - 1 / (M₁ : ℝ) + (2 / 3 - 1 / 1000 : ℝ) / (2 * (M₁ : ℝ)) =
                1 - 2 / (3 * (M₁ : ℝ)) - 1 / (2000 * (M₁ : ℝ)) := by field_simp; ring
            have hinv_le1 : 1 / (2 * (M₁ : ℝ)) < 1 := by rw [div_lt_one (by positivity)]; linarith
            have hM1inv_pos : (0 : ℝ) < 1 / (M₁ : ℝ) := by positivity
            constructor <;> linarith
          exact le_trans cantorNu_checkpoints.2.2.2.2 (measure_mono hsub_t)
        calc (1 / (64 * (M₁ : ℝ≥0∞)))
            = ((M₁ : ℝ≥0∞))⁻¹ * (1 / 64 : ℝ≥0∞) := by
                rw [one_div, one_div, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), mul_comm]
          _ ≤ ((M₁ : ℝ≥0∞))⁻¹ * σ₀ ((fun y => ((M₁ - 1 : ℕ) : ℝ) * (1 / (M₁ : ℝ)) + y) ⁻¹' G) :=
                mul_le_mul_of_nonneg_left htail_le zero_le
          _ ≤ ((M₁ : ℝ≥0∞))⁻¹ * ∑ j ∈ Finset.range M₁, σ₀ ((fun y => (j : ℝ) * (1 / (M₁ : ℝ)) + y) ⁻¹' G) :=
                mul_le_mul_of_nonneg_left hsingle zero_le
  -- Apply Theorem 4.1 (`gabardo_lai_single_step`) to (μ, ν)
  have : IsProbabilityMeasure μ := hsub.1
  have : IsProbabilityMeasure ν := hsub.2.1
  obtain ⟨M₁, M₂, μ', ν', hM1, hM2, hμ'p, hν'p, hμ's, hν's, hcv', hor⟩ :=
    gabardo_lai_single_step hsub.2.2.2.2.1 hsub.2.2.1 hsub.2.2.2.1 hμ_ne hν_ne
  have hM2_eq2 : M₂ = 2 := by
    have hbd : (2 * (M₂ : ℝ) + 2) / ((M₂ : ℝ) + 2) ≤ lam := by
      rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact lemma_4_2 hsub hM1 hM2 hμ's hν's hcv' h1 h2
      · have hswap : IsSubcriticalPair ν μ lam :=
          ⟨hsub.2.1, hsub.1, hsub.2.2.2.1, hsub.2.2.1,
           by rw [Measure.conv_comm]; exact hsub.2.2.2.2.1,
           fun u hu0 hu1 => by rw [mul_comm]; exact hsub.2.2.2.2.2 u hu0 hu1⟩
        exact lemma_4_2 hswap hM1 hM2 hμ's hν's hcv' h1 h2
    by_contra hne
    have hM2_3 : (3 : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast (show 3 ≤ M₂ by omega)
    have hge85 : (8 / 5 : ℝ) ≤ (2 * (M₂ : ℝ) + 2) / ((M₂ : ℝ) + 2) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
    linarith
  subst hM2_eq2
  rcases hor with ⟨hμ_eq, hν_eq⟩ | ⟨hν_eq, hμ_eq⟩
  · rcases horient μ ν M₁ μ' ν' hsub hM1 hμ'p hν'p hμ's hν's hcv' hμ_eq hν_eq with h1 | ⟨hM1_3, h2, h3⟩
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨M₁, hM1_3, Or.inl ⟨h2, h3⟩⟩)
  · have hswap : IsSubcriticalPair ν μ lam :=
      ⟨hsub.2.1, hsub.1, hsub.2.2.2.1, hsub.2.2.1,
       by rw [Measure.conv_comm]; exact hsub.2.2.2.2.1,
       fun u hu0 hu1 => by rw [mul_comm]; exact hsub.2.2.2.2.2 u hu0 hu1⟩
    rcases horient ν μ M₁ μ' ν' hswap hM1 hμ'p hν'p hμ's hν's hcv' hν_eq hμ_eq with ⟨h1, h2⟩ | ⟨hM1_3, h2, h3⟩
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (Or.inr ⟨M₁, hM1_3, Or.inr ⟨h2, h3⟩⟩)

/-! ### Part 3: Empirical Measures on `[0, 1]` and Weak-Limit Convergence -/

/-- Unit interval `UnitI = [0, 1]` as a compact topological subtype of `ℝ`. -/
abbrev UnitI : Type := Set.Icc (0 : ℝ) 1

/-- Clean empirical measure on `UnitI` using `Finset.attach` so every `a ≤ N` is proved statically. -/
def empProbI (S : Set ℕ) (N : ℕ) (hS : 1 ≤ countNat S N) : ProbabilityMeasure UnitI :=
  letI := Classical.decPred (· ∈ S)
  let F := (Finset.range (N + 1)).filter (· ∈ S)
  let m : Measure UnitI :=
    ((countNat S N : ℝ≥0∞))⁻¹ •
      ∑ a ∈ F.attach,
        Measure.dirac (⟨(a.1 : ℝ) / (N : ℝ), by
          have ha_le : a.1 ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp a.2).1)
          by_cases hN : N = 0
          · subst hN; simp
          · have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
            exact ⟨by positivity, (div_le_one hNpos).mpr (by exact_mod_cast ha_le)⟩⟩ : UnitI)
  ⟨m, by
    constructor
    simp only [m, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply,
      Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply,
      Finset.sum_const, Finset.card_attach, nsmul_eq_mul, mul_one]
    have hcard : F.card = countNat S N := rfl
    rw [hcard]
    exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr (by omega)) (ENNReal.natCast_ne_top _)⟩

/-- Pushforward of a `ProbabilityMeasure UnitI` to a `Measure ℝ`. -/
def pushToReal (μ : ProbabilityMeasure UnitI) : Measure ℝ :=
  (μ : Measure UnitI).map Subtype.val

lemma isProbabilityMeasure_pushToReal (μ : ProbabilityMeasure UnitI) :
    IsProbabilityMeasure (pushToReal μ) := by
  constructor
  rw [pushToReal, Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ, measure_univ]

lemma pushToReal_supported (μ : ProbabilityMeasure UnitI) :
    IsSupportedIn (pushToReal μ) (Set.Icc 0 1) := by
  unfold IsSupportedIn pushToReal
  rw [Measure.map_apply measurable_subtype_coe measurableSet_Icc.compl]
  have hemp : (Subtype.val : UnitI → ℝ) ⁻¹' (Set.Icc 0 1)ᶜ = ∅ := by
    ext x; simp
  rw [hemp, measure_empty]

lemma pushToReal_empProbI {S : Set ℕ} {N : ℕ} (hS : 1 ≤ countNat S N) :
    letI := Classical.decPred (· ∈ S)
    pushToReal (empProbI S N hS) =
      ((countNat S N : ℝ≥0∞))⁻¹ •
        ∑ a ∈ (Finset.range (N + 1)).filter (· ∈ S), Measure.dirac ((a : ℝ) / (N : ℝ)) := by
  classical
  ext s hs
  simp only [pushToReal, empProbI, ProbabilityMeasure.coe_mk,
    Measure.map_apply measurable_subtype_coe hs, Measure.smul_apply, smul_eq_mul,
    Measure.finsetSum_apply]
  congr 1
  rw [← Finset.sum_attach ((Finset.range (N + 1)).filter (· ∈ S)) (fun a => Measure.dirac ((a : ℝ) / (N : ℝ)) s)]
  apply Finset.sum_congr rfl; intro a _
  rw [Measure.dirac_apply' _ (measurable_subtype_coe hs), Measure.dirac_apply' _ hs]
  rfl

lemma ft_pushToReal_empProbI {S : Set ℕ} {N : ℕ} (hS : 1 ≤ countNat S N) (ξ : ℝ) :
    letI := Classical.decPred (· ∈ S)
    ft (pushToReal (empProbI S N hS)) ξ =
      ((countNat S N : ℂ))⁻¹ *
        ∑ a ∈ (Finset.range (N + 1)).filter (· ∈ S), Complex.exp (-2 * Real.pi * ξ * ((a : ℝ) / (N : ℝ)) * Complex.I) := by
  classical
  rw [pushToReal_empProbI hS, ft_apply, integral_smul_measure, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
  congr 1
  set F := (Finset.range (N + 1)).filter (· ∈ S)
  have hfin : ∀ t : Finset ℕ,
      ∫ x, Complex.exp (-2 * Real.pi * ξ * x * Complex.I) ∂(∑ a ∈ t, Measure.dirac ((a : ℝ) / (N : ℝ))) =
        ∑ a ∈ t, Complex.exp (-2 * Real.pi * ξ * ((a : ℝ) / (N : ℝ)) * Complex.I) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a u ha ih =>
      have hint_u : ∀ v : Finset ℕ, Integrable (fun x : ℝ => Complex.exp (-2 * Real.pi * ξ * x * Complex.I))
          (∑ b ∈ v, Measure.dirac ((b : ℝ) / (N : ℝ))) := by
        intro v; induction v using Finset.induction_on with
        | empty => simp
        | insert b w hb ihw => rw [Finset.sum_insert hb]; exact (integrable_dirac (by norm_num)).add_measure ihw
      rw [Finset.sum_insert ha, Finset.sum_insert ha, integral_add_measure (integrable_dirac (by norm_num)) (hint_u u),
          integral_dirac, ih, Complex.ofReal_div]
  exact hfin F

lemma empProbI_measure_Iic {S : Set ℕ} {N : ℕ} (hS : 1 ≤ countNat S N) (hN : 1 ≤ N)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((pushToReal (empProbI S N hS)) (Set.Icc 0 t)).toReal =
      (countNat S ⌊t * (N : ℝ)⌋₊ : ℝ) / (countNat S N : ℝ) := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hcard : pushToReal (empProbI S N hS) (Set.Icc 0 t) =
      ((countNat S N : ℝ≥0∞))⁻¹ * (countNat S ⌊t * (N : ℝ)⌋₊ : ℝ≥0∞) := by
    rw [pushToReal_empProbI hS, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
    congr 1
    have hterm : ∀ a ∈ (Finset.range (N + 1)).filter (· ∈ S),
        Measure.dirac ((a : ℝ) / (N : ℝ)) (Set.Icc 0 t) =
          if a ≤ ⌊t * (N : ℝ)⌋₊ then (1 : ℝ≥0∞) else 0 := by
      intro a _
      rw [Measure.dirac_apply' _ measurableSet_Icc]
      by_cases hle : a ≤ ⌊t * (N : ℝ)⌋₊
      · rw [Set.indicator_of_mem, Pi.one_apply, ite_eq_left_iff.mpr (fun h => absurd hle h)]
        refine ⟨by positivity, ?_⟩
        rw [div_le_iff₀ hNpos]
        exact le_trans (by exact_mod_cast hle) (Nat.floor_le (by positivity))
      · rw [Set.indicator_of_notMem, ite_eq_right_iff.mpr (fun h => absurd h hle)]
        intro hmem; apply hle
        rw [Nat.le_floor_iff (by positivity)]
        exact (div_le_iff₀ hNpos).mp hmem.2
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1; unfold countNat; congr 1; ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    have hfl_le : ⌊t * (N : ℝ)⌋₊ ≤ N := Nat.floor_le_of_le (by nlinarith)
    constructor
    · rintro ⟨⟨_, haS⟩, hafl⟩; exact ⟨by omega, haS⟩
    · rintro ⟨hafl, haS⟩; exact ⟨⟨by omega, haS⟩, by omega⟩
  rw [hcard, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
      div_eq_inv_mul]

/-- Weak convergence of `ProbabilityMeasure UnitI` implies pointwise convergence of Fourier transforms `ft`. -/
lemma tendsto_ft_of_tendsto_probI {ι : Type*} {L : Filter ι} {μs : ι → ProbabilityMeasure UnitI}
    {μ : ProbabilityMeasure UnitI} (hlim : Tendsto μs L (𝓝 μ)) (ξ : ℝ) :
    Tendsto (fun i => ft (pushToReal (μs i)) ξ) L (𝓝 (ft (pushToReal μ) ξ)) := by
  let fre : BoundedContinuousFunction UnitI ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun x => Real.cos (-2 * Real.pi * ξ * x.1), by fun_prop⟩
  let fim : BoundedContinuousFunction UnitI ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun x => Real.sin (-2 * Real.pi * ξ * x.1), by fun_prop⟩
  have hre_t := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) fre
  have him_t := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) fim
  have hft_eq : ∀ ρ : ProbabilityMeasure UnitI,
      ft (pushToReal ρ) ξ = Complex.ofReal (∫ x, fre x ∂ρ) + Complex.ofReal (∫ x, fim x ∂ρ) * Complex.I := by
    intro ρ
    have : IsProbabilityMeasure (pushToReal ρ) := isProbabilityMeasure_pushToReal ρ
    rw [ft_apply, pushToReal,
        integral_map measurable_subtype_coe.aemeasurable (by fun_prop : Continuous fun x : ℝ => Complex.exp (-2 * Real.pi * ξ * x * Complex.I)).aestronglyMeasurable]
    have hpt : ∀ x : UnitI, Complex.exp (-2 * Real.pi * ξ * (x.1 : ℂ) * Complex.I) =
        Complex.ofReal (fre x) + Complex.ofReal (fim x) * Complex.I := by
      intro x
      have harg : (-2 * Real.pi * ξ * (x.1 : ℂ) * Complex.I : ℂ) =
          ((-2 * Real.pi * ξ * x.1 : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [harg, Complex.exp_ofReal_mul_I]
      rfl
    simp_rw [hpt]
    have hint1 : Integrable (fun x : UnitI => Complex.ofReal (fre x)) (ρ : Measure UnitI) :=
      (Complex.continuous_ofReal.comp fre.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hint2 : Integrable (fun x : UnitI => Complex.ofReal (fim x) * Complex.I) (ρ : Measure UnitI) :=
      ((Complex.continuous_ofReal.comp fim.continuous).mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have h1 : ∫ a : UnitI, (fre a : ℂ) ∂(ρ : Measure UnitI) = ↑(∫ x : UnitI, fre x ∂(ρ : Measure UnitI)) :=
      integral_ofReal
    have h2 : ∫ a : UnitI, (fim a : ℂ) ∂(ρ : Measure UnitI) = ↑(∫ x : UnitI, fim x ∂(ρ : Measure UnitI)) :=
      integral_ofReal
    rw [integral_add hint1 hint2, integral_mul_const, h1, h2]
  simp_rw [hft_eq]
  exact (Complex.continuous_ofReal.continuousAt.tendsto.comp hre_t).add
    ((Complex.continuous_ofReal.continuousAt.tendsto.comp him_t).mul tendsto_const_nhds)

/-- Discrete Riemann sum `(1 / N) ∑_{n=0}^N exp(-2πi ξ n / N) → ft leb01 ξ` as `N → ∞`. -/
private lemma tendsto_riemann_exp (ξ : ℝ) :
    Tendsto (fun N : ℕ => ((N : ℂ))⁻¹ * ∑ n ∈ Finset.range (N + 1),
      Complex.exp (-2 * Real.pi * ξ * ((n : ℝ) / (N : ℝ)) * Complex.I)) atTop (𝓝 (ft leb01 ξ)) := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, ft_zero]
    have h1 : ∀ᶠ N : ℕ in atTop, ((N : ℂ))⁻¹ * ((N + 1 : ℕ) : ℂ) = 1 + ((N : ℂ))⁻¹ := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast; field_simp
    refine Tendsto.congr' (EventuallyEq.symm h1) ?_
    have hinv : Tendsto (fun N : ℕ => ((N : ℂ))⁻¹) atTop (𝓝 0) := by
      have hr : Tendsto (fun N : ℕ => ((N : ℝ))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      convert Complex.continuous_ofReal.continuousAt.tendsto.comp hr using 1
      ext N; simp
    simpa using tendsto_const_nhds.add hinv
  · rw [← lebScaled_one, ft_lebScaled one_pos ξ]
    simp only [hξ, ↓reduceIte, Complex.ofReal_one, mul_one]
    set c : ℂ := -2 * Real.pi * ξ * Complex.I
    have hc : c ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        (Complex.ofReal_ne_zero.mpr hξ)) Complex.I_ne_zero
    -- For large N, exp(c / N) ≠ 1 and the geometric sum equals (exp(c * (N+1)/N) - 1) / (N * (exp(c/N) - 1))
    have hinv0 : Tendsto (fun N : ℕ => ((N : ℂ))⁻¹) atTop (𝓝 0) := by
      have hr : Tendsto (fun N : ℕ => ((N : ℝ))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      convert Complex.continuous_ofReal.continuousAt.tendsto.comp hr using 1
      ext N; simp
    have hden_lim : Tendsto (fun N : ℕ => (N : ℂ) * (Complex.exp (c * ((N : ℂ))⁻¹) - 1)) atTop (𝓝 c) := by
      have hd : HasDerivAt (fun z : ℂ => Complex.exp (c * z)) c 0 := by
        have h1 : HasDerivAt (fun z : ℂ => c * z) c 0 := by simpa using (hasDerivAt_id (0 : ℂ)).const_mul c
        simpa using h1.cexp
      rw [hasDerivAt_iff_tendsto_slope] at hd
      have hslope : Tendsto (fun N : ℕ => slope (fun z : ℂ => Complex.exp (c * z)) 0 ((N : ℂ))⁻¹) atTop (𝓝 c) := by
        refine hd.comp ?_
        rw [tendsto_nhdsWithin_iff]
        refine ⟨hinv0, ?_⟩
        filter_upwards [eventually_ge_atTop 1] with N hN
        exact inv_ne_zero (Nat.cast_ne_zero.mpr (by omega))
      refine hslope.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N _hN
      simp only [slope, vsub_eq_sub, sub_zero, mul_zero, Complex.exp_zero, smul_eq_mul, inv_inv]
    have hnum_lim : Tendsto (fun N : ℕ => Complex.exp (c * (((N + 1 : ℕ) : ℂ) * ((N : ℂ))⁻¹)) - 1) atTop
        (𝓝 (Complex.exp c - 1)) := by
      have hratio : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℂ) * ((N : ℂ))⁻¹) atTop (𝓝 1) := by
        have h1 : ∀ᶠ N : ℕ in atTop, ((N + 1 : ℕ) : ℂ) * ((N : ℂ))⁻¹ = 1 + ((N : ℂ))⁻¹ := by
          filter_upwards [eventually_ge_atTop 1] with N hN
          have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          push_cast; field_simp
        refine Tendsto.congr' (EventuallyEq.symm h1) ?_
        simpa using tendsto_const_nhds.add hinv0
      simpa using ((Complex.continuous_exp.continuousAt.tendsto.comp (hratio.const_mul c)).sub tendsto_const_nhds)
    have hquot := hnum_lim.div hden_lim hc
    refine hquot.congr' ?_
    have hden_ne : ∀ᶠ N : ℕ in atTop, (N : ℂ) * (Complex.exp (c * ((N : ℂ))⁻¹) - 1) ≠ 0 :=
      hden_lim.eventually_ne hc
    filter_upwards [hden_ne, eventually_ge_atTop 1] with N hne hN1
    have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    set r : ℂ := Complex.exp (c * ((N : ℂ))⁻¹)
    have hsum_r : ∑ n ∈ Finset.range (N + 1), Complex.exp (-2 * Real.pi * ξ * ((n : ℝ) / (N : ℝ)) * Complex.I) =
        ∑ n ∈ Finset.range (N + 1), r ^ n := by
      apply Finset.sum_congr rfl; intro n _
      simp only [r, c, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    rw [hsum_r]
    have hgeom := geom_sum_mul r (N + 1)
    have hrpow : r ^ (N + 1) = Complex.exp (c * (((N + 1 : ℕ) : ℂ) * ((N : ℂ))⁻¹)) := by
      simp only [r, ← Complex.exp_nat_mul]; congr 1; ring
    rw [hrpow] at hgeom
    simp only [Pi.div_apply]
    rw [div_eq_iff hne]
    symm
    calc ((N : ℂ))⁻¹ * (∑ n ∈ Finset.range (N + 1), r ^ n) * ((N : ℂ) * (r - 1))
        = (((N : ℂ))⁻¹ * (N : ℂ)) * ((∑ n ∈ Finset.range (N + 1), r ^ n) * (r - 1)) := by ring
      _ = 1 * (Complex.exp (c * (((N + 1 : ℕ) : ℂ) * ((N : ℂ))⁻¹)) - 1) := by rw [inv_mul_cancel₀ hNc, hgeom]
      _ = _ := one_mul _

/-- Step 1 of Proposition 4.3: along any filter `L` where `N_j → ∞` with `T(N_j) ≤ K` and
`empProbI → (μ, ν)`, we have `μ ∗ ν = leb01` and `IsSubcriticalPair μ ν lam` for every
`lam > limsup A(x)B(x)/x`. -/
lemma weak_limit_is_subcritical {A B : Set ℕ} {n₀ K : ℕ} (_hn₀ : 1 ≤ n₀)
    (hstab : ∀ n ≥ n₀, repCount A B n = 1)
    {lam : ℝ} (hprod_ev : ∀ᶠ x : ℝ in atTop, (countReal A x : ℝ) * (countReal B x : ℝ) ≤ lam * x)
    {N : ℕ → ℕ} (hN_top : Tendsto N atTop atTop) (hT_le : ∀ j, crossExcess A B (N j) ≤ K)
    (hA1 : ∀ j, 1 ≤ countNat A (N j)) (hB1 : ∀ j, 1 ≤ countNat B (N j))
    {L : Filter ℕ} [L.NeBot] (hL_le : L ≤ atTop)
    {μI νI : ProbabilityMeasure UnitI}
    (hμ_lim : Tendsto (fun j => empProbI A (N j) (hA1 j)) L (𝓝 μI))
    (hν_lim : Tendsto (fun j => empProbI B (N j) (hB1 j)) L (𝓝 νI)) :
    IsSubcriticalPair (pushToReal μI) (pushToReal νI) lam := by
  classical
  have : IsProbabilityMeasure (pushToReal μI) := isProbabilityMeasure_pushToReal μI
  have : IsProbabilityMeasure (pushToReal νI) := isProbabilityMeasure_pushToReal νI
  have hN_L : Tendsto N L atTop := hN_top.mono_left hL_le
  -- Part A: pushToReal μI ∗ pushToReal νI = leb01 via ft
  have hconv : pushToReal μI ∗ pushToReal νI = leb01 := by
    apply ext_of_ft
    intro ξ
    have hlim_lhs : Tendsto (fun j => ft (pushToReal (empProbI A (N j) (hA1 j))) ξ *
        ft (pushToReal (empProbI B (N j) (hB1 j))) ξ) L (𝓝 (ft (pushToReal μI ∗ pushToReal νI) ξ)) := by
      rw [ft_conv]
      exact (tendsto_ft_of_tendsto_probI hμ_lim ξ).mul (tendsto_ft_of_tendsto_probI hν_lim ξ)
    have hlim_rhs : Tendsto (fun j => ft (pushToReal (empProbI A (N j) (hA1 j))) ξ *
        ft (pushToReal (empProbI B (N j) (hB1 j))) ξ) L (𝓝 (ft leb01 ξ)) := by
      -- Compare product with Riemann sum ((N j)⁻¹ * ∑_{n ≤ N j} exp(-2πi ξ n / N j))
      have hriem : Tendsto (fun j => ((N j : ℂ))⁻¹ * ∑ n ∈ Finset.range (N j + 1),
          Complex.exp (-2 * Real.pi * ξ * ((n : ℝ) / (N j : ℝ)) * Complex.I)) L (𝓝 (ft leb01 ξ)) :=
        (tendsto_riemann_exp ξ).comp hN_L
      -- Ratio (N j) / (A(N j) * B(N j)) → 1 since A(N) B(N) = N + 1 + c + T(N)
      set E := errSum A B n₀
      have hAB_eq : ∀ᶠ j in L, (countNat A (N j) : ℤ) * (countNat B (N j) : ℤ) =
          (N j : ℤ) + 1 + errSigned A B n₀ + (crossExcess A B (N j) : ℤ) := by
        filter_upwards [hN_L.eventually (eventually_ge_atTop n₀)] with j hj
        exact countNat_mul_eq_N_add_c_add_T hstab hj
      -- Show norm difference tends to 0!
      have hdiff0 : Tendsto (fun j =>
          ft (pushToReal (empProbI A (N j) (hA1 j))) ξ * ft (pushToReal (empProbI B (N j) (hB1 j))) ξ -
          ((N j : ℂ))⁻¹ * ∑ n ∈ Finset.range (N j + 1),
            Complex.exp (-2 * Real.pi * ξ * ((n : ℝ) / (N j : ℝ)) * Complex.I)) L (𝓝 0) := by
        rw [Metric.tendsto_nhds]
        intro ε hε
        have hM_ev : ∀ᶠ j in L, max (2 * (E + K + n₀ + 1)) 1 ≤ N j ∧
            ((8 * (E + K + 2 : ℝ)) / (N j : ℝ) < ε) := by
          have hbig : ∀ᶠ n : ℕ in atTop, max (2 * (E + K + n₀ + 1)) 1 ≤ n ∧ (8 * (E + K + 2 : ℝ)) / (n : ℝ) < ε := by
            have h1 := eventually_ge_atTop (max (2 * (E + K + n₀ + 1)) 1)
            have h2 : Tendsto (fun n : ℕ => (8 * (E + K + 2 : ℝ)) / (n : ℝ)) atTop (𝓝 0) := by
              simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (8 * (E + K + 2 : ℝ))
            exact h1.and (h2.eventually (gt_mem_nhds hε))
          exact hN_L.eventually hbig
        filter_upwards [hAB_eq, hM_ev] with j hAB ⟨hNbig, hNε⟩
        rw [dist_zero_right, ft_pushToReal_empProbI (hA1 j), ft_pushToReal_empProbI (hB1 j)]
        set Nj := N j
        set A0 := (Finset.range (Nj + 1)).filter (· ∈ A)
        set B0 := (Finset.range (Nj + 1)).filter (· ∈ B)
        set S_ab : ℂ := ∑ a ∈ A0, ∑ b ∈ B0, Complex.exp (-2 * Real.pi * ξ * (((a + b : ℕ) : ℝ) / (Nj : ℝ)) * Complex.I)
        set S_riem : ℂ := ∑ n ∈ Finset.range (Nj + 1), Complex.exp (-2 * Real.pi * ξ * ((n : ℝ) / (Nj : ℝ)) * Complex.I)
        have hprod_S : ((countNat A Nj : ℂ))⁻¹ * (∑ a ∈ A0, Complex.exp (-2 * Real.pi * ξ * ((a : ℝ) / (Nj : ℝ)) * Complex.I)) *
            (((countNat B Nj : ℂ))⁻¹ * ∑ b ∈ B0, Complex.exp (-2 * Real.pi * ξ * ((b : ℝ) / (Nj : ℝ)) * Complex.I)) =
            (((countNat A Nj : ℂ) * (countNat B Nj : ℂ)))⁻¹ * S_ab := by
          rw [show ((countNat A Nj : ℂ))⁻¹ * (∑ a ∈ A0, _) * (((countNat B Nj : ℂ))⁻¹ * ∑ b ∈ B0, _) =
              (((countNat A Nj : ℂ))⁻¹ * ((countNat B Nj : ℂ))⁻¹) *
              ((∑ a ∈ A0, Complex.exp (-2 * Real.pi * ξ * ((a : ℝ) / (Nj : ℝ)) * Complex.I)) *
               (∑ b ∈ B0, Complex.exp (-2 * Real.pi * ξ * ((b : ℝ) / (Nj : ℝ)) * Complex.I))) by ring,
              ← mul_inv, Finset.sum_mul_sum]
          congr 1; simp only [S_ab]
          apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _
          rw [← Complex.exp_add]; congr 1; push_cast; ring
        rw [hprod_S]
        -- Bound ‖S_ab - S_riem‖ ≤ E + K
        have hexp_norm_div : ∀ a b : ℕ, ‖Complex.exp (-2 * Real.pi * ξ * (((a : ℝ) : ℂ) / ((b : ℝ) : ℂ)) * Complex.I)‖ = 1 := fun a b => by
          have : (-2 * Real.pi * ξ * (((a : ℝ) : ℂ) / ((b : ℝ) : ℂ)) * Complex.I : ℂ) =
              ((-2 * Real.pi * ξ * ((a : ℝ) / (b : ℝ)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
          rw [this, Complex.norm_exp_ofReal_mul_I]
        have hSab_diff : ‖S_ab - S_riem‖ ≤ (E : ℝ) + (K : ℝ) := by
          -- Split A0 × B0 into a + b ≤ Nj and a + b > Nj
          set P_le := (A0 ×ˢ B0).filter (fun p => p.1 + p.2 ≤ Nj)
          set P_gt := (A0 ×ˢ B0).filter (fun p => Nj < p.1 + p.2)
          have hS_split : S_ab = (∑ p ∈ P_le, Complex.exp (-2 * Real.pi * ξ * (((p.1 + p.2 : ℕ) : ℝ) / (Nj : ℝ)) * Complex.I)) +
              (∑ p ∈ P_gt, Complex.exp (-2 * Real.pi * ξ * (((p.1 + p.2 : ℕ) : ℝ) / (Nj : ℝ)) * Complex.I)) := by
            simp only [S_ab, ← Finset.sum_product']
            rw [← Finset.sum_union]
            · congr 1; ext p; simp only [P_le, P_gt, Finset.mem_union, Finset.mem_filter]; have := le_or_gt (p.1 + p.2) Nj; tauto
            · rw [Finset.disjoint_left]; intro p h1 h2; simp only [P_le, P_gt, Finset.mem_filter] at h1 h2; omega
          have hPle_eq : ∑ p ∈ P_le, Complex.exp (-2 * Real.pi * ξ * (((p.1 + p.2 : ℕ) : ℝ) / (Nj : ℝ)) * Complex.I) =
              ∑ n ∈ Finset.range (Nj + 1), (repCount A B n : ℂ) * Complex.exp (-2 * Real.pi * ξ * ((n : ℝ) / (Nj : ℝ)) * Complex.I) := by
            rw [← Finset.sum_fiberwise_of_maps_to (s := P_le) (g := fun p : ℕ × ℕ => p.1 + p.2) (t := Finset.range (Nj + 1))
                (fun p hp => Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hp).2; omega))]
            apply Finset.sum_congr rfl; intro n hn
            have hconst : ∀ p ∈ P_le.filter (fun p => p.1 + p.2 = n),
                Complex.exp (-2 * Real.pi * ξ * (((p.1 + p.2 : ℕ) : ℝ) / (Nj : ℝ)) * Complex.I) =
                Complex.exp (-2 * Real.pi * ξ * ((n : ℝ) / (Nj : ℝ)) * Complex.I) := fun p hp => by
              rw [(Finset.mem_filter.mp hp).2]
            rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
            congr 1; norm_cast; unfold repCount
            apply Finset.card_bij (fun p _ => p.1)
            · intro p hp
              simp only [P_le, A0, B0, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
              refine ⟨by omega, hp.1.1.1.2, ?_⟩
              have : n - p.1 = p.2 := by omega
              rw [this]; exact hp.1.1.2.2
            · rintro ⟨a1, b1⟩ h1 ⟨a2, b2⟩ h2 heq
              simp only [Finset.mem_filter] at h1 h2; dsimp only at heq; ext <;> omega
            · intro a ha
              simp only [Finset.mem_filter, Finset.mem_range] at ha
              refine ⟨(a, n - a), ?_, rfl⟩
              simp only [P_le, A0, B0, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
              have hn_le : n ≤ Nj := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
              exact ⟨⟨⟨⟨by omega, ha.2.1⟩, ⟨by omega, ha.2.2⟩⟩, by omega⟩, by omega⟩
          have hPgt_card : P_gt.card ≤ K := by
            have hmap : ∀ p ∈ P_gt, p.1 + p.2 - (Nj + 1) ∈ Finset.range Nj := fun p hp => by
              simp only [P_gt, A0, B0, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢; omega
            have hle_T : P_gt.card ≤ crossExcess A B Nj := by
              rw [Finset.card_eq_sum_card_fiberwise hmap]; unfold crossExcess
              apply Finset.sum_le_sum; intro m _; unfold repTrunc
              apply Finset.card_le_card_of_injOn Prod.fst
              · intro p hp
                simp only [P_gt, A0, B0, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
                refine ⟨hp.1.1.1.1, hp.1.1.1.2, by omega, by omega, ?_⟩
                have : Nj + 1 + m - p.1 = p.2 := by omega
                rw [this]; exact hp.1.1.2.2
              · rintro ⟨a1, b1⟩ h1 ⟨a2, b2⟩ h2 heq
                simp only [P_gt, Finset.mem_coe, Finset.mem_filter] at h1 h2; dsimp only at heq; ext <;> omega
            exact le_trans hle_T (hT_le j)
          have hdiff_le : ‖(∑ p ∈ P_le, Complex.exp (-2 * Real.pi * ξ * (((p.1 + p.2 : ℕ) : ℝ) / (Nj : ℝ)) * Complex.I)) - S_riem‖ ≤ (E : ℝ) := by
            rw [hPle_eq, ← Finset.sum_sub_distrib]
            calc ‖∑ n ∈ Finset.range (Nj + 1), ((repCount A B n : ℂ) * Complex.exp (-2 * Real.pi * ξ * ((n : ℝ) / (Nj : ℝ)) * Complex.I) -
                    Complex.exp (-2 * Real.pi * ξ * ((n : ℝ) / (Nj : ℝ)) * Complex.I))‖
                ≤ ∑ n ∈ Finset.range (Nj + 1), ‖((repCount A B n : ℂ) - 1) * Complex.exp (-2 * Real.pi * ξ * ((n : ℝ) / (Nj : ℝ)) * Complex.I)‖ := by
                  calc _ ≤ ∑ n ∈ Finset.range (Nj + 1), ‖(repCount A B n : ℂ) * Complex.exp (-2 * Real.pi * ξ * ((n : ℝ) / (Nj : ℝ)) * Complex.I) -
                        Complex.exp (-2 * Real.pi * ξ * ((n : ℝ) / (Nj : ℝ)) * Complex.I)‖ := norm_sum_le _ _
                    _ = _ := Finset.sum_congr rfl (fun n _ => by congr 1; ring)
              _ = ∑ n ∈ Finset.range (Nj + 1), |(repCount A B n : ℝ) - 1| := by
                  apply Finset.sum_congr rfl; intro n _
                  rw [norm_mul, hexp_norm_div, mul_one]
                  have : ((repCount A B n : ℂ) - 1) = (((repCount A B n : ℝ) - 1 : ℝ) : ℂ) := by push_cast; rfl
                  rw [this, Complex.norm_real, Real.norm_eq_abs]
              _ = (E : ℝ) := by
                  have hsp : Nj + 1 = n₀ + (Nj + 1 - n₀) := by omega
                  rw [hsp, Finset.sum_range_add]
                  have hz : ∑ m ∈ Finset.range (Nj + 1 - n₀), |(repCount A B (n₀ + m) : ℝ) - 1| = 0 := by
                    apply Finset.sum_eq_zero; intro m _; simp [hstab (n₀ + m) (by omega)]
                  rw [hz, add_zero]; unfold E errSum; push_cast
                  apply Finset.sum_congr rfl; intro n _
                  have habs : (((repCount A B n : ℤ) - 1).natAbs : ℝ) = |((repCount A B n : ℤ) - 1 : ℤ)| := by
                    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
                  push_cast at habs
                  exact habs.symm
          have hgt_norm : ‖∑ p ∈ P_gt, Complex.exp (-2 * Real.pi * ξ * (((p.1 + p.2 : ℕ) : ℝ) / (Nj : ℝ)) * Complex.I)‖ ≤ (K : ℝ) := by
            calc _ ≤ ∑ p ∈ P_gt, ‖Complex.exp (-2 * Real.pi * ξ * (((p.1 + p.2 : ℕ) : ℝ) / (Nj : ℝ)) * Complex.I)‖ := norm_sum_le _ _
              _ = (P_gt.card : ℝ) := by
                  rw [Finset.sum_congr rfl (fun p _ => hexp_norm_div (p.1 + p.2) Nj), Finset.sum_const, nsmul_eq_mul, mul_one]
              _ ≤ (K : ℝ) := by exact_mod_cast hPgt_card
          rw [hS_split, add_sub_right_comm]
          exact (norm_add_le _ _).trans (add_le_add hdiff_le hgt_norm)
        have hSriem_norm : ‖S_riem‖ ≤ (Nj : ℝ) + 1 := by
          calc ‖S_riem‖ ≤ ∑ n ∈ Finset.range (Nj + 1), ‖Complex.exp (-2 * Real.pi * ξ * ((n : ℝ) / (Nj : ℝ)) * Complex.I)‖ := norm_sum_le _ _
            _ = (Nj : ℝ) + 1 := by
                rw [Finset.sum_congr rfl (fun n _ => hexp_norm_div n Nj), Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
                push_cast; rfl
        -- Triangle inequality: ‖(AB)⁻¹ S_ab - N⁻¹ S_riem‖ ≤ (AB)⁻¹ ‖S_ab - S_riem‖ + |(AB)⁻¹ - N⁻¹| ‖S_riem‖
        set AB_r : ℝ := (countNat A Nj : ℝ) * (countNat B Nj : ℝ)
        have hAB_real : AB_r = (Nj : ℝ) + 1 + (errSigned A B n₀ : ℝ) + (crossExcess A B Nj : ℝ) := by
          simp only [AB_r]; exact_mod_cast hAB
        have hc_abs : |(errSigned A B n₀ : ℝ)| ≤ (E : ℝ) := by exact_mod_cast abs_errSigned_le_errSum A B n₀
        have hT_r : (crossExcess A B Nj : ℝ) ≤ (K : ℝ) := by exact_mod_cast hT_le j
        have hAB_ge : (Nj : ℝ) / 2 ≤ AB_r := by
          have := (abs_le.mp hc_abs).1
          have : (0 : ℝ) ≤ (crossExcess A B Nj : ℝ) := Nat.cast_nonneg _
          have hNj_r : 2 * ((E : ℝ) + (K : ℝ) + (n₀ : ℝ) + 1) ≤ (Nj : ℝ) := by
            have : 2 * (E + K + n₀ + 1) ≤ Nj := le_trans (le_max_left _ _) hNbig
            exact_mod_cast this
          linarith
        have hNj_pos : (0 : ℝ) < (Nj : ℝ) := by
          have : 1 ≤ Nj := le_trans (le_max_right _ _) hNbig; exact_mod_cast this
        have hAB_pos : 0 < AB_r := by linarith
        have hAB_diff : |AB_r - (Nj : ℝ)| ≤ (E : ℝ) + (K : ℝ) + 1 := by
          have h1 := abs_le.mp hc_abs
          have h2 : (0 : ℝ) ≤ (crossExcess A B Nj : ℝ) := Nat.cast_nonneg _
          rw [abs_le]; constructor <;> linarith
        have hrewrite : ((countNat A Nj : ℂ) * (countNat B Nj : ℂ))⁻¹ * S_ab - ((Nj : ℂ))⁻¹ * S_riem =
            ((AB_r : ℂ))⁻¹ * (S_ab - S_riem) + (((AB_r : ℂ))⁻¹ - ((Nj : ℂ))⁻¹) * S_riem := by
          simp only [AB_r]; push_cast; ring
        rw [hrewrite]
        have ht1 : ‖((AB_r : ℂ))⁻¹ * (S_ab - S_riem)‖ ≤ 2 * ((E : ℝ) + (K : ℝ)) / (Nj : ℝ) := by
          rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hAB_pos]
          calc AB_r⁻¹ * ‖S_ab - S_riem‖ ≤ ((Nj : ℝ) / 2)⁻¹ * ((E : ℝ) + (K : ℝ)) :=
                mul_le_mul (inv_anti₀ (by positivity) hAB_ge) hSab_diff (norm_nonneg _) (by positivity)
            _ = 2 * ((E : ℝ) + (K : ℝ)) / (Nj : ℝ) := by field_simp
        have ht2 : ‖(((AB_r : ℂ))⁻¹ - ((Nj : ℂ))⁻¹) * S_riem‖ ≤ 2 * ((E : ℝ) + (K : ℝ) + 1) * ((Nj : ℝ) + 1) / ((Nj : ℝ) ^ 2) := by
          rw [norm_mul]
          have hsub_inv : ((AB_r : ℂ))⁻¹ - ((Nj : ℂ))⁻¹ = ((((Nj : ℝ) - AB_r) / (AB_r * (Nj : ℝ)) : ℝ) : ℂ) := by
            have h1 : (AB_r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hAB_pos.ne'
            have h2 : (Nj : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hNj_pos.ne'
            push_cast; field_simp
          rw [hsub_inv, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_sub_comm, abs_of_pos (mul_pos hAB_pos hNj_pos)]
          have h1 : |AB_r - (Nj : ℝ)| / (AB_r * (Nj : ℝ)) ≤ ((E : ℝ) + (K : ℝ) + 1) / ((Nj : ℝ) / 2 * (Nj : ℝ)) :=
            div_le_div₀ (by positivity) hAB_diff (by positivity) (mul_le_mul_of_nonneg_right hAB_ge (le_of_lt hNj_pos))
          calc |AB_r - (Nj : ℝ)| / (AB_r * (Nj : ℝ)) * ‖S_riem‖
              ≤ (((E : ℝ) + (K : ℝ) + 1) / ((Nj : ℝ) / 2 * (Nj : ℝ))) * ((Nj : ℝ) + 1) :=
                mul_le_mul h1 hSriem_norm (norm_nonneg _) (by positivity)
            _ = 2 * ((E : ℝ) + (K : ℝ) + 1) * ((Nj : ℝ) + 1) / ((Nj : ℝ) ^ 2) := by field_simp
        have ht2' : 2 * ((E : ℝ) + (K : ℝ) + 1) * ((Nj : ℝ) + 1) / ((Nj : ℝ) ^ 2) ≤
            (4 * ((E : ℝ) + (K : ℝ) + 1)) / (Nj : ℝ) := by
          have hNj_ge1 : (1 : ℝ) ≤ (Nj : ℝ) := by
            have : 1 ≤ Nj := le_trans (le_max_right _ _) hNbig; exact_mod_cast this
          have hEK1 : (0 : ℝ) ≤ (E : ℝ) + (K : ℝ) + 1 := by positivity
          rw [div_le_div_iff₀ (by positivity) hNj_pos]
          nlinarith [mul_le_mul_of_nonneg_left hNj_ge1 hEK1]
        -- Wait: ht1 + ht2' ≤ (6*(E+K) + 4) / Nj; let's bound by 4*(E+K+2)/Nj? Better: check factor:
        -- Wait: 2*(E+K) + 2*(E+K+1)*(1 + 1/Nj)! Since Nj ≥ 2, (Nj+1)/Nj ≤ 3/2, so 2*(E+K+1)*3/2 = 3*(E+K+1) -> 5*(E+K)+3!
        -- Actually with Nj ≥ 2*(E+K+n₀+1) ≥ 4 (since n₀ ≥ 1), (Nj+1)/Nj ≤ 5/4!
        -- Then 2*(E+K) + 2*(E+K+1)*(5/4) = 4.5*(E+K) + 2.5... wait, better: make numerator in hM_ev 8*(E+K+2)!
        calc ‖((AB_r : ℂ))⁻¹ * (S_ab - S_riem) + (((AB_r : ℂ))⁻¹ - ((Nj : ℂ))⁻¹) * S_riem‖
            ≤ ‖((AB_r : ℂ))⁻¹ * (S_ab - S_riem)‖ + ‖(((AB_r : ℂ))⁻¹ - ((Nj : ℂ))⁻¹) * S_riem‖ := norm_add_le _ _
          _ ≤ 2 * ((E : ℝ) + (K : ℝ)) / (Nj : ℝ) + (4 * ((E : ℝ) + (K : ℝ) + 1)) / (Nj : ℝ) := add_le_add ht1 (le_trans ht2 ht2')
          _ = (6 * ((E : ℝ) + (K : ℝ)) + 4) / (Nj : ℝ) := by ring
          _ ≤ (8 * ((E : ℝ) + (K : ℝ) + 2)) / (Nj : ℝ) := by
                apply div_le_div_of_nonneg_right _ (le_of_lt hNj_pos); linarith
          _ < ε := hNε
      simpa using hdiff0.add hriem
    exact tendsto_nhds_unique hlim_lhs hlim_rhs
  -- Part B: ∀ u ∈ (0, 1), μ([0, u]) * ν([0, u]) ≤ lam * u via Portmanteau on open Iio (u + δ)
  have hbound : ∀ u : ℝ, 0 < u → u < 1 →
      (pushToReal μI (Set.Icc 0 u)).toReal * (pushToReal νI (Set.Icc 0 u)).toReal ≤ lam * u := by
    intro u hu0 hu1
    set mA := (pushToReal μI (Set.Icc 0 u)).toReal
    set mB := (pushToReal νI (Set.Icc 0 u)).toReal
    by_contra hgt; push Not at hgt
    -- Choose small ε > 0 so u + ε < 1 and (mA - ε)(mB - ε) > lam * (u + ε) / (1 - ε)
    have hcont : ContinuousAt (fun t : ℝ => max 0 (mA - t) * max 0 (mB - t) * (1 - t) - lam * (u + t)) 0 := by
      fun_prop
    have hpos0 : 0 < max 0 (mA - 0) * max 0 (mB - 0) * (1 - 0) - lam * (u + 0) := by
      have hmA : 0 ≤ mA := ENNReal.toReal_nonneg
      have hmB : 0 ≤ mB := ENNReal.toReal_nonneg
      simp only [sub_zero, max_eq_right hmA, max_eq_right hmB, mul_one, add_zero]; linarith
    have hev_t := hcont.eventually (lt_mem_nhds hpos0)
    rw [Metric.eventually_nhds_iff] at hev_t
    rcases hev_t with ⟨r₀, hr₀, hr₀_prop⟩
    set δ := min (min (r₀ / 2) ((1 - u) / 2)) (1 / 2)
    have hδpos : 0 < δ := lt_min (lt_min (half_pos hr₀) (by linarith)) (by norm_num)
    have hδ_lt_r0 : dist δ 0 < r₀ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hδpos]
      exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (half_lt_self hr₀)
    have hstrict := hr₀_prop hδ_lt_r0
    have huδ_lt1 : u + δ < 1 := by
      have : δ ≤ (1 - u) / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
      linarith
    -- Open set G := {x : UnitI | x.1 < u + δ}
    let G : Set UnitI := {x : UnitI | x.1 < u + δ}
    have hG_open : IsOpen G := isOpen_lt continuous_subtype_val continuous_const
    have hmA_le : (pushToReal μI (Set.Icc 0 u)) ≤ (μI : Measure UnitI) G := by
      rw [pushToReal, Measure.map_apply measurable_subtype_coe measurableSet_Icc]
      apply measure_mono; intro x hx; simp only [Set.mem_preimage, Set.mem_Icc] at hx
      exact lt_of_le_of_lt hx.2 (by linarith)
    have hmB_le : (pushToReal νI (Set.Icc 0 u)) ≤ (νI : Measure UnitI) G := by
      rw [pushToReal, Measure.map_apply measurable_subtype_coe measurableSet_Icc]
      apply measure_mono; intro x hx; simp only [Set.mem_preimage, Set.mem_Icc] at hx
      exact lt_of_le_of_lt hx.2 (by linarith)
    have hliminfA := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ_lim hG_open
    have hliminfB := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hν_lim hG_open
    have hevA : ∀ᶠ j in L, max 0 (mA - δ) ≤ (countNat A ⌊(u + δ) * (N j : ℝ)⌋₊ : ℝ) / (countNat A (N j) : ℝ) := by
      by_cases h0 : mA - δ ≤ 0
      · rw [max_eq_left h0]; exact Eventually.of_forall (fun _ => by positivity)
      · push Not at h0
        have hlt_en : ENNReal.ofReal (mA - δ) < (μI : Measure UnitI) G := by
          have h1 : ENNReal.ofReal (mA - δ) < ENNReal.ofReal mA :=
            ENNReal.ofReal_lt_ofReal_iff (by linarith) |>.mpr (by linarith)
          rw [ENNReal.ofReal_toReal (measure_ne_top _ _)] at h1
          exact lt_of_lt_of_le h1 hmA_le
        have hlt_lim : ENNReal.ofReal (mA - δ) < L.liminf (fun j => (empProbI A (N j) (hA1 j) : Measure UnitI) G) :=
          lt_of_lt_of_le hlt_en hliminfA
        have hev_en := eventually_lt_of_lt_liminf hlt_lim
        filter_upwards [hev_en, hN_L.eventually (eventually_ge_atTop 1)] with j hj hN1
        rw [max_eq_right (le_of_lt h0)]
        have hle_Icc : (empProbI A (N j) (hA1 j) : Measure UnitI) G ≤
            pushToReal (empProbI A (N j) (hA1 j)) (Set.Icc 0 (u + δ)) := by
          rw [pushToReal, Measure.map_apply measurable_subtype_coe measurableSet_Icc]
          apply measure_mono; intro x hx; exact ⟨x.2.1, le_of_lt hx⟩
        have : IsProbabilityMeasure (pushToReal (empProbI A (N j) (hA1 j))) := isProbabilityMeasure_pushToReal _
        have hto := ENNReal.toReal_mono (measure_ne_top _ _) (le_trans (le_of_lt hj) hle_Icc)
        rw [ENNReal.toReal_ofReal (le_of_lt h0), empProbI_measure_Iic (hA1 j) hN1 (by linarith) (le_of_lt huδ_lt1)] at hto
        exact hto
    have hevB : ∀ᶠ j in L, max 0 (mB - δ) ≤ (countNat B ⌊(u + δ) * (N j : ℝ)⌋₊ : ℝ) / (countNat B (N j) : ℝ) := by
      by_cases h0 : mB - δ ≤ 0
      · rw [max_eq_left h0]; exact Eventually.of_forall (fun _ => by positivity)
      · push Not at h0
        have hlt_en : ENNReal.ofReal (mB - δ) < (νI : Measure UnitI) G := by
          have h1 : ENNReal.ofReal (mB - δ) < ENNReal.ofReal mB :=
            ENNReal.ofReal_lt_ofReal_iff (by linarith) |>.mpr (by linarith)
          rw [ENNReal.ofReal_toReal (measure_ne_top _ _)] at h1
          exact lt_of_lt_of_le h1 hmB_le
        have hlt_lim : ENNReal.ofReal (mB - δ) < L.liminf (fun j => (empProbI B (N j) (hB1 j) : Measure UnitI) G) :=
          lt_of_lt_of_le hlt_en hliminfB
        have hev_en := eventually_lt_of_lt_liminf hlt_lim
        filter_upwards [hev_en, hN_L.eventually (eventually_ge_atTop 1)] with j hj hN1
        rw [max_eq_right (le_of_lt h0)]
        have hle_Icc : (empProbI B (N j) (hB1 j) : Measure UnitI) G ≤
            pushToReal (empProbI B (N j) (hB1 j)) (Set.Icc 0 (u + δ)) := by
          rw [pushToReal, Measure.map_apply measurable_subtype_coe measurableSet_Icc]
          apply measure_mono; intro x hx; exact ⟨x.2.1, le_of_lt hx⟩
        have : IsProbabilityMeasure (pushToReal (empProbI B (N j) (hB1 j))) := isProbabilityMeasure_pushToReal _
        have hto := ENNReal.toReal_mono (measure_ne_top _ _) (le_trans (le_of_lt hj) hle_Icc)
        rw [ENNReal.toReal_ofReal (le_of_lt h0), empProbI_measure_Iic (hB1 j) hN1 (by linarith) (le_of_lt huδ_lt1)] at hto
        exact hto
    have hprod_L : ∀ᶠ j in L, (countNat A ⌊(u + δ) * (N j : ℝ)⌋₊ : ℝ) * (countNat B ⌊(u + δ) * (N j : ℝ)⌋₊ : ℝ) ≤
        lam * ((u + δ) * (N j : ℝ)) := by
      have htend_x : Tendsto (fun j => (u + δ) * (N j : ℝ)) L atTop :=
        Tendsto.const_mul_atTop (by linarith) (tendsto_natCast_atTop_atTop.comp hN_L)
      filter_upwards [htend_x.eventually hprod_ev] with j hj
      have hnn : ¬ ((u + δ) * (N j : ℝ) < 0) := by push Not; positivity
      simpa [countReal, hnn] using hj
    have hAB_lb : ∀ᶠ j in L, (1 - δ) * (N j : ℝ) ≤ (countNat A (N j) : ℝ) * (countNat B (N j) : ℝ) ∧ 1 ≤ N j := by
      have h1 : Tendsto (fun j => (N j : ℝ)) L atTop := tendsto_natCast_atTop_atTop.comp hN_L
      filter_upwards [hN_L.eventually (eventually_ge_atTop (max n₀ 1)),
          h1.eventually (eventually_ge_atTop ((errSum A B n₀ : ℝ) / δ + 1))] with j hNj hbig
      have hAB := countNat_mul_eq_N_add_c_add_T hstab (le_trans (le_max_left _ _) hNj)
      have hcast : (countNat A (N j) : ℝ) * (countNat B (N j) : ℝ) =
          (N j : ℝ) + 1 + (errSigned A B n₀ : ℝ) + (crossExcess A B (N j) : ℝ) := by exact_mod_cast hAB
      have hc_ge : -(errSum A B n₀ : ℝ) ≤ (errSigned A B n₀ : ℝ) := by
        exact_mod_cast (abs_le.mp (abs_errSigned_le_errSum A B n₀)).1
      have hT_nn : (0 : ℝ) ≤ (crossExcess A B (N j) : ℝ) := Nat.cast_nonneg _
      have hδN : (errSum A B n₀ : ℝ) ≤ δ * (N j : ℝ) := by
        have h2 : (errSum A B n₀ : ℝ) / δ ≤ (N j : ℝ) := by linarith
        linarith [(div_le_iff₀ hδpos).mp h2]
      exact ⟨by linarith, le_trans (le_max_right _ _) hNj⟩
    obtain ⟨j, hjA, hjB, hjP, hjAB, hN1⟩ := (hevA.and (hevB.and (hprod_L.and hAB_lb))).exists
    have hNj_pos : (0 : ℝ) < (N j : ℝ) := Nat.cast_pos.mpr (by omega)
    have hAB_pos : (0 : ℝ) < (countNat A (N j) : ℝ) * (countNat B (N j) : ℝ) :=
      mul_pos (Nat.cast_pos.mpr (by have := hA1 j; omega)) (Nat.cast_pos.mpr (by have := hB1 j; omega))
    have hmul := mul_le_mul hjA hjB (le_max_left _ _) (by positivity)
    have hle1 : max 0 (mA - δ) * max 0 (mB - δ) * ((countNat A (N j) : ℝ) * (countNat B (N j) : ℝ)) ≤
        lam * ((u + δ) * (N j : ℝ)) := by
      have : ((countNat A ⌊(u + δ) * (N j : ℝ)⌋₊ : ℝ) / (countNat A (N j) : ℝ)) *
          ((countNat B ⌊(u + δ) * (N j : ℝ)⌋₊ : ℝ) / (countNat B (N j) : ℝ)) *
          ((countNat A (N j) : ℝ) * (countNat B (N j) : ℝ)) =
          (countNat A ⌊(u + δ) * (N j : ℝ)⌋₊ : ℝ) * (countNat B ⌊(u + δ) * (N j : ℝ)⌋₊ : ℝ) := by
        have hA0 : (countNat A (N j) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hA1 j; omega)
        have hB0 : (countNat B (N j) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hB1 j; omega)
        field_simp
      calc _ ≤ _ := mul_le_mul_of_nonneg_right hmul (le_of_lt hAB_pos)
        _ = _ := this
        _ ≤ _ := hjP
    have hle2 : max 0 (mA - δ) * max 0 (mB - δ) * ((1 - δ) * (N j : ℝ)) ≤ lam * ((u + δ) * (N j : ℝ)) :=
      le_trans (mul_le_mul_of_nonneg_left hjAB (mul_nonneg (le_max_left _ _) (le_max_left _ _))) hle1
    have hcancel : max 0 (mA - δ) * max 0 (mB - δ) * (1 - δ) ≤ lam * (u + δ) := by
      have : (max 0 (mA - δ) * max 0 (mB - δ) * (1 - δ)) * (N j : ℝ) ≤ (lam * (u + δ)) * (N j : ℝ) := by linarith
      exact le_of_mul_le_mul_right this hNj_pos
    linarith
  exact ⟨inferInstance, inferInstance, pushToReal_supported μI, pushToReal_supported νI, hconv, hbound⟩

/-! ### Part 4: Step 2 (No `(δ₀, leb01)`), Step 4 (No `M₁ ≥ 3`), and Proposition 4.3 -/

/-- Step 2 of Proposition 4.3: `(pushToReal μI, pushToReal νI)` cannot be `(δ₀, leb01)` when `lam < 8/5`. -/
private lemma weak_limit_ne_dirac_zero {A B : Set ℕ} (hA_inf : A.Infinite) (hB_inf : B.Infinite)
    {n₀ K : ℕ} (hn₀ : 1 ≤ n₀) (hstab : ∀ n ≥ n₀, repCount A B n = 1)
    {lam : ℝ} (hlam : lam < 8 / 5)
    (hprod_ev : ∀ᶠ x : ℝ in atTop, (countReal A x : ℝ) * (countReal B x : ℝ) ≤ lam * x)
    {N : ℕ → ℕ} (hN_top : Tendsto N atTop atTop) (hT_le : ∀ j, crossExcess A B (N j) ≤ K)
    (hA1 : ∀ j, 1 ≤ countNat A (N j)) (hB1 : ∀ j, 1 ≤ countNat B (N j))
    {L : Filter ℕ} [L.NeBot] (hL_le : L ≤ atTop)
    {μI νI : ProbabilityMeasure UnitI}
    (hν_lim : Tendsto (fun j => empProbI B (N j) (hB1 j)) L (𝓝 νI))
    (hconv : pushToReal μI ∗ pushToReal νI = leb01) :
    pushToReal μI ≠ Measure.dirac 0 := by
  classical
  intro hμ0
  have : IsProbabilityMeasure (pushToReal μI) := isProbabilityMeasure_pushToReal μI
  have : IsProbabilityMeasure (pushToReal νI) := isProbabilityMeasure_pushToReal νI
  have hν_leb : pushToReal νI = leb01 := by
    rw [hμ0, Measure.dirac_conv] at hconv; simpa using hconv
  have hN_L : Tendsto N L atTop := hN_top.mono_left hL_le
  have hcount_top : ∀ (S : Set ℕ), S.Infinite → Tendsto (fun M : ℕ => countNat S M) atTop atTop := by
    intro S hS
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨t, ht_sub, ht_card⟩ := hS.exists_subset_card_eq b
    refine ⟨t.sup id, fun M hM => ?_⟩
    unfold countNat
    calc b = t.card := ht_card.symm
      _ ≤ ((Finset.range (M + 1)).filter (· ∈ S)).card := by
            apply Finset.card_le_card; intro x hx
            have hle : x ≤ t.sup id := Finset.le_sup (f := id) hx
            exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ht_sub hx⟩
  -- For any η > 0, eventually along L we have maxLe A (N j) ≤ η * N j
  have ha_small : ∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ j in L, (maxLe A (N j) : ℝ) ≤ η * (N j : ℝ) := by
    intro η hη0 hη1
    -- νI (Ioo (1 - η) 1) = η > 0, so eventually B ∩ ((1 - η) N, N] has size ≥ (η/2) B(N) > K
    let G : Set UnitI := {x : UnitI | 1 - η < x.1}
    have hG_open : IsOpen G := isOpen_lt continuous_const continuous_subtype_val
    have hνG : (νI : Measure UnitI) G = ENNReal.ofReal η := by
      have h1 : (νI : Measure UnitI) G = pushToReal νI (Set.Ioc (1 - η) 1) := by
        rw [pushToReal, Measure.map_apply measurable_subtype_coe measurableSet_Ioc]
        congr 1; ext x; simp only [G, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioc]
        exact ⟨fun h => ⟨h, x.2.2⟩, fun h => h.1⟩
      rw [h1, hν_leb, leb01, Measure.restrict_apply measurableSet_Ioc]
      have hinter : Set.Ioc (1 - η) 1 ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc (1 - η) 1 :=
        Set.inter_eq_left.mpr (fun x hx => ⟨by linarith [hx.1], hx.2⟩)
      rw [hinter, Real.volume_Ioc]; congr 1; ring
    have hlt_lim : ENNReal.ofReal (η / 2) < L.liminf (fun j => (empProbI B (N j) (hB1 j) : Measure UnitI) G) :=
      lt_of_lt_of_le (by rw [hνG]; exact (ENNReal.ofReal_lt_ofReal_iff hη0).mpr (half_lt_self hη0))
        (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hν_lim hG_open)
    have hB_big : ∀ᶠ j in L, (2 * (K : ℝ) + 2) / η < (countNat B (N j) : ℝ) :=
      ((tendsto_natCast_atTop_atTop.comp ((hcount_top B hB_inf).comp hN_L)).eventually
        (eventually_gt_atTop ((2 * (K : ℝ) + 2) / η)))
    filter_upwards [eventually_lt_of_lt_liminf hlt_lim, hB_big, hN_L.eventually (eventually_ge_atTop 1)] with j hj hBj hN1
    by_contra hgt; push Not at hgt
    have ha_mem := maxLe_mem (N := N j) (by
      obtain ⟨a, ha⟩ := Finset.card_pos.mp (by have := hA1 j; unfold countNat at this; omega :
        0 < ((Finset.range (N j + 1)).filter (· ∈ A)).card)
      simp only [Finset.mem_filter, Finset.mem_range] at ha
      exact ⟨a, ha.2, by omega⟩)
    set a := maxLe A (N j)
    -- Every b ∈ B ∩ ((1 - η) N j, N j] gives a + b > N j!
    set Btail := ((Finset.range (N j + 1)).filter (· ∈ B)).filter (fun b : ℕ => (1 - η) * (N j : ℝ) < (b : ℝ))
    have htail_ge : (η / 2) * (countNat B (N j) : ℝ) ≤ (Btail.card : ℝ) := by
      have hG_eq : (empProbI B (N j) (hB1 j) : Measure UnitI) G =
          ((countNat B (N j) : ℝ≥0∞))⁻¹ * (Btail.card : ℝ≥0∞) := by
        have h1 : (empProbI B (N j) (hB1 j) : Measure UnitI) G =
            pushToReal (empProbI B (N j) (hB1 j)) (Set.Ioi (1 - η)) := by
          rw [pushToReal, Measure.map_apply measurable_subtype_coe measurableSet_Ioi]; rfl
        rw [h1, pushToReal_empProbI (hB1 j), Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
        congr 1
        have hNpos : (0 : ℝ) < (N j : ℝ) := Nat.cast_pos.mpr (by omega)
        have hterm : ∀ b ∈ (Finset.range (N j + 1)).filter (· ∈ B),
            Measure.dirac ((b : ℝ) / (N j : ℝ)) (Set.Ioi (1 - η)) =
              if (1 - η) * (N j : ℝ) < (b : ℝ) then (1 : ℝ≥0∞) else 0 := by
          intro b _; rw [Measure.dirac_apply' _ measurableSet_Ioi]
          by_cases h : (1 - η) * (N j : ℝ) < (b : ℝ)
          · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr ((lt_div_iff₀ hNpos).mpr h)), Pi.one_apply,
                ite_eq_left_iff.mpr (fun hn => absurd h hn)]
          · rw [Set.indicator_of_notMem (fun hm => h ((lt_div_iff₀ hNpos).mp (Set.mem_Ioi.mp hm))),
                ite_eq_right_iff.mpr (fun hn => absurd hn h)]
        rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hto := ENNReal.toReal_mono (measure_ne_top _ _) (le_of_lt hj)
      rw [hG_eq, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_mul, ENNReal.toReal_inv,
          ENNReal.toReal_natCast, ENNReal.toReal_natCast] at hto
      have hBp : (0 : ℝ) < (countNat B (N j) : ℝ) := Nat.cast_pos.mpr (by have := hB1 j; omega)
      have := mul_le_mul_of_nonneg_left hto (le_of_lt hBp)
      rw [← mul_assoc, mul_inv_cancel₀ hBp.ne', one_mul] at this
      linarith
    have htail_le_K : Btail.card ≤ K := by
      have hle_T : Btail.card ≤ crossExcess A B (N j) := by
        have hinj : Btail.card ≤ ((Finset.range (N j)).filter (fun m => 1 ≤ repTrunc A B (N j) (N j + 1 + m))).card := by
          apply Finset.card_le_card_of_injOn (fun b => a + b - (N j + 1))
          · intro b hb
            simp only [Btail, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hb ⊢
            have hab_gt : (N j : ℝ) < (a : ℝ) + (b : ℝ) := by linarith [hb.2]
            have hab_nat : N j < a + b := by exact_mod_cast hab_gt
            refine ⟨by omega, Finset.card_pos.mpr ⟨a, ?_⟩⟩
            simp only [Finset.mem_filter, Finset.mem_range]
            refine ⟨by omega, ha_mem.1, by omega, by omega, ?_⟩
            have : N j + 1 + (a + b - (N j + 1)) - a = b := by omega
            rw [this]; exact hb.1.2
          · intro b₁ h1 b₂ h2 heq
            simp only [Btail, Finset.mem_coe, Finset.mem_filter] at h1 h2
            have h1gt : N j < a + b₁ := by exact_mod_cast (show (N j : ℝ) < (a : ℝ) + (b₁ : ℝ) by linarith [h1.2])
            have h2gt : N j < a + b₂ := by exact_mod_cast (show (N j : ℝ) < (a : ℝ) + (b₂ : ℝ) by linarith [h2.2])
            dsimp only at heq; omega
        calc Btail.card ≤ ∑ _m ∈ (Finset.range (N j)).filter (fun m => 1 ≤ repTrunc A B (N j) (N j + 1 + m)), 1 := by simp [hinj]
          _ ≤ ∑ m ∈ (Finset.range (N j)).filter (fun m => 1 ≤ repTrunc A B (N j) (N j + 1 + m)), repTrunc A B (N j) (N j + 1 + m) :=
                Finset.sum_le_sum (fun m hm => (Finset.mem_filter.mp hm).2)
          _ ≤ crossExcess A B (N j) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      exact le_trans hle_T (hT_le j)
    have hK_r : (Btail.card : ℝ) ≤ (K : ℝ) := by exact_mod_cast htail_le_K
    have hmul := mul_lt_mul_of_pos_left hBj (half_pos hη0)
    have hsimp : η / 2 * ((2 * (K : ℝ) + 2) / η) = (K : ℝ) + 1 := by field_simp
    linarith
  -- Choose fixed η := 1 / 10000 and pick one huge j from L!
  set C1 := C1Const A B n₀ K
  set E := errSum A B n₀
  have hN_huge : ∀ᶠ j in L,
      max (10 ^ 6 * (C1 + K + E + n₀ + 1) ^ 2) (10 ^ 6) ≤ N j ∧
      (maxLe A (N j) : ℝ) ≤ (1 / 10000 : ℝ) * (N j : ℝ) ∧
      (K + 2) ≤ countNat A (N j) ∧
      (10 ^ 4 * (C1 + K + E + n₀ + 1)) ≤ countNat B (N j) ∧
      (10 ^ 4 * (C1 + K + E + n₀ + 1)) ≤ countNat B ⌊(1 / 100 : ℝ) * (N j : ℝ)⌋₊ ∧
      (∀ t ≥ N j, (countNat A t : ℝ) * (countNat B t : ℝ) ≤ lam * (t : ℝ)) := by
    have h1 := hN_L.eventually (eventually_ge_atTop (max (10 ^ 6 * (C1 + K + E + n₀ + 1) ^ 2) (10 ^ 6)))
    have h2 := ha_small (1 / 10000) (by norm_num) (by norm_num)
    have h2a := ((hcount_top A hA_inf).comp hN_L).eventually (eventually_ge_atTop (K + 2))
    have h3 := ((hcount_top B hB_inf).comp hN_L).eventually (eventually_ge_atTop (10 ^ 4 * (C1 + K + E + n₀ + 1)))
    have h4 : ∀ᶠ j in L, 10 ^ 4 * (C1 + K + E + n₀ + 1) ≤ countNat B ⌊(1 / 100 : ℝ) * (N j : ℝ)⌋₊ := by
      have htend : Tendsto (fun j => ⌊(1 / 100 : ℝ) * (N j : ℝ)⌋₊) L atTop :=
        tendsto_nat_floor_atTop.comp (Tendsto.const_mul_atTop (by norm_num) (tendsto_natCast_atTop_atTop.comp hN_L))
      exact ((hcount_top B hB_inf).comp htend).eventually (eventually_ge_atTop (10 ^ 4 * (C1 + K + E + n₀ + 1)))
    have h5 : ∀ᶠ j in L, ∀ t ≥ N j, (countNat A t : ℝ) * (countNat B t : ℝ) ≤ lam * (t : ℝ) := by
      rw [eventually_atTop] at hprod_ev
      rcases hprod_ev with ⟨R, hR⟩
      filter_upwards [hN_L.eventually (eventually_ge_atTop (⌈max R 0⌉₊ + 1))] with j hj t ht
      have ht_ge : R ≤ (t : ℝ) := by
        have h1 : (⌈max R 0⌉₊ : ℝ) ≤ (t : ℝ) := by exact_mod_cast (by omega : ⌈max R 0⌉₊ ≤ t)
        exact le_trans (le_max_left R 0) (le_trans (Nat.le_ceil _) h1)
      have hnn : ¬ ((t : ℝ) < 0) := by push Not; positivity
      have := hR (t : ℝ) ht_ge
      simpa [countReal, hnn, Nat.floor_natCast] using this
    exact h1.and (h2.and (h2a.and (h3.and (h4.and h5))))
  obtain ⟨j, hNbig, haj_le, hAN_big, _hBN_big, hBx_big, hprod_ge⟩ := hN_huge.exists
  set Nj := N j
  set aj := maxLe A Nj
  set gj := nextGt hA_inf Nj - 1
  set xj := ⌊(1 / 100 : ℝ) * (Nj : ℝ)⌋₊
  have hNj_ge_n0 : n₀ ≤ Nj := by
    calc n₀ ≤ C1 + K + E + n₀ + 1 := by omega
      _ ≤ (C1 + K + E + n₀ + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
      _ ≤ 10 ^ 6 * (C1 + K + E + n₀ + 1) ^ 2 := Nat.le_mul_of_pos_left _ (by norm_num)
      _ ≤ Nj := le_trans (le_max_left _ _) hNbig
  have hNj_big1 : 10 ^ 6 * (C1 + K + E + n₀ + 1) ^ 2 ≤ Nj := le_trans (le_max_left _ _) hNbig
  have hy_spec := nextGt_spec hA_inf Nj
  have hgj_ge_Nj : Nj ≤ gj := by omega
  have hNA : Nj ∉ A := by
    intro hmem
    have := le_maxLe (N := Nj) hmem le_rfl
    have h1 : (Nj : ℝ) ≤ (aj : ℝ) := by exact_mod_cast this
    have h2 : (1 : ℝ) ≤ (Nj : ℝ) := by exact_mod_cast (by omega : 1 ≤ Nj)
    linarith
  have hNB : Nj ∉ B := by
    intro hmem
    -- Every a ∈ A ∩ [1, Nj] gives crossing pair (a, Nj) with a + Nj > Nj, contradicting T(Nj) ≤ K < K + 1 ≤ A(Nj) - 1!
    set Apos := ((Finset.range (Nj + 1)).filter (· ∈ A)).filter (fun a => 1 ≤ a)
    have hApos_card : K + 1 ≤ Apos.card := by
      have hle : countNat A Nj ≤ Apos.card + 1 := by
        unfold countNat
        calc ((Finset.range (Nj + 1)).filter (· ∈ A)).card
            ≤ (Apos ∪ {0}).card := by
              apply Finset.card_le_card; intro a ha
              simp only [Finset.mem_union, Finset.mem_singleton, Apos, Finset.mem_filter] at ha ⊢
              by_cases ha0 : a = 0
              · right; exact ha0
              · left; exact ⟨ha, by omega⟩
          _ ≤ Apos.card + ({0} : Finset ℕ).card := Finset.card_union_le _ _
          _ = Apos.card + 1 := by simp
      omega
    have hApos_le_T : Apos.card ≤ crossExcess A B Nj := by
      have hinj : Apos.card ≤ ((Finset.range Nj).filter (fun m => 1 ≤ repTrunc A B Nj (Nj + 1 + m))).card := by
        apply Finset.card_le_card_of_injOn (fun a => a - 1)
        · intro a ha
          simp only [Apos, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha ⊢
          refine ⟨by omega, Finset.card_pos.mpr ⟨a, ?_⟩⟩
          simp only [Finset.mem_filter, Finset.mem_range]
          refine ⟨by omega, ha.1.2, by omega, by omega, ?_⟩
          have : Nj + 1 + (a - 1) - a = Nj := by omega
          rw [this]; exact hmem
        · intro a1 h1 a2 h2 heq
          simp only [Apos, Finset.mem_coe, Finset.mem_filter] at h1 h2; dsimp only at heq; omega
      calc Apos.card ≤ ∑ _m ∈ (Finset.range Nj).filter (fun m => 1 ≤ repTrunc A B Nj (Nj + 1 + m)), 1 := by simp [hinj]
        _ ≤ ∑ m ∈ (Finset.range Nj).filter (fun m => 1 ≤ repTrunc A B Nj (Nj + 1 + m)), repTrunc A B Nj (Nj + 1 + m) :=
              Finset.sum_le_sum (fun m hm => (Finset.mem_filter.mp hm).2)
        _ ≤ crossExcess A B Nj := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hTj : crossExcess A B Nj ≤ K := hT_le j
    omega
  -- Bounds on aj, xj, T(gj), A(gj) = A(aj), and B(gj + xj) - B(gj) ≤ C1 + 1
  have hxj_le : (xj : ℝ) ≤ (1 / 100 : ℝ) * (Nj : ℝ) := Nat.floor_le (by positivity)
  have hxj_gt : (1 / 100 : ℝ) * (Nj : ℝ) - 1 < (xj : ℝ) := by
    have := Nat.lt_floor_add_one ((1 / 100 : ℝ) * (Nj : ℝ))
    change (1 / 100 : ℝ) * (Nj : ℝ) < (xj : ℝ) + 1 at this; linarith
  have hAgj_eq : countNat A gj = countNat A aj := by
    unfold countNat; congr 1; ext a; simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, haA⟩
      have haN : a ≤ Nj := by
        by_contra hgt; have := nextGt_le hA_inf (N := Nj) haA (by omega); omega
      exact ⟨by have := le_maxLe (N := Nj) haA haN; omega, haA⟩
    · rintro ⟨h1, haA⟩
      have haj_le_N : aj ≤ Nj := by
        have : (aj : ℝ) ≤ (Nj : ℝ) := by linarith
        exact_mod_cast this
      exact ⟨by omega, haA⟩
  have hTgj_le : crossExcess A B gj ≤ aj + 2 * E := by
    have h1 := countNat_mul_eq_N_add_c_add_T hstab (by omega : n₀ ≤ gj)
    have h2 := countNat_mul_le_add_errSum hstab aj gj
    rw [hAgj_eq] at h1
    have hc := (abs_le.mp (abs_errSigned_le_errSum A B n₀)).1
    omega
  have hAgj_Bgj_ge : (gj : ℝ) - (E : ℝ) ≤ (countNat A gj : ℝ) * (countNat B gj : ℝ) := by
    have h1 := countNat_mul_eq_N_add_c_add_T hstab (by omega : n₀ ≤ gj)
    have hcast : (countNat A gj : ℝ) * (countNat B gj : ℝ) =
        (gj : ℝ) + 1 + (errSigned A B n₀ : ℝ) + (crossExcess A B gj : ℝ) := by exact_mod_cast h1
    have hc : -(E : ℝ) ≤ (errSigned A B n₀ : ℝ) := by exact_mod_cast (abs_le.mp (abs_errSigned_le_errSum A B n₀)).1
    have hTnn : (0 : ℝ) ≤ (crossExcess A B gj : ℝ) := Nat.cast_nonneg _
    linarith
  have hNj_ge106_r : (10 ^ 6 : ℝ) ≤ (Nj : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hNbig
  -- Bound B(gj + xj) - B(gj) ≤ C1 + 1 via modular_difference_density
  have hB_diff_le : countNat B (gj + xj) - countNat B gj ≤ C1 + 1 := by
    have hmd := (modular_difference_density hstab hNj_ge_n0 (by omega) hNA hNB (hT_le j)
      (x₀ := aj) (z₀ := maxLe B Nj)
      (fun a ha haN => le_maxLe (N := Nj) ha (le_of_lt haN))
      (fun b hb hbN => le_maxLe (N := Nj) hb (le_of_lt hbN))).1
    set B_new := (Finset.Ioc (gj + 1) (gj + xj)).filter (· ∈ B)
    have hdiff_le : countNat B (gj + xj) - countNat B gj ≤ B_new.card + 1 := by
      have hunion : (Finset.range (gj + xj + 1)).filter (· ∈ B) ⊆
          (Finset.range (gj + 1)).filter (· ∈ B) ∪ B_new ∪ {gj + 1} := by
        intro b hb
        simp only [Finset.mem_union, Finset.mem_singleton, B_new, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hb ⊢
        by_cases h1 : b ≤ gj
        · left; left; exact ⟨by omega, hb.2⟩
        · by_cases h2 : b = gj + 1
          · right; exact h2
          · left; right; exact ⟨⟨by omega, by omega⟩, hb.2⟩
      have hc : countNat B (gj + xj) ≤ countNat B gj + B_new.card + 1 := by
        unfold countNat
        calc ((Finset.range (gj + xj + 1)).filter (· ∈ B)).card
            ≤ ((Finset.range (gj + 1)).filter (· ∈ B) ∪ B_new ∪ {gj + 1}).card := Finset.card_le_card hunion
          _ ≤ ((Finset.range (gj + 1)).filter (· ∈ B) ∪ B_new).card + ({gj + 1} : Finset ℕ).card := Finset.card_union_le _ _
          _ ≤ ((Finset.range (gj + 1)).filter (· ∈ B)).card + B_new.card + 1 := by
                have := Finset.card_union_le ((Finset.range (gj + 1)).filter (· ∈ B)) B_new; simp at this ⊢; omega
      omega
    have hBnew_le : B_new.card ≤ C1 := by
      set A₀ := (Finset.range Nj).filter (· ∈ A)
      set B₀ := (Finset.range Nj).filter (· ∈ B)
      calc B_new.card
          ≤ ((Finset.range (Nj - aj)).filter (fun d => ¬ ∃ a ∈ A₀, ∃ b ∈ B₀, b = a + d)).card := by
            apply Finset.card_le_card_of_injOn (fun b => b - (gj + 1))
            · intro b hb
              simp only [B_new, Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hb ⊢
              have hlt_diff : b - (gj + 1) < Nj - aj := by
                have h1 : b - (gj + 1) ≤ xj := by omega
                have h2 : (xj : ℝ) + (aj : ℝ) + 1 ≤ (Nj : ℝ) := by linarith
                have h3 : xj + aj + 1 ≤ Nj := by exact_mod_cast h2
                omega
              refine ⟨hlt_diff, ?_⟩
              rintro ⟨a₀, ha₀, b₀, hb₀, heq⟩
              simp only [A₀, B₀, Finset.mem_filter, Finset.mem_range] at ha₀ hb₀
              have hy_eq : gj + 1 = nextGt hA_inf Nj := by omega
              have hdiff : b + a₀ = b₀ + nextGt hA_inf Nj := by omega
              have hne : nextGt hA_inf Nj ≠ a₀ ∨ b ≠ b₀ := Or.inl (by omega)
              have hsmall := unique_large_diff hstab hy_spec.2 ha₀.2 hb.2 hb₀.2 hdiff hne
              omega
            · intro b1 h1 b2 h2 heq
              simp only [B_new, Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at h1 h2
              dsimp only at heq; omega
        _ ≤ C1 := hmd
    omega
  -- Cover [gj + 1, gj + xj] by crossing pairs (≤ T(gj)), (A_new + B_x), and (A_aj + B_new)
  set Icov := Finset.Icc (gj + 1) (gj + xj)
  set A_new := (Finset.Icc (gj + 1) (gj + xj)).filter (· ∈ A)
  set B_x := (Finset.range (xj + 1)).filter (· ∈ B)
  set A_0 := (Finset.range (aj + 1)).filter (· ∈ A)
  set B_new_all := (Finset.Icc (gj + 1) (gj + xj)).filter (· ∈ B)
  set S_cross := (((Finset.range (gj + 1)).filter (· ∈ A) ×ˢ (Finset.range (gj + 1)).filter (· ∈ B)).filter
    (fun p => gj < p.1 + p.2)).image (fun p => p.1 + p.2)
  have hcover : Icov ⊆ S_cross ∪ (A_new ×ˢ B_x).image (fun p => p.1 + p.2) ∪
      (A_0 ×ˢ B_new_all).image (fun p => p.1 + p.2) := by
    intro n hn
    simp only [Icov, Finset.mem_Icc] at hn
    have hr1 : repCount A B n = 1 := hstab n (by omega)
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < repCount A B n)
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    set b := n - a
    have hab : a + b = n := by omega
    by_cases ha_le : a ≤ gj
    · by_cases hb_le : b ≤ gj
      · apply Finset.mem_union_left; apply Finset.mem_union_left
        rw [Finset.mem_image]; refine ⟨(a, b), ?_, hab⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        exact ⟨⟨⟨by omega, ha.2.1⟩, ⟨by omega, ha.2.2⟩⟩, by omega⟩
      · apply Finset.mem_union_right
        rw [Finset.mem_image]; refine ⟨(a, b), ?_, hab⟩
        have ha_aj : a ≤ aj := by
          have haN : a ≤ Nj := by by_contra hgt; have := nextGt_le hA_inf (N := Nj) ha.2.1 (by omega); omega
          exact le_maxLe (N := Nj) ha.2.1 haN
        simp only [Finset.mem_product, A_0, B_new_all, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
        exact ⟨⟨by omega, ha.2.1⟩, ⟨⟨by omega, by omega⟩, ha.2.2⟩⟩
    · apply Finset.mem_union_left; apply Finset.mem_union_right
      rw [Finset.mem_image]; refine ⟨(a, b), ?_, hab⟩
      simp only [Finset.mem_product, A_new, B_x, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
      exact ⟨⟨⟨by omega, by omega⟩, ha.2.1⟩, ⟨by omega, ha.2.2⟩⟩
  have hScross_le : S_cross.card ≤ crossExcess A B gj := by
    have hmap : ∀ p ∈ ((Finset.range (gj + 1)).filter (· ∈ A) ×ˢ (Finset.range (gj + 1)).filter (· ∈ B)).filter
        (fun p => gj < p.1 + p.2), p.1 + p.2 - (gj + 1) ∈ Finset.range gj := fun p hp => by
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢; omega
    have hle : (((Finset.range (gj + 1)).filter (· ∈ A) ×ˢ (Finset.range (gj + 1)).filter (· ∈ B)).filter
        (fun p => gj < p.1 + p.2)).card ≤ crossExcess A B gj := by
      rw [Finset.card_eq_sum_card_fiberwise hmap]; unfold crossExcess
      apply Finset.sum_le_sum; intro m _; unfold repTrunc
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
        refine ⟨hp.1.1.1.1, hp.1.1.1.2, by omega, by omega, ?_⟩
        have : gj + 1 + m - p.1 = p.2 := by omega
        rw [this]; exact hp.1.1.2.2
      · rintro ⟨a1, b1⟩ h1 ⟨a2, b2⟩ h2 heq
        simp only [Finset.mem_coe, Finset.mem_filter] at h1 h2; dsimp only at heq; ext <;> omega
    exact le_trans Finset.card_image_le hle
  have hBnew_all_le : B_new_all.card ≤ C1 + 1 := by
    have heq : B_new_all.card = countNat B (gj + xj) - countNat B gj := by
      have hadd : countNat B gj + B_new_all.card = countNat B (gj + xj) := by
        unfold countNat; rw [← Finset.card_union_of_disjoint]
        · congr 1; ext b; simp only [B_new_all, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
          constructor
          · rintro (⟨h1, hB⟩ | ⟨⟨h1, h2⟩, hB⟩) <;> exact ⟨by omega, hB⟩
          · rintro ⟨h1, hB⟩
            by_cases h : b ≤ gj
            · left; exact ⟨by omega, hB⟩
            · right; exact ⟨⟨by omega, by omega⟩, hB⟩
        · rw [Finset.disjoint_left]; intro b h1 h2
          simp only [B_new_all, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at h1 h2; omega
      omega
    omega
  have hcov_card : xj ≤ crossExcess A B gj + A_new.card * countNat B xj + countNat A gj * (C1 + 1) := by
    have hIcov : Icov.card = xj := by simp [Icov, Nat.card_Icc]
    calc xj = Icov.card := hIcov.symm
      _ ≤ (S_cross ∪ (A_new ×ˢ B_x).image (fun p => p.1 + p.2) ∪
            (A_0 ×ˢ B_new_all).image (fun p => p.1 + p.2)).card := Finset.card_le_card hcover
      _ ≤ (S_cross ∪ (A_new ×ˢ B_x).image (fun p => p.1 + p.2)).card +
            ((A_0 ×ˢ B_new_all).image (fun p => p.1 + p.2)).card := Finset.card_union_le _ _
      _ ≤ S_cross.card + ((A_new ×ˢ B_x).image (fun p => p.1 + p.2)).card +
            ((A_0 ×ˢ B_new_all).image (fun p => p.1 + p.2)).card :=
            Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ crossExcess A B gj + (A_new ×ˢ B_x).card + (A_0 ×ˢ B_new_all).card := by
            have h1 := Finset.card_image_le (s := A_new ×ˢ B_x) (f := fun p : ℕ × ℕ => p.1 + p.2)
            have h2 := Finset.card_image_le (s := A_0 ×ˢ B_new_all) (f := fun p : ℕ × ℕ => p.1 + p.2)
            omega
      _ = crossExcess A B gj + A_new.card * countNat B xj + countNat A aj * B_new_all.card := by
            rw [Finset.card_product, Finset.card_product]; rfl
      _ ≤ crossExcess A B gj + A_new.card * countNat B xj + countNat A gj * (C1 + 1) := by
            rw [hAgj_eq]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hBnew_all_le) _
  -- Also A(gj) * B(xj) = A(aj) * B(xj) ≤ aj + xj + 1 + E
  have hAgj_Bx : countNat A gj * countNat B xj ≤ aj + xj + 1 + E := by
    rw [hAgj_eq]; exact countNat_mul_le_add_errSum hstab aj xj
  -- Now deduce (A(gj + xj) - A(gj)) ≥ 0.95 * A(gj), hence A(gj + xj) * B(gj + xj) / (gj + xj) ≥ 1.9 > 8/5!
  have hNj_lin : (10 ^ 6 : ℝ) * ((C1 : ℝ) + (K : ℝ) + (E : ℝ) + (n₀ : ℝ) + 1) ≤ (Nj : ℝ) := by
    have hnat : 10 ^ 6 * (C1 + K + E + n₀ + 1) ≤ Nj := by
      calc 10 ^ 6 * (C1 + K + E + n₀ + 1)
          ≤ 10 ^ 6 * (C1 + K + E + n₀ + 1) ^ 2 :=
            Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _)
        _ ≤ Nj := hNj_big1
    exact_mod_cast hnat
  have hBx_r : (10 ^ 4 : ℝ) * ((C1 : ℝ) + (K : ℝ) + (E : ℝ) + (n₀ : ℝ) + 1) ≤ (countNat B xj : ℝ) := by exact_mod_cast hBx_big
  have hBx_pos : (0 : ℝ) < (countNat B xj : ℝ) := by linarith
  have hcov_r : (xj : ℝ) ≤ (aj : ℝ) + 2 * (E : ℝ) + (A_new.card : ℝ) * (countNat B xj : ℝ) +
      (countNat A gj : ℝ) * ((C1 : ℝ) + 1) := by
    have h1 : xj ≤ (aj + 2 * E) + A_new.card * countNat B xj + countNat A gj * (C1 + 1) := by omega
    exact_mod_cast h1
  have hABx_r : (countNat A gj : ℝ) * (countNat B xj : ℝ) ≤ (aj : ℝ) + (xj : ℝ) + 1 + (E : ℝ) := by exact_mod_cast hAgj_Bx
  have hA_new_ge : (95 / 100 : ℝ) * (countNat A gj : ℝ) ≤ (A_new.card : ℝ) := by
    have hmul : (95 / 100 : ℝ) * ((countNat A gj : ℝ) * (countNat B xj : ℝ)) ≤
        (A_new.card : ℝ) * (countNat B xj : ℝ) := by
      have h1 : (countNat A gj : ℝ) * ((C1 : ℝ) + 1) ≤ (1 / 1000 : ℝ) * ((countNat A gj : ℝ) * (countNat B xj : ℝ)) := by
        have : ((C1 : ℝ) + 1) ≤ (1 / 1000 : ℝ) * (countNat B xj : ℝ) := by linarith
        have := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg (countNat A gj))
        linarith
      linarith
    exact le_of_mul_le_mul_right (by linarith) hBx_pos
  have hAgjxj_ge : (195 / 100 : ℝ) * (countNat A gj : ℝ) ≤ (countNat A (gj + xj) : ℝ) := by
    have h1 : countNat A gj + A_new.card = countNat A (gj + xj) := by
      unfold countNat; rw [← Finset.card_union_of_disjoint]
      · congr 1; ext a; simp only [A_new, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
        constructor
        · rintro (⟨h1, hA⟩ | ⟨⟨h1, h2⟩, hA⟩) <;> exact ⟨by omega, hA⟩
        · rintro ⟨h1, hA⟩
          by_cases h : a ≤ gj
          · left; exact ⟨by omega, hA⟩
          · right; exact ⟨⟨by omega, by omega⟩, hA⟩
      · rw [Finset.disjoint_left]; intro a h1 h2
        simp only [A_new, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at h1 h2; omega
    have h2 : (countNat A gj : ℝ) + (A_new.card : ℝ) = (countNat A (gj + xj) : ℝ) := by exact_mod_cast h1
    linarith
  have hBgjxj_ge : (countNat B gj : ℝ) ≤ (countNat B (gj + xj) : ℝ) := by
    have hle : countNat B gj ≤ countNat B (gj + xj) := by
      unfold countNat; apply Finset.card_le_card; intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb ⊢; exact ⟨by omega, hb.2⟩
    exact_mod_cast hle
  have hprod_gjxj := hprod_ge (gj + xj) (by omega)
  have hprod_lb : (195 / 100 : ℝ) * ((gj : ℝ) - (E : ℝ)) ≤ (countNat A (gj + xj) : ℝ) * (countNat B (gj + xj) : ℝ) := by
    calc (195 / 100 : ℝ) * ((gj : ℝ) - (E : ℝ))
        ≤ (195 / 100 : ℝ) * ((countNat A gj : ℝ) * (countNat B gj : ℝ)) := by linarith
      _ = ((195 / 100 : ℝ) * (countNat A gj : ℝ)) * (countNat B gj : ℝ) := by ring
      _ ≤ (countNat A (gj + xj) : ℝ) * (countNat B (gj + xj) : ℝ) :=
            mul_le_mul hAgjxj_ge hBgjxj_ge (Nat.cast_nonneg _) (by positivity)
  have hgj_ge_N_r : (Nj : ℝ) ≤ (gj : ℝ) := by exact_mod_cast hgj_ge_Nj
  have hcast_sum : ((gj + xj : ℕ) : ℝ) = (gj : ℝ) + (xj : ℝ) := by push_cast; rfl
  rw [hcast_sum] at hprod_gjxj
  -- 1.95 * (gj - E) ≤ lam * (gj + xj) < 1.6 * (1.01 * gj) = 1.616 * gj, contradiction!
  have hlam_bound : lam * ((gj : ℝ) + (xj : ℝ)) ≤ (8 / 5 : ℝ) * ((gj : ℝ) + (xj : ℝ)) :=
    mul_le_mul_of_nonneg_right (le_of_lt hlam) (by positivity)
  linarith

/-- Step 4 of Proposition 4.3: rules out the `M₁ ≥ 3` branch using `zhang_gap_lemma`. -/
private lemma weak_limit_no_M1_ge_3 {A B : Set ℕ} (hA_inf : A.Infinite) (hB_inf : B.Infinite)
    {n₀ K : ℕ} (hn₀ : 1 ≤ n₀) (hstab : ∀ n ≥ n₀, repCount A B n = 1)
    {lam : ℝ} (hlam : lam < 8 / 5)
    (hprod_ev : ∀ᶠ x : ℝ in atTop, (countReal A x : ℝ) * (countReal B x : ℝ) ≤ lam * x)
    {N : ℕ → ℕ} (hN_top : Tendsto N atTop atTop) (hT_le : ∀ j, crossExcess A B (N j) ≤ K)
    (hA1 : ∀ j, 1 ≤ countNat A (N j)) (hB1 : ∀ j, 1 ≤ countNat B (N j))
    {L : Filter ℕ} [L.NeBot] (hL_le : L ≤ atTop)
    {μI : ProbabilityMeasure UnitI}
    (hμ_lim : Tendsto (fun j => empProbI A (N j) (hA1 j)) L (𝓝 μI))
    {M₁ : ℕ} (hM1 : 3 ≤ M₁)
    (hμ_tail : (1 / (64 * (M₁ : ℝ≥0∞))) ≤ pushToReal μI (Set.Ioo (1 - 2 / (3 * (M₁ : ℝ)) - 1 / 100) 2)) :
    False := by
  classical
  have hN_L : Tendsto N L atTop := hN_top.mono_left hL_le
  have hcount_top : ∀ (S : Set ℕ), S.Infinite → Tendsto (fun M : ℕ => countNat S M) atTop atTop := by
    intro S hS; rw [tendsto_atTop_atTop]; intro b
    obtain ⟨t, ht_sub, ht_card⟩ := hS.exists_subset_card_eq b
    refine ⟨t.sup id, fun M hM => ?_⟩
    unfold countNat
    calc b = t.card := ht_card.symm
      _ ≤ ((Finset.range (M + 1)).filter (· ∈ S)).card := by
            apply Finset.card_le_card; intro x hx
            have hle : x ≤ t.sup id := Finset.le_sup (f := id) hx
            exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ht_sub hx⟩
  -- Open set G := {x : UnitI | 1 - 2/(3 M₁) - 1/100 < x.1} has μI G ≥ 1/(64 M₁) > 0
  set α := 2 / (3 * (M₁ : ℝ)) + 1 / 100
  have hα_le : α ≤ 2 / 9 + 1 / 100 := by
    have hM1r : (3 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hM1
    have : 2 / (3 * (M₁ : ℝ)) ≤ 2 / 9 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    simp only [α]; linarith
  let G : Set UnitI := {x : UnitI | 1 - α < x.1}
  have hG_open : IsOpen G := isOpen_lt continuous_const continuous_subtype_val
  have hμG : (1 / (64 * (M₁ : ℝ≥0∞))) ≤ (μI : Measure UnitI) G := by
    have h1 : pushToReal μI (Set.Ioo (1 - 2 / (3 * (M₁ : ℝ)) - 1 / 100) 2) ≤ (μI : Measure UnitI) G := by
      rw [pushToReal, Measure.map_apply measurable_subtype_coe measurableSet_Ioo]
      apply measure_mono; intro x hx; simp only [Set.mem_preimage, Set.mem_Ioo] at hx
      simp only [G, Set.mem_ofPred_eq, α]; linarith [hx.1]
    exact le_trans hμ_tail h1
  have hM1p : (0 : ℝ) < (M₁ : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlt_lim : ENNReal.ofReal (1 / (128 * (M₁ : ℝ))) < L.liminf (fun j => (empProbI A (N j) (hA1 j) : Measure UnitI) G) := by
    have hstrict : ENNReal.ofReal (1 / (128 * (M₁ : ℝ))) < 1 / (64 * (M₁ : ℝ≥0∞)) := by
      have heq : (1 / (64 * (M₁ : ℝ≥0∞))) = ENNReal.ofReal (1 / (64 * (M₁ : ℝ))) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
      rw [heq, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith
    exact lt_of_lt_of_le hstrict (le_trans hμG (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ_lim hG_open))
  -- Eventually along L: B ∩ (α * N j, N j] = ∅!
  have hB_gap : ∀ᶠ j in L, (maxLe B (N j) : ℝ) ≤ α * (N j : ℝ) := by
    have hA_big : ∀ᶠ j in L, 128 * (M₁ : ℝ) * ((K : ℝ) + 1) < (countNat A (N j) : ℝ) :=
      (tendsto_natCast_atTop_atTop.comp ((hcount_top A hA_inf).comp hN_L)).eventually
        (eventually_gt_atTop (128 * (M₁ : ℝ) * ((K : ℝ) + 1)))
    filter_upwards [eventually_lt_of_lt_liminf hlt_lim, hA_big, hN_L.eventually (eventually_ge_atTop 1)] with j hj hAj hN1
    by_contra hgt; push Not at hgt
    have hb_mem := maxLe_mem (N := N j) (by
      obtain ⟨b, hb⟩ := Finset.card_pos.mp (by have := hB1 j; unfold countNat at this; omega :
        0 < ((Finset.range (N j + 1)).filter (· ∈ B)).card)
      simp only [Finset.mem_filter, Finset.mem_range] at hb
      exact ⟨b, hb.2, by omega⟩)
    set b := maxLe B (N j)
    set Atail := ((Finset.range (N j + 1)).filter (· ∈ A)).filter (fun a : ℕ => (1 - α) * (N j : ℝ) < (a : ℝ))
    have htail_ge : (1 / (128 * (M₁ : ℝ))) * (countNat A (N j) : ℝ) ≤ (Atail.card : ℝ) := by
      have hG_eq : (empProbI A (N j) (hA1 j) : Measure UnitI) G =
          ((countNat A (N j) : ℝ≥0∞))⁻¹ * (Atail.card : ℝ≥0∞) := by
        have h1 : (empProbI A (N j) (hA1 j) : Measure UnitI) G =
            pushToReal (empProbI A (N j) (hA1 j)) (Set.Ioi (1 - α)) := by
          rw [pushToReal, Measure.map_apply measurable_subtype_coe measurableSet_Ioi]; rfl
        rw [h1, pushToReal_empProbI (hA1 j), Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
        congr 1
        have hNpos : (0 : ℝ) < (N j : ℝ) := Nat.cast_pos.mpr (by omega)
        have hterm : ∀ a ∈ (Finset.range (N j + 1)).filter (· ∈ A),
            Measure.dirac ((a : ℝ) / (N j : ℝ)) (Set.Ioi (1 - α)) =
              if (1 - α) * (N j : ℝ) < (a : ℝ) then (1 : ℝ≥0∞) else 0 := by
          intro a _; rw [Measure.dirac_apply' _ measurableSet_Ioi]
          by_cases h : (1 - α) * (N j : ℝ) < (a : ℝ)
          · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr ((lt_div_iff₀ hNpos).mpr h)), Pi.one_apply,
                ite_eq_left_iff.mpr (fun hn => absurd h hn)]
          · rw [Set.indicator_of_notMem (fun hm => h ((lt_div_iff₀ hNpos).mp (Set.mem_Ioi.mp hm))),
                ite_eq_right_iff.mpr (fun hn => absurd hn h)]
        rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hto := ENNReal.toReal_mono (measure_ne_top _ _) (le_of_lt hj)
      rw [hG_eq, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul, ENNReal.toReal_inv,
          ENNReal.toReal_natCast, ENNReal.toReal_natCast] at hto
      have hAp : (0 : ℝ) < (countNat A (N j) : ℝ) := Nat.cast_pos.mpr (by have := hA1 j; omega)
      have := mul_le_mul_of_nonneg_left hto (le_of_lt hAp)
      rw [← mul_assoc, mul_inv_cancel₀ hAp.ne', one_mul] at this
      linarith
    have htail_le_K : Atail.card ≤ K := by
      have hinj : Atail.card ≤ ((Finset.range (N j)).filter (fun m => 1 ≤ repTrunc A B (N j) (N j + 1 + m))).card := by
        apply Finset.card_le_card_of_injOn (fun a => a + b - (N j + 1))
        · intro a ha
          simp only [Atail, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha ⊢
          have hab_nat : N j < a + b := by exact_mod_cast (show (N j : ℝ) < (a : ℝ) + (b : ℝ) by linarith [ha.2])
          refine ⟨by omega, Finset.card_pos.mpr ⟨a, ?_⟩⟩
          simp only [Finset.mem_filter, Finset.mem_range]
          refine ⟨by omega, ha.1.2, by omega, by omega, ?_⟩
          have : N j + 1 + (a + b - (N j + 1)) - a = b := by omega
          rw [this]; exact hb_mem.1
        · intro a1 h1 a2 h2 heq
          simp only [Atail, Finset.mem_coe, Finset.mem_filter] at h1 h2
          have h1gt : N j < a1 + b := by exact_mod_cast (show (N j : ℝ) < (a1 : ℝ) + (b : ℝ) by linarith [h1.2])
          have h2gt : N j < a2 + b := by exact_mod_cast (show (N j : ℝ) < (a2 : ℝ) + (b : ℝ) by linarith [h2.2])
          dsimp only at heq; omega
      have hle_T : Atail.card ≤ crossExcess A B (N j) := by
        calc Atail.card ≤ ∑ _m ∈ (Finset.range (N j)).filter (fun m => 1 ≤ repTrunc A B (N j) (N j + 1 + m)), 1 := by simp [hinj]
          _ ≤ ∑ m ∈ (Finset.range (N j)).filter (fun m => 1 ≤ repTrunc A B (N j) (N j + 1 + m)), repTrunc A B (N j) (N j + 1 + m) :=
                Finset.sum_le_sum (fun m hm => (Finset.mem_filter.mp hm).2)
          _ ≤ crossExcess A B (N j) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      exact le_trans hle_T (hT_le j)
    have hK_r : (Atail.card : ℝ) ≤ (K : ℝ) := by exact_mod_cast htail_le_K
    have hmul := mul_lt_mul_of_pos_left hAj (show (0 : ℝ) < 1 / (128 * (M₁ : ℝ)) by positivity)
    have hsimp : 1 / (128 * (M₁ : ℝ)) * (128 * (M₁ : ℝ) * ((K : ℝ) + 1)) = (K : ℝ) + 1 := by field_simp
    linarith
  -- Apply Zhang's Gap Lemma (with B playing the role of A!) at a huge index j ∈ L
  set E := errSum A B n₀
  set C := E + n₀
  have hrep_swap : ∀ n ≥ n₀, repCount B A n = 1 := fun n hn => by rw [repCount_comm]; exact hstab n hn
  have hE_swap : errSum B A n₀ = E := by
    unfold E errSum; apply Finset.sum_congr rfl; intro n _; rw [repCount_comm]
  have hhuge : ∀ᶠ j in L,
      max (10 ^ 4 * (C + n₀ + 1)) (10 ^ 4) ≤ N j ∧
      (maxLe B (N j) : ℝ) ≤ α * (N j : ℝ) ∧
      max (2 * n₀) (10 ^ 3 * (C + 1)) ≤ maxLe B (N j) ∧
      10 ^ 3 * (C + 1) ≤ countNat B (maxLe B (N j)) ∧
      (∀ t ≥ N j, (countNat A t : ℝ) * (countNat B t : ℝ) ≤ lam * (t : ℝ)) := by
    have h1 := hN_L.eventually (eventually_ge_atTop (max (10 ^ 4 * (C + n₀ + 1)) (10 ^ 4)))
    have h2 : ∀ᶠ j in L, max (2 * n₀) (10 ^ 3 * (C + 1)) ≤ maxLe B (N j) := by
      -- Pick b₀ ∈ B with b₀ ≥ max (2 * n₀) (10^3 * (C + 1)); for N j ≥ b₀, b₀ ≤ maxLe B (N j)!
      obtain ⟨b₀, hb₀B, hb₀_gt⟩ := hB_inf.exists_gt (max (2 * n₀) (10 ^ 3 * (C + 1)))
      filter_upwards [hN_L.eventually (eventually_ge_atTop b₀)] with j hj
      exact le_trans (le_of_lt hb₀_gt) (le_maxLe (N := N j) hb₀B hj)
    have h3 : ∀ᶠ j in L, 10 ^ 3 * (C + 1) ≤ countNat B (maxLe B (N j)) := by
      -- Since countNat B (maxLe B N) = countNat B N!
      filter_upwards [((hcount_top B hB_inf).comp hN_L).eventually (eventually_ge_atTop (10 ^ 3 * (C + 1)))] with j hj
      have heq : countNat B (maxLe B (N j)) = countNat B (N j) := by
        unfold countNat; congr 1; ext b; simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨h1, hbB⟩
          have hmem := maxLe_mem (N := N j) (by
            obtain ⟨b', hb'⟩ := Finset.card_pos.mp (by have := hB1 j; unfold countNat at this; omega :
              0 < ((Finset.range (N j + 1)).filter (· ∈ B)).card)
            simp only [Finset.mem_filter, Finset.mem_range] at hb'; exact ⟨b', hb'.2, by omega⟩)
          exact ⟨by omega, hbB⟩
        · rintro ⟨h1, hbB⟩; exact ⟨by have := le_maxLe (N := N j) hbB (by omega); omega, hbB⟩
      rwa [heq]
    have h4 : ∀ᶠ j in L, ∀ t ≥ N j, (countNat A t : ℝ) * (countNat B t : ℝ) ≤ lam * (t : ℝ) := by
      rw [eventually_atTop] at hprod_ev
      rcases hprod_ev with ⟨R, hR⟩
      filter_upwards [hN_L.eventually (eventually_ge_atTop (⌈max R 0⌉₊ + 1))] with j hj t ht
      have ht_ge : R ≤ (t : ℝ) := by
        have h1 : (⌈max R 0⌉₊ : ℝ) ≤ (t : ℝ) := by exact_mod_cast (by omega : ⌈max R 0⌉₊ ≤ t)
        exact le_trans (le_max_left R 0) (le_trans (Nat.le_ceil _) h1)
      have hnn : ¬ ((t : ℝ) < 0) := by push Not; positivity
      have := hR (t : ℝ) ht_ge
      simpa [countReal, hnn, Nat.floor_natCast] using this
    exact h1.and (hB_gap.and (h2.and (h3.and h4)))
  obtain ⟨j, hNbig, hxj_le, hxj_big, hBx_big, hprod_ge⟩ := hhuge.exists
  set Nj := N j
  set xj := maxLe B Nj
  set yj := nextGt hB_inf Nj
  have hx_mem := maxLe_mem (N := Nj) (by
    obtain ⟨b', hb'⟩ := Finset.card_pos.mp (by
      have h1 := hB1 j; unfold countNat at h1
      change 1 ≤ ((Finset.range (Nj + 1)).filter (· ∈ B)).card at h1
      omega : 0 < ((Finset.range (Nj + 1)).filter (· ∈ B)).card)
    simp only [Finset.mem_filter, Finset.mem_range] at hb'; exact ⟨b', hb'.2, by omega⟩)
  have hy_spec := nextGt_spec hB_inf Nj
  have hgap_B : ∀ b ∈ B, xj < b → yj ≤ b := fun b hbB hlt =>
    not_mem_Ioo_maxLe_nextGt hB_inf hbB hlt
  have h3x_le_y : 3 * xj + n₀ ≤ yj := by
    have hNj_r : (10 ^ 4 : ℝ) * ((C : ℝ) + (n₀ : ℝ) + 1) ≤ (Nj : ℝ) := by
      exact_mod_cast (le_trans (le_max_left _ _) hNbig)
    have hy_r : (Nj : ℝ) < (yj : ℝ) := by exact_mod_cast hy_spec.1
    have hαN : α * (Nj : ℝ) ≤ (2 / 9 + 1 / 100 : ℝ) * (Nj : ℝ) :=
      mul_le_mul_of_nonneg_right hα_le (Nat.cast_nonneg _)
    have : ((3 * xj + n₀ : ℕ) : ℝ) ≤ (yj : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hE_le : (∑ m ∈ Finset.range n₀, |(repCount B A m : ℤ) - 1|) ≤ (E : ℤ) := by
    rw [← hE_swap]; unfold errSum; push_cast
    exact le_rfl
  have hgap := zhang_gap_lemma hn₀ hrep_swap hE_le hx_mem.1 hy_spec.2 hgap_B
    (le_trans (le_max_left _ _) hxj_big) h3x_le_y
  have hB_dbl := (hgap.2.2 xj le_rfl).1
  have hprod_gap := (hgap.2.2 xj le_rfl).2
  -- Extract lower bounds B(yj + xj) ≥ 2 B(xj) - C and B(xj) * A(yj + xj) ≥ yj - C
  have hB_ge : 2 * (countNat B xj : ℝ) - (C : ℝ) ≤ (countNat B (yj + xj) : ℝ) := by
    have h1 := (abs_le.mp hB_dbl).1
    have hcast : -((E + n₀ : ℕ) : ℝ) ≤ (countNat B (yj + xj) : ℝ) - (countNat B xj : ℝ) - (countNat B xj : ℝ) := by
      exact_mod_cast h1
    simp only [C]; push_cast at hcast ⊢; linarith
  have hBA_ge : (yj : ℝ) - (C : ℝ) ≤ (countNat B xj : ℝ) * (countNat A (yj + xj) : ℝ) := by
    have h1 := (abs_le.mp hprod_gap).1
    have hcast : -((E + n₀ : ℕ) : ℝ) ≤ (countNat B xj : ℝ) * (countNat A (yj + xj) : ℝ) - (yj : ℝ) := by
      exact_mod_cast h1
    simp only [C]; push_cast at hcast ⊢; linarith
  have hprod_ub := hprod_ge (yj + xj) (by omega)
  -- Multiply: B(xj) * (A(yj+xj) * B(yj+xj)) ≥ (yj - C) * (2 B(xj) - C), divide by B(xj) > 0!
  have hBx_r : (10 ^ 3 : ℝ) * ((C : ℝ) + 1) ≤ (countNat B xj : ℝ) := by exact_mod_cast hBx_big
  have hBx_pos : (0 : ℝ) < (countNat B xj : ℝ) := by linarith
  have hNj_r : (10 ^ 4 : ℝ) * ((C : ℝ) + (n₀ : ℝ) + 1) ≤ (Nj : ℝ) := by
    exact_mod_cast (le_trans (le_max_left _ _) hNbig)
  have hy_r : (Nj : ℝ) < (yj : ℝ) := by exact_mod_cast hy_spec.1
  have hmul : ((yj : ℝ) - (C : ℝ)) * (2 * (countNat B xj : ℝ) - (C : ℝ)) ≤
      (countNat B xj : ℝ) * ((countNat A (yj + xj) : ℝ) * (countNat B (yj + xj) : ℝ)) := by
    calc ((yj : ℝ) - (C : ℝ)) * (2 * (countNat B xj : ℝ) - (C : ℝ))
        ≤ ((countNat B xj : ℝ) * (countNat A (yj + xj) : ℝ)) * (countNat B (yj + xj) : ℝ) :=
          mul_le_mul hBA_ge hB_ge (by linarith) (by positivity)
      _ = _ := by ring
  have hmul_ub : (countNat B xj : ℝ) * ((countNat A (yj + xj) : ℝ) * (countNat B (yj + xj) : ℝ)) ≤
      (countNat B xj : ℝ) * (lam * ((yj : ℝ) + (xj : ℝ))) := by
    have h1 := mul_le_mul_of_nonneg_left hprod_ub (le_of_lt hBx_pos)
    have hcast : ((yj + xj : ℕ) : ℝ) = (yj : ℝ) + (xj : ℝ) := by push_cast; rfl
    rwa [hcast] at h1
  -- Compare: (yj - C) * (2 B(xj) - C) ≥ 1.99 * yj * B(xj), while lam * (yj + xj) * B(xj) < 1.6 * (1 + 0.233) * yj * B(xj) < 1.98 * yj * B(xj)!
  have h1 : (199 / 100 : ℝ) * (yj : ℝ) * (countNat B xj : ℝ) ≤
      ((yj : ℝ) - (C : ℝ)) * (2 * (countNat B xj : ℝ) - (C : ℝ)) := by
    have hC1 : (C : ℝ) ≤ (1 / 1000 : ℝ) * (yj : ℝ) := by linarith
    have hC2 : (C : ℝ) ≤ (1 / 1000 : ℝ) * (countNat B xj : ℝ) := by linarith
    have h1a : (999 / 1000 : ℝ) * (yj : ℝ) ≤ (yj : ℝ) - (C : ℝ) := by linarith
    have h1b : (1999 / 1000 : ℝ) * (countNat B xj : ℝ) ≤ 2 * (countNat B xj : ℝ) - (C : ℝ) := by linarith
    have hnum : (199 / 100 : ℝ) ≤ (999 / 1000 : ℝ) * (1999 / 1000 : ℝ) := by norm_num
    calc (199 / 100 : ℝ) * (yj : ℝ) * (countNat B xj : ℝ)
        = (199 / 100 : ℝ) * ((yj : ℝ) * (countNat B xj : ℝ)) := by ring
      _ ≤ ((999 / 1000 : ℝ) * (1999 / 1000 : ℝ)) * ((yj : ℝ) * (countNat B xj : ℝ)) :=
          mul_le_mul_of_nonneg_right hnum (by positivity)
      _ = ((999 / 1000 : ℝ) * (yj : ℝ)) * ((1999 / 1000 : ℝ) * (countNat B xj : ℝ)) := by ring
      _ ≤ ((yj : ℝ) - (C : ℝ)) * (2 * (countNat B xj : ℝ) - (C : ℝ)) :=
          mul_le_mul h1a h1b (by positivity) (by linarith)
  have h2 : lam * ((yj : ℝ) + (xj : ℝ)) < (198 / 100 : ℝ) * (yj : ℝ) := by
    have hαN : α * (Nj : ℝ) ≤ (2 / 9 + 1 / 100 : ℝ) * (Nj : ℝ) :=
      mul_le_mul_of_nonneg_right hα_le (Nat.cast_nonneg _)
    have hx_lt_y : (xj : ℝ) ≤ (233 / 1000 : ℝ) * (yj : ℝ) := by linarith
    have hlam_lt : lam * ((yj : ℝ) + (xj : ℝ)) < (8 / 5 : ℝ) * ((yj : ℝ) + (xj : ℝ)) :=
      mul_lt_mul_of_pos_right hlam (by linarith)
    linarith
  have h3 := mul_lt_mul_of_pos_left h2 hBx_pos
  have hcomm : (countNat B xj : ℝ) * ((198 / 100 : ℝ) * (yj : ℝ)) =
      (198 / 100 : ℝ) * (yj : ℝ) * (countNat B xj : ℝ) := by ring
  have hyB_pos : (0 : ℝ) < (yj : ℝ) * (countNat B xj : ℝ) := mul_pos (by linarith) hBx_pos
  linarith

/-- **Proposition 4.3 (Unique Weak Limit Along Every Bounded-Crossing Sequence):**
Under `limsup A(x)B(x)/x < 8/5`, any weak cluster point `(μI, νI)` of `(empProbI A (N j), empProbI B (N j))`
along a filter `L ≤ atTop` with `T(N j) ≤ K` satisfies
`(pushToReal μI, pushToReal νI) ∈ {(cantorNu, cantorMu), (cantorMu, cantorNu)}`. -/
theorem weak_limit_unique {A B : Set ℕ} (hA_inf : A.Infinite) (hB_inf : B.Infinite)
    {n₀ K : ℕ} (hn₀ : 1 ≤ n₀) (hstab : ∀ n ≥ n₀, repCount A B n = 1)
    {lam : ℝ} (hlam : lam < 8 / 5)
    (hprod_ev : ∀ᶠ x : ℝ in atTop, (countReal A x : ℝ) * (countReal B x : ℝ) ≤ lam * x)
    {N : ℕ → ℕ} (hN_top : Tendsto N atTop atTop) (hT_le : ∀ j, crossExcess A B (N j) ≤ K)
    (hA1 : ∀ j, 1 ≤ countNat A (N j)) (hB1 : ∀ j, 1 ≤ countNat B (N j))
    {L : Filter ℕ} [L.NeBot] (hL_le : L ≤ atTop)
    {μI νI : ProbabilityMeasure UnitI}
    (hμ_lim : Tendsto (fun j => empProbI A (N j) (hA1 j)) L (𝓝 μI))
    (hν_lim : Tendsto (fun j => empProbI B (N j) (hB1 j)) L (𝓝 νI)) :
    (pushToReal μI = cantorNu ∧ pushToReal νI = cantorMu) ∨
    (pushToReal μI = cantorMu ∧ pushToReal νI = cantorNu) := by
  have : IsProbabilityMeasure (pushToReal μI) := isProbabilityMeasure_pushToReal μI
  have : IsProbabilityMeasure (pushToReal νI) := isProbabilityMeasure_pushToReal νI
  have hsub := weak_limit_is_subcritical hn₀ hstab hprod_ev hN_top hT_le hA1 hB1 hL_le hμ_lim hν_lim
  have hμ_ne : pushToReal μI ≠ Measure.dirac 0 :=
    weak_limit_ne_dirac_zero hA_inf hB_inf hn₀ hstab hlam hprod_ev hN_top hT_le hA1 hB1 hL_le hν_lim hsub.2.2.2.2.1
  have hν_ne : pushToReal νI ≠ Measure.dirac 0 := by
    have hstab' : ∀ n ≥ n₀, repCount B A n = 1 := fun n hn => by rw [repCount_comm]; exact hstab n hn
    have hprod_ev' : ∀ᶠ x : ℝ in atTop, (countReal B x : ℝ) * (countReal A x : ℝ) ≤ lam * x := by
      filter_upwards [hprod_ev] with x hx; linarith
    have hT_le' : ∀ j, crossExcess B A (N j) ≤ K := fun j => by rw [crossExcess_comm]; exact hT_le j
    exact weak_limit_ne_dirac_zero hB_inf hA_inf hn₀ hstab' hlam hprod_ev' hN_top hT_le' hB1 hA1 hL_le hμ_lim
      (by rw [Measure.conv_comm]; exact hsub.2.2.2.2.1)
  rcases classify_subcritical_pair hsub hlam hμ_ne hν_ne with h1 | h2 | ⟨M₁, hM1, hor⟩
  · exact Or.inl h1
  · exact Or.inr h2
  · exfalso
    rcases hor with ⟨_, htail⟩ | ⟨_, htail⟩
    · exact weak_limit_no_M1_ge_3 hA_inf hB_inf hn₀ hstab hlam hprod_ev hN_top hT_le hA1 hB1 hL_le hμ_lim hM1 htail
    · have hstab' : ∀ n ≥ n₀, repCount B A n = 1 := fun n hn => by rw [repCount_comm]; exact hstab n hn
      have hprod_ev' : ∀ᶠ x : ℝ in atTop, (countReal B x : ℝ) * (countReal A x : ℝ) ≤ lam * x := by
        filter_upwards [hprod_ev] with x hx; linarith
      have hT_le' : ∀ j, crossExcess B A (N j) ≤ K := fun j => by rw [crossExcess_comm]; exact hT_le j
      exact weak_limit_no_M1_ge_3 hB_inf hA_inf hn₀ hstab' hlam hprod_ev' hN_top hT_le' hB1 hA1 hL_le hν_lim hM1 htail

/-! ### Part 5: Corollary 4.4 (`exists_levelApprox`) -/

/-- Helper: if `(empProbI A (N j), empProbI B (N j)) → (cantorNu, cantorMu)` along `L`, then all
pointwise CDF and support inequalities of `LevelApprox A B n₀ K (N j)` hold eventually along `L`. -/
private lemma eventually_levelApprox_of_cantor_limit {A B : Set ℕ} (hA_inf : A.Infinite) (hB_inf : B.Infinite)
    {K : ℕ}
    {N : ℕ → ℕ} (hN_top : Tendsto N atTop atTop) (hT_le : ∀ j, crossExcess A B (N j) ≤ K)
    (hA1 : ∀ j, 1 ≤ countNat A (N j)) (hB1 : ∀ j, 1 ≤ countNat B (N j))
    {L : Filter ℕ} [L.NeBot] (hL_le : L ≤ atTop)
    {μI νI : ProbabilityMeasure UnitI}
    (hμ_lim : Tendsto (fun j => empProbI A (N j) (hA1 j)) L (𝓝 μI))
    (hν_lim : Tendsto (fun j => empProbI B (N j) (hB1 j)) L (𝓝 νI))
    (hμ_eq : pushToReal μI = cantorNu) (hν_eq : pushToReal νI = cantorMu) :
    ∀ᶠ j in L,
      (∃ a ∈ A, a ≤ N j ∧ (1 / 3 - 1 / 1000 : ℝ) * (N j : ℝ) ≤ (a : ℝ)) ∧
      (∀ a ∈ A, a ≤ N j → (a : ℝ) ≤ (1 / 3 + 1 / 1000 : ℝ) * (N j : ℝ)) ∧
      (∃ b ∈ B, b ≤ N j ∧ (2 / 3 - 1 / 1000 : ℝ) * (N j : ℝ) ≤ (b : ℝ)) ∧
      (∀ b ∈ B, b ≤ N j → (b : ℝ) ≤ (2 / 3 + 1 / 1000 : ℝ) * (N j : ℝ)) ∧
      ((countNat A ⌊(1 / 4 - 2 / 1000 : ℝ) * (N j : ℝ)⌋₊ : ℝ) -
        (countNat A ⌊(1 / 12 + 3 / 1000 : ℝ) * (N j : ℝ)⌋₊ : ℝ) ≤ (2 / 1000 : ℝ) * (countNat A (N j) : ℝ)) ∧
      ((248 / 1000 : ℝ) * (countNat A (N j) : ℝ) ≤
        (countNat A ⌊(1 / 12 + 1 / 1000 : ℝ) * (N j : ℝ)⌋₊ : ℝ) -
        (countNat A ⌊(1 / 16 - 1 / 1000 : ℝ) * (N j : ℝ)⌋₊ : ℝ)) ∧
      ((248 / 1000 : ℝ) * (countNat A (N j) : ℝ) ≤
        (countNat A ⌊(1 / 3 + 1 / 1000 : ℝ) * (N j : ℝ)⌋₊ : ℝ) -
        (countNat A ⌊(5 / 16 - 1 / 1000 : ℝ) * (N j : ℝ)⌋₊ : ℝ)) := by
  classical
  have hN_L : Tendsto N L atTop := hN_top.mono_left hL_le
  have hcount_top : ∀ (S : Set ℕ), S.Infinite → Tendsto (fun M : ℕ => countNat S M) atTop atTop := by
    intro S hS; rw [tendsto_atTop_atTop]; intro b
    obtain ⟨t, ht_sub, ht_card⟩ := hS.exists_subset_card_eq b
    refine ⟨t.sup id, fun M hM => ?_⟩
    unfold countNat
    calc b = t.card := ht_card.symm
      _ ≤ ((Finset.range (M + 1)).filter (· ∈ S)).card := by
            apply Finset.card_le_card; intro x hx
            have hle : x ≤ t.sup id := Finset.le_sup (f := id) hx
            exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ht_sub hx⟩
  -- Portmanteau helper: for any 0 < u < v < 1, μ_N(Ioc u v) → cantorNu(Ioc u v) because cantorNu is atomless!
  have hIoc_conv : ∀ u v : ℝ, 0 < u → u < v → v < 1 →
      Tendsto (fun j => ((countNat A ⌊v * (N j : ℝ)⌋₊ : ℝ) - (countNat A ⌊u * (N j : ℝ)⌋₊ : ℝ)) /
        (countNat A (N j) : ℝ)) L (𝓝 (cantorNu (Set.Ioc u v)).toReal) := by
    intro u v hu0 huv hv1
    let E : Set UnitI := {x : UnitI | u < x.1 ∧ x.1 ≤ v}
    have hfront : (μI : Measure UnitI) (frontier E) = 0 := by
      have hsub : frontier E ⊆ {x : UnitI | x.1 = u} ∪ {x : UnitI | x.1 = v} := by
        intro x hx
        have hcl : x ∈ closure E := hx.1
        have hni : x ∉ interior E := hx.2
        have hle_u : u ≤ x.1 := by
          have hclosed : IsClosed {y : UnitI | u ≤ y.1} := isClosed_le continuous_const continuous_subtype_val
          exact closure_minimal (fun y hy => le_of_lt hy.1) hclosed hcl
        have hle_v : x.1 ≤ v := by
          have hclosed : IsClosed {y : UnitI | y.1 ≤ v} := isClosed_le continuous_subtype_val continuous_const
          exact closure_minimal (fun y hy => hy.2) hclosed hcl
        by_contra hnot
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hnot
        have hopen : IsOpen {y : UnitI | u < y.1 ∧ y.1 < v} :=
          (isOpen_lt continuous_const continuous_subtype_val).inter (isOpen_lt continuous_subtype_val continuous_const)
        have hsubE : {y : UnitI | u < y.1 ∧ y.1 < v} ⊆ E := fun y hy => ⟨hy.1, le_of_lt hy.2⟩
        exact hni (interior_maximal hsubE hopen ⟨lt_of_le_of_ne hle_u (Ne.symm hnot.1), lt_of_le_of_ne hle_v hnot.2⟩)
      have h0u : (μI : Measure UnitI) {x : UnitI | x.1 = u} = 0 := by
        have h1 : (μI : Measure UnitI) {x : UnitI | x.1 = u} = pushToReal μI {u} := by
          rw [pushToReal, Measure.map_apply measurable_subtype_coe (measurableSet_singleton u)]; rfl
        rw [h1, hμ_eq, cantorNu_singleton_zero]
      have h0v : (μI : Measure UnitI) {x : UnitI | x.1 = v} = 0 := by
        have h1 : (μI : Measure UnitI) {x : UnitI | x.1 = v} = pushToReal μI {v} := by
          rw [pushToReal, Measure.map_apply measurable_subtype_coe (measurableSet_singleton v)]; rfl
        rw [h1, hμ_eq, cantorNu_singleton_zero]
      exact measure_mono_null hsub (measure_union_null h0u h0v)
    have hlim_en := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ_lim hfront
    have hμE : (μI : Measure UnitI) E = cantorNu (Set.Ioc u v) := by
      rw [← hμ_eq, pushToReal, Measure.map_apply measurable_subtype_coe measurableSet_Ioc]; rfl
    rw [hμE] at hlim_en
    have hlim_r := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hlim_en
    refine hlim_r.congr' ?_
    filter_upwards [hN_L.eventually (eventually_ge_atTop 1)] with j hN1
    have : IsProbabilityMeasure (pushToReal (empProbI A (N j) (hA1 j))) := isProbabilityMeasure_pushToReal _
    have hE_eq : (empProbI A (N j) (hA1 j) : Measure UnitI) E =
        pushToReal (empProbI A (N j) (hA1 j)) (Set.Icc 0 v) - pushToReal (empProbI A (N j) (hA1 j)) (Set.Icc 0 u) := by
      have h1 : (empProbI A (N j) (hA1 j) : Measure UnitI) E =
          pushToReal (empProbI A (N j) (hA1 j)) (Set.Icc 0 v \ Set.Icc 0 u) := by
        rw [pushToReal, Measure.map_apply measurable_subtype_coe (measurableSet_Icc.diff measurableSet_Icc)]
        congr 1; ext x; simp only [E, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_sdiff, Set.mem_Icc]
        constructor
        · intro ⟨h1, h2⟩; exact ⟨⟨x.2.1, h2⟩, fun hc => by linarith [hc.2]⟩
        · intro ⟨⟨_, h2⟩, hnot⟩; exact ⟨by by_contra hle; exact hnot ⟨x.2.1, le_of_not_gt hle⟩, h2⟩
      rw [h1, measure_sdiff (show Set.Icc (0 : ℝ) u ⊆ Set.Icc (0 : ℝ) v from fun x hx => ⟨hx.1, le_trans hx.2 (le_of_lt huv)⟩)
          measurableSet_Icc.nullMeasurableSet (measure_ne_top _ _)]
    have hle_m : pushToReal (empProbI A (N j) (hA1 j)) (Set.Icc 0 u) ≤
        pushToReal (empProbI A (N j) (hA1 j)) (Set.Icc 0 v) :=
      measure_mono (fun x hx => ⟨hx.1, le_trans hx.2 (le_of_lt huv)⟩)
    simp only [Function.comp_apply, hE_eq]
    rw [ENNReal.toReal_sub_of_le hle_m (measure_ne_top _ _),
        empProbI_measure_Iic (hA1 j) hN1 (le_of_lt (lt_trans hu0 huv)) (le_of_lt hv1),
        empProbI_measure_Iic (hA1 j) hN1 (le_of_lt hu0) (le_of_lt (lt_trans huv hv1)), sub_div]
  -- Apply hIoc_conv to the 3 intervals of LevelApprox!
  have hgap_ev : ∀ᶠ j in L, (countNat A ⌊(1 / 4 - 2 / 1000 : ℝ) * (N j : ℝ)⌋₊ : ℝ) -
      (countNat A ⌊(1 / 12 + 3 / 1000 : ℝ) * (N j : ℝ)⌋₊ : ℝ) ≤ (2 / 1000 : ℝ) * (countNat A (N j) : ℝ) := by
    have ht := hIoc_conv (1 / 12 + 3 / 1000) (1 / 4 - 2 / 1000) (by norm_num) (by norm_num) (by norm_num)
    rw [cantorNu_checkpoints.1, ENNReal.toReal_zero] at ht
    filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 2 / 1000))] with j hj
    have hAp : (0 : ℝ) < (countNat A (N j) : ℝ) := Nat.cast_pos.mpr (by have := hA1 j; omega)
    exact le_of_lt ((div_lt_iff₀ hAp).mp hj)
  have hblk1_ev : ∀ᶠ j in L, (248 / 1000 : ℝ) * (countNat A (N j) : ℝ) ≤
      (countNat A ⌊(1 / 12 + 1 / 1000 : ℝ) * (N j : ℝ)⌋₊ : ℝ) -
      (countNat A ⌊(1 / 16 - 1 / 1000 : ℝ) * (N j : ℝ)⌋₊ : ℝ) := by
    have ht := hIoc_conv (1 / 16 - 1 / 1000) (1 / 12 + 1 / 1000) (by norm_num) (by norm_num) (by norm_num)
    rw [cantorNu_checkpoints.2.1] at ht
    have hval : ((1 / 4 : ℝ≥0∞)).toReal = 1 / 4 := by simp
    rw [hval] at ht
    filter_upwards [ht.eventually (lt_mem_nhds (by norm_num : (248 / 1000 : ℝ) < 1 / 4))] with j hj
    have hAp : (0 : ℝ) < (countNat A (N j) : ℝ) := Nat.cast_pos.mpr (by have := hA1 j; omega)
    exact le_of_lt ((lt_div_iff₀ hAp).mp hj)
  have hblk2_ev : ∀ᶠ j in L, (248 / 1000 : ℝ) * (countNat A (N j) : ℝ) ≤
      (countNat A ⌊(1 / 3 + 1 / 1000 : ℝ) * (N j : ℝ)⌋₊ : ℝ) -
      (countNat A ⌊(5 / 16 - 1 / 1000 : ℝ) * (N j : ℝ)⌋₊ : ℝ) := by
    have ht := hIoc_conv (5 / 16 - 1 / 1000) (1 / 3 + 1 / 1000) (by norm_num) (by norm_num) (by norm_num)
    rw [cantorNu_checkpoints.2.2.1] at ht
    have hval : ((1 / 4 : ℝ≥0∞)).toReal = 1 / 4 := by simp
    rw [hval] at ht
    filter_upwards [ht.eventually (lt_mem_nhds (by norm_num : (248 / 1000 : ℝ) < 1 / 4))] with j hj
    have hAp : (0 : ℝ) < (countNat A (N j) : ℝ) := Nat.cast_pos.mpr (by have := hA1 j; omega)
    exact le_of_lt ((lt_div_iff₀ hAp).mp hj)
  -- Tail mass helper for A near 1/3 and B near 2/3 -> gives BOTH lower bounds and upper bounds!
  have hAtail_big : ∀ᶠ j in L, K + 1 ≤ (((Finset.range (N j + 1)).filter (· ∈ A)).filter
      (fun a : ℕ => (1 / 3 - 1 / 1000 : ℝ) * (N j : ℝ) < (a : ℝ))).card := by
    let GA : Set UnitI := {x : UnitI | 1 / 3 - 1 / 1000 < x.1}
    have hGA_open : IsOpen GA := isOpen_lt continuous_const continuous_subtype_val
    have hGA_ge : (1 / 64 : ℝ≥0∞) ≤ (μI : Measure UnitI) GA := by
      have h1 : cantorNu (Set.Ioo (1 / 3 - 1 / 1000) 1) ≤ (μI : Measure UnitI) GA := by
        rw [← hμ_eq, pushToReal, Measure.map_apply measurable_subtype_coe measurableSet_Ioo]
        exact measure_mono (fun x hx => hx.1)
      exact le_trans cantorNu_checkpoints.2.2.2.1 h1
    have hlt_lim : ENNReal.ofReal (1 / 128) < L.liminf (fun j => (empProbI A (N j) (hA1 j) : Measure UnitI) GA) :=
      lt_of_lt_of_le (by
        have heq : (1 / 64 : ℝ≥0∞) = ENNReal.ofReal (1 / 64) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
        rw [heq, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]; norm_num)
        (le_trans hGA_ge (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ_lim hGA_open))
    have hA_big := (tendsto_natCast_atTop_atTop.comp ((hcount_top A hA_inf).comp hN_L)).eventually
      (eventually_gt_atTop (128 * ((K : ℝ) + 1)))
    filter_upwards [eventually_lt_of_lt_liminf hlt_lim, hA_big, hN_L.eventually (eventually_ge_atTop 1)] with j hj hAj hN1
    set Atail := ((Finset.range (N j + 1)).filter (· ∈ A)).filter (fun a : ℕ => (1 / 3 - 1 / 1000 : ℝ) * (N j : ℝ) < (a : ℝ))
    have hG_eq : (empProbI A (N j) (hA1 j) : Measure UnitI) GA = ((countNat A (N j) : ℝ≥0∞))⁻¹ * (Atail.card : ℝ≥0∞) := by
      have h1 : (empProbI A (N j) (hA1 j) : Measure UnitI) GA = pushToReal (empProbI A (N j) (hA1 j)) (Set.Ioi (1 / 3 - 1 / 1000)) := by
        rw [pushToReal, Measure.map_apply measurable_subtype_coe measurableSet_Ioi]; rfl
      rw [h1, pushToReal_empProbI (hA1 j), Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
      congr 1
      have hNpos : (0 : ℝ) < (N j : ℝ) := Nat.cast_pos.mpr (by omega)
      have hterm : ∀ a ∈ (Finset.range (N j + 1)).filter (· ∈ A),
          Measure.dirac ((a : ℝ) / (N j : ℝ)) (Set.Ioi (1 / 3 - 1 / 1000)) =
            if (1 / 3 - 1 / 1000 : ℝ) * (N j : ℝ) < (a : ℝ) then (1 : ℝ≥0∞) else 0 := by
        intro a _; rw [Measure.dirac_apply' _ measurableSet_Ioi]
        by_cases h : (1 / 3 - 1 / 1000 : ℝ) * (N j : ℝ) < (a : ℝ)
        · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr ((lt_div_iff₀ hNpos).mpr h)), Pi.one_apply,
              ite_eq_left_iff.mpr (fun hn => absurd h hn)]
        · rw [Set.indicator_of_notMem (fun hm => h ((lt_div_iff₀ hNpos).mp (Set.mem_Ioi.mp hm))),
              ite_eq_right_iff.mpr (fun hn => absurd hn h)]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hto := ENNReal.toReal_mono (measure_ne_top _ _) (le_of_lt hj)
    rw [hG_eq, ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_natCast, ENNReal.toReal_natCast] at hto
    have hAp : (0 : ℝ) < (countNat A (N j) : ℝ) := Nat.cast_pos.mpr (by have := hA1 j; omega)
    have h1 := mul_le_mul_of_nonneg_left hto (le_of_lt hAp)
    rw [← mul_assoc, mul_inv_cancel₀ hAp.ne', one_mul] at h1
    simp only [Function.comp_apply] at hAj
    have h2 : ((K + 1 : ℕ) : ℝ) ≤ (Atail.card : ℝ) := by push_cast; linarith
    exact_mod_cast h2
  have hBtail_big : ∀ᶠ j in L, K + 1 ≤ (((Finset.range (N j + 1)).filter (· ∈ B)).filter
      (fun b : ℕ => (2 / 3 - 1 / 1000 : ℝ) * (N j : ℝ) < (b : ℝ))).card := by
    let GB : Set UnitI := {x : UnitI | 2 / 3 - 1 / 1000 < x.1}
    have hGB_open : IsOpen GB := isOpen_lt continuous_const continuous_subtype_val
    have hGB_ge : (1 / 64 : ℝ≥0∞) ≤ (νI : Measure UnitI) GB := by
      have h1 : cantorMu (Set.Ioo (2 / 3 - 1 / 1000) 1) ≤ (νI : Measure UnitI) GB := by
        rw [← hν_eq, pushToReal, Measure.map_apply measurable_subtype_coe measurableSet_Ioo]
        exact measure_mono (fun x hx => hx.1)
      exact le_trans cantorNu_checkpoints.2.2.2.2 h1
    have hlt_lim : ENNReal.ofReal (1 / 128) < L.liminf (fun j => (empProbI B (N j) (hB1 j) : Measure UnitI) GB) :=
      lt_of_lt_of_le (by
        have heq : (1 / 64 : ℝ≥0∞) = ENNReal.ofReal (1 / 64) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
        rw [heq, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]; norm_num)
        (le_trans hGB_ge (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hν_lim hGB_open))
    have hB_big := (tendsto_natCast_atTop_atTop.comp ((hcount_top B hB_inf).comp hN_L)).eventually
      (eventually_gt_atTop (128 * ((K : ℝ) + 1)))
    filter_upwards [eventually_lt_of_lt_liminf hlt_lim, hB_big, hN_L.eventually (eventually_ge_atTop 1)] with j hj hBj hN1
    set Btail := ((Finset.range (N j + 1)).filter (· ∈ B)).filter (fun b : ℕ => (2 / 3 - 1 / 1000 : ℝ) * (N j : ℝ) < (b : ℝ))
    have hG_eq : (empProbI B (N j) (hB1 j) : Measure UnitI) GB = ((countNat B (N j) : ℝ≥0∞))⁻¹ * (Btail.card : ℝ≥0∞) := by
      have h1 : (empProbI B (N j) (hB1 j) : Measure UnitI) GB = pushToReal (empProbI B (N j) (hB1 j)) (Set.Ioi (2 / 3 - 1 / 1000)) := by
        rw [pushToReal, Measure.map_apply measurable_subtype_coe measurableSet_Ioi]; rfl
      rw [h1, pushToReal_empProbI (hB1 j), Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
      congr 1
      have hNpos : (0 : ℝ) < (N j : ℝ) := Nat.cast_pos.mpr (by omega)
      have hterm : ∀ b ∈ (Finset.range (N j + 1)).filter (· ∈ B),
          Measure.dirac ((b : ℝ) / (N j : ℝ)) (Set.Ioi (2 / 3 - 1 / 1000)) =
            if (2 / 3 - 1 / 1000 : ℝ) * (N j : ℝ) < (b : ℝ) then (1 : ℝ≥0∞) else 0 := by
        intro b _; rw [Measure.dirac_apply' _ measurableSet_Ioi]
        by_cases h : (2 / 3 - 1 / 1000 : ℝ) * (N j : ℝ) < (b : ℝ)
        · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr ((lt_div_iff₀ hNpos).mpr h)), Pi.one_apply,
              ite_eq_left_iff.mpr (fun hn => absurd h hn)]
        · rw [Set.indicator_of_notMem (fun hm => h ((lt_div_iff₀ hNpos).mp (Set.mem_Ioi.mp hm))),
              ite_eq_right_iff.mpr (fun hn => absurd hn h)]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hto := ENNReal.toReal_mono (measure_ne_top _ _) (le_of_lt hj)
    rw [hG_eq, ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_natCast, ENNReal.toReal_natCast] at hto
    have hBp : (0 : ℝ) < (countNat B (N j) : ℝ) := Nat.cast_pos.mpr (by have := hB1 j; omega)
    have h1 := mul_le_mul_of_nonneg_left hto (le_of_lt hBp)
    rw [← mul_assoc, mul_inv_cancel₀ hBp.ne', one_mul] at h1
    simp only [Function.comp_apply] at hBj
    have h2 : ((K + 1 : ℕ) : ℝ) ≤ (Btail.card : ℝ) := by push_cast; linarith
    exact_mod_cast h2
  -- Combine all 7 properties!
  filter_upwards [hAtail_big, hBtail_big, hgap_ev, hblk1_ev, hblk2_ev] with j hAt hBt hgap hblk1 hblk2
  refine ⟨?_, ?_, ?_, ?_, hgap, hblk1, hblk2⟩
  · obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega :
      0 < (((Finset.range (N j + 1)).filter (· ∈ A)).filter
        (fun a : ℕ => (1 / 3 - 1 / 1000 : ℝ) * (N j : ℝ) < (a : ℝ))).card)
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    exact ⟨a, ha.1.2, by omega, le_of_lt ha.2⟩
  · intro a haA haN; by_contra hgt; push Not at hgt
    set Btail := ((Finset.range (N j + 1)).filter (· ∈ B)).filter (fun b : ℕ => (2 / 3 - 1 / 1000 : ℝ) * (N j : ℝ) < (b : ℝ))
    have hinj : Btail.card ≤ ((Finset.range (N j)).filter (fun m => 1 ≤ repTrunc A B (N j) (N j + 1 + m))).card := by
      apply Finset.card_le_card_of_injOn (fun b => a + b - (N j + 1))
      · intro b hb; simp only [Btail, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hb ⊢
        have hab : N j < a + b := by exact_mod_cast (show (N j : ℝ) < (a : ℝ) + (b : ℝ) by linarith [hb.2])
        refine ⟨by omega, Finset.card_pos.mpr ⟨a, ?_⟩⟩
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, haA, by omega, by omega, ?_⟩
        have : N j + 1 + (a + b - (N j + 1)) - a = b := by omega
        rw [this]; exact hb.1.2
      · intro b1 h1 b2 h2 heq; simp only [Btail, Finset.mem_coe, Finset.mem_filter] at h1 h2
        have h1gt : N j < a + b1 := by exact_mod_cast (show (N j : ℝ) < (a : ℝ) + (b1 : ℝ) by linarith [h1.2])
        have h2gt : N j < a + b2 := by exact_mod_cast (show (N j : ℝ) < (a : ℝ) + (b2 : ℝ) by linarith [h2.2])
        dsimp only at heq; omega
    have hle_T : Btail.card ≤ crossExcess A B (N j) := by
      calc Btail.card ≤ ∑ _m ∈ (Finset.range (N j)).filter (fun m => 1 ≤ repTrunc A B (N j) (N j + 1 + m)), 1 := by simp [hinj]
        _ ≤ ∑ m ∈ (Finset.range (N j)).filter (fun m => 1 ≤ repTrunc A B (N j) (N j + 1 + m)), repTrunc A B (N j) (N j + 1 + m) :=
              Finset.sum_le_sum (fun m hm => (Finset.mem_filter.mp hm).2)
        _ ≤ crossExcess A B (N j) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have := hT_le j; omega
  · obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega :
      0 < (((Finset.range (N j + 1)).filter (· ∈ B)).filter
        (fun b : ℕ => (2 / 3 - 1 / 1000 : ℝ) * (N j : ℝ) < (b : ℝ))).card)
    simp only [Finset.mem_filter, Finset.mem_range] at hb
    exact ⟨b, hb.1.2, by omega, le_of_lt hb.2⟩
  · intro b hbB hbN; by_contra hgt; push Not at hgt
    set Atail := ((Finset.range (N j + 1)).filter (· ∈ A)).filter (fun a : ℕ => (1 / 3 - 1 / 1000 : ℝ) * (N j : ℝ) < (a : ℝ))
    have hinj : Atail.card ≤ ((Finset.range (N j)).filter (fun m => 1 ≤ repTrunc A B (N j) (N j + 1 + m))).card := by
      apply Finset.card_le_card_of_injOn (fun a => a + b - (N j + 1))
      · intro a ha; simp only [Atail, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha ⊢
        have hab : N j < a + b := by exact_mod_cast (show (N j : ℝ) < (a : ℝ) + (b : ℝ) by linarith [ha.2])
        refine ⟨by omega, Finset.card_pos.mpr ⟨a, ?_⟩⟩
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ha.1.2, by omega, by omega, ?_⟩
        have : N j + 1 + (a + b - (N j + 1)) - a = b := by omega
        rw [this]; exact hbB
      · intro a1 h1 a2 h2 heq; simp only [Atail, Finset.mem_coe, Finset.mem_filter] at h1 h2
        have h1gt : N j < a1 + b := by exact_mod_cast (show (N j : ℝ) < (a1 : ℝ) + (b : ℝ) by linarith [h1.2])
        have h2gt : N j < a2 + b := by exact_mod_cast (show (N j : ℝ) < (a2 : ℝ) + (b : ℝ) by linarith [h2.2])
        dsimp only at heq; omega
    have hle_T : Atail.card ≤ crossExcess A B (N j) := by
      calc Atail.card ≤ ∑ _m ∈ (Finset.range (N j)).filter (fun m => 1 ≤ repTrunc A B (N j) (N j + 1 + m)), 1 := by simp [hinj]
        _ ≤ ∑ m ∈ (Finset.range (N j)).filter (fun m => 1 ≤ repTrunc A B (N j) (N j + 1 + m)), repTrunc A B (N j) (N j + 1 + m) :=
              Finset.sum_le_sum (fun m hm => (Finset.mem_filter.mp hm).2)
        _ ≤ crossExcess A B (N j) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have := hT_le j; omega

/-- **Corollary 4.4 (`exists_levelApprox`):**
Under `IsAlmostPerfect A B` and `limsup A(x)B(x)/x < 8/5`, for every `K ≥ n₀`, there exists a
threshold `N_star` such that every `N ≥ N_star` with `crossExcess A B N ≤ K` satisfies either
`LevelApprox A B n₀ K N` or `LevelApprox B A n₀ K N`. -/
theorem exists_levelApprox {A B : Set ℕ} (hAP : IsAlmostPerfect A B)
    (hlim : Filter.limsup (ratioEReal A B) Filter.atTop < ((8 / 5 : ℝ) : EReal))
    {n₀ : ℕ} (hn₀ : 1 ≤ n₀) (hstab : ∀ n ≥ n₀, repCount A B n = 1)
    (K : ℕ) (hK : n₀ ≤ K) :
    ∃ N_star : ℕ, ∀ N ≥ N_star, crossExcess A B N ≤ K →
      LevelApprox A B n₀ K N ∨ LevelApprox B A n₀ K N := by
  classical
  have hA_inf : A.Infinite := hAP.1
  have hB_inf : B.Infinite := hAP.2.1
  -- Extract strict real upper bound lam < 8/5 with A(x)B(x) ≤ lam * x eventually
  obtain ⟨lam, hlam_gt, hlam_lt_e⟩ := EReal.exists_between_coe_real hlim
  have hlam_lt : lam < 8 / 5 := EReal.coe_lt_coe_iff.mp hlam_lt_e
  have hprod_ev : ∀ᶠ x : ℝ in atTop, (countReal A x : ℝ) * (countReal B x : ℝ) ≤ lam * x := by
    have hlt_ev := eventually_lt_of_limsup_lt hlam_gt
    filter_upwards [hlt_ev, eventually_gt_atTop (0 : ℝ)] with x hx hx0
    unfold ratioEReal at hx
    have hreal : (countReal A x : ℝ) * (countReal B x : ℝ) / x < lam := EReal.coe_lt_coe_iff.mp hx
    exact le_of_lt ((div_lt_iff₀ hx0).mp hreal)
  -- First establish a base threshold N_base where all size & product bounds hold (independent of orientation)
  have hcount_top : ∀ (S : Set ℕ), S.Infinite → Tendsto (fun M : ℕ => countNat S M) atTop atTop := by
    intro S hS; rw [tendsto_atTop_atTop]; intro b
    obtain ⟨t, ht_sub, ht_card⟩ := hS.exists_subset_card_eq b
    refine ⟨t.sup id, fun M hM => ?_⟩
    unfold countNat
    calc b = t.card := ht_card.symm
      _ ≤ ((Finset.range (M + 1)).filter (· ∈ S)).card := by
            apply Finset.card_le_card; intro x hx
            have hle : x ≤ t.sup id := Finset.le_sup (f := id) hx
            exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ht_sub hx⟩
  set E := errSum A B n₀
  have hE_comm : errSum B A n₀ = E := by
    unfold E errSum; apply Finset.sum_congr rfl; intro n _; rw [repCount_comm]
  have hC1_comm : C1Const B A n₀ K = C1Const A B n₀ K := by
    unfold C1Const; rw [hE_comm, repPairSum_comm]
  set M_size := max (10 ^ 7 * (K + E + n₀ + 1) * (E + n₀ + 1)) 1
  set M_cnt := 10 ^ 7 * (C1Const A B n₀ K + K + E + n₀ + 1)
  obtain ⟨N_prod, hN_prod⟩ : ∃ N_prod : ℕ, ∀ t ≥ N_prod, (countNat A t : ℝ) * (countNat B t : ℝ) ≤ (8 / 5 : ℝ) * (t : ℝ) := by
    rw [eventually_atTop] at hprod_ev
    rcases hprod_ev with ⟨R, hR⟩
    refine ⟨⌈max R 0⌉₊ + 1, fun t ht => ?_⟩
    have ht_ge : R ≤ (t : ℝ) := le_trans (le_max_left R 0) (le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : ⌈max R 0⌉₊ ≤ t)))
    have hnn : ¬ ((t : ℝ) < 0) := by push Not; positivity
    have h1 := hR (t : ℝ) ht_ge
    simp only [countReal, hnn, ↓reduceIte, Nat.floor_natCast] at h1
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    nlinarith
  obtain ⟨N_A, hN_A⟩ := ((hcount_top A hA_inf).eventually (eventually_ge_atTop (max M_cnt 1))).exists_forall_of_atTop
  obtain ⟨N_B, hN_B⟩ := ((hcount_top B hB_inf).eventually (eventually_ge_atTop (max M_cnt 1))).exists_forall_of_atTop
  set N_base := max (max M_size N_prod) (max N_A N_B)
  -- Core compactness claim: ∃ N_star ≥ N_base such that all 7 distributional inequalities hold (in one of the 2 orientations)
  have hcore : ∃ N_star ≥ N_base, ∀ N ≥ N_star, crossExcess A B N ≤ K →
      ((∃ a ∈ A, a ≤ N ∧ (1 / 3 - 1 / 1000 : ℝ) * (N : ℝ) ≤ (a : ℝ)) ∧
       (∀ a ∈ A, a ≤ N → (a : ℝ) ≤ (1 / 3 + 1 / 1000 : ℝ) * (N : ℝ)) ∧
       (∃ b ∈ B, b ≤ N ∧ (2 / 3 - 1 / 1000 : ℝ) * (N : ℝ) ≤ (b : ℝ)) ∧
       (∀ b ∈ B, b ≤ N → (b : ℝ) ≤ (2 / 3 + 1 / 1000 : ℝ) * (N : ℝ)) ∧
       ((countNat A ⌊(1 / 4 - 2 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) -
         (countNat A ⌊(1 / 12 + 3 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) ≤ (2 / 1000 : ℝ) * (countNat A N : ℝ)) ∧
       ((248 / 1000 : ℝ) * (countNat A N : ℝ) ≤
         (countNat A ⌊(1 / 12 + 1 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) -
         (countNat A ⌊(1 / 16 - 1 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ)) ∧
       ((248 / 1000 : ℝ) * (countNat A N : ℝ) ≤
         (countNat A ⌊(1 / 3 + 1 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) -
         (countNat A ⌊(5 / 16 - 1 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ))) ∨
      ((∃ b ∈ B, b ≤ N ∧ (1 / 3 - 1 / 1000 : ℝ) * (N : ℝ) ≤ (b : ℝ)) ∧
       (∀ b ∈ B, b ≤ N → (b : ℝ) ≤ (1 / 3 + 1 / 1000 : ℝ) * (N : ℝ)) ∧
       (∃ a ∈ A, a ≤ N ∧ (2 / 3 - 1 / 1000 : ℝ) * (N : ℝ) ≤ (a : ℝ)) ∧
       (∀ a ∈ A, a ≤ N → (a : ℝ) ≤ (2 / 3 + 1 / 1000 : ℝ) * (N : ℝ)) ∧
       ((countNat B ⌊(1 / 4 - 2 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) -
         (countNat B ⌊(1 / 12 + 3 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) ≤ (2 / 1000 : ℝ) * (countNat B N : ℝ)) ∧
       ((248 / 1000 : ℝ) * (countNat B N : ℝ) ≤
         (countNat B ⌊(1 / 12 + 1 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) -
         (countNat B ⌊(1 / 16 - 1 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ)) ∧
       ((248 / 1000 : ℝ) * (countNat B N : ℝ) ≤
         (countNat B ⌊(1 / 3 + 1 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) -
         (countNat B ⌊(5 / 16 - 1 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ))) := by
    by_contra hno
    -- Construct a sequence N_seq : ℕ → ℕ with N_seq j ≥ max N_base j, T(N_seq j) ≤ K, failing both orientations!
    have hex : ∀ j : ℕ, ∃ N ≥ max N_base j, crossExcess A B N ≤ K ∧
        ¬ (((∃ a ∈ A, a ≤ N ∧ (1 / 3 - 1 / 1000 : ℝ) * (N : ℝ) ≤ (a : ℝ)) ∧
            (∀ a ∈ A, a ≤ N → (a : ℝ) ≤ (1 / 3 + 1 / 1000 : ℝ) * (N : ℝ)) ∧
            (∃ b ∈ B, b ≤ N ∧ (2 / 3 - 1 / 1000 : ℝ) * (N : ℝ) ≤ (b : ℝ)) ∧
            (∀ b ∈ B, b ≤ N → (b : ℝ) ≤ (2 / 3 + 1 / 1000 : ℝ) * (N : ℝ)) ∧
            ((countNat A ⌊(1 / 4 - 2 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) -
              (countNat A ⌊(1 / 12 + 3 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) ≤ (2 / 1000 : ℝ) * (countNat A N : ℝ)) ∧
            ((248 / 1000 : ℝ) * (countNat A N : ℝ) ≤
              (countNat A ⌊(1 / 12 + 1 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) -
              (countNat A ⌊(1 / 16 - 1 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ)) ∧
            ((248 / 1000 : ℝ) * (countNat A N : ℝ) ≤
              (countNat A ⌊(1 / 3 + 1 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) -
              (countNat A ⌊(5 / 16 - 1 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ))) ∨
           ((∃ b ∈ B, b ≤ N ∧ (1 / 3 - 1 / 1000 : ℝ) * (N : ℝ) ≤ (b : ℝ)) ∧
            (∀ b ∈ B, b ≤ N → (b : ℝ) ≤ (1 / 3 + 1 / 1000 : ℝ) * (N : ℝ)) ∧
            (∃ a ∈ A, a ≤ N ∧ (2 / 3 - 1 / 1000 : ℝ) * (N : ℝ) ≤ (a : ℝ)) ∧
            (∀ a ∈ A, a ≤ N → (a : ℝ) ≤ (2 / 3 + 1 / 1000 : ℝ) * (N : ℝ)) ∧
            ((countNat B ⌊(1 / 4 - 2 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) -
              (countNat B ⌊(1 / 12 + 3 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) ≤ (2 / 1000 : ℝ) * (countNat B N : ℝ)) ∧
            ((248 / 1000 : ℝ) * (countNat B N : ℝ) ≤
              (countNat B ⌊(1 / 12 + 1 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) -
              (countNat B ⌊(1 / 16 - 1 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ)) ∧
            ((248 / 1000 : ℝ) * (countNat B N : ℝ) ≤
              (countNat B ⌊(1 / 3 + 1 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) -
              (countNat B ⌊(5 / 16 - 1 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ)))) := by
      intro j
      by_contra hall
      apply hno
      exact ⟨max N_base j, le_max_left _ _, fun N hN hTN => by
        by_contra hfail; exact hall ⟨N, hN, hTN, hfail⟩⟩
    choose N_seq hN_ge hT_seq hfail_seq using hex
    have hN_top : Tendsto N_seq atTop atTop :=
      tendsto_atTop_mono (fun j => le_trans (le_max_right N_base j) (hN_ge j)) tendsto_id
    have hA1 : ∀ j, 1 ≤ countNat A (N_seq j) := fun j =>
      le_trans (le_max_right M_cnt 1) (hN_A (N_seq j) (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
        (le_trans (le_max_left _ _) (hN_ge j))))
    have hB1 : ∀ j, 1 ≤ countNat B (N_seq j) := fun j =>
      le_trans (le_max_right M_cnt 1) (hN_B (N_seq j) (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
        (le_trans (le_max_left _ _) (hN_ge j))))
    -- By Prokhorov compactness of ProbabilityMeasure UnitI × ProbabilityMeasure UnitI, extract a cluster point (μI, νI)!
    let f : ℕ → ProbabilityMeasure UnitI × ProbabilityMeasure UnitI :=
      fun j => (empProbI A (N_seq j) (hA1 j), empProbI B (N_seq j) (hB1 j))
    obtain ⟨⟨μI, νI⟩, _, hcl⟩ := isCompact_univ.exists_clusterPt (f := Filter.map f atTop) (by simp)
    -- ClusterPt (μI, νI) (map f atTop) means L := atTop ⊓ comap f (𝓝 (μI, νI)) is NeBot!
    let L : Filter ℕ := atTop ⊓ Filter.comap f (𝓝 (μI, νI))
    have hL_ne : L.NeBot := by
      rw [Filter.neBot_iff]; intro hemp
      have hmem : (∅ : Set ℕ) ∈ atTop ⊓ Filter.comap f (𝓝 (μI, νI)) := by
        change (∅ : Set ℕ) ∈ L
        rw [hemp]
        exact Filter.empty_mem_iff_bot.mpr rfl
      rw [Filter.mem_inf_iff] at hmem
      rcases hmem with ⟨s, hs, t, ht, hst⟩
      rw [Filter.mem_comap] at ht
      rcases ht with ⟨u, hu, hut⟩
      have hne_inter : ((f '' s) ∩ u).Nonempty := by
        have h1 : f '' s ∈ Filter.map f atTop := Filter.image_mem_map hs
        have h2 : (f '' s) ∩ u ∈ 𝓝 (μI, νI) ⊓ Filter.map f atTop :=
          Filter.inter_mem (Filter.mem_inf_of_right h1) (Filter.mem_inf_of_left hu)
        exact hcl.nonempty_of_mem h2
      rcases hne_inter with ⟨_, ⟨j, hj, rfl⟩, hju⟩
      have : j ∈ (∅ : Set ℕ) := hst ▸ ⟨hj, hut hju⟩
      exact this
    have hL_le : L ≤ atTop := inf_le_left
    have hf_lim : Tendsto f L (𝓝 (μI, νI)) :=
      tendsto_iff_comap.mpr inf_le_right
    have hμ_lim : Tendsto (fun j => empProbI A (N_seq j) (hA1 j)) L (𝓝 μI) :=
      continuous_fst.continuousAt.tendsto.comp hf_lim
    have hν_lim : Tendsto (fun j => empProbI B (N_seq j) (hB1 j)) L (𝓝 νI) :=
      continuous_snd.continuousAt.tendsto.comp hf_lim
    -- Proposition 4.3 forces (pushToReal μI, pushToReal νI) ∈ {(cantorNu, cantorMu), (cantorMu, cantorNu)}!
    rcases weak_limit_unique hA_inf hB_inf hn₀ hstab hlam_lt hprod_ev hN_top hT_seq hA1 hB1 hL_le hμ_lim hν_lim with
      ⟨hμ_eq, hν_eq⟩ | ⟨hμ_eq, hν_eq⟩
    · have hev := eventually_levelApprox_of_cantor_limit hA_inf hB_inf hN_top hT_seq hA1 hB1 hL_le hμ_lim hν_lim hμ_eq hν_eq
      obtain ⟨j, hj⟩ := hev.exists
      exact hfail_seq j (Or.inl hj)
    · have hT_seq' : ∀ j, crossExcess B A (N_seq j) ≤ K := fun j => by rw [crossExcess_comm]; exact hT_seq j
      have hev := eventually_levelApprox_of_cantor_limit hB_inf hA_inf hN_top hT_seq' hB1 hA1 hL_le hν_lim hμ_lim hν_eq hμ_eq
      obtain ⟨j, hj⟩ := hev.exists
      exact hfail_seq j (Or.inr hj)
  -- Package N_star from hcore into full LevelApprox A B n₀ K N ∨ LevelApprox B A n₀ K N!
  rcases hcore with ⟨N_star, hNs_ge, hNs_prop⟩
  refine ⟨N_star, fun N hN hTN => ?_⟩
  have hN_base : N_base ≤ N := le_trans hNs_ge hN
  have hM_size : 10 ^ 7 * (K + E + n₀ + 1) * (E + n₀ + 1) ≤ N :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN_base))
  have hprod_N : ∀ t ≥ N, (countNat A t : ℝ) * (countNat B t : ℝ) ≤ (8 / 5 : ℝ) * (t : ℝ) :=
    fun t ht => hN_prod t (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans hN_base ht))
  have hA_big : M_cnt ≤ countNat A N :=
    le_trans (le_max_left M_cnt 1) (hN_A N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN_base))
  have hB_big : M_cnt ≤ countNat B N :=
    le_trans (le_max_left M_cnt 1) (hN_B N (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN_base))
  have hMax_A : ∀ M ≥ N, crossExcess A B M ≤ K →
      ∃ a ∈ A, a ≤ M ∧ (1 / 3 - 1 / 1000 : ℝ) * (M : ℝ) ≤ (a : ℝ) := by
    intro M hM hTM
    rcases hNs_prop M (le_trans hN hM) hTM with h1 | h2
    · exact h1.1
    · rcases h2.2.2.1 with ⟨a, haA, haM, ha23⟩
      exact ⟨a, haA, haM, by linarith [Nat.cast_nonneg (α := ℝ) M]⟩
  have hMax_B : ∀ M ≥ N, crossExcess B A M ≤ K →
      ∃ b ∈ B, b ≤ M ∧ (1 / 3 - 1 / 1000 : ℝ) * (M : ℝ) ≤ (b : ℝ) := by
    intro M hM hTM
    rw [crossExcess_comm] at hTM
    rcases hNs_prop M (le_trans hN hM) hTM with h1 | h2
    · rcases h1.2.2.1 with ⟨b, hbB, hbM, hb23⟩
      exact ⟨b, hbB, hbM, by linarith [Nat.cast_nonneg (α := ℝ) M]⟩
    · exact h2.1
  rcases hNs_prop N hN hTN with ⟨h1, h2, h3, h4, h5, h6, h7⟩ | ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · left
    exact {
      hK_ge_n0 := hK
      hN_large := hM_size
      hT_le := hTN
      hprod_le := hprod_N
      hA_large := hA_big
      hB_large := hB_big
      hx₀_lo := h1
      hx₀_hi := h2
      hz₀_lo := h3
      hz₀_hi := h4
      hMaxAtAny := hMax_A
      hgap_A := h5
      hblock1_A := h6
      hblock2_A := h7
    }
  · right
    exact {
      hK_ge_n0 := hK
      hN_large := by rw [hE_comm]; exact hM_size
      hT_le := by rw [crossExcess_comm]; exact hTN
      hprod_le := fun t ht => by rw [mul_comm]; exact hprod_N t ht
      hA_large := by rw [hC1_comm, hE_comm]; exact hB_big
      hB_large := by rw [hC1_comm, hE_comm]; exact hA_big
      hx₀_lo := h1
      hx₀_hi := h2
      hz₀_lo := h3
      hz₀_hi := h4
      hMaxAtAny := hMax_B
      hgap_A := h5
      hblock1_A := h6
      hblock2_A := h7
    }

end

end AlmostPerfect


