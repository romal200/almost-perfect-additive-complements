import AlmostPerfect.GabardoLaiBase
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Gabardo–Lai Factorization (Part 2): Lemma `lem1` and Single-Step Theorem 4.1

Completes the self-contained, zero-axiom formalization of Section 2 of
J.-P. Gabardo and C.-K. Lai, *Factorization of Lebesgue measures on an interval*,
J. Fourier Anal. Appl. 20 (2014), Thm. 2.2:

1. `gabardo_lai_lem1`: if `μ ∗ ν = lebHalf` with `sInf μ.support = -a`, `sSup μ.support = a`
   (`0 < a < 1/2`), and `r ≥ 2` is the smallest positive integer with `ft μ r = 0`, then every
   integer zero `k : ℤ` of `ft μ` is divisible by `r`. Proved by strong induction on `r` via
   Radon–Nikodym densities (`Measure.rnDeriv`) for both even `r` and odd `r`.
2. `gabardo_lai_strip_one`: one-sided periodic stripping `μ = unifDiscrete M (1/M) ∗ α`,
   `α ∗ ν = lebScaled (1/M)` when `ft μ 1 = 0`.
3. `gabardo_lai_single_step` (**Theorem 4.1**): every nontrivial complementary pair
   `(μ, ν)` on `[0, 1]` with `μ ∗ ν = leb01` factors in one step (up to swapping `μ, ν`) as
   `μ = unifDiscrete M₁ (1/M₁) ∗ μ'`, `ν = unifDiscrete M₂ (1/(M₁ M₂)) ∗ ν'` with `M₁, M₂ ≥ 2`
   and `μ' ∗ ν' = lebScaled (1/(M₁ M₂))`.
-/

namespace AlmostPerfect

open MeasureTheory Filter Topology Real Complex BigOperators
open scoped ENNReal MeasureTheory

noncomputable section

/-! ### Support, Convolution, and Fourier Helpers -/

lemma ft_im_eq_zero_of_check {μ : Measure ℝ} (hcheck : checkMeasure μ = μ) (ξ : ℝ) :
    (ft μ ξ).im = 0 := by
  have h1 : starRingEnd ℂ (ft μ ξ) = ft μ ξ := by
    rw [← ft_neg, ← ft_check, hcheck]
  have him := congrArg Complex.im h1
  simp only [Complex.conj_im] at him
  linarith

lemma checkMeasure_conv (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    checkMeasure (μ ∗ ν) = checkMeasure μ ∗ checkMeasure ν := by
  unfold checkMeasure
  let negHom : ℝ →+ ℝ := ⟨⟨fun x => -x, neg_zero⟩, neg_add⟩
  simpa [negHom] using Measure.map_conv_addMonoidHom (μ := μ) (ν := ν) negHom measurable_neg

lemma conv_supported_Icc {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a₁ a₂ b₁ b₂ : ℝ} (hμ : IsSupportedIn μ (Set.Icc a₁ a₂)) (hν : IsSupportedIn ν (Set.Icc b₁ b₂)) :
    IsSupportedIn (μ ∗ ν) (Set.Icc (a₁ + b₁) (a₂ + b₂)) := by
  unfold IsSupportedIn at hμ hν ⊢
  rw [Measure.conv, Measure.map_apply measurable_add measurableSet_Icc.compl]
  have hsub : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' (Set.Icc (a₁ + b₁) (a₂ + b₂))ᶜ ⊆
      ((Set.Icc a₁ a₂)ᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ (Set.Icc b₁ b₂)ᶜ) := by
    rintro ⟨x, y⟩ hxy
    by_contra hnot
    simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff, Set.mem_univ, and_true,
      true_and, not_or, not_not, Set.mem_Icc] at hnot
    exact hxy ⟨by linarith, by linarith⟩
  apply measure_mono_null hsub
  exact measure_union_null (by rw [Measure.prod_prod, hμ, zero_mul])
    (by rw [Measure.prod_prod, hν, mul_zero])

lemma isProbabilityMeasure_map_measurable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hf : Measurable f) : IsProbabilityMeasure (μ.map f) := by
  constructor
  rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ, measure_univ]

lemma map_conv_mul_left (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c : ℝ) :
    (μ ∗ ν).map (c * ·) = μ.map (c * ·) ∗ ν.map (c * ·) := by
  let hom : ℝ →+ ℝ := ⟨⟨fun x => c * x, mul_zero c⟩, mul_add c⟩
  simpa [hom] using Measure.map_conv_addMonoidHom (μ := μ) (ν := ν) hom (measurable_const_mul c)

lemma map_conv_add_const (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (a b : ℝ) :
    (μ ∗ ν).map (· + (a + b)) = μ.map (· + a) ∗ ν.map (· + b) := by
  have : IsFiniteMeasure (μ.map (· + a)) := by
    constructor; rw [Measure.map_apply (measurable_add_const a) MeasurableSet.univ, Set.preimage_univ]
    exact measure_lt_top μ Set.univ
  have : IsFiniteMeasure (ν.map (· + b)) := by
    constructor; rw [Measure.map_apply (measurable_add_const b) MeasurableSet.univ, Set.preimage_univ]
    exact measure_lt_top ν Set.univ
  have : IsFiniteMeasure ((μ ∗ ν).map (· + (a + b))) := by
    constructor; rw [Measure.map_apply (measurable_add_const _) MeasurableSet.univ, Set.preimage_univ]
    exact measure_lt_top (μ ∗ ν) Set.univ
  apply ext_of_ft
  intro ξ
  rw [ft_map_add_const, ft_conv, ft_conv, ft_map_add_const, ft_map_add_const]
  have hexp : Complex.exp (-2 * Real.pi * ξ * ((a + b : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-2 * Real.pi * ξ * a * Complex.I) * Complex.exp (-2 * Real.pi * ξ * b * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hexp]; ring

lemma map_add_const_support (μ : Measure ℝ) (t : ℝ) :
    (μ.map (· + t)).support = (· + t) '' μ.support := by
  ext y
  rw [Measure.mem_support_iff_forall, Set.mem_image]
  constructor
  · intro hy
    refine ⟨y - t, ?_, by ring⟩
    rw [Measure.mem_support_iff_forall]
    intro U hU
    rcases mem_nhds_iff.mp hU with ⟨V, hVU, hVopen, hyV⟩
    have hopenV : IsOpen ((· + t) '' V) := (Homeomorph.addRight t).isOpenMap V hVopen
    have h1 := hy ((· + t) '' V) (hopenV.mem_nhds ⟨y - t, hyV, by ring⟩)
    rw [Measure.map_apply (measurable_add_const t) hopenV.measurableSet] at h1
    have hpre : (· + t) ⁻¹' ((· + t) '' V) = V := by ext x; simp
    rw [hpre] at h1
    exact lt_of_lt_of_le h1 (measure_mono hVU)
  · rintro ⟨x, hx, rfl⟩
    rw [Measure.mem_support_iff_forall] at hx
    intro U hU
    rcases mem_nhds_iff.mp hU with ⟨V, hVU, hVopen, hxV⟩
    have h1 := hx ((· + t) ⁻¹' V) ((hVopen.preimage (by fun_prop : Continuous (· + t))).mem_nhds hxV)
    rw [← Measure.map_apply (measurable_add_const t) hVopen.measurableSet] at h1
    exact lt_of_lt_of_le h1 (measure_mono hVU)

lemma map_mul_pos_support (μ : Measure ℝ) {c : ℝ} (hc : 0 < c) :
    (μ.map (c * ·)).support = (c * ·) '' μ.support := by
  ext y
  rw [Measure.mem_support_iff_forall, Set.mem_image]
  constructor
  · intro hy
    refine ⟨c⁻¹ * y, ?_, by field_simp⟩
    rw [Measure.mem_support_iff_forall]
    intro U hU
    rcases mem_nhds_iff.mp hU with ⟨V, hVU, hVopen, hyV⟩
    have hopenV : IsOpen ((c * ·) '' V) := (Homeomorph.mulLeft₀ c hc.ne').isOpenMap V hVopen
    have h1 := hy ((c * ·) '' V) (hopenV.mem_nhds ⟨c⁻¹ * y, hyV, by field_simp⟩)
    rw [Measure.map_apply (measurable_const_mul c) hopenV.measurableSet] at h1
    have hpre : (c * ·) ⁻¹' ((c * ·) '' V) = V := by
      ext x; simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨z, hz, heq⟩; have := mul_left_cancel₀ hc.ne' heq; rwa [← this]
      · intro hx; exact ⟨x, hx, rfl⟩
    rw [hpre] at h1
    exact lt_of_lt_of_le h1 (measure_mono hVU)
  · rintro ⟨x, hx, rfl⟩
    rw [Measure.mem_support_iff_forall] at hx
    intro U hU
    rcases mem_nhds_iff.mp hU with ⟨V, hVU, hVopen, hxV⟩
    have h1 := hx ((c * ·) ⁻¹' V) ((hVopen.preimage (continuous_const_mul c)).mem_nhds hxV)
    rw [← Measure.map_apply (measurable_const_mul c) hVopen.measurableSet] at h1
    exact lt_of_lt_of_le h1 (measure_mono hVU)

lemma sInf_image_add_const {s : Set ℝ} (hne : s.Nonempty) (hbb : BddBelow s) (t : ℝ) :
    sInf ((· + t) '' s) = sInf s + t := by
  have hbb' : BddBelow ((· + t) '' s) := by
    rcases hbb with ⟨m, hm⟩
    exact ⟨m + t, by rintro _ ⟨x, hx, rfl⟩; linarith [hm hx]⟩
  apply le_antisymm
  · rw [csInf_le_iff hbb' (hne.image _)]
    intro b hb
    have h1 : b - t ≤ sInf s := le_csInf hne (fun x hx => by
      have := hb ⟨x, hx, rfl⟩; linarith)
    linarith
  · apply le_csInf (hne.image _)
    rintro _ ⟨x, hx, rfl⟩
    linarith [csInf_le hbb hx]

lemma sSup_image_add_const {s : Set ℝ} (hne : s.Nonempty) (hba : BddAbove s) (t : ℝ) :
    sSup ((· + t) '' s) = sSup s + t := by
  have hba' : BddAbove ((· + t) '' s) := by
    rcases hba with ⟨M, hM⟩
    exact ⟨M + t, by rintro _ ⟨x, hx, rfl⟩; linarith [hM hx]⟩
  apply le_antisymm
  · apply csSup_le (hne.image _)
    rintro _ ⟨x, hx, rfl⟩
    linarith [le_csSup hba hx]
  · rw [le_csSup_iff hba' (hne.image _)]
    intro b hb
    have h1 : sSup s ≤ b - t := csSup_le hne (fun x hx => by
      have := hb ⟨x, hx, rfl⟩; linarith)
    linarith

lemma sInf_image_mul_pos {s : Set ℝ} (hne : s.Nonempty) (hbb : BddBelow s) {c : ℝ} (hc : 0 < c) :
    sInf ((c * ·) '' s) = c * sInf s := by
  have hbb' : BddBelow ((c * ·) '' s) := by
    rcases hbb with ⟨m, hm⟩
    exact ⟨c * m, by rintro _ ⟨x, hx, rfl⟩; exact mul_le_mul_of_nonneg_left (hm hx) (le_of_lt hc)⟩
  apply le_antisymm
  · rw [csInf_le_iff hbb' (hne.image _)]
    intro b hb
    have h1 : b / c ≤ sInf s := le_csInf hne (fun x hx => by
      rw [div_le_iff₀ hc]; linarith [hb ⟨x, hx, rfl⟩])
    rw [div_le_iff₀ hc] at h1; linarith
  · apply le_csInf (hne.image _)
    rintro _ ⟨x, hx, rfl⟩
    exact mul_le_mul_of_nonneg_left (csInf_le hbb hx) (le_of_lt hc)

lemma sSup_image_mul_pos {s : Set ℝ} (hne : s.Nonempty) (hba : BddAbove s) {c : ℝ} (hc : 0 < c) :
    sSup ((c * ·) '' s) = c * sSup s := by
  have hba' : BddAbove ((c * ·) '' s) := by
    rcases hba with ⟨M, hM⟩
    exact ⟨c * M, by rintro _ ⟨x, hx, rfl⟩; exact mul_le_mul_of_nonneg_left (hM hx) (le_of_lt hc)⟩
  apply le_antisymm
  · apply csSup_le (hne.image _)
    rintro _ ⟨x, hx, rfl⟩
    exact mul_le_mul_of_nonneg_left (le_csSup hba hx) (le_of_lt hc)
  · rw [le_csSup_iff hba' (hne.image _)]
    intro b hb
    have h1 : sSup s ≤ b / c := csSup_le hne (fun x hx => by
      rw [le_div_iff₀ hc]; linarith [hb ⟨x, hx, rfl⟩])
    rw [le_div_iff₀ hc] at h1; linarith

lemma eq_dirac_zero_of_supp_le_zero {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : IsSupportedIn μ (Set.Icc 0 0)) : μ = Measure.dirac 0 := by
  apply ext_of_ft
  intro ξ
  rw [ft_apply, ft_dirac]
  have hae : ∀ᵐ x ∂μ, x = 0 := by
    have hmem : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 0 := by rw [ae_iff]; exact hsupp
    filter_upwards [hmem] with x hx
    linarith [hx.1, hx.2]
  have hint : ∫ x, Complex.exp (-2 * Real.pi * ξ * x * Complex.I) ∂μ =
      ∫ _x, Complex.exp (-2 * Real.pi * ξ * (0 : ℝ) * Complex.I) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
  rw [hint]; simp

lemma ft_unifDiscrete {M : ℕ} (_hM : 0 < M) (step ξ : ℝ) :
    ft (unifDiscrete M step) ξ =
      ((M : ℂ))⁻¹ * ∑ j ∈ Finset.range M, Complex.exp (-2 * Real.pi * ξ * ((j : ℝ) * step) * Complex.I) := by
  rw [ft_apply, unifDiscrete, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
  congr 1
  have hsum_int : ∀ t : Finset ℕ,
      Integrable (fun x : ℝ => Complex.exp (-2 * Real.pi * ξ * x * Complex.I))
        (∑ j ∈ t, Measure.dirac ((j : ℝ) * step)) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert b u hb ihu =>
      rw [Finset.sum_insert hb]
      exact (integrable_dirac (by norm_num)).add_measure ihu
  have hsum : ∀ t : Finset ℕ,
      ∫ x, Complex.exp (-2 * Real.pi * ξ * x * Complex.I) ∂(∑ j ∈ t, Measure.dirac ((j : ℝ) * step)) =
        ∑ j ∈ t, Complex.exp (-2 * Real.pi * ξ * ((j : ℝ) * step) * Complex.I) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, integral_add_measure (integrable_dirac (by norm_num)) (hsum_int s),
          integral_dirac, ih, Complex.ofReal_mul]
  exact hsum (Finset.range M)

lemma unifDiscrete_conv_lebScaled {M : ℕ} (hM : 1 ≤ M) {c : ℝ} (hc : 0 < c) :
    unifDiscrete M c ∗ lebScaled c = lebScaled ((M : ℝ) * c) := by
  have hMpos_n : 0 < M := by omega
  have hMc_pos : (0 : ℝ) < (M : ℝ) * c := mul_pos (Nat.cast_pos.mpr hMpos_n) hc
  have : IsProbabilityMeasure (unifDiscrete M c) := isProbabilityMeasure_unifDiscrete hMpos_n c
  have : IsProbabilityMeasure (lebScaled c) := isProbabilityMeasure_lebScaled hc
  have : IsProbabilityMeasure (lebScaled ((M : ℝ) * c)) := isProbabilityMeasure_lebScaled hMc_pos
  apply ext_of_ft
  have hdense : Dense {ξ : ℝ | ∀ k : ℤ, ξ * c ≠ (k : ℝ)} := by
    intro x
    rw [Metric.mem_closure_iff]
    intro ε hε
    by_cases hx : ∃ k : ℤ, x * c = k
    · rcases hx with ⟨k, hk⟩
      set δ := min (ε / 2) (1 / (2 * c))
      have hδpos : 0 < δ := lt_min (half_pos hε) (by positivity)
      refine ⟨x + δ, ?_, ?_⟩
      · intro m hm
        have h1 : 0 < δ * c := mul_pos hδpos hc
        have h2 : δ * c ≤ 1 / 2 := by
          have : δ ≤ 1 / (2 * c) := min_le_right _ _
          have := mul_le_mul_of_nonneg_right this (le_of_lt hc)
          have hcancel : 1 / (2 * c) * c = 1 / 2 := by field_simp
          linarith
        have hkm1 : (k : ℝ) < (m : ℝ) := by linarith
        have hkm2 : (m : ℝ) < (k : ℝ) + 1 := by linarith
        have h1z : k < m := by exact_mod_cast hkm1
        have h2z : m < k + 1 := by exact_mod_cast hkm2
        omega
      · rw [Real.dist_eq, abs_sub_comm, show x + δ - x = δ by ring, abs_of_pos hδpos]
        exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
    · push Not at hx; exact ⟨x, hx, by simp [hε]⟩
  have hfun : ft (unifDiscrete M c ∗ lebScaled c) = ft (lebScaled ((M : ℝ) * c)) := by
    apply Continuous.ext_on hdense (continuous_ft _) (continuous_ft _)
    intro ξ hξ
    have hξ0 : ξ ≠ 0 := by intro h0; apply hξ 0; simp [h0]
    rw [ft_conv, ft_unifDiscrete hMpos_n c ξ, ft_lebScaled hc ξ,
        ft_lebScaled hMc_pos ξ]
    simp only [hξ0, ↓reduceIte]
    set z : ℂ := Complex.exp (-2 * Real.pi * ξ * c * Complex.I)
    have hsum_z : ∑ j ∈ Finset.range M, Complex.exp (-2 * Real.pi * ξ * ((j : ℝ) * c) * Complex.I) =
        ∑ j ∈ Finset.range M, z ^ j := by
      apply Finset.sum_congr rfl; intro j _
      simp only [z, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    rw [hsum_z]
    have hgeom := geom_sum_mul z M
    have hzM : z ^ M = Complex.exp (-2 * Real.pi * ξ * (((M : ℝ) * c : ℝ) : ℂ) * Complex.I) := by
      simp only [z, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have hMc : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hξc : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ0
    have hcc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    rw [← hzM]
    calc
      (M : ℂ)⁻¹ * (∑ j ∈ Finset.range M, z ^ j) * ((z - 1) / (-2 * Real.pi * ξ * c * Complex.I))
          = ((∑ j ∈ Finset.range M, z ^ j) * (z - 1)) / ((M : ℂ) * (-2 * Real.pi * ξ * c * Complex.I)) := by
            field_simp
      _ = (z ^ M - 1) / ((M : ℂ) * (-2 * Real.pi * ξ * c * Complex.I)) := by rw [hgeom]
      _ = (z ^ M - 1) / (-2 * Real.pi * ξ * ((M : ℝ) * c : ℝ) * Complex.I) := by
            congr 1; push_cast; ring
  exact congrFun hfun

lemma unifDiscrete_map_mul {M : ℕ} (step c : ℝ) :
    (unifDiscrete M step).map (c * ·) = unifDiscrete M (c * step) := by
  ext s hs
  rw [Measure.map_apply (measurable_const_mul c) hs, unifDiscrete, unifDiscrete,
      Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
      Measure.finsetSum_apply, Measure.finsetSum_apply]
  congr 1
  apply Finset.sum_congr rfl; intro j _
  rw [Measure.dirac_apply' _ ((measurable_const_mul c) hs), Measure.dirac_apply' _ hs]
  have heq : c * ((j : ℝ) * step) = (j : ℝ) * (c * step) := by ring
  by_cases hm : (j : ℝ) * (c * step) ∈ s
  · have hm' : (j : ℝ) * step ∈ (c * ·) ⁻¹' s := by simpa [Set.mem_preimage, heq] using hm
    rw [Set.indicator_of_mem hm', Set.indicator_of_mem hm]; rfl
  · have hm' : (j : ℝ) * step ∉ (c * ·) ⁻¹' s := by simpa [Set.mem_preimage, heq] using hm
    rw [Set.indicator_of_notMem hm', Set.indicator_of_notMem hm]

/-! ### Elementary Trig Integrals via Fundamental Theorem of Calculus -/

private lemma integral_sin_two_pi_mul (r : ℝ) (hr : r ≠ 0) (c : ℝ) :
    ∫ x in (0 : ℝ)..c, Real.sin (2 * Real.pi * r * x) =
      (1 - Real.cos (2 * Real.pi * r * c)) / (2 * Real.pi * r) := by
  have h2pr : 2 * Real.pi * r ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hr
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) c,
      HasDerivAt (fun t : ℝ => -Real.cos (2 * Real.pi * r * t) / (2 * Real.pi * r))
        (Real.sin (2 * Real.pi * r * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * r * t) (2 * Real.pi * r) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * Real.pi * r)
    have h2 : HasDerivAt (fun t : ℝ => -Real.cos (2 * Real.pi * r * t))
        (Real.sin (2 * Real.pi * r * x) * (2 * Real.pi * r)) x := by
      convert h1.cos.neg using 1; ring
    have h3 := h2.div_const (2 * Real.pi * r)
    convert h3 using 1; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((by fun_prop : Continuous fun x => Real.sin (2 * Real.pi * r * x)).intervalIntegrable 0 c)]
  simp only [mul_zero, Real.cos_zero]
  ring

private lemma integral_cos_two_pi_mul (ξ : ℝ) (hξ : ξ ≠ 0) (c : ℝ) :
    ∫ x in (0 : ℝ)..c, Real.cos (2 * Real.pi * ξ * x) =
      Real.sin (2 * Real.pi * ξ * c) / (2 * Real.pi * ξ) := by
  have h2pξ : 2 * Real.pi * ξ ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hξ
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) c,
      HasDerivAt (fun t : ℝ => Real.sin (2 * Real.pi * ξ * t) / (2 * Real.pi * ξ))
        (Real.cos (2 * Real.pi * ξ * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * ξ * t) (2 * Real.pi * ξ) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * Real.pi * ξ)
    have h2 := h1.sin.div_const (2 * Real.pi * ξ)
    convert h2 using 1; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((by fun_prop : Continuous fun x => Real.cos (2 * Real.pi * ξ * x)).intervalIntegrable 0 c)]
  simp only [mul_zero, Real.sin_zero, zero_div, sub_zero]

/-! ### Radon–Nikodym Density Helpers -/

private lemma integral_comp_neg_vol {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : ∫ x, f (-x) ∂volume = ∫ x, f x ∂volume := by
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.neg ℝ).toMeasurableEquiv
  have hmap : Measure.map e volume = volume := by
    have he : (e : ℝ → ℝ) = ((-1 : ℝ) * ·) := by ext x; simp [e]
    rw [he, Real.map_volume_mul_left (by norm_num : (-1 : ℝ) ≠ 0)]; simp
  calc ∫ x, f (-x) ∂volume = ∫ x, f (e x) ∂volume := rfl
    _ = ∫ y, f y ∂(Measure.map e volume) := (integral_map_equiv e f).symm
    _ = ∫ y, f y ∂volume := by rw [hmap]

private lemma rnDeriv_ae_zero_of_measure_zero {σ : Measure ℝ} [IsFiniteMeasure σ]
    (hac : σ ≪ volume) {s : Set ℝ} (hs : MeasurableSet s) (h0 : σ s = 0) :
    ∀ᵐ x ∂volume, x ∈ s → σ.rnDeriv volume x = 0 := by
  have hlint : ∫⁻ x in s, σ.rnDeriv volume x ∂volume = 0 := by
    rw [← withDensity_apply _ hs, Measure.withDensity_rnDeriv_eq σ volume hac]
    exact h0
  have hae : σ.rnDeriv volume =ᵐ[volume.restrict s] 0 :=
    (lintegral_eq_zero_iff (Measure.measurable_rnDeriv σ volume)).mp hlint
  exact (ae_restrict_iff' hs).mp hae

private lemma rnDeriv_le_const_ae {σ : Measure ℝ} [IsFiniteMeasure σ]
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hle : σ ≤ C • volume) :
    ∀ᵐ x ∂volume, σ.rnDeriv volume x ≤ C := by
  have hac : σ ≪ volume := Measure.AbsolutelyContinuous.mk fun s _ hs => by
    have h1 := hle s; rw [Measure.smul_apply, smul_eq_mul, hs, mul_zero] at h1
    exact nonpos_iff_eq_zero.mp h1
  have hmeas_lt : MeasurableSet {x : ℝ | C < σ.rnDeriv volume x} :=
    measurableSet_lt measurable_const (Measure.measurable_rnDeriv σ volume)
  have hnull_n : ∀ n : ℕ, volume ({x : ℝ | C < σ.rnDeriv volume x} ∩ Set.Icc (-(n : ℝ)) n) = 0 := by
    intro n
    set t := {x : ℝ | C < σ.rnDeriv volume x} ∩ Set.Icc (-(n : ℝ)) n
    have ht_meas : MeasurableSet t := hmeas_lt.inter measurableSet_Icc
    have ht_fin : volume t < ⊤ :=
      lt_of_le_of_lt (measure_mono Set.inter_subset_right) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
    have hle_int : ∫⁻ x in t, σ.rnDeriv volume x ∂volume ≤ ∫⁻ _x in t, C ∂volume := by
      rw [← withDensity_apply _ ht_meas, Measure.withDensity_rnDeriv_eq σ volume hac, setLIntegral_const]
      exact (hle t).trans (by simp [Measure.smul_apply, smul_eq_mul])
    have hdecomp : ∫⁻ x in t, σ.rnDeriv volume x ∂volume =
        (∫⁻ _x in t, C ∂volume) + ∫⁻ x in t, (σ.rnDeriv volume x - C) ∂volume := by
      rw [← lintegral_add_left measurable_const]
      apply setLIntegral_congr_fun ht_meas
      intro x hx
      exact (add_tsub_cancel_of_le (le_of_lt hx.1)).symm
    rw [hdecomp] at hle_int
    have hCfin : ∫⁻ _x in t, C ∂volume ≠ ⊤ := by
      rw [setLIntegral_const]; exact ENNReal.mul_ne_top hC ht_fin.ne
    have hsub0 : ∫⁻ x in t, (σ.rnDeriv volume x - C) ∂volume = 0 := by
      by_contra hne
      exact not_le_of_gt (ENNReal.lt_add_right hCfin hne) hle_int
    have hae0 := (ae_restrict_iff' ht_meas).mp
      ((lintegral_eq_zero_iff ((Measure.measurable_rnDeriv σ volume).sub measurable_const)).mp hsub0)
    have hae_not : ∀ᵐ x ∂volume, x ∉ t := by
      filter_upwards [hae0] with x hx hxt
      exact not_le_of_gt hxt.1 (tsub_eq_zero_iff_le.mp (hx hxt))
    rw [ae_iff] at hae_not
    simpa only [not_not, Set.ofPred_mem_eq] using hae_not
  have hunion : {x : ℝ | ¬ σ.rnDeriv volume x ≤ C} =
      ⋃ n : ℕ, ({x : ℝ | C < σ.rnDeriv volume x} ∩ Set.Icc (-(n : ℝ)) n) := by
    ext x
    simp only [Set.mem_ofPred_eq, not_le, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Icc]
    constructor
    · intro hlt
      refine ⟨Nat.ceil |x|, hlt, ?_, ?_⟩
      · have h1 : |x| ≤ (Nat.ceil |x| : ℝ) := Nat.le_ceil |x|
        linarith [(abs_le.mp h1).1]
      · have h1 : |x| ≤ (Nat.ceil |x| : ℝ) := Nat.le_ceil |x|
        exact (abs_le.mp h1).2
    · rintro ⟨_, hlt, _⟩; exact hlt
  rw [ae_iff, hunion]
  exact measure_iUnion_null hnull_n

/-! ### Gabardo–Lai Lemma 2.3 (`lem1`): Even Step and Odd Case -/

/-- Even step of `gabardo_lai_lem1`: constructs `ρ` supported in `[0, 1/2 - a]` with
`μ ∗ ρ = lebScaled (1/2)` and deduces `2 ∣ k` for every integer zero `k` of `ft μ`. -/
private lemma gabardo_lai_lem1_even_step {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : ℝ} (ha0 : 0 < a) (ha_half : a < 1 / 2)
    (hconv : μ ∗ ν = lebHalf)
    (hμ_supp : IsSupportedIn μ (Set.Icc (-a) a))
    (hν_supp : IsSupportedIn ν (Set.Icc (-(1 / 2 - a)) (1 / 2 - a)))
    (hcheck_μ : checkMeasure μ = μ) (hcheck_ν : checkMeasure ν = ν)
    {r : ℕ} (hr2 : 2 ≤ r) (heven : Even r) (ha_le : a ≤ 1 / (2 * (r : ℝ)))
    (hμr : ft μ r = 0) :
    ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
      IsSupportedIn ρ (Set.Icc 0 (1 / 2 - a)) ∧
      μ ∗ ρ = lebScaled (1 / 2) ∧
      (∀ k : ℤ, ft μ k = 0 → (2 : ℤ) ∣ k) := by
  set b := 1 / 2 - a with hb_def
  have hb0 : 0 < b := by simp only [b]; linarith
  let ρ : Measure ℝ := ν {0} • Measure.dirac 0 + (2 : ℝ≥0∞) • ν.restrict (Set.Ioc (0 : ℝ) (1 / 2))
  -- Symmetry: ρ + checkMeasure ρ = 2 • ν
  have hρ_sum : ρ + checkMeasure ρ = (2 : ℝ≥0∞) • ν := by
    ext s hs
    simp only [ρ, checkMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply measurable_neg hs, Measure.restrict_apply hs,
      Measure.restrict_apply (hs.preimage measurable_neg)]
    have hdir : Measure.dirac (0 : ℝ) ((fun x : ℝ => -x) ⁻¹' s) = Measure.dirac (0 : ℝ) s := by
      rw [Measure.dirac_apply' _ (hs.preimage measurable_neg), Measure.dirac_apply' _ hs]
      by_cases h0 : (0 : ℝ) ∈ s
      · have h0' : (0 : ℝ) ∈ (fun x : ℝ => -x) ⁻¹' s := by simpa [Set.mem_preimage] using h0
        rw [Set.indicator_of_mem h0', Set.indicator_of_mem h0]
      · have h0' : (0 : ℝ) ∉ (fun x : ℝ => -x) ⁻¹' s := by simpa [Set.mem_preimage] using h0
        rw [Set.indicator_of_notMem h0', Set.indicator_of_notMem h0]
    have hneg_Ioc : ν ((fun x : ℝ => -x) ⁻¹' s ∩ Set.Ioc 0 (1 / 2)) =
        ν (s ∩ Set.Ico (-(1 / 2)) 0) := by
      have hpre : (fun x : ℝ => -x) ⁻¹' s ∩ Set.Ioc 0 (1 / 2) =
          (fun x : ℝ => -x) ⁻¹' (s ∩ Set.Ico (-(1 / 2)) 0) := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioc, Set.mem_Ico]
        constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1, by linarith, by linarith⟩
      rw [hpre, ← Measure.map_apply measurable_neg (hs.inter measurableSet_Ico)]
      change (checkMeasure ν) (s ∩ Set.Ico (-(1 / 2)) 0) = _
      rw [hcheck_ν]
    rw [hdir, hneg_Ioc]
    have hzero_term : ν {0} * Measure.dirac (0 : ℝ) s = ν (s ∩ {0}) := by
      rw [Measure.dirac_apply' _ hs]
      by_cases h0 : (0 : ℝ) ∈ s
      · rw [Set.indicator_of_mem h0, Pi.one_apply, mul_one]
        congr 1; ext x; simp only [Set.mem_singleton_iff, Set.mem_inter_iff]
        exact ⟨fun hx => ⟨hx ▸ h0, hx⟩, fun h => h.2⟩
      · rw [Set.indicator_of_notMem h0, mul_zero]
        have : s ∩ {0} = ∅ := by ext x; simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]; rintro ⟨hx, rfl⟩; exact h0 hx
        rw [this, measure_empty]
    rw [hzero_term]
    have hdisj1 : Disjoint (s ∩ Set.Ico (-(1 / 2)) 0) (s ∩ {0}) := by
      rw [Set.disjoint_left]; intro x h1 h2; simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_singleton_iff] at h1 h2; linarith
    have hdisj2 : Disjoint ((s ∩ Set.Ico (-(1 / 2)) 0) ∪ (s ∩ {0})) (s ∩ Set.Ioc 0 (1 / 2)) := by
      rw [Set.disjoint_left]; intro x h1 h2
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Ico, Set.mem_singleton_iff, Set.mem_Ioc] at h1 h2
      rcases h1 with ⟨_, _, hlt⟩ | ⟨_, rfl⟩ <;> linarith
    have hunion : (s ∩ Set.Ico (-(1 / 2)) 0) ∪ (s ∩ {0}) ∪ (s ∩ Set.Ioc 0 (1 / 2)) =
        s ∩ Set.Icc (-(1 / 2)) (1 / 2) := by
      ext x; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Ico, Set.mem_singleton_iff, Set.mem_Ioc, Set.mem_Icc]
      constructor
      · rintro ((⟨h1, h2, h3⟩ | ⟨h1, rfl⟩) | ⟨h1, h2, h3⟩) <;> exact ⟨h1, by linarith, by linarith⟩
      · rintro ⟨h1, h2, h3⟩
        rcases lt_trichotomy x 0 with hlt | rfl | hgt
        · left; left; exact ⟨h1, h2, hlt⟩
        · left; right; exact ⟨h1, rfl⟩
        · right; exact ⟨h1, hgt, h3⟩
    have hsum_Icc : ν (s ∩ Set.Ico (-(1 / 2)) 0) + ν (s ∩ {0}) + ν (s ∩ Set.Ioc 0 (1 / 2)) =
        ν (s ∩ Set.Icc (-(1 / 2)) (1 / 2)) := by
      rw [← measure_union hdisj1 (hs.inter (measurableSet_singleton 0)),
          ← measure_union hdisj2 (hs.inter measurableSet_Ioc), hunion]
    have hν_half : ν (Set.Icc (-(1 / 2)) (1 / 2))ᶜ = 0 := by
      have hsub : (Set.Icc (-(1 / 2 : ℝ)) (1 / 2))ᶜ ⊆ (Set.Icc (-b) b)ᶜ :=
        Set.compl_subset_compl.mpr (fun x hx => ⟨by linarith [hx.1, hb_def], by linarith [hx.2, hb_def]⟩)
      exact measure_mono_null hsub hν_supp
    have hs_eq : ν (s ∩ Set.Icc (-(1 / 2)) (1 / 2)) = ν s := by
      have hsp := measure_inter_add_sdiff s (measurableSet_Icc : MeasurableSet (Set.Icc (-(1 / 2 : ℝ)) (1 / 2))) (μ := ν)
      have hd : ν (s \ Set.Icc (-(1 / 2)) (1 / 2)) = 0 := measure_mono_null (fun _ hx => hx.2) hν_half
      rw [hd, add_zero] at hsp; exact hsp
    rw [← hs_eq, ← hsum_Icc]
    ring
  have hρ_prob : IsProbabilityMeasure ρ := by
    constructor
    have hu := congrArg (fun m : Measure ℝ => m Set.univ) hρ_sum
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] at hu
    have hcheck_u : (checkMeasure ρ) Set.univ = ρ Set.univ := by
      rw [checkMeasure, Measure.map_apply measurable_neg MeasurableSet.univ, Set.preimage_univ]
    rw [hcheck_u, ← two_mul] at hu
    have hne : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have htop : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
    have h1 := congrArg ((2 : ℝ≥0∞)⁻¹ * ·) hu
    simp only [← mul_assoc, ENNReal.inv_mul_cancel hne htop, one_mul] at h1
    exact h1
  have hρ_supp : IsSupportedIn ρ (Set.Icc 0 b) := by
    unfold IsSupportedIn
    simp only [ρ, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ measurableSet_Icc.compl, Measure.restrict_apply measurableSet_Icc.compl]
    have h0_in : (0 : ℝ) ∈ Set.Icc 0 b := ⟨le_rfl, le_of_lt hb0⟩
    rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr h0_in), mul_zero, zero_add]
    have hsub : (Set.Icc (0 : ℝ) b)ᶜ ∩ Set.Ioc 0 (1 / 2) ⊆ (Set.Icc (-b) b)ᶜ := by
      intro x ⟨h1, h2, _⟩ hbb
      exact h1 ⟨le_of_lt h2, hbb.2⟩
    rw [measure_mono_null hsub hν_supp, mul_zero]
  -- Convolution identity: μ ∗ ρ + checkMeasure (μ ∗ ρ) = 2 • lebHalf
  have hconv_sum : μ ∗ ρ + checkMeasure (μ ∗ ρ) = (2 : ℝ≥0∞) • lebHalf := by
    rw [checkMeasure_conv, hcheck_μ, ← Measure.conv_add, hρ_sum, Measure.conv_smul_right, hconv]
  have hle_2vol : μ ∗ ρ ≤ (2 : ℝ≥0∞) • volume := by
    intro s
    calc (μ ∗ ρ) s ≤ (μ ∗ ρ + checkMeasure (μ ∗ ρ)) s := by simp
      _ = (2 : ℝ≥0∞) * lebHalf s := by rw [hconv_sum]; rfl
      _ ≤ (2 : ℝ≥0∞) * volume s := mul_le_mul_of_nonneg_left (Measure.restrict_le_self s) zero_le
  have hac : μ ∗ ρ ≪ volume := Measure.AbsolutelyContinuous.mk fun s _ hs => by
    have h1 := hle_2vol s; rw [Measure.smul_apply, smul_eq_mul, hs, mul_zero] at h1
    exact nonpos_iff_eq_zero.mp h1
  set g_en := (μ ∗ ρ).rnDeriv volume
  set g : ℝ → ℝ := fun x => (g_en x).toReal
  have hg_meas : Measurable g := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hg_nn : ∀ x, 0 ≤ g x := fun _ => ENNReal.toReal_nonneg
  have hg_le2_en : ∀ᵐ x ∂volume, g_en x ≤ 2 := rnDeriv_le_const_ae (by norm_num) hle_2vol
  have hg_le2 : ∀ᵐ x ∂volume, g x ≤ 2 := by
    filter_upwards [hg_le2_en] with x hx
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using hx)
  -- Support of μ ∗ ρ is in [-a, 1/2], so g = 0 a.e. outside [-a, 1/2]
  have hμρ_supp : IsSupportedIn (μ ∗ ρ) (Set.Icc (-a) (1 / 2)) := by
    have h1 := conv_supported_Icc hμ_supp hρ_supp
    have heq : -a + 0 = -a := by ring
    have heq2 : a + b = 1 / 2 := by simp only [b]; ring
    rwa [heq, heq2] at h1
  have hg_zero_out : ∀ᵐ x ∂volume, x ∉ Set.Icc (-a) (1 / 2) → g x = 0 := by
    have h1 := rnDeriv_ae_zero_of_measure_zero hac measurableSet_Icc.compl hμρ_supp
    filter_upwards [h1] with x hx hnot
    simp only [g, g_en, hx hnot, ENNReal.toReal_zero]
  -- checkMeasure (μ ∗ ρ) = volume.withDensity (fun x => g_en (-x))
  have hcheck_wd : checkMeasure (μ ∗ ρ) = volume.withDensity (fun x => g_en (-x)) := by
    ext s hs
    rw [checkMeasure, Measure.map_apply measurable_neg hs,
        ← Measure.withDensity_rnDeriv_eq (μ ∗ ρ) volume hac,
        withDensity_apply _ (hs.preimage measurable_neg), withDensity_apply _ hs]
    have hneg_map : Measure.map (fun x : ℝ => -x) volume = volume := by
      have : (fun x : ℝ => -x) = ((-1 : ℝ) * ·) := by ext x; ring
      rw [this, Real.map_volume_mul_left (by norm_num : (-1 : ℝ) ≠ 0)]; simp
    calc
      ∫⁻ x in (fun x : ℝ => -x) ⁻¹' s, g_en x ∂volume
          = ∫⁻ x, ((fun x : ℝ => -x) ⁻¹' s).indicator g_en x ∂volume := (lintegral_indicator (hs.preimage measurable_neg) _).symm
      _ = ∫⁻ x, ((fun x : ℝ => -x) ⁻¹' s).indicator g_en x ∂(volume.map (fun x : ℝ => -x)) := by rw [hneg_map]
      _ = ∫⁻ x, ((fun x : ℝ => -x) ⁻¹' s).indicator g_en (-x) ∂volume := by
            rw [lintegral_map ((Measure.measurable_rnDeriv _ _).indicator (hs.preimage measurable_neg)) measurable_neg]
      _ = ∫⁻ x, s.indicator (fun y => g_en (-y)) x ∂volume := by
            congr 1; ext x
            by_cases hx : x ∈ s
            · have hx' : -x ∈ (fun y : ℝ => -y) ⁻¹' s := by simpa [Set.mem_preimage] using hx
              rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx]
            · have hx' : -x ∉ (fun y : ℝ => -y) ⁻¹' s := by simpa [Set.mem_preimage] using hx
              rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx]
      _ = ∫⁻ x in s, g_en (-x) ∂volume := lintegral_indicator hs _
  -- Deduce g x + g (-x) = 2 a.e. on [-1/2, 1/2]
  have hg_symm_en : (fun x => g_en x + g_en (-x)) =ᵐ[volume]
      Set.indicator (Set.Icc (-(1 / 2)) (1 / 2)) (fun _ => (2 : ℝ≥0∞)) := by
    have hwd1 : volume.withDensity (fun x => g_en x + g_en (-x)) =
        volume.withDensity (Set.indicator (Set.Icc (-(1 / 2)) (1 / 2)) (fun _ => (2 : ℝ≥0∞))) := by
      ext s hs
      rw [withDensity_apply _ hs, withDensity_apply _ hs,
          lintegral_add_left (Measure.measurable_rnDeriv _ _)]
      have h1 : ∫⁻ x in s, g_en x ∂volume = (μ ∗ ρ) s := by
        rw [← withDensity_apply _ hs, Measure.withDensity_rnDeriv_eq (μ ∗ ρ) volume hac]
      have h2 : ∫⁻ x in s, g_en (-x) ∂volume = checkMeasure (μ ∗ ρ) s := by
        rw [hcheck_wd, withDensity_apply _ hs]
      rw [h1, h2]
      have h3 : (μ ∗ ρ) s + checkMeasure (μ ∗ ρ) s = (2 : ℝ≥0∞) * lebHalf s := by
        have := congrArg (fun m : Measure ℝ => m s) hconv_sum
        simpa [Measure.add_apply, Measure.smul_apply] using this
      rw [h3, lebHalf, Measure.restrict_apply hs, lintegral_indicator measurableSet_Icc,
          Measure.restrict_restrict measurableSet_Icc, setLIntegral_const, Set.inter_comm]
    have hm1 : Measurable (fun x => g_en x + g_en (-x)) :=
      (Measure.measurable_rnDeriv _ _).add ((Measure.measurable_rnDeriv _ _).comp measurable_neg)
    have hm2 : Measurable (Set.indicator (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) (fun _ => (2 : ℝ≥0∞))) :=
      measurable_const.indicator measurableSet_Icc
    have hr1 := Measure.rnDeriv_withDensity volume hm1
    have hr2 := Measure.rnDeriv_withDensity volume hm2
    rw [hwd1] at hr1
    exact hr1.symm.trans hr2
  have hg_symm : ∀ᵐ x ∂volume, x ∈ Set.Icc (-(1 / 2)) (1 / 2) → g x + g (-x) = 2 := by
    have hg_le2_neg : ∀ᵐ x ∂volume, g_en (-x) ≤ 2 := by
      have hneg_map : Measure.map (fun x : ℝ => -x) volume = volume := by
        have : (fun x : ℝ => -x) = ((-1 : ℝ) * ·) := by ext x; ring
        rw [this, Real.map_volume_mul_left (by norm_num : (-1 : ℝ) ≠ 0)]; simp
      have h1 : ∀ᵐ x ∂(volume.map (fun x : ℝ => -x)), g_en x ≤ 2 := by rw [hneg_map]; exact hg_le2_en
      exact ae_of_ae_map measurable_neg.aemeasurable h1
    filter_upwards [hg_symm_en, hg_le2_en, hg_le2_neg] with x hsym h1 h2 hx
    rw [Set.indicator_of_mem hx] at hsym
    have hlt1 : g_en x ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) h1
    have hlt2 : g_en (-x) ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) h2
    have hto := congrArg ENNReal.toReal hsym
    rw [ENNReal.toReal_add hlt1 hlt2] at hto
    simpa [g] using hto
  have hg_neg_zero_gt_a : ∀ᵐ x ∂volume, x ∈ Set.Ioo a (1 / 2) → g (-x) = 0 := by
    have hneg_map : Measure.map (fun x : ℝ => -x) volume = volume := by
      have : (fun x : ℝ => -x) = ((-1 : ℝ) * ·) := by ext x; ring
      rw [this, Real.map_volume_mul_left (by norm_num : (-1 : ℝ) ≠ 0)]; simp
    have h1 : ∀ᵐ x ∂(volume.map (fun x : ℝ => -x)), x ∉ Set.Icc (-a) (1 / 2) → g x = 0 := by
      rw [hneg_map]; exact hg_zero_out
    filter_upwards [ae_of_ae_map measurable_neg.aemeasurable h1] with x hx hxI
    apply hx
    intro hmem; linarith [hmem.1, hxI.1]
  have hg_eq2_on : ∀ᵐ x ∂volume, x ∈ Set.Ioo a (1 / 2) → g x = 2 := by
    filter_upwards [hg_symm, hg_neg_zero_gt_a] with x h1 h2 hx
    have hmem : x ∈ Set.Icc (-(1 / 2)) (1 / 2) := ⟨by linarith [hx.1], le_of_lt hx.2⟩
    have := h1 hmem
    rw [h2 hx, add_zero] at this
    exact this
  -- Integrability of g * exp(-2πi ξ x) and g(-x) * exp(±2πi ξ x) on bounded intervals
  have hg_int_on : ∀ s : Set ℝ, volume s < ⊤ → IntegrableOn g s volume := fun s hs =>
    (integrableOn_const (C := (2 : ℝ)) (hs := hs.ne)).mono'
      hg_meas.aestronglyMeasurable (ae_restrict_of_ae (by
        filter_upwards [hg_le2] with x hx; rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn x)]; exact hx))
  -- Exact Fourier formula (eqpf1.3) for EVERY ξ : ℝ
  have hft_formula : ∀ ξ : ℝ,
      ft (μ ∗ ρ) ξ = ft (lebScaled (1 / 2)) ξ +
        (2 * Complex.I) * Complex.ofReal (∫ x in Set.Icc (0 : ℝ) a, g (-x) * Real.sin (2 * Real.pi * ξ * x)) := by
    intro ξ
    have h1 : ft (μ ∗ ρ) ξ = ∫ x, g x • Complex.exp (-2 * Real.pi * ξ * x * Complex.I) ∂volume := by
      rw [ft_apply, ← integral_rnDeriv_smul hac]
    rw [h1]
    set F : ℝ → ℂ := fun x => Complex.exp (-2 * Real.pi * ξ * x * Complex.I)
    have hF_norm : ∀ x, ‖F x‖ = 1 := fun x => by
      have : (-2 * Real.pi * ξ * x * Complex.I : ℂ) = ((-2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      simp only [F, this, Complex.norm_exp_ofReal_mul_I]
    have hF_meas : Measurable F := by fun_prop
    have hgF_int : Integrable (fun x => g x • F x) volume := by
      rw [integrable_rnDeriv_smul_iff hac]
      exact (integrable_const (1 : ℝ)).mono' hF_meas.aestronglyMeasurable (ae_of_all _ fun x => by rw [hF_norm])
    -- Restrict full integral to [-a, 1/2] = [-a, 0] ∪ (0, a] ∪ (a, 1/2]
    have hfull_eq : ∫ x, g x • F x ∂volume = ∫ x in Set.Icc (-a) (1 / 2), g x • F x ∂volume := by
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards [hg_zero_out] with x hx
      by_cases hmem : x ∈ Set.Icc (-a) (1 / 2)
      · rw [Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hmem, hx hmem, zero_smul]
    rw [hfull_eq]
    have hsplit1 : Set.Icc (-a) (1 / 2) = Set.Icc (-a) 0 ∪ Set.Ioc 0 (1 / 2) := by
      ext x; simp only [Set.mem_Icc, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro ⟨h1, h2⟩
        by_cases hx : x ≤ 0
        · left; exact ⟨h1, hx⟩
        · right; exact ⟨by linarith, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨by linarith, by linarith⟩
    have hsplit2 : Set.Ioc (0 : ℝ) (1 / 2) = Set.Ioc 0 a ∪ Set.Ioc a (1 / 2) := by
      ext x; simp only [Set.mem_Ioc, Set.mem_union]
      constructor
      · intro ⟨h1, h2⟩
        by_cases hx : x ≤ a
        · left; exact ⟨h1, hx⟩
        · right; exact ⟨by linarith, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨by linarith, by linarith⟩
    rw [hsplit1, setIntegral_union (by rw [Set.disjoint_left]; intro x h1 h2; linarith [h1.2, h2.1])
        measurableSet_Ioc hgF_int.integrableOn hgF_int.integrableOn]
    rw [hsplit2, setIntegral_union (by rw [Set.disjoint_left]; intro x h1 h2; linarith [h1.2, h2.1])
        measurableSet_Ioc hgF_int.integrableOn hgF_int.integrableOn]
    -- Piece 1: ∫_{[-a, 0]} g(x) F(x) = ∫_{[0, a]} g(-x) F(-x)
    have hp1 : ∫ x in Set.Icc (-a) 0, g x • F x ∂volume =
        ∫ x in Set.Icc 0 a, g (-x) • F (-x) ∂volume := by
      rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc]
      have hneg_int := integral_comp_neg_vol (fun x => (Set.Icc (-a) 0).indicator (fun y => g y • F y) x)
      rw [← hneg_int]
      congr 1; ext x
      by_cases hx : x ∈ Set.Icc (0 : ℝ) a
      · have hnx : -x ∈ Set.Icc (-a) 0 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
        rw [Set.indicator_of_mem hnx, Set.indicator_of_mem hx]
      · have hnx : -x ∉ Set.Icc (-a) 0 := fun h => hx ⟨by linarith [h.2], by linarith [h.1]⟩
        rw [Set.indicator_of_notMem hnx, Set.indicator_of_notMem hx]
    -- Piece 2: ∫_{(0, a]} g(x) F(x) = ∫_{[0, a]} (2 - g(-x)) F(x)
    have hp2 : ∫ x in Set.Ioc 0 a, g x • F x ∂volume =
        ∫ x in Set.Icc 0 a, ((2 : ℝ) • F x - g (-x) • F x) ∂volume := by
      rw [← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_ae measurableSet_Icc
      filter_upwards [hg_symm] with x hsym hx
      have hmem : x ∈ Set.Icc (-(1 / 2)) (1 / 2) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hgx : g x = 2 - g (-x) := by linarith [hsym hmem]
      rw [hgx, sub_smul]
    -- Piece 3: ∫_{(a, 1/2]} g(x) F(x) = ∫_{(a, 1/2]} 2 F(x)
    have hp3 : ∫ x in Set.Ioc a (1 / 2), g x • F x ∂volume =
        ∫ x in Set.Ioc a (1 / 2), (2 : ℝ) • F x ∂volume := by
      rw [← setIntegral_congr_set Ioo_ae_eq_Ioc, ← setIntegral_congr_set Ioo_ae_eq_Ioc]
      apply setIntegral_congr_ae measurableSet_Ioo
      filter_upwards [hg_eq2_on] with x h2 hx
      rw [h2 hx]
    rw [hp1, hp2, hp3]
    have hint_2F_0a : IntegrableOn (fun x => (2 : ℝ) • F x) (Set.Icc 0 a) volume :=
      (integrableOn_const (C := (2 : ℝ)) (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).mono'
        (by fun_prop) (ae_of_all _ fun x => by rw [norm_smul, hF_norm, mul_one, Real.norm_ofNat])
    have hint_2F_a : IntegrableOn (fun x => (2 : ℝ) • F x) (Set.Ioc a (1 / 2)) volume :=
      (integrableOn_const (C := (2 : ℝ)) (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).mono'
        (by fun_prop) (ae_of_all _ fun x => by rw [norm_smul, hF_norm, mul_one, Real.norm_ofNat])
    have hint_gnF : IntegrableOn (fun x => g (-x) • F x) (Set.Icc 0 a) volume := by
      have hg_neg_le2 : ∀ᵐ x ∂volume, g (-x) ≤ 2 := by
        have hneg_map : Measure.map (fun x : ℝ => -x) volume = volume := by
          have : (fun x : ℝ => -x) = ((-1 : ℝ) * ·) := by ext x; ring
          rw [this, Real.map_volume_mul_left (by norm_num : (-1 : ℝ) ≠ 0)]; simp
        have h1 : ∀ᵐ x ∂(volume.map (fun x : ℝ => -x)), g x ≤ 2 := by rw [hneg_map]; exact hg_le2
        exact ae_of_ae_map measurable_neg.aemeasurable h1
      exact (integrableOn_const (C := (2 : ℝ)) (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).mono'
        ((hg_meas.comp measurable_neg).smul hF_meas).aestronglyMeasurable
        (ae_restrict_of_ae (by filter_upwards [hg_neg_le2] with x hx; rw [norm_smul, hF_norm, mul_one, Real.norm_eq_abs, abs_of_nonneg (hg_nn _)]; exact hx))
    have hint_gnFn : IntegrableOn (fun x => g (-x) • F (-x)) (Set.Icc 0 a) volume := by
      have hg_neg_le2 : ∀ᵐ x ∂volume, g (-x) ≤ 2 := by
        have hneg_map : Measure.map (fun x : ℝ => -x) volume = volume := by
          have : (fun x : ℝ => -x) = ((-1 : ℝ) * ·) := by ext x; ring
          rw [this, Real.map_volume_mul_left (by norm_num : (-1 : ℝ) ≠ 0)]; simp
        have h1 : ∀ᵐ x ∂(volume.map (fun x : ℝ => -x)), g x ≤ 2 := by rw [hneg_map]; exact hg_le2
        exact ae_of_ae_map measurable_neg.aemeasurable h1
      exact (integrableOn_const (C := (2 : ℝ)) (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).mono'
        ((hg_meas.comp measurable_neg).smul (hF_meas.comp measurable_neg)).aestronglyMeasurable
        (ae_restrict_of_ae (by filter_upwards [hg_neg_le2] with x hx; rw [norm_smul, hF_norm, mul_one, Real.norm_eq_abs, abs_of_nonneg (hg_nn _)]; exact hx))
    rw [integral_sub hint_2F_0a hint_gnF]
    -- Combine ∫_{[0, a]} 2 F + ∫_{(a, 1/2]} 2 F = ∫_{[0, 1/2]} 2 F = ft (lebScaled (1/2)) ξ
    have hleb_part : (∫ x in Set.Icc 0 a, (2 : ℝ) • F x ∂volume) +
        (∫ x in Set.Ioc a (1 / 2), (2 : ℝ) • F x ∂volume) = ft (lebScaled (1 / 2)) ξ := by
      have hunion : Set.Icc (0 : ℝ) a ∪ Set.Ioc a (1 / 2) = Set.Icc 0 (1 / 2) := by
        ext x; simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ioc]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨by linarith, by linarith⟩
        · rintro ⟨h1, h2⟩
          by_cases hx : x ≤ a
          · left; exact ⟨h1, hx⟩
          · right; exact ⟨by linarith, h2⟩
      rw [← setIntegral_union (by rw [Set.disjoint_left]; intro x h1 h2; linarith [h1.2, h2.1])
          measurableSet_Ioc hint_2F_0a hint_2F_a, hunion]
      rw [ft_apply, lebScaled, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by norm_num)]
      have : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
      rw [this, integral_smul]
    -- Combine ∫_{[0, a]} g(-x) F(-x) - ∫_{[0, a]} g(-x) F(x) = 2i * ∫_{[0, a]} g(-x) sin(2πξx)
    have hsin_part : (∫ x in Set.Icc 0 a, g (-x) • F (-x) ∂volume) -
        (∫ x in Set.Icc 0 a, g (-x) • F x ∂volume) =
        (2 * Complex.I) * Complex.ofReal (∫ x in Set.Icc (0 : ℝ) a, g (-x) * Real.sin (2 * Real.pi * ξ * x)) := by
      have hco : Complex.ofReal (∫ x in Set.Icc (0 : ℝ) a, g (-x) * Real.sin (2 * Real.pi * ξ * x)) =
          ∫ x in Set.Icc (0 : ℝ) a, ((g (-x) * Real.sin (2 * Real.pi * ξ * x) : ℝ) : ℂ) := integral_ofReal.symm
      rw [← integral_sub hint_gnFn hint_gnF, hco, ← integral_const_mul]
      congr 1; ext x
      simp only [F, Complex.real_smul, Complex.ofReal_mul]
      have harg1 : (-2 * Real.pi * ξ * (-x : ℝ) * Complex.I : ℂ) = ((2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      have harg2 : (-2 * Real.pi * ξ * x * Complex.I : ℂ) = -(((2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I) := by
        push_cast; ring
      rw [harg1, harg2]
      have hsin_c : Complex.exp (((2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I) -
          Complex.exp (-(((2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I)) =
          2 * Complex.I * Complex.ofReal (Real.sin (2 * Real.pi * ξ * x)) := by
        have h1 := Complex.exp_mul_I ((2 * Real.pi * ξ * x : ℝ) : ℂ)
        have h2 := Complex.exp_mul_I (-(2 * Real.pi * ξ * x : ℝ) : ℂ)
        rw [Complex.ofReal_sin]
        have hneg : -(((2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I) = (-(2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [hneg, h1, h2]
        simp only [Complex.cos_neg, Complex.sin_neg]
        ring
      calc
        (g (-x) : ℂ) * Complex.exp (((2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I) -
            (g (-x) : ℂ) * Complex.exp (-(((2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I))
            = (g (-x) : ℂ) * (Complex.exp (((2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I) -
                Complex.exp (-(((2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I))) := by ring
        _ = (g (-x) : ℂ) * (2 * Complex.I * Complex.ofReal (Real.sin (2 * Real.pi * ξ * x))) := by rw [hsin_c]
        _ = 2 * Complex.I * ((g (-x) : ℂ) * Complex.ofReal (Real.sin (2 * Real.pi * ξ * x))) := by ring
    linear_combination hleb_part + hsin_part
  -- Substitute ξ = r (even): ft(μ∗ρ) r = 0 and ft(lebScaled (1/2)) r = 0, so ∫_0^a g(-x) sin(2πrx) = 0
  have hint_zero : ∫ x in Set.Icc (0 : ℝ) a, g (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x) = 0 := by
    have hr_eq := hft_formula (r : ℝ)
    have hlhs0 : ft (μ ∗ ρ) (r : ℝ) = 0 := by rw [ft_conv, hμr, zero_mul]
    have hleb0 : ft (lebScaled (1 / 2)) (r : ℝ) = 0 := by
      rw [ft_lebScaled (by norm_num)]
      have hrne : ((r : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      simp only [hrne, ↓reduceIte]
      rcases heven with ⟨m, rfl⟩
      have harg : (-2 * Real.pi * (((m + m : ℕ) : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ) * Complex.I) =
          ((-(m : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
      rw [harg, Complex.exp_int_mul_two_pi_mul_I, sub_self, zero_div]
    rw [hlhs0, hleb0, zero_add] at hr_eq
    have hmul0 : (2 * Complex.I : ℂ) * Complex.ofReal (∫ x in Set.Icc (0 : ℝ) a, g (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x)) = 0 :=
      hr_eq.symm
    have h2I : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
    exact Complex.ofReal_eq_zero.mp ((mul_eq_zero.mp hmul0).resolve_left h2I)
  -- Since sin(2πrx) > 0 on (0, a) (as a ≤ 1/(2r)), deduce g(-x) = 0 a.e. on [0, a]
  have hg_neg_zero_0a : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) a)), g (-x) = 0 := by
    have hIoo_zero : ∫ x in Set.Ioo (0 : ℝ) a, g (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x) = 0 := by
      rw [setIntegral_congr_set Ioo_ae_eq_Icc]; exact hint_zero
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) a)] fun x => g (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x) := by
      change ∀ᵐ x ∂volume.restrict (Set.Ioo (0 : ℝ) a), 0 ≤ g (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x)
      rw [ae_restrict_iff' measurableSet_Ioo]
      apply ae_of_all; intro x hx
      apply mul_nonneg (hg_nn _)
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · have := hx.1; positivity
      · have h1 : 2 * (r : ℝ) * a ≤ 1 := by
          have hrpos : (0 : ℝ) < 2 * (r : ℝ) := by positivity
          rw [le_div_iff₀ hrpos] at ha_le; linarith
        have h2 : 2 * (r : ℝ) * x ≤ 1 := by nlinarith [hx.2]
        nlinarith [Real.pi_pos]
    have hint_g : IntegrableOn (fun x => g (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x)) (Set.Ioo 0 a) volume := by
      have hg_neg_le2 : ∀ᵐ x ∂volume, g (-x) ≤ 2 := by
        have hneg_map : Measure.map (fun x : ℝ => -x) volume = volume := by
          have : (fun x : ℝ => -x) = ((-1 : ℝ) * ·) := by ext x; ring
          rw [this, Real.map_volume_mul_left (by norm_num : (-1 : ℝ) ≠ 0)]; simp
        have h1 : ∀ᵐ x ∂(volume.map (fun x : ℝ => -x)), g x ≤ 2 := by rw [hneg_map]; exact hg_le2
        exact ae_of_ae_map measurable_neg.aemeasurable h1
      exact (integrableOn_const (C := (2 : ℝ)) (hs := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).mono'
        ((hg_meas.comp measurable_neg).mul (by fun_prop)).aestronglyMeasurable
        (ae_restrict_of_ae (by
          filter_upwards [hg_neg_le2] with x hx
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg_nn _)]
          calc g (-x) * |Real.sin (2 * Real.pi * (r : ℝ) * x)| ≤ g (-x) * 1 :=
                mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (hg_nn _)
            _ ≤ 2 := by linarith))
    have hae0 : (fun x => g (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x)) =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) a)] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hnn hint_g).mp hIoo_zero
    have hae_g_Ioo : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0 : ℝ) a)), g (-x) = 0 := by
      change ∀ᵐ x ∂volume.restrict (Set.Ioo (0 : ℝ) a), g (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x) = 0 at hae0
      rw [ae_restrict_iff' measurableSet_Ioo] at hae0 ⊢
      filter_upwards [hae0] with x hx hxI
      have hsin_pos : 0 < Real.sin (2 * Real.pi * (r : ℝ) * x) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · have hrpos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
          have := hxI.1; positivity
        · have h1 : 2 * (r : ℝ) * a ≤ 1 := by
            have hrpos : (0 : ℝ) < 2 * (r : ℝ) := by positivity
            rw [le_div_iff₀ hrpos] at ha_le; linarith
          have hrpos : (0 : ℝ) < 2 * (r : ℝ) := by positivity
          have h2 : 2 * (r : ℝ) * x < 1 := by nlinarith [hxI.2]
          nlinarith [Real.pi_pos]
      exact (mul_eq_zero.mp (hx hxI)).resolve_right hsin_pos.ne'
    have hres_eq : volume.restrict (Set.Ioo (0 : ℝ) a) = volume.restrict (Set.Icc (0 : ℝ) a) :=
      Measure.restrict_congr_set Ioo_ae_eq_Icc
    rwa [← hres_eq]
  -- Plug g(-x) = 0 back into hft_formula to obtain μ ∗ ρ = lebScaled (1/2)
  have hconv_half : μ ∗ ρ = lebScaled (1 / 2) := by
    have := isProbabilityMeasure_lebScaled (by norm_num : (0 : ℝ) < 1 / 2)
    apply ext_of_ft
    intro ξ
    rw [hft_formula ξ]
    have h0 : ∫ x in Set.Icc (0 : ℝ) a, g (-x) * Real.sin (2 * Real.pi * ξ * x) = 0 := by
      calc ∫ x in Set.Icc (0 : ℝ) a, g (-x) * Real.sin (2 * Real.pi * ξ * x)
          = ∫ _x in Set.Icc (0 : ℝ) a, (0 : ℝ) := by
            apply integral_congr_ae
            filter_upwards [hg_neg_zero_0a] with x hx; rw [hx, zero_mul]
        _ = 0 := by simp
    rw [h0, Complex.ofReal_zero, mul_zero, add_zero]
  -- Deduce 2 ∣ k for every integer zero k of ft μ
  have hdvd2 : ∀ k : ℤ, ft μ k = 0 → (2 : ℤ) ∣ k := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0; exact dvd_zero 2
    · have hleb0 : ft (lebScaled (1 / 2)) (k : ℝ) = 0 := by
        rw [← hconv_half, ft_conv, hk, zero_mul]
      rw [ft_lebScaled (by norm_num)] at hleb0
      have hkr : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk0
      simp only [hkr, ↓reduceIte] at hleb0
      have hden : (-2 * Real.pi * (k : ℂ) * ((1 / 2 : ℝ) : ℂ) * Complex.I) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (Int.cast_ne_zero.mpr hk0)) (by norm_num))
          Complex.I_ne_zero
      have hexp1 : Complex.exp (-2 * Real.pi * (k : ℂ) * ((1 / 2 : ℝ) : ℂ) * Complex.I) = 1 :=
        sub_eq_zero.mp ((div_eq_zero_iff.mp hleb0).resolve_right hden)
      have hre := congrArg Complex.re hexp1
      have harg : (-2 * Real.pi * (k : ℂ) * ((1 / 2 : ℝ) : ℂ) * Complex.I) =
          ((-(Real.pi * (k : ℝ)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [harg, Complex.exp_ofReal_mul_I_re, Complex.one_re, Real.cos_neg, mul_comm] at hre
      -- cos(k * π) = 1 implies Even k!
      by_contra hndvd
      have hodd : k % 2 = 1 := by omega
      obtain ⟨m, rfl⟩ : ∃ m : ℤ, k = 2 * m + 1 := ⟨k / 2, by omega⟩
      have hcos_neg1 : Real.cos (((2 * m + 1 : ℤ) : ℝ) * Real.pi) = -1 := by
        have : (((2 * m + 1 : ℤ) : ℝ) * Real.pi) = Real.pi + (m : ℤ) * (2 * Real.pi) := by push_cast; ring
        rw [this, Real.cos_add_int_mul_two_pi, Real.cos_pi]
      linarith
  exact ⟨ρ, hρ_prob, hρ_supp, hconv_half, hdvd2⟩

/-- Odd case of `gabardo_lai_lem1`: splits `ν = ν₁ + ν₂` at `-a` and uses `g₁ = 1_{[0, 1/(2r)]}` a.e. -/
private lemma gabardo_lai_lem1_odd {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : ℝ} (ha0 : 0 < a) (ha_half : a < 1 / 2)
    (hconv : μ ∗ ν = lebHalf)
    (hμ_supp : IsSupportedIn μ (Set.Icc (-a) a))
    (hν_supp : IsSupportedIn ν (Set.Icc (-(1 / 2 - a)) (1 / 2 - a)))
    (_hcheck_μ : checkMeasure μ = μ)
    {r : ℕ} (hr2 : 2 ≤ r) (hodd : ¬ Even r)
    (ha_lo : 1 / (4 * (r : ℝ)) ≤ a) (ha_hi : a ≤ 1 / (2 * (r : ℝ)))
    (hμr : ft μ r = 0) :
    ∀ k : ℤ, ft μ k = 0 → (r : ℤ) ∣ k := by
  set b := 1 / 2 - a
  have hr_mod : r % 2 = 1 := by by_contra h0; exact hodd (Nat.even_iff.mpr (by omega))
  have hr3 : 3 ≤ r := by omega
  have hrpos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
  have ha_lt_b : a < b := by
    have : 1 / (2 * (r : ℝ)) ≤ 1 / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr3
      linarith
    simp only [b]; linarith
  let ν₁ : Measure ℝ := ν.restrict (Set.Icc (-a) b)
  let ν₂ : Measure ℝ := ν.restrict (Set.Ico (-b) (-a))
  have hν_split : ν₁ + ν₂ = ν := by
    ext s hs
    simp only [ν₁, ν₂, Measure.add_apply, Measure.restrict_apply hs]
    have hdisj : Disjoint (s ∩ Set.Icc (-a) b) (s ∩ Set.Ico (-b) (-a)) := by
      rw [Set.disjoint_left]; intro x h1 h2; linarith [h1.2.1, h2.2.2]
    have hunion : (s ∩ Set.Icc (-a) b) ∪ (s ∩ Set.Ico (-b) (-a)) = s ∩ Set.Icc (-b) b := by
      ext x; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ico]
      constructor
      · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;> exact ⟨h1, by linarith, by linarith⟩
      · rintro ⟨h1, h2, h3⟩
        by_cases hx : -a ≤ x
        · left; exact ⟨h1, hx, h3⟩
        · right; exact ⟨h1, h2, by linarith⟩
    rw [← measure_union hdisj (hs.inter measurableSet_Ico), hunion]
    have hsp := measure_inter_add_sdiff s (measurableSet_Icc : MeasurableSet (Set.Icc (-b) b)) (μ := ν)
    have hd : ν (s \ Set.Icc (-b) b) = 0 := measure_mono_null (fun _ hx => hx.2) hν_supp
    rw [hd, add_zero] at hsp; exact hsp
  have hconv_split : μ ∗ ν₁ + μ ∗ ν₂ = lebHalf := by
    rw [← Measure.conv_add, hν_split, hconv]
  have hle1 : μ ∗ ν₁ ≤ (1 : ℝ≥0∞) • volume := by
    intro s; rw [Measure.smul_apply, smul_eq_mul, one_mul]
    calc (μ ∗ ν₁) s ≤ (μ ∗ ν₁ + μ ∗ ν₂) s := by simp
      _ = lebHalf s := by rw [hconv_split]
      _ ≤ volume s := Measure.restrict_le_self s
  have hle2 : μ ∗ ν₂ ≤ (1 : ℝ≥0∞) • volume := by
    intro s; rw [Measure.smul_apply, smul_eq_mul, one_mul]
    calc (μ ∗ ν₂) s ≤ (μ ∗ ν₁ + μ ∗ ν₂) s := by simp
      _ = lebHalf s := by rw [hconv_split]
      _ ≤ volume s := Measure.restrict_le_self s
  have hac1 : μ ∗ ν₁ ≪ volume := Measure.AbsolutelyContinuous.mk fun s _ hs => by
    have h1 := hle1 s; rw [Measure.smul_apply, smul_eq_mul, hs, mul_zero] at h1
    exact nonpos_iff_eq_zero.mp h1
  have hac2 : μ ∗ ν₂ ≪ volume := Measure.AbsolutelyContinuous.mk fun s _ hs => by
    have h1 := hle2 s; rw [Measure.smul_apply, smul_eq_mul, hs, mul_zero] at h1
    exact nonpos_iff_eq_zero.mp h1
  set g₁_en := (μ ∗ ν₁).rnDeriv volume
  set g₂_en := (μ ∗ ν₂).rnDeriv volume
  set g₁ : ℝ → ℝ := fun x => (g₁_en x).toReal
  set g₂ : ℝ → ℝ := fun x => (g₂_en x).toReal
  have hg₁_meas : Measurable g₁ := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hg₁_nn : ∀ x, 0 ≤ g₁ x := fun _ => ENNReal.toReal_nonneg
  have hg₁_le1_en : ∀ᵐ x ∂volume, g₁_en x ≤ 1 := rnDeriv_le_const_ae (by norm_num) hle1
  have hg₂_le1_en : ∀ᵐ x ∂volume, g₂_en x ≤ 1 := rnDeriv_le_const_ae (by norm_num) hle2
  have hg₁_le1 : ∀ᵐ x ∂volume, g₁ x ≤ 1 := by
    filter_upwards [hg₁_le1_en] with x hx
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using hx)
  -- Supports: μ ∗ ν₁ in [-2a, 1/2], μ ∗ ν₂ in [-1/2, 0]
  have hν₁_supp : IsSupportedIn ν₁ (Set.Icc (-a) b) := by
    unfold IsSupportedIn ν₁; rw [Measure.restrict_apply measurableSet_Icc.compl, Set.compl_inter_self, measure_empty]
  have hν₂_supp : IsSupportedIn ν₂ (Set.Icc (-b) (-a)) := by
    unfold IsSupportedIn ν₂; rw [Measure.restrict_apply measurableSet_Icc.compl]
    have hsub : (Set.Icc (-b) (-a))ᶜ ∩ Set.Ico (-b) (-a) = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_Icc, Set.mem_Ico, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, h3⟩; exact h1 ⟨h2, le_of_lt h3⟩
    rw [hsub, measure_empty]
  have hμν₁_supp : IsSupportedIn (μ ∗ ν₁) (Set.Icc (-(2 * a)) (1 / 2)) := by
    have h1 := conv_supported_Icc hμ_supp hν₁_supp
    have heq1 : -a + -a = -(2 * a) := by ring
    have heq2 : a + b = 1 / 2 := by simp only [b]; ring
    rwa [heq1, heq2] at h1
  have hμν₂_supp : IsSupportedIn (μ ∗ ν₂) (Set.Icc (-(1 / 2)) 0) := by
    have h1 := conv_supported_Icc hμ_supp hν₂_supp
    have heq1 : -a + -b = -(1 / 2) := by simp only [b]; ring
    have heq2 : a + -a = 0 := by ring
    rwa [heq1, heq2] at h1
  have hg₁_zero_out : ∀ᵐ x ∂volume, x ∉ Set.Icc (-(2 * a)) (1 / 2) → g₁ x = 0 := by
    have h1 := rnDeriv_ae_zero_of_measure_zero hac1 measurableSet_Icc.compl hμν₁_supp
    filter_upwards [h1] with x hx hnot; simp only [g₁, g₁_en, hx hnot, ENNReal.toReal_zero]
  have hg₂_zero_out : ∀ᵐ x ∂volume, x ∉ Set.Icc (-(1 / 2)) 0 → g₂ x = 0 := by
    have h1 := rnDeriv_ae_zero_of_measure_zero hac2 measurableSet_Icc.compl hμν₂_supp
    filter_upwards [h1] with x hx hnot; simp only [g₂, g₂_en, hx hnot, ENNReal.toReal_zero]
  -- g₁ + g₂ = 1 a.e. on [-1/2, 1/2], hence g₁ = 1 a.e. on (0, 1/2]
  have hg_sum_en : (fun x => g₁_en x + g₂_en x) =ᵐ[volume]
      Set.indicator (Set.Icc (-(1 / 2)) (1 / 2)) (fun _ => (1 : ℝ≥0∞)) := by
    have hwd : volume.withDensity (fun x => g₁_en x + g₂_en x) =
        volume.withDensity (Set.indicator (Set.Icc (-(1 / 2)) (1 / 2)) (fun _ => (1 : ℝ≥0∞))) := by
      ext s hs
      rw [withDensity_apply _ hs, withDensity_apply _ hs,
          lintegral_add_left (Measure.measurable_rnDeriv _ _),
          ← withDensity_apply _ hs, ← withDensity_apply _ hs,
          Measure.withDensity_rnDeriv_eq _ _ hac1, Measure.withDensity_rnDeriv_eq _ _ hac2]
      have h1 : (μ ∗ ν₁) s + (μ ∗ ν₂) s = lebHalf s := by
        have := congrArg (fun m : Measure ℝ => m s) hconv_split
        simpa [Measure.add_apply] using this
      rw [h1, lebHalf, Measure.restrict_apply hs, lintegral_indicator measurableSet_Icc,
          Measure.restrict_restrict measurableSet_Icc, setLIntegral_const, one_mul, Set.inter_comm]
    have hm1 : Measurable (fun x => g₁_en x + g₂_en x) :=
      (Measure.measurable_rnDeriv (μ ∗ ν₁) volume).add (Measure.measurable_rnDeriv (μ ∗ ν₂) volume)
    have hr1 := Measure.rnDeriv_withDensity (volume : Measure ℝ) hm1
    have hm2 : Measurable (Set.indicator (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) (fun _ => (1 : ℝ≥0∞))) :=
      measurable_const.indicator measurableSet_Icc
    have hr2 := Measure.rnDeriv_withDensity (volume : Measure ℝ) hm2
    rw [hwd] at hr1
    exact hr1.symm.trans hr2
  have hg₁_eq1_on : ∀ᵐ x ∂volume, x ∈ Set.Ioc (0 : ℝ) (1 / 2) → g₁ x = 1 := by
    filter_upwards [hg_sum_en, hg₁_le1_en, hg₂_le1_en, hg₂_zero_out] with x hsum h1 h2 h2z hx
    have hmem : x ∈ Set.Icc (-(1 / 2)) (1 / 2) := ⟨by linarith [hx.1], hx.2⟩
    rw [Set.indicator_of_mem hmem] at hsum
    have hto := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_add (ne_top_of_le_ne_top (by norm_num) h1) (ne_top_of_le_ne_top (by norm_num) h2),
        ENNReal.toReal_one] at hto
    have hnot : x ∉ Set.Icc (-(1 / 2)) 0 := fun h => by linarith [hx.1, h.2]
    have hg20 : g₂ x = 0 := h2z hnot
    change g₁ x + g₂ x = 1 at hto
    linarith
  -- Fourier formula (eqpf1.5) for EVERY ξ : ℝ
  have hft_formula : ∀ ξ : ℝ,
      ft (μ ∗ ν₁) ξ = (∫ x in Set.Icc (0 : ℝ) (1 / 2), Complex.exp (-2 * Real.pi * ξ * x * Complex.I)) +
        ∫ x in Set.Icc (0 : ℝ) (2 * a), g₁ (-x) • Complex.exp (2 * Real.pi * ξ * x * Complex.I) := by
    intro ξ
    rw [ft_apply, ← integral_rnDeriv_smul hac1]
    set F : ℝ → ℂ := fun x => Complex.exp (-2 * Real.pi * ξ * x * Complex.I)
    have hF_norm : ∀ x, ‖F x‖ = 1 := fun x => by
      have : (-2 * Real.pi * ξ * x * Complex.I : ℂ) = ((-2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      simp only [F, this, Complex.norm_exp_ofReal_mul_I]
    have hF_meas : Measurable F := by fun_prop
    have hgF_int : Integrable (fun x => g₁ x • F x) volume := by
      rw [integrable_rnDeriv_smul_iff hac1]
      exact (integrable_const (1 : ℝ)).mono' hF_meas.aestronglyMeasurable (ae_of_all _ fun x => by rw [hF_norm])
    have hfull : ∫ x, g₁ x • F x ∂volume = ∫ x in Set.Icc (-(2 * a)) (1 / 2), g₁ x • F x ∂volume := by
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards [hg₁_zero_out] with x hx
      by_cases hmem : x ∈ Set.Icc (-(2 * a)) (1 / 2)
      · rw [Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hmem, hx hmem, zero_smul]
    rw [hfull]
    have hsplit : Set.Icc (-(2 * a)) (1 / 2) = Set.Icc (-(2 * a)) 0 ∪ Set.Ioc 0 (1 / 2) := by
      ext x; simp only [Set.mem_Icc, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro ⟨h1, h2⟩
        by_cases hx : x ≤ 0
        · left; exact ⟨h1, hx⟩
        · right; exact ⟨by linarith, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨by linarith, by linarith⟩
    rw [hsplit, setIntegral_union (by rw [Set.disjoint_left]; intro x h1 h2; linarith [h1.2, h2.1])
        measurableSet_Ioc hgF_int.integrableOn hgF_int.integrableOn, add_comm]
    congr 1
    · rw [integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_ae measurableSet_Ioc
      filter_upwards [hg₁_eq1_on] with x h1 hx
      rw [h1 hx, one_smul]
    · rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc]
      have hneg := integral_comp_neg_vol (fun x => (Set.Icc (-(2 * a)) 0).indicator (fun y => g₁ y • F y) x)
      rw [← hneg]
      congr 1; ext x
      by_cases hx : x ∈ Set.Icc (0 : ℝ) (2 * a)
      · have hnx : -x ∈ Set.Icc (-(2 * a)) 0 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
        rw [Set.indicator_of_mem hnx, Set.indicator_of_mem hx]
        simp only [F]; congr 2; push_cast; ring
      · have hnx : -x ∉ Set.Icc (-(2 * a)) 0 := fun h => hx ⟨by linarith [h.2], by linarith [h.1]⟩
        rw [Set.indicator_of_notMem hnx, Set.indicator_of_notMem hx]
  -- Helper: g₁(-x) ≤ 1 a.e.
  have hg₁_neg_le1 : ∀ᵐ x ∂volume, g₁ (-x) ≤ 1 := by
    have hneg_map : Measure.map (fun x : ℝ => -x) volume = volume := by
      have : (fun x : ℝ => -x) = ((-1 : ℝ) * ·) := by ext x; ring
      rw [this, Real.map_volume_mul_left (by norm_num : (-1 : ℝ) ≠ 0)]; simp
    have h1 : ∀ᵐ x ∂(volume.map (fun x : ℝ => -x)), g₁ x ≤ 1 := by rw [hneg_map]; exact hg₁_le1
    exact ae_of_ae_map measurable_neg.aemeasurable h1
  -- Evaluate imaginary part at ξ = r (odd): ∫_0^{2a} g₁(-x) sin(2πrx) dx = 1 / (π r)
  have hint_im_eq : ∫ x in Set.Icc (0 : ℝ) (2 * a), g₁ (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x) =
      1 / (Real.pi * (r : ℝ)) := by
    have hr_eq := hft_formula (r : ℝ)
    have hlhs0 : ft (μ ∗ ν₁) (r : ℝ) = 0 := by rw [ft_conv, hμr, zero_mul]
    rw [hlhs0] at hr_eq
    have him := congrArg Complex.im hr_eq
    rw [Complex.zero_im, Complex.add_im] at him
    have him1 : (∫ x in Set.Icc (0 : ℝ) (1 / 2), Complex.exp (-2 * Real.pi * (r : ℝ) * x * Complex.I)).im =
        -(1 / (Real.pi * (r : ℝ))) := by
      have hint_exp : IntegrableOn (fun x : ℝ => Complex.exp (-2 * Real.pi * (r : ℝ) * x * Complex.I))
          (Set.Icc 0 (1 / 2)) volume :=
        (integrableOn_const (C := (1 : ℝ)) (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).mono'
          (by fun_prop) (ae_of_all _ fun x => by
            have harg : (-2 * Real.pi * (r : ℝ) * x * Complex.I : ℂ) =
                ((-2 * Real.pi * (r : ℝ) * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
            rw [harg, Complex.norm_exp_ofReal_mul_I])
      rw [← Complex.imCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.imCLM hint_exp]
      have hfn : (fun x : ℝ => Complex.imCLM (Complex.exp (-2 * Real.pi * (r : ℝ) * x * Complex.I))) =
          fun x : ℝ => -Real.sin (2 * Real.pi * (r : ℝ) * x) := by
        ext x
        rw [Complex.imCLM_apply]
        have harg : (-2 * Real.pi * (r : ℝ) * x * Complex.I : ℂ) =
            ((-2 * Real.pi * (r : ℝ) * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [harg, Complex.exp_ofReal_mul_I_im,
            show -2 * Real.pi * (r : ℝ) * x = -(2 * Real.pi * (r : ℝ) * x) by ring, Real.sin_neg]
      rw [hfn, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
          intervalIntegral.integral_neg, integral_sin_two_pi_mul (r : ℝ) hrpos.ne' (1 / 2)]
      have hcos_odd : Real.cos (2 * Real.pi * (r : ℝ) * (1 / 2)) = -1 := by
        have : 2 * Real.pi * (r : ℝ) * (1 / 2) = Real.pi + ((r / 2 : ℕ) : ℤ) * (2 * Real.pi) := by
          have hr_eq2 : r = 2 * (r / 2) + 1 := by omega
          have hr_r : (r : ℝ) = 2 * ((r / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hr_eq2
          have hq : (((r / 2 : ℕ) : ℤ) : ℝ) = ((r / 2 : ℕ) : ℝ) := Int.cast_natCast (r / 2)
          rw [hr_r, hq]; ring
        rw [this, Real.cos_add_int_mul_two_pi, Real.cos_pi]
      rw [hcos_odd]; ring
    have him2 : (∫ x in Set.Icc (0 : ℝ) (2 * a), g₁ (-x) • Complex.exp (2 * Real.pi * (r : ℝ) * x * Complex.I)).im =
        ∫ x in Set.Icc (0 : ℝ) (2 * a), g₁ (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x) := by
      have hint_g1 : IntegrableOn (fun x : ℝ => g₁ (-x) • Complex.exp (2 * Real.pi * (r : ℝ) * x * Complex.I))
          (Set.Icc 0 (2 * a)) volume :=
        (integrableOn_const (C := (1 : ℝ)) (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).mono'
          ((hg₁_meas.comp measurable_neg).smul (by fun_prop)).aestronglyMeasurable
          (ae_restrict_of_ae (by
            filter_upwards [hg₁_neg_le1] with x hx
            have harg : (2 * Real.pi * (r : ℝ) * x * Complex.I : ℂ) =
                ((2 * Real.pi * (r : ℝ) * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
            rw [norm_smul, harg, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs, abs_of_nonneg (hg₁_nn _)]
            exact hx))
      rw [← Complex.imCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.imCLM hint_g1]
      congr 1; ext x
      rw [Complex.imCLM_apply, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      have harg : (2 * Real.pi * (r : ℝ) * x * Complex.I : ℂ) =
          ((2 * Real.pi * (r : ℝ) * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [harg, Complex.exp_ofReal_mul_I_im]
    rw [him1, him2] at him
    linarith
  -- Split [0, 2a] = [0, 1/(2r)] ∪ (1/(2r), 2a] using 1/(2r) ≤ 2a ≤ 1/r
  set c := 1 / (2 * (r : ℝ))
  have hc_pos : 0 < c := by simp only [c]; positivity
  have hc_le_2a : c ≤ 2 * a := by
    have : 2 * (1 / (4 * (r : ℝ))) = c := by simp only [c]; ring
    linarith
  have h2a_le_invr : 2 * a ≤ 1 / (r : ℝ) := by
    have : 2 * (1 / (2 * (r : ℝ))) = 1 / (r : ℝ) := by field_simp
    linarith
  have hint_g1_sin_2a : IntegrableOn (fun x => g₁ (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x)) (Set.Icc 0 (2 * a)) volume :=
    (integrableOn_const (C := (1 : ℝ)) (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).mono'
      ((hg₁_meas.comp measurable_neg).mul (by fun_prop)).aestronglyMeasurable
      (ae_restrict_of_ae (by
        filter_upwards [hg₁_neg_le1] with x hx
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg₁_nn _)]
        exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (hg₁_nn _)).trans (by linarith)))
  have hsplit_2a : Set.Icc (0 : ℝ) (2 * a) = Set.Icc 0 c ∪ Set.Ioc c (2 * a) := by
    ext x; simp only [Set.mem_Icc, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro ⟨h1, h2⟩
      by_cases hx : x ≤ c
      · left; exact ⟨h1, hx⟩
      · right; exact ⟨by linarith, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨by linarith, by linarith⟩
  have hsub1 : Set.Icc (0 : ℝ) c ⊆ Set.Icc 0 (2 * a) := fun _ hx => ⟨hx.1, le_trans hx.2 hc_le_2a⟩
  have hsub2 : Set.Ioc c (2 * a) ⊆ Set.Icc 0 (2 * a) := fun _ hx => ⟨by linarith [hx.1], hx.2⟩
  have hsum_split : (∫ x in Set.Icc (0 : ℝ) c, g₁ (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x)) +
      (∫ x in Set.Ioc c (2 * a), g₁ (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x)) = 1 / (Real.pi * (r : ℝ)) := by
    rw [← setIntegral_union (by rw [Set.disjoint_left]; intro x h1 h2; linarith [h1.2, h2.1])
        measurableSet_Ioc (hint_g1_sin_2a.mono_set hsub1) (hint_g1_sin_2a.mono_set hsub2),
        ← hsplit_2a, hint_im_eq]
  have hsin_int_c : ∫ x in Set.Icc (0 : ℝ) c, Real.sin (2 * Real.pi * (r : ℝ) * x) = 1 / (Real.pi * (r : ℝ)) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (le_of_lt hc_pos),
        integral_sin_two_pi_mul (r : ℝ) hrpos.ne' c]
    have harg : 2 * Real.pi * (r : ℝ) * c = Real.pi := by simp only [c]; field_simp
    rw [harg, Real.cos_pi]; ring
  have hpart1_le : ∫ x in Set.Icc (0 : ℝ) c, g₁ (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x) ≤
      1 / (Real.pi * (r : ℝ)) := by
    rw [← hsin_int_c]
    apply setIntegral_mono_ae_restrict (hint_g1_sin_2a.mono_set hsub1)
      ((by fun_prop : Continuous fun x => Real.sin (2 * Real.pi * (r : ℝ) * x)).integrableOn_Icc)
    change ∀ᵐ x ∂volume.restrict (Set.Icc (0 : ℝ) c), g₁ (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x) ≤ Real.sin (2 * Real.pi * (r : ℝ) * x)
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hg₁_neg_le1] with x hx hxI
    have hsin_nn : 0 ≤ Real.sin (2 * Real.pi * (r : ℝ) * x) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · have := hxI.1; positivity
      · have h1 : 2 * Real.pi * (r : ℝ) * c = Real.pi := by simp only [c]; field_simp
        nlinarith [hxI.2, Real.pi_pos]
    nlinarith
  have hpart2_le : ∫ x in Set.Ioc c (2 * a), g₁ (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x) ≤ 0 := by
    calc ∫ x in Set.Ioc c (2 * a), g₁ (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x)
        ≤ ∫ _x in Set.Ioc c (2 * a), (0 : ℝ) := by
          apply setIntegral_mono_ae_restrict (hint_g1_sin_2a.mono_set hsub2) integrableOn_zero
          change ∀ᵐ x ∂volume.restrict (Set.Ioc c (2 * a)), g₁ (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x) ≤ 0
          rw [ae_restrict_iff' measurableSet_Ioc]
          apply ae_of_all; intro x hxI
          have hsin_np : Real.sin (2 * Real.pi * (r : ℝ) * x) ≤ 0 := by
            have harg1 : Real.pi ≤ 2 * Real.pi * (r : ℝ) * x := by
              have h1 : 2 * Real.pi * (r : ℝ) * c = Real.pi := by simp only [c]; field_simp
              nlinarith [hxI.1, Real.pi_pos]
            have harg2 : 2 * Real.pi * (r : ℝ) * x ≤ 2 * Real.pi := by
              have h1 : 2 * Real.pi * (r : ℝ) * (1 / (r : ℝ)) = 2 * Real.pi := by field_simp
              nlinarith [hxI.2, h2a_le_invr, Real.pi_pos]
            have hsin_sub : Real.sin (2 * Real.pi * (r : ℝ) * x) = -Real.sin (2 * Real.pi * (r : ℝ) * x - Real.pi) := by
              rw [Real.sin_sub_pi]; ring
            rw [hsin_sub]
            linarith [Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : 0 ≤ 2 * Real.pi * (r : ℝ) * x - Real.pi)
              (by linarith : 2 * Real.pi * (r : ℝ) * x - Real.pi ≤ Real.pi)]
          exact mul_nonpos_of_nonneg_of_nonpos (hg₁_nn _) hsin_np
      _ = 0 := by simp
  -- Deduce g₁(-x) = 1 a.e. on [0, c] and g₁(-x) = 0 a.e. on (c, 2a]
  have hg₁_eq1_0c : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) c)), g₁ (-x) = 1 := by
    have hdiff0 : ∫ x in Set.Ioo (0 : ℝ) c, (1 - g₁ (-x)) * Real.sin (2 * Real.pi * (r : ℝ) * x) = 0 := by
      rw [setIntegral_congr_set Ioo_ae_eq_Icc]
      have hsub_fn : (fun x => (1 - g₁ (-x)) * Real.sin (2 * Real.pi * (r : ℝ) * x)) =
          fun x => Real.sin (2 * Real.pi * (r : ℝ) * x) - g₁ (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x) := by
        ext x; ring
      rw [hsub_fn, integral_sub ((by fun_prop : Continuous fun x => Real.sin (2 * Real.pi * (r : ℝ) * x)).integrableOn_Icc)
          (hint_g1_sin_2a.mono_set hsub1), hsin_int_c]
      linarith
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) c)] fun x => (1 - g₁ (-x)) * Real.sin (2 * Real.pi * (r : ℝ) * x) := by
      change ∀ᵐ x ∂volume.restrict (Set.Ioo (0 : ℝ) c), 0 ≤ (1 - g₁ (-x)) * Real.sin (2 * Real.pi * (r : ℝ) * x)
      rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hg₁_neg_le1] with x hx hxI
      have hsin_nn : 0 ≤ Real.sin (2 * Real.pi * (r : ℝ) * x) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi (by have := hxI.1; positivity)
        have h1 : 2 * Real.pi * (r : ℝ) * c = Real.pi := by simp only [c]; field_simp
        nlinarith [hxI.2, Real.pi_pos]
      exact mul_nonneg (by linarith) hsin_nn
    have hint_diff : IntegrableOn (fun x => (1 - g₁ (-x)) * Real.sin (2 * Real.pi * (r : ℝ) * x)) (Set.Ioo 0 c) volume := by
      have hsub_fn : (fun x => (1 - g₁ (-x)) * Real.sin (2 * Real.pi * (r : ℝ) * x)) =
          fun x => Real.sin (2 * Real.pi * (r : ℝ) * x) - g₁ (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x) := by ext x; ring
      rw [hsub_fn]
      exact ((by fun_prop : Continuous fun x => Real.sin (2 * Real.pi * (r : ℝ) * x)).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self).sub
        (hint_g1_sin_2a.mono_set (Set.Ioo_subset_Icc_self.trans hsub1))
    have hae0 := (integral_eq_zero_iff_of_nonneg_ae hnn hint_diff).mp hdiff0
    have hae_Ioo : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0 : ℝ) c)), g₁ (-x) = 1 := by
      change ∀ᵐ x ∂volume.restrict (Set.Ioo (0 : ℝ) c), (1 - g₁ (-x)) * Real.sin (2 * Real.pi * (r : ℝ) * x) = 0 at hae0
      rw [ae_restrict_iff' measurableSet_Ioo] at hae0 ⊢
      filter_upwards [hae0] with x hx hxI
      have hsin_pos : 0 < Real.sin (2 * Real.pi * (r : ℝ) * x) := by
        apply Real.sin_pos_of_pos_of_lt_pi (by have := hxI.1; positivity)
        have h1 : 2 * Real.pi * (r : ℝ) * c = Real.pi := by simp only [c]; field_simp
        have h2pr : 0 < 2 * Real.pi * (r : ℝ) := by positivity
        nlinarith [hxI.2]
      have h1 := (mul_eq_zero.mp (hx hxI)).resolve_right hsin_pos.ne'
      linarith
    rwa [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  have hg₁_eq0_c2a : ∀ᵐ x ∂(volume.restrict (Set.Ioc c (2 * a))), g₁ (-x) = 0 := by
    have h0 : ∫ x in Set.Ioo c (2 * a), g₁ (-x) * (-Real.sin (2 * Real.pi * (r : ℝ) * x)) = 0 := by
      rw [setIntegral_congr_set Ioo_ae_eq_Ioc]
      have hneg_fn : (fun x => g₁ (-x) * (-Real.sin (2 * Real.pi * (r : ℝ) * x))) =
          fun x => -(g₁ (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x)) := by ext x; ring
      rw [hneg_fn, integral_neg]
      linarith
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo c (2 * a))] fun x => g₁ (-x) * (-Real.sin (2 * Real.pi * (r : ℝ) * x)) := by
      change ∀ᵐ x ∂volume.restrict (Set.Ioo c (2 * a)), 0 ≤ g₁ (-x) * (-Real.sin (2 * Real.pi * (r : ℝ) * x))
      rw [ae_restrict_iff' measurableSet_Ioo]
      apply ae_of_all; intro x hxI
      have hsin_np : Real.sin (2 * Real.pi * (r : ℝ) * x) ≤ 0 := by
        have h1 : 2 * Real.pi * (r : ℝ) * c = Real.pi := by simp only [c]; field_simp
        have h2 : 2 * Real.pi * (r : ℝ) * (1 / (r : ℝ)) = 2 * Real.pi := by field_simp
        have harg1 : Real.pi ≤ 2 * Real.pi * (r : ℝ) * x := by nlinarith [hxI.1, Real.pi_pos]
        have harg2 : 2 * Real.pi * (r : ℝ) * x ≤ 2 * Real.pi := by nlinarith [hxI.2, h2a_le_invr, Real.pi_pos]
        rw [show Real.sin (2 * Real.pi * (r : ℝ) * x) = -Real.sin (2 * Real.pi * (r : ℝ) * x - Real.pi) by rw [Real.sin_sub_pi]; ring]
        have hnn_sin := Real.sin_nonneg_of_nonneg_of_le_pi
          (by linarith : 0 ≤ 2 * Real.pi * (r : ℝ) * x - Real.pi)
          (by linarith : 2 * Real.pi * (r : ℝ) * x - Real.pi ≤ Real.pi)
        linarith
      exact mul_nonneg (hg₁_nn _) (by linarith)
    have hint_neg : IntegrableOn (fun x => g₁ (-x) * (-Real.sin (2 * Real.pi * (r : ℝ) * x))) (Set.Ioo c (2 * a)) volume := by
      have hneg_fn : (fun x => g₁ (-x) * (-Real.sin (2 * Real.pi * (r : ℝ) * x))) =
          fun x => -(g₁ (-x) * Real.sin (2 * Real.pi * (r : ℝ) * x)) := by ext x; ring
      rw [hneg_fn]
      exact (hint_g1_sin_2a.mono_set (Set.Ioo_subset_Ioc_self.trans hsub2)).neg
    have hae0 := (integral_eq_zero_iff_of_nonneg_ae hnn hint_neg).mp h0
    have hae_Ioo : ∀ᵐ x ∂(volume.restrict (Set.Ioo c (2 * a))), g₁ (-x) = 0 := by
      change ∀ᵐ x ∂volume.restrict (Set.Ioo c (2 * a)), g₁ (-x) * (-Real.sin (2 * Real.pi * (r : ℝ) * x)) = 0 at hae0
      rw [ae_restrict_iff' measurableSet_Ioo] at hae0 ⊢
      filter_upwards [hae0] with x hx hxI
      have hsin_neg : 0 < -Real.sin (2 * Real.pi * (r : ℝ) * x) := by
        have h1 : 2 * Real.pi * (r : ℝ) * c = Real.pi := by simp only [c]; field_simp
        have h2 : 2 * Real.pi * (r : ℝ) * (1 / (r : ℝ)) = 2 * Real.pi := by field_simp
        have h2pr : 0 < 2 * Real.pi * (r : ℝ) := by positivity
        have harg1 : Real.pi < 2 * Real.pi * (r : ℝ) * x := by nlinarith [hxI.1]
        have harg2 : 2 * Real.pi * (r : ℝ) * x < 2 * Real.pi := by nlinarith [hxI.2, h2a_le_invr]
        rw [show -Real.sin (2 * Real.pi * (r : ℝ) * x) = Real.sin (2 * Real.pi * (r : ℝ) * x - Real.pi) by rw [Real.sin_sub_pi]]
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      exact (mul_eq_zero.mp (hx hxI)).resolve_right hsin_neg.ne'
    rwa [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  -- Now take real part of hft_formula at any integer k with ft μ k = 0!
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0; exact dvd_zero (r : ℤ)
  · have hkr : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk0
    have hkeq := hft_formula (k : ℝ)
    have hlhs0 : ft (μ ∗ ν₁) (k : ℝ) = 0 := by rw [ft_conv, hk, zero_mul]
    rw [hlhs0] at hkeq
    have hre := congrArg Complex.re hkeq
    rw [Complex.zero_re, Complex.add_re] at hre
    have hre1 : (∫ x in Set.Icc (0 : ℝ) (1 / 2), Complex.exp (-2 * Real.pi * (k : ℝ) * x * Complex.I)).re = 0 := by
      have hint_exp : IntegrableOn (fun x : ℝ => Complex.exp (-2 * Real.pi * (k : ℝ) * x * Complex.I))
          (Set.Icc 0 (1 / 2)) volume :=
        (integrableOn_const (C := (1 : ℝ)) (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).mono'
          (by fun_prop) (ae_of_all _ fun x => by
            have harg : (-2 * Real.pi * (k : ℝ) * x * Complex.I : ℂ) =
                ((-2 * Real.pi * (k : ℝ) * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
            rw [harg, Complex.norm_exp_ofReal_mul_I])
      rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.reCLM hint_exp]
      have hfn : (fun x : ℝ => Complex.reCLM (Complex.exp (-2 * Real.pi * (k : ℝ) * x * Complex.I))) =
          fun x : ℝ => Real.cos (2 * Real.pi * (k : ℝ) * x) := by
        ext x; rw [Complex.reCLM_apply]
        have harg : (-2 * Real.pi * (k : ℝ) * x * Complex.I : ℂ) =
            ((-2 * Real.pi * (k : ℝ) * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [harg, Complex.exp_ofReal_mul_I_re,
            show -2 * Real.pi * (k : ℝ) * x = -(2 * Real.pi * (k : ℝ) * x) by ring, Real.cos_neg]
      rw [hfn, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
          integral_cos_two_pi_mul (k : ℝ) hkr (1 / 2)]
      have hsin0 : Real.sin (2 * Real.pi * (k : ℝ) * (1 / 2)) = 0 := by
        rw [show 2 * Real.pi * (k : ℝ) * (1 / 2) = (k : ℝ) * Real.pi by ring]
        exact Real.sin_int_mul_pi k
      rw [hsin0, zero_div]
    have hre2 : (∫ x in Set.Icc (0 : ℝ) (2 * a), g₁ (-x) • Complex.exp (2 * Real.pi * (k : ℝ) * x * Complex.I)).re =
        Real.sin (Real.pi * (k : ℝ) / (r : ℝ)) / (2 * Real.pi * (k : ℝ)) := by
      have hint_g1k : IntegrableOn (fun x : ℝ => g₁ (-x) • Complex.exp (2 * Real.pi * (k : ℝ) * x * Complex.I))
          (Set.Icc 0 (2 * a)) volume :=
        (integrableOn_const (C := (1 : ℝ)) (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).mono'
          ((hg₁_meas.comp measurable_neg).smul (by fun_prop)).aestronglyMeasurable
          (ae_restrict_of_ae (by
            filter_upwards [hg₁_neg_le1] with x hx
            have harg : (2 * Real.pi * (k : ℝ) * x * Complex.I : ℂ) =
                ((2 * Real.pi * (k : ℝ) * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
            rw [norm_smul, harg, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs, abs_of_nonneg (hg₁_nn _)]
            exact hx))
      rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.reCLM hint_g1k]
      have hfn : (fun x : ℝ => Complex.reCLM (g₁ (-x) • Complex.exp (2 * Real.pi * (k : ℝ) * x * Complex.I))) =
          fun x : ℝ => g₁ (-x) * Real.cos (2 * Real.pi * (k : ℝ) * x) := by
        ext x; rw [Complex.reCLM_apply, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        have harg : (2 * Real.pi * (k : ℝ) * x * Complex.I : ℂ) =
            ((2 * Real.pi * (k : ℝ) * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [harg, Complex.exp_ofReal_mul_I_re]
      rw [hfn]
      have hint_cos : IntegrableOn (fun x => g₁ (-x) * Real.cos (2 * Real.pi * (k : ℝ) * x)) (Set.Icc 0 (2 * a)) volume :=
        (integrableOn_const (C := (1 : ℝ)) (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).mono'
          ((hg₁_meas.comp measurable_neg).mul (by fun_prop)).aestronglyMeasurable
          (ae_restrict_of_ae (by
            filter_upwards [hg₁_neg_le1] with x hx
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg₁_nn _)]
            exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (hg₁_nn _)).trans (by linarith)))
      rw [hsplit_2a, setIntegral_union (by rw [Set.disjoint_left]; intro x h1 h2; linarith [h1.2, h2.1])
          measurableSet_Ioc (hint_cos.mono_set hsub1) (hint_cos.mono_set hsub2)]
      have hp1 : ∫ x in Set.Icc (0 : ℝ) c, g₁ (-x) * Real.cos (2 * Real.pi * (k : ℝ) * x) =
          ∫ x in Set.Icc (0 : ℝ) c, Real.cos (2 * Real.pi * (k : ℝ) * x) := by
        apply integral_congr_ae; filter_upwards [hg₁_eq1_0c] with x hx; rw [hx, one_mul]
      have hp2 : ∫ x in Set.Ioc c (2 * a), g₁ (-x) * Real.cos (2 * Real.pi * (k : ℝ) * x) = 0 := by
        calc ∫ x in Set.Ioc c (2 * a), g₁ (-x) * Real.cos (2 * Real.pi * (k : ℝ) * x)
            = ∫ _x in Set.Ioc c (2 * a), (0 : ℝ) := by
              apply integral_congr_ae; filter_upwards [hg₁_eq0_c2a] with x hx; rw [hx, zero_mul]
          _ = 0 := by simp
      rw [hp1, hp2, add_zero, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (le_of_lt hc_pos), integral_cos_two_pi_mul (k : ℝ) hkr c]
      congr 2; simp only [c]; field_simp
    rw [hre1, hre2, zero_add] at hre
    have hsin0 : Real.sin (Real.pi * (k : ℝ) / (r : ℝ)) = 0 :=
      (div_eq_zero_iff.mp hre.symm).resolve_right (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hkr)
    rcases Real.sin_eq_zero_iff.mp hsin0 with ⟨m, hm⟩
    have hkr_eq : (k : ℝ) = (r : ℝ) * (m : ℝ) := by
      have h1 : Real.pi * (k : ℝ) = Real.pi * ((r : ℝ) * (m : ℝ)) := by
        have := congrArg (· * (r : ℝ)) hm
        rw [div_mul_cancel₀ _ hrpos.ne'] at this
        linarith
      exact mul_left_cancel₀ Real.pi_ne_zero h1
    have hkz : k = (r : ℤ) * m := by exact_mod_cast hkr_eq
    exact ⟨m, hkz⟩

/-- **Gabardo–Lai Lemma 2.3 (`lem1`):**
If `μ ∗ ν = lebHalf`, `sInf μ.support = -a`, `sSup μ.support = a` with `0 < a < 1/2`, and
`r ≥ 2` is the smallest positive integer with `ft μ r = 0`, then every integer zero of `ft μ`
is divisible by `r`. -/
theorem gabardo_lai_lem1 {r : ℕ} (hr2 : 2 ≤ r) :
    ∀ {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
      {a : ℝ}, 0 < a → a < 1 / 2 →
      μ ∗ ν = lebHalf →
      sInf μ.support = -a → sSup μ.support = a →
      ft μ r = 0 →
      (∀ m : ℕ, 1 ≤ m → m < r → ft μ m ≠ 0) →
      ∀ k : ℤ, ft μ k = 0 → (r : ℤ) ∣ k := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro μ ν _ _ a ha0 ha_half hconv hinf_μ hsup_μ hμr hr_min
    have h01 := gabardo_lai_lem01 (le_of_lt ha0) (le_of_lt ha_half) hconv hinf_μ hsup_μ
    have hlem0 := gabardo_lai_lem0 ha0 ha_half hconv hinf_μ hsup_μ (by omega) hμr hr_min
    rcases support_endpoints_of_conv_lebHalf hconv with ⟨hμ_bb, hμ_ba, hν_bb, hν_ba, _, _⟩
    have hμ_supp : IsSupportedIn μ (Set.Icc (-a) a) := by
      have hsub : μ.support ⊆ Set.Icc (-a) a := fun x hx =>
        ⟨hinf_μ ▸ csInf_le hμ_bb hx, hsup_μ ▸ le_csSup hμ_ba hx⟩
      exact measure_mono_null (Set.compl_subset_compl.mpr hsub) Measure.measure_compl_support
    have hν_supp : IsSupportedIn ν (Set.Icc (-(1 / 2 - a)) (1 / 2 - a)) := by
      have hsub : ν.support ⊆ Set.Icc (-(1 / 2 - a)) (1 / 2 - a) := fun y hy =>
        ⟨h01.2.1 ▸ csInf_le hν_bb hy, h01.2.2.1 ▸ le_csSup hν_ba hy⟩
      exact measure_mono_null (Set.compl_subset_compl.mpr hsub) Measure.measure_compl_support
    by_cases heven : Even r
    · obtain ⟨ρ, hρ_prob, _, hconv_half, hdvd2⟩ :=
        gabardo_lai_lem1_even_step ha0 ha_half hconv hμ_supp hν_supp h01.2.2.2.1 h01.2.2.2.2
          hr2 heven hlem0.2 hμr
      rcases heven with ⟨m, rfl⟩
      by_cases hm1 : m = 1
      · subst hm1; exact hdvd2
      · have hm2 : 2 ≤ m := by omega
        have hm_lt : m < m + m := by omega
        -- Rescale μ₁ = μ.map (2 * ·) and ν₁ = (ρ.map (2 * ·)).map (· - 1/2)
        let μ₁ : Measure ℝ := μ.map ((2 : ℝ) * ·)
        let ν₁ : Measure ℝ := (ρ.map ((2 : ℝ) * ·)).map (· + -(1 / 2 : ℝ))
        have hμ₁_prob : IsProbabilityMeasure μ₁ := isProbabilityMeasure_map_measurable (measurable_const_mul 2)
        have hρ2_prob : IsProbabilityMeasure (ρ.map ((2 : ℝ) * ·)) := isProbabilityMeasure_map_measurable (measurable_const_mul 2)
        have hν₁_prob : IsProbabilityMeasure ν₁ := isProbabilityMeasure_map_measurable (measurable_add_const _)
        have hconv₁ : μ₁ ∗ ν₁ = lebHalf := by
          have h1 : μ₁ ∗ ρ.map ((2 : ℝ) * ·) = leb01 := by
            rw [← map_conv_mul_left, hconv_half, lebScaled_map_mul (by norm_num) (by norm_num)]
            have : (2 : ℝ) * (1 / 2) = 1 := by norm_num
            rw [this, lebScaled_one]
          have h2 : μ₁.map (· + (0 : ℝ)) ∗ (ρ.map ((2 : ℝ) * ·)).map (· + -(1 / 2 : ℝ)) =
              (μ₁ ∗ ρ.map ((2 : ℝ) * ·)).map (· + (0 + -(1 / 2 : ℝ))) :=
            (map_conv_add_const μ₁ (ρ.map ((2 : ℝ) * ·)) 0 (-(1 / 2))).symm
          have hid : μ₁.map (· + (0 : ℝ)) = μ₁ := by simp
          rw [hid, h1, zero_add] at h2
          rw [h2]
          have hsub : (fun x : ℝ => x + -(1 / 2 : ℝ)) = (fun x : ℝ => x - 1 / 2) := by ext x; ring
          rw [hsub, leb01_map_sub_half]
        have hμne : μ.support.Nonempty := Measure.nonempty_support (IsProbabilityMeasure.ne_zero μ)
        have hinf₁ : sInf μ₁.support = -(2 * a) := by
          rw [map_mul_pos_support μ (by norm_num), sInf_image_mul_pos hμne hμ_bb (by norm_num), hinf_μ]; ring
        have hsup₁ : sSup μ₁.support = 2 * a := by
          rw [map_mul_pos_support μ (by norm_num), sSup_image_mul_pos hμne hμ_ba (by norm_num), hsup_μ]
        have h2a_lt : 2 * a < 1 / 2 := by
          have hm_r : (4 : ℝ) ≤ ((m + m : ℕ) : ℝ) := by exact_mod_cast (show 4 ≤ m + m by omega)
          have h1 : 1 / (2 * ((m + m : ℕ) : ℝ)) ≤ 1 / 8 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
          linarith [hlem0.2]
        have hμ₁m : ft μ₁ m = 0 := by
          simp only [μ₁, ft_map_mul]
          have : (2 : ℝ) * (m : ℝ) = ((m + m : ℕ) : ℝ) := by push_cast; ring
          rw [this]; exact hμr
        have hμ₁_min : ∀ j : ℕ, 1 ≤ j → j < m → ft μ₁ j ≠ 0 := by
          intro j hj1 hjm
          simp only [μ₁, ft_map_mul]
          have : (2 : ℝ) * (j : ℝ) = ((2 * j : ℕ) : ℝ) := by push_cast; ring
          rw [this]; exact hr_min (2 * j) (by omega) (by omega)
        have hih := ih m hm_lt hm2 (by linarith : 0 < 2 * a) h2a_lt hconv₁ hinf₁ hsup₁ hμ₁m hμ₁_min
        intro k hk
        rcases hdvd2 k hk with ⟨q, rfl⟩
        have hμ₁q : ft μ₁ q = 0 := by
          simp only [μ₁, ft_map_mul]
          have : (2 : ℝ) * (q : ℝ) = ((2 * q : ℤ) : ℝ) := by push_cast; ring
          rw [this]; exact hk
        rcases hih q hμ₁q with ⟨t, rfl⟩
        refine ⟨t, ?_⟩; push_cast; ring
    · exact gabardo_lai_lem1_odd ha0 ha_half hconv hμ_supp hν_supp h01.2.2.2.1 hr2 heven hlem0.1 hlem0.2 hμr

/-! ### One-Sided Stripping and Single-Step Theorem 4.1 -/

/-- Support endpoints for a complementary pair on `[0, 1]` with `μ ∗ ν = leb01`. -/
lemma support_endpoints_of_conv_leb01 {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hconv : μ ∗ ν = leb01) (hμ_supp : IsSupportedIn μ (Set.Icc 0 1)) (hν_supp : IsSupportedIn ν (Set.Icc 0 1)) :
    BddBelow μ.support ∧ BddAbove μ.support ∧ BddBelow ν.support ∧ BddAbove ν.support ∧
    sInf μ.support = 0 ∧ sInf ν.support = 0 ∧
    sSup μ.support + sSup ν.support = 1 := by
  let μ' := μ.map (· + -(1 / 2 : ℝ))
  have : IsProbabilityMeasure μ' := isProbabilityMeasure_map_measurable (measurable_add_const _)
  have hconv' : μ' ∗ ν = lebHalf := by
    have h1 := (map_conv_add_const μ ν (-(1 / 2)) 0).symm
    have hν0 : ν.map (· + (0 : ℝ)) = ν := by simp
    rw [hν0, add_zero, hconv] at h1
    rw [h1]
    have hsub : (fun x : ℝ => x + -(1 / 2 : ℝ)) = (fun x : ℝ => x - 1 / 2) := by ext x; ring
    rw [hsub, leb01_map_sub_half]
  rcases support_endpoints_of_conv_lebHalf hconv' with ⟨hμ'_bb, hμ'_ba, hν_bb, hν_ba, hinf_sum, hsup_sum⟩
  have hμne : μ.support.Nonempty := Measure.nonempty_support (IsProbabilityMeasure.ne_zero μ)
  have hνne : ν.support.Nonempty := Measure.nonempty_support (IsProbabilityMeasure.ne_zero ν)
  have hμ_sub : μ.support ⊆ Set.Icc 0 1 := by
    intro x hx
    by_contra hnot
    have hopen : IsOpen (Set.Icc (0 : ℝ) 1)ᶜ := isClosed_Icc.isOpen_compl
    have hpos := (Measure.mem_support_iff_forall x).mp hx _ (hopen.mem_nhds hnot)
    exact hpos.ne' hμ_supp
  have hν_sub : ν.support ⊆ Set.Icc 0 1 := by
    intro y hy
    by_contra hnot
    have hopen : IsOpen (Set.Icc (0 : ℝ) 1)ᶜ := isClosed_Icc.isOpen_compl
    have hpos := (Measure.mem_support_iff_forall y).mp hy _ (hopen.mem_nhds hnot)
    exact hpos.ne' hν_supp
  have hμ_bb : BddBelow μ.support := ⟨0, fun x hx => (hμ_sub hx).1⟩
  have hμ_ba : BddAbove μ.support := ⟨1, fun x hx => (hμ_sub hx).2⟩
  have hinf_μ' : sInf μ'.support = sInf μ.support + -(1 / 2) := by
    rw [map_add_const_support, sInf_image_add_const hμne hμ_bb]
  have hsup_μ' : sSup μ'.support = sSup μ.support + -(1 / 2) := by
    rw [map_add_const_support, sSup_image_add_const hμne hμ_ba]
  rw [hinf_μ'] at hinf_sum
  rw [hsup_μ'] at hsup_sum
  have hinf_μ_nn : 0 ≤ sInf μ.support := le_csInf hμne (fun x hx => (hμ_sub hx).1)
  have hinf_ν_nn : 0 ≤ sInf ν.support := le_csInf hνne (fun y hy => (hν_sub hy).1)
  exact ⟨hμ_bb, hμ_ba, hν_bb, hν_ba, by linarith, by linarith, by linarith⟩

/-- One-sided periodic stripping: if `μ ∗ ν = leb01`, both supported in `[0, 1]`, neither is `δ₀`,
and `ft μ 1 = 0`, then there exist `M ≥ 2` and `α` with `μ = unifDiscrete M (1/M) ∗ α`,
`α ∗ ν = lebScaled (1/M)`, and `ft ν M = 0`. -/
lemma gabardo_lai_strip_one {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hconv : μ ∗ ν = leb01) (hμ_supp : IsSupportedIn μ (Set.Icc 0 1))
    (hν_supp : IsSupportedIn ν (Set.Icc 0 1))
    (hμ_ne : μ ≠ Measure.dirac 0) (hν_ne : ν ≠ Measure.dirac 0)
    (hμ1 : ft μ 1 = 0) :
    ∃ (M : ℕ) (α : Measure ℝ), 2 ≤ M ∧ IsProbabilityMeasure α ∧
      IsSupportedIn α (Set.Icc 0 (1 / (M : ℝ))) ∧
      IsSupportedIn ν (Set.Icc 0 (1 / (M : ℝ))) ∧
      μ = unifDiscrete M (1 / (M : ℝ)) ∗ α ∧
      α ∗ ν = lebScaled (1 / (M : ℝ)) ∧
      ft ν M = 0 := by
  classical
  rcases support_endpoints_of_conv_leb01 hconv hμ_supp hν_supp with
    ⟨hμ_bb, hμ_ba, hν_bb, hν_ba, hinf_μ, hinf_ν, hsup_sum⟩
  have hμne : μ.support.Nonempty := Measure.nonempty_support (IsProbabilityMeasure.ne_zero μ)
  have hνne : ν.support.Nonempty := Measure.nonempty_support (IsProbabilityMeasure.ne_zero ν)
  have hsup_μ_pos : 0 < sSup μ.support := by
    by_contra hle; push Not at hle
    have hsupp0 : IsSupportedIn μ (Set.Icc 0 0) := by
      have hsub : μ.support ⊆ Set.Icc 0 0 := fun x hx =>
        ⟨hinf_μ ▸ csInf_le hμ_bb hx, le_trans (le_csSup hμ_ba hx) hle⟩
      exact measure_mono_null (Set.compl_subset_compl.mpr hsub) Measure.measure_compl_support
    exact hμ_ne (eq_dirac_zero_of_supp_le_zero hsupp0)
  have hsup_ν_pos : 0 < sSup ν.support := by
    by_contra hle; push Not at hle
    have hsupp0 : IsSupportedIn ν (Set.Icc 0 0) := by
      have hsub : ν.support ⊆ Set.Icc 0 0 := fun y hy =>
        ⟨hinf_ν ▸ csInf_le hν_bb hy, le_trans (le_csSup hν_ba hy) hle⟩
      exact measure_mono_null (Set.compl_subset_compl.mpr hsub) Measure.measure_compl_support
    exact hν_ne (eq_dirac_zero_of_supp_le_zero hsupp0)
  set a := sSup μ.support / 2
  set b := sSup ν.support / 2
  have ha0 : 0 < a := half_pos hsup_μ_pos
  have hb0 : 0 < b := half_pos hsup_ν_pos
  have hab : a + b = 1 / 2 := by simp only [a, b]; linarith
  have ha_half : a < 1 / 2 := by linarith
  have hb_half : b < 1 / 2 := by linarith
  let μc := μ.map (· + (-a))
  let νc := ν.map (· + (-b))
  have hμc_prob : IsProbabilityMeasure μc := isProbabilityMeasure_map_measurable (measurable_add_const _)
  have hνc_prob : IsProbabilityMeasure νc := isProbabilityMeasure_map_measurable (measurable_add_const _)
  have hconv_c : μc ∗ νc = lebHalf := by
    rw [← map_conv_add_const, hconv]
    have hsub : (fun x : ℝ => x + (-a + -b)) = (fun x : ℝ => x - 1 / 2) := by ext x; linarith
    rw [hsub, leb01_map_sub_half]
  have hinf_μc : sInf μc.support = -a := by
    rw [map_add_const_support, sInf_image_add_const hμne hμ_bb, hinf_μ, zero_add]
  have hsup_μc : sSup μc.support = a := by
    rw [map_add_const_support, sSup_image_add_const hμne hμ_ba]; simp only [a]; ring
  have hinf_νc : sInf νc.support = -b := by
    rw [map_add_const_support, sInf_image_add_const hνne hν_bb, hinf_ν, zero_add]
  have hsup_νc : sSup νc.support = b := by
    rw [map_add_const_support, sSup_image_add_const hνne hν_ba]; simp only [b]; ring
  have hft_μc_zero : ∀ ξ : ℝ, ft μc ξ = 0 ↔ ft μ ξ = 0 := fun ξ => by
    simp only [μc, ft_map_add_const, mul_eq_zero, Complex.exp_ne_zero, or_false]
  have hft_νc_zero : ∀ ξ : ℝ, ft νc ξ = 0 ↔ ft ν ξ = 0 := fun ξ => by
    simp only [νc, ft_map_add_const, mul_eq_zero, Complex.exp_ne_zero, or_false]
  have h01 := gabardo_lai_lem01 (le_of_lt ha0) (le_of_lt ha_half) hconv_c hinf_μc hsup_μc
  have hμc1 : ft μc (1 : ℤ) = 0 := by rw [Int.cast_one, hft_μc_zero]; exact hμ1
  have hνc1_ne : ft νc (1 : ℤ) ≠ 0 := fun h => (h01.1 1 one_ne_zero).2 ⟨hμc1, h⟩
  -- Prove ∃ m ≥ 2, ft νc m = 0 (otherwise μc = lebHalf, contradicting a < 1/2)
  have hex_M : ∃ m : ℕ, 2 ≤ m ∧ ft νc m = 0 := by
    by_contra hno; push Not at hno
    have hμc_all : ∀ k : ℤ, k ≠ 0 → ft μc k = 0 := by
      intro k hk
      have hν_ne_k : ft νc k ≠ 0 := by
        cases Int.natAbs_eq k with
        | inl heq =>
          have hm1 : 1 ≤ k.natAbs := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hk)
          have hkr : (k : ℝ) = (k.natAbs : ℝ) := by rw [← Int.cast_natCast k.natAbs, ← heq]
          rw [hkr]
          by_cases hm : k.natAbs = 1
          · rw [hm, Nat.cast_one]; simpa using hνc1_ne
          · exact hno k.natAbs (by omega)
        | inr heq =>
          have hm1 : 1 ≤ k.natAbs := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hk)
          intro h0
          have hkr : (k : ℝ) = -((k.natAbs : ℕ) : ℝ) := by exact_mod_cast heq
          rw [hkr, ft_neg] at h0
          have hpos0 : ft νc (k.natAbs : ℝ) = 0 := (starRingEnd ℂ).map_eq_zero_iff.mp h0
          by_cases hm : k.natAbs = 1
          · rw [hm, Nat.cast_one] at hpos0; exact hνc1_ne (by simpa using hpos0)
          · exact hno k.natAbs (by omega) hpos0
      exact (h01.1 k hk).1.resolve_right hν_ne_k
    have hμc_supp : IsSupportedIn μc (Set.Icc (-(1 / 2)) (1 / 2)) := by
      have hsub : μc.support ⊆ Set.Icc (-(1 / 2)) (1 / 2) := by
        rw [map_add_const_support]
        rintro _ ⟨x, hx, rfl⟩
        have hx1 := hinf_μ ▸ csInf_le hμ_bb hx
        have hx2 := le_csSup hμ_ba hx
        exact ⟨by linarith, by simp only [a] at *; linarith⟩
      exact measure_mono_null (Set.compl_subset_compl.mpr hsub) Measure.measure_compl_support
    have hμc_eq := eq_lebHalf_of_ft_int hμc_supp hμc_all
    -- Contradiction: lebHalf (a, 1/2) > 0 whereas μc (a, 1/2) = 0
    have hpos : 0 < lebHalf (Set.Ioo a (1 / 2)) := by
      rw [lebHalf, Measure.restrict_apply measurableSet_Ioo]
      have hinter : Set.Ioo a (1 / 2) ∩ Set.Icc (-(1 / 2)) (1 / 2) = Set.Ioo a (1 / 2) :=
        Set.inter_eq_left.mpr (fun x hx => ⟨by linarith [hx.1], le_of_lt hx.2⟩)
      rw [hinter, Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by linarith)
    have hzero : μc (Set.Ioo a (1 / 2)) = 0 := by
      have hsub : Set.Ioo a (1 / 2) ⊆ μc.supportᶜ := fun x hx hmem => by
        have hba' : BddAbove μc.support := by
          rw [map_add_const_support]
          rcases hμ_ba with ⟨M, hM⟩
          exact ⟨M + -a, by rintro _ ⟨y, hy, rfl⟩; linarith [hM hy]⟩
        have := le_csSup hba' hmem
        rw [hsup_μc] at this; linarith [hx.1]
      exact measure_mono_null hsub Measure.measure_compl_support
    rw [hμc_eq] at hzero
    exact hpos.ne' hzero
  set M := Nat.find hex_M
  have hM_spec : 2 ≤ M ∧ ft νc M = 0 := Nat.find_spec hex_M
  have hM_min : ∀ m : ℕ, 1 ≤ m → m < M → ft νc m ≠ 0 := by
    intro m hm1 hmM
    by_cases hm : m = 1
    · subst hm; simpa using hνc1_ne
    · intro h0; exact Nat.find_min hex_M hmM ⟨by omega, h0⟩
  -- Apply gabardo_lai_lem1 to (νc, μc)
  have hconv_swap : νc ∗ μc = lebHalf := by rw [Measure.conv_comm]; exact hconv_c
  have hdvd_νc := gabardo_lai_lem1 hM_spec.1 hb0 hb_half hconv_swap hinf_νc hsup_νc hM_spec.2 hM_min
  -- Hence for all k : ℤ with ¬ (M ∣ k), ft μ k = 0
  have hμ_div : ∀ k : ℤ, ¬ ((M : ℤ) ∣ k) → ft μ k = 0 := by
    intro k hndvd
    have hk0 : k ≠ 0 := fun h => hndvd (h ▸ dvd_zero _)
    have hν_ne_k : ft νc k ≠ 0 := fun h => hndvd (hdvd_νc k h)
    exact (hft_μc_zero k).mp ((h01.1 k hk0).1.resolve_right hν_ne_k)
  -- μ is supported in [0, 1) since sSup μ.support = 2a < 1
  have hμ_Ico : IsSupportedIn μ (Set.Ico 0 1) := by
    have hsub : μ.support ⊆ Set.Ico 0 1 := fun x hx =>
      ⟨hinf_μ ▸ csInf_le hμ_bb hx, by have := le_csSup hμ_ba hx; simp only [a] at ha_half; linarith⟩
    exact measure_mono_null (Set.compl_subset_compl.mpr hsub) Measure.measure_compl_support
  -- Apply periodic_decomp_of_ft_div to μ
  rcases periodic_decomp_of_ft_div hM_spec.1 hμ_Ico hμ_div with ⟨hα_prob, hα_supp, hμ_eq⟩
  set α : Measure ℝ := (M : ℝ≥0∞) • μ.restrict (Set.Ico (0 : ℝ) (1 / (M : ℝ)))
  -- Deduce α ∗ ν = lebScaled (1 / M) by cancelling unifDiscrete M (1 / M)
  have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
  have hαν_eq : α ∗ ν = lebScaled (1 / (M : ℝ)) := by
    have := isProbabilityMeasure_unifDiscrete (by omega : 0 < M) (1 / (M : ℝ))
    have := isProbabilityMeasure_lebScaled (div_pos one_pos hMpos)
    have hunif_leb : unifDiscrete M (1 / (M : ℝ)) ∗ lebScaled (1 / (M : ℝ)) = leb01 := by
      rw [unifDiscrete_conv_lebScaled (by omega) (div_pos one_pos hMpos)]
      have : (M : ℝ) * (1 / (M : ℝ)) = 1 := by field_simp
      rw [this, lebScaled_one]
    have hdense : Dense {ξ : ℝ | ∀ k : ℤ, ξ ≠ (k : ℝ)} := by
      intro x; rw [Metric.mem_closure_iff]; intro ε hε
      by_cases hx : ∃ k : ℤ, x = k
      · rcases hx with ⟨k, rfl⟩
        refine ⟨(k : ℝ) + min (ε / 2) (1 / 2), ?_, ?_⟩
        · intro m hm
          have h1 : (0 : ℝ) < min (ε / 2) (1 / 2) := lt_min (half_pos hε) (by norm_num)
          have h2 : min (ε / 2) (1 / 2) < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
          have : k < m := by exact_mod_cast (show (k : ℝ) < (m : ℝ) by linarith)
          have : m < k + 1 := by exact_mod_cast (show (m : ℝ) < (k : ℝ) + 1 by linarith)
          omega
        · rw [Real.dist_eq, abs_sub_comm]
          have h1 : (0 : ℝ) < min (ε / 2) (1 / 2) := lt_min (half_pos hε) (by norm_num)
          rw [show (k : ℝ) + min (ε / 2) (1 / 2) - (k : ℝ) = min (ε / 2) (1 / 2) by ring, abs_of_pos h1]
          exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
      · push Not at hx; exact ⟨x, hx, by simp [hε]⟩
    apply ext_of_ft
    have hfun : ft (α ∗ ν) = ft (lebScaled (1 / (M : ℝ))) := by
      apply Continuous.ext_on hdense (continuous_ft _) (continuous_ft _)
      intro ξ hξ
      have hξ0 : ξ ≠ 0 := by simpa using hξ 0
      have hunif_ne : ft (unifDiscrete M (1 / (M : ℝ))) ξ ≠ 0 := by
        intro h0
        have h1 : ft leb01 ξ = 0 := by rw [← hunif_leb, ft_conv, h0, zero_mul]
        have h2 : ft lebHalf ξ = 0 := by
          rw [← leb01_map_sub_half]
          have hsub : (fun x : ℝ => x - 1 / 2) = (· + -(1 / 2 : ℝ)) := by ext x; ring
          rw [hsub, ft_map_add_const, h1, zero_mul]
        rw [ft_lebHalf] at h2; simp only [hξ0, ↓reduceIte] at h2
        have hsin0 : Real.sin (Real.pi * ξ) = 0 :=
          (div_eq_zero_iff.mp (Complex.ofReal_eq_zero.mp h2)).resolve_right (mul_ne_zero Real.pi_ne_zero hξ0)
        rcases Real.sin_eq_zero_iff.mp hsin0 with ⟨k, hk⟩
        exact hξ k (mul_left_cancel₀ Real.pi_ne_zero (by linarith))
      have hprod : ft (unifDiscrete M (1 / (M : ℝ))) ξ * ft (α ∗ ν) ξ =
          ft (unifDiscrete M (1 / (M : ℝ))) ξ * ft (lebScaled (1 / (M : ℝ))) ξ := by
        rw [← ft_conv, ← ft_conv, ← Measure.conv_assoc, ← hμ_eq, hconv, hunif_leb]
      exact mul_left_cancel₀ hunif_ne hprod
    exact congrFun hfun
  -- Deduce ν is supported in [0, 1/M]
  have hν_supp_M : IsSupportedIn ν (Set.Icc 0 (1 / (M : ℝ))) := by
    have hα_s_prob : IsProbabilityMeasure (α.map ((M : ℝ) * ·)) := isProbabilityMeasure_map_measurable (measurable_const_mul _)
    have hν_s_prob : IsProbabilityMeasure (ν.map ((M : ℝ) * ·)) := isProbabilityMeasure_map_measurable (measurable_const_mul _)
    have hconv_s : α.map ((M : ℝ) * ·) ∗ ν.map ((M : ℝ) * ·) = leb01 := by
      rw [← map_conv_mul_left, hαν_eq, lebScaled_map_mul (div_pos one_pos hMpos) hMpos]
      have : (M : ℝ) * (1 / (M : ℝ)) = 1 := by field_simp
      rw [this, lebScaled_one]
    have hν_sub : ν.support ⊆ Set.Icc 0 (1 / (M : ℝ)) := by
      intro y hy
      refine ⟨hinf_ν ▸ csInf_le hν_bb hy, ?_⟩
      by_contra hgt; push Not at hgt
      -- Since 0 ∈ α.support? More simply: sInf α.support ≥ 0 and ∃ x ∈ α.support with x ≥ 0;
      -- actually sSup(α ∗ ν) = 1/M, so sInf α.support + y ≤ 1/M!
      have hαne : α.support.Nonempty := Measure.nonempty_support (IsProbabilityMeasure.ne_zero α)
      rcases hαne with ⟨x₀, hx₀⟩
      have hx₀_nn : 0 ≤ x₀ := by
        by_contra hlt; push Not at hlt
        have hpos := (Measure.mem_support_iff_forall x₀).mp hx₀ _ (isOpen_Iio.mem_nhds hlt)
        have hsub : Set.Iio (0 : ℝ) ⊆ (Set.Icc (0 : ℝ) (1 / (M : ℝ)))ᶜ :=
          fun x hx hc => by linarith [Set.mem_Iio.mp hx, hc.1]
        exact hpos.ne' (measure_mono_null hsub hα_supp)
      -- Then x₀ + y > 1/M, contradicting (α ∗ ν) (1/M, ∞) = 0
      set δ := (x₀ + y - 1 / (M : ℝ)) / 2
      have hδ : 0 < δ := by simp only [δ]; linarith
      have h1 : 0 < α (Set.Ioo (x₀ - δ) (x₀ + δ)) :=
        (Measure.mem_support_iff_forall x₀).mp hx₀ _ (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
      have h2 : 0 < ν (Set.Ioo (y - δ) (y + δ)) :=
        (Measure.mem_support_iff_forall y).mp hy _ (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
      have hsub_prod : Set.Ioo (x₀ - δ) (x₀ + δ) ×ˢ Set.Ioo (y - δ) (y + δ) ⊆
          (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' (Set.Icc 0 (1 / (M : ℝ)))ᶜ := by
        rintro ⟨x, z⟩ ⟨⟨hx1, _⟩, ⟨hz1, _⟩⟩ hmem
        simp only [Set.mem_Icc] at hmem
        simp only [δ] at hx1 hz1; linarith
      have hpos_conv : 0 < (α ∗ ν) (Set.Icc 0 (1 / (M : ℝ)))ᶜ := by
        rw [Measure.conv, Measure.map_apply measurable_add measurableSet_Icc.compl]
        calc (0 : ℝ≥0∞) < α (Set.Ioo (x₀ - δ) (x₀ + δ)) * ν (Set.Ioo (y - δ) (y + δ)) := ENNReal.mul_pos h1.ne' h2.ne'
          _ = (α.prod ν) (Set.Ioo (x₀ - δ) (x₀ + δ) ×ˢ Set.Ioo (y - δ) (y + δ)) := (Measure.prod_prod _ _).symm
          _ ≤ (α.prod ν) ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' (Set.Icc 0 (1 / (M : ℝ)))ᶜ) := measure_mono hsub_prod
      rw [hαν_eq, lebScaled_supported] at hpos_conv
      exact lt_irrefl 0 hpos_conv
    exact measure_mono_null (Set.compl_subset_compl.mpr hν_sub) Measure.measure_compl_support
  have hνM : ft ν M = 0 := (hft_νc_zero M).mp hM_spec.2
  exact ⟨M, α, hM_spec.1, hα_prob, hα_supp, hν_supp_M, hμ_eq, hαν_eq, hνM⟩

/-- **Theorem 4.1 (Gabardo–Lai Single-Step Factorization):**
Let `μ, ν` be nontrivial probability measures on `[0, 1]` with `μ ∗ ν = leb01`.
Then there exist integers `M₁ ≥ 2`, `M₂ ≥ 2` and probability measures `μ', ν'` supported in
`[0, 1 / (M₁ * M₂)]` with `μ' ∗ ν' = lebScaled (1 / (M₁ * M₂))` such that (up to swapping `μ, ν`)
`μ = unifDiscrete M₁ (1 / M₁) ∗ μ'` and `ν = unifDiscrete M₂ (1 / (M₁ * M₂)) ∗ ν'`. -/
theorem gabardo_lai_single_step {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hconv : μ ∗ ν = leb01) (hμ_supp : IsSupportedIn μ (Set.Icc 0 1))
    (hν_supp : IsSupportedIn ν (Set.Icc 0 1))
    (hμ_ne : μ ≠ Measure.dirac 0) (hν_ne : ν ≠ Measure.dirac 0) :
    ∃ (M₁ M₂ : ℕ) (μ' ν' : Measure ℝ), 2 ≤ M₁ ∧ 2 ≤ M₂ ∧
      IsProbabilityMeasure μ' ∧ IsProbabilityMeasure ν' ∧
      IsSupportedIn μ' (Set.Icc 0 (1 / ((M₁ : ℝ) * (M₂ : ℝ)))) ∧
      IsSupportedIn ν' (Set.Icc 0 (1 / ((M₁ : ℝ) * (M₂ : ℝ)))) ∧
      μ' ∗ ν' = lebScaled (1 / ((M₁ : ℝ) * (M₂ : ℝ))) ∧
      ((μ = unifDiscrete M₁ (1 / (M₁ : ℝ)) ∗ μ' ∧ ν = unifDiscrete M₂ (1 / ((M₁ : ℝ) * (M₂ : ℝ))) ∗ ν') ∨
       (ν = unifDiscrete M₁ (1 / (M₁ : ℝ)) ∗ μ' ∧ μ = unifDiscrete M₂ (1 / ((M₁ : ℝ) * (M₂ : ℝ))) ∗ ν')) := by
  -- Helper for the case ft μ 1 = 0
  have hcase : ∀ (μ₁ ν₁ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁],
      μ₁ ∗ ν₁ = leb01 → IsSupportedIn μ₁ (Set.Icc 0 1) → IsSupportedIn ν₁ (Set.Icc 0 1) →
      μ₁ ≠ Measure.dirac 0 → ν₁ ≠ Measure.dirac 0 → ft μ₁ 1 = 0 →
      ∃ (M₁ M₂ : ℕ) (μ' ν' : Measure ℝ), 2 ≤ M₁ ∧ 2 ≤ M₂ ∧
        IsProbabilityMeasure μ' ∧ IsProbabilityMeasure ν' ∧
        IsSupportedIn μ' (Set.Icc 0 (1 / ((M₁ : ℝ) * (M₂ : ℝ)))) ∧
        IsSupportedIn ν' (Set.Icc 0 (1 / ((M₁ : ℝ) * (M₂ : ℝ)))) ∧
        μ' ∗ ν' = lebScaled (1 / ((M₁ : ℝ) * (M₂ : ℝ))) ∧
        μ₁ = unifDiscrete M₁ (1 / (M₁ : ℝ)) ∗ μ' ∧
        ν₁ = unifDiscrete M₂ (1 / ((M₁ : ℝ) * (M₂ : ℝ))) ∗ ν' := by
    intro μ₁ ν₁ _ _ hcv hμs hνs hμn hνn hft1
    obtain ⟨M₁, α₁, hM1, hα1_prob, hα1_supp, hν1_supp_M1, hμ1_eq, hα1ν1, hν1_M1⟩ :=
      gabardo_lai_strip_one hcv hμs hνs hμn hνn hft1
    have hM1pos : (0 : ℝ) < (M₁ : ℝ) := Nat.cast_pos.mpr (by omega)
    by_cases hα1_dirac : α₁ = Measure.dirac 0
    · -- Type I case: α₁ = δ₀, so ν₁ = lebScaled (1 / M₁); take M₂ = 2, μ' = δ₀, ν' = lebScaled (1 / (2 M₁))
      have hν1_leb : ν₁ = lebScaled (1 / (M₁ : ℝ)) := by
        rw [hα1_dirac, Measure.dirac_conv] at hα1ν1
        simpa using hα1ν1
      have hc2_pos : (0 : ℝ) < 1 / ((M₁ : ℝ) * (2 : ℕ)) := by positivity
      have : IsProbabilityMeasure (lebScaled (1 / ((M₁ : ℝ) * (2 : ℕ)))) := isProbabilityMeasure_lebScaled hc2_pos
      refine ⟨M₁, 2, Measure.dirac 0, lebScaled (1 / ((M₁ : ℝ) * (2 : ℕ))), hM1, le_rfl,
        inferInstance, inferInstance, ?_, lebScaled_supported _, ?_, ?_, ?_⟩
      · unfold IsSupportedIn
        have h0in : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / ((M₁ : ℝ) * (2 : ℕ))) := ⟨le_rfl, le_of_lt hc2_pos⟩
        rw [Measure.dirac_apply' _ measurableSet_Icc.compl,
            Set.indicator_of_notMem (Set.notMem_compl_iff.mpr h0in)]
      · rw [Measure.dirac_conv]; simp
      · rwa [← hα1_dirac]
      · rw [unifDiscrete_conv_lebScaled (by omega) hc2_pos, hν1_leb]
        congr 1; push_cast; field_simp
    · -- Non-Dirac case: rescale (ν₁, α₁) by M₁ and strip one factor from ν₁
      let ν_s := ν₁.map ((M₁ : ℝ) * ·)
      let α_s := α₁.map ((M₁ : ℝ) * ·)
      have hνs_prob : IsProbabilityMeasure ν_s := isProbabilityMeasure_map_measurable (measurable_const_mul _)
      have hαs_prob : IsProbabilityMeasure α_s := isProbabilityMeasure_map_measurable (measurable_const_mul _)
      have hconv_s : ν_s ∗ α_s = leb01 := by
        rw [Measure.conv_comm, ← map_conv_mul_left, hα1ν1, lebScaled_map_mul (div_pos one_pos hM1pos) hM1pos]
        have : (M₁ : ℝ) * (1 / (M₁ : ℝ)) = 1 := by field_simp
        rw [this, lebScaled_one]
      have hmap_supp : ∀ (ρ : Measure ℝ), IsSupportedIn ρ (Set.Icc 0 (1 / (M₁ : ℝ))) →
          IsSupportedIn (ρ.map ((M₁ : ℝ) * ·)) (Set.Icc 0 1) := by
        intro ρ hρ
        unfold IsSupportedIn
        rw [Measure.map_apply (measurable_const_mul _) measurableSet_Icc.compl]
        have hsub : ((M₁ : ℝ) * ·) ⁻¹' (Set.Icc 0 1)ᶜ ⊆ (Set.Icc 0 (1 / (M₁ : ℝ)))ᶜ := by
          intro x hx hmem; apply hx
          refine ⟨mul_nonneg (le_of_lt hM1pos) hmem.1, ?_⟩
          have := mul_le_mul_of_nonneg_left hmem.2 (le_of_lt hM1pos)
          have h1 : (M₁ : ℝ) * (1 / (M₁ : ℝ)) = 1 := by field_simp
          linarith
        exact measure_mono_null hsub hρ
      have hdir0 : Measure.map ((M₁ : ℝ)⁻¹ * ·) (Measure.dirac (0 : ℝ)) = Measure.dirac 0 := by
        ext s hs
        rw [Measure.map_apply (measurable_const_mul _) hs,
            Measure.dirac_apply' _ ((measurable_const_mul _) hs), Measure.dirac_apply' _ hs]
        by_cases h0 : (0 : ℝ) ∈ s
        · have h0' : (0 : ℝ) ∈ ((M₁ : ℝ)⁻¹ * ·) ⁻¹' s := by simpa [Set.mem_preimage] using h0
          rw [Set.indicator_of_mem h0', Set.indicator_of_mem h0]
        · have h0' : (0 : ℝ) ∉ ((M₁ : ℝ)⁻¹ * ·) ⁻¹' s := by simpa [Set.mem_preimage] using h0
          rw [Set.indicator_of_notMem h0', Set.indicator_of_notMem h0]
      have hνs_ne : ν_s ≠ Measure.dirac 0 := by
        intro h0
        have hback : ν₁ = (ν_s).map ((M₁ : ℝ)⁻¹ * ·) := by
          simp only [ν_s, Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
          have : ((M₁ : ℝ)⁻¹ * ·) ∘ ((M₁ : ℝ) * ·) = id := by ext x; simp; field_simp
          rw [this, Measure.map_id]
        rw [h0, hdir0] at hback
        exact hνn hback
      have hαs_ne : α_s ≠ Measure.dirac 0 := by
        intro h0
        have hback : α₁ = (α_s).map ((M₁ : ℝ)⁻¹ * ·) := by
          simp only [α_s, Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
          have : ((M₁ : ℝ)⁻¹ * ·) ∘ ((M₁ : ℝ) * ·) = id := by ext x; simp; field_simp
          rw [this, Measure.map_id]
        rw [h0, hdir0] at hback
        exact hα1_dirac hback
      have hνs_ft1 : ft ν_s 1 = 0 := by
        simp only [ν_s, ft_map_mul, mul_one]; exact hν1_M1
      obtain ⟨M₂, β₂, hM2, hβ2_prob, hβ2_supp, hαs_supp_M2, hνs_eq, hβ2αs, _⟩ :=
        gabardo_lai_strip_one hconv_s (hmap_supp ν₁ hν1_supp_M1) (hmap_supp α₁ hα1_supp) hνs_ne hαs_ne hνs_ft1
      have hM2pos : (0 : ℝ) < (M₂ : ℝ) := Nat.cast_pos.mpr (by omega)
      let ν' := β₂.map ((M₁ : ℝ)⁻¹ * ·)
      have hν'_prob : IsProbabilityMeasure ν' := isProbabilityMeasure_map_measurable (measurable_const_mul _)
      have hpull_supp : ∀ (ρ : Measure ℝ), IsSupportedIn ρ (Set.Icc 0 (1 / (M₂ : ℝ))) →
          IsSupportedIn (ρ.map ((M₁ : ℝ)⁻¹ * ·)) (Set.Icc 0 (1 / ((M₁ : ℝ) * (M₂ : ℝ)))) := by
        intro ρ hρ; unfold IsSupportedIn
        rw [Measure.map_apply (measurable_const_mul _) measurableSet_Icc.compl]
        have hsub : ((M₁ : ℝ)⁻¹ * ·) ⁻¹' (Set.Icc 0 (1 / ((M₁ : ℝ) * (M₂ : ℝ))))ᶜ ⊆ (Set.Icc 0 (1 / (M₂ : ℝ)))ᶜ := by
          intro x hx hmem; apply hx
          refine ⟨mul_nonneg (inv_nonneg.mpr (le_of_lt hM1pos)) hmem.1, ?_⟩
          have := mul_le_mul_of_nonneg_left hmem.2 (inv_nonneg.mpr (le_of_lt hM1pos))
          have h1 : (M₁ : ℝ)⁻¹ * (1 / (M₂ : ℝ)) = 1 / ((M₁ : ℝ) * (M₂ : ℝ)) := by field_simp
          linarith
        exact measure_mono_null hsub hρ
      have hα1_back : α₁ = α_s.map ((M₁ : ℝ)⁻¹ * ·) := by
        simp only [α_s, Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
        have : ((M₁ : ℝ)⁻¹ * ·) ∘ ((M₁ : ℝ) * ·) = id := by ext x; simp; field_simp
        rw [this, Measure.map_id]
      have hν1_back : ν₁ = ν_s.map ((M₁ : ℝ)⁻¹ * ·) := by
        simp only [ν_s, Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
        have : ((M₁ : ℝ)⁻¹ * ·) ∘ ((M₁ : ℝ) * ·) = id := by ext x; simp; field_simp
        rw [this, Measure.map_id]
      have hα1_supp_12 : IsSupportedIn α₁ (Set.Icc 0 (1 / ((M₁ : ℝ) * (M₂ : ℝ)))) := by
        rw [hα1_back]; exact hpull_supp α_s hαs_supp_M2
      have hconv_12 : α₁ ∗ ν' = lebScaled (1 / ((M₁ : ℝ) * (M₂ : ℝ))) := by
        rw [hα1_back, Measure.conv_comm, ← map_conv_mul_left, hβ2αs,
            lebScaled_map_mul (div_pos one_pos hM2pos) (inv_pos.mpr hM1pos)]
        congr 1; field_simp
      have hν1_eq : ν₁ = unifDiscrete M₂ (1 / ((M₁ : ℝ) * (M₂ : ℝ))) ∗ ν' := by
        have := isProbabilityMeasure_unifDiscrete (by omega : 0 < M₂) (1 / (M₂ : ℝ))
        rw [hν1_back, hνs_eq, map_conv_mul_left, unifDiscrete_map_mul]
        congr 2; field_simp
      exact ⟨M₁, M₂, α₁, ν', hM1, hM2, hα1_prob, hν'_prob, hα1_supp_12, hpull_supp β₂ hβ2_supp,
        hconv_12, hμ1_eq, hν1_eq⟩
  -- Either ft μ 1 = 0 or ft ν 1 = 0 (since ft(μ∗ν) 1 = ft leb01 1 = 0)
  have hprod1 : ft μ 1 * ft ν 1 = 0 := by
    rw [← ft_conv, hconv, ← lebScaled_one, ft_lebScaled one_pos 1]
    simp only [one_ne_zero, ↓reduceIte]
    have harg : (-2 * Real.pi * ((1 : ℝ) : ℂ) * ((1 : ℝ) : ℂ) * Complex.I) =
        ((-1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [harg, Complex.exp_int_mul_two_pi_mul_I, sub_self, zero_div]
  rcases mul_eq_zero.mp hprod1 with hμ1 | hν1
  · obtain ⟨M₁, M₂, μ', ν', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
      hcase μ ν hconv hμ_supp hν_supp hμ_ne hν_ne hμ1
    exact ⟨M₁, M₂, μ', ν', h1, h2, h3, h4, h5, h6, h7, Or.inl ⟨h8, h9⟩⟩
  · have hconv' : ν ∗ μ = leb01 := by rw [Measure.conv_comm]; exact hconv
    obtain ⟨M₁, M₂, μ', ν', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
      hcase ν μ hconv' hν_supp hμ_supp hν_ne hμ_ne hν1
    exact ⟨M₁, M₂, μ', ν', h1, h2, h3, h4, h5, h6, h7, Or.inr ⟨h8, h9⟩⟩

end

end AlmostPerfect
