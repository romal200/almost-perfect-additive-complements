import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-!
# Gabardo–Lai Factorization (Part 1): Fourier Uniqueness, Symmetry, and Support Bounds

Self-contained, zero-axiom formalization of the first half of Section 2 of
J.-P. Gabardo and C.-K. Lai, *Factorization of Lebesgue measures on an interval*,
J. Fourier Anal. Appl. 20 (2014), Thm. 2.2:

1. Normalized Lebesgue measures `leb01`, `lebHalf`, `lebScaled`, discrete uniform measure
   `unifDiscrete`, and the Fourier transform `ft μ ξ = ∫ exp(-2πi ξ x) dμ(x)` via Mathlib `charFun`.
2. Circle Fourier uniqueness on `AddCircle 1` via `AddCircle.span_fourier_closure_eq_top`
   (replacing tempered distributions completely).
3. `eq_lebHalf_of_ft_int`: a probability measure on `[-1/2, 1/2]` whose integer Fourier
   coefficients vanish for `k ≠ 0` is `lebHalf`.
4. `periodic_decomp_of_ft_div`: a probability measure on `[0, 1)` whose Fourier transform
   vanishes off `Nℤ` decomposes as `unifDiscrete N (1/N) ∗ α₁`.
5. `gabardo_lai_lem01`: disjoint integer zero sets `ℤ \ {0} = Z(μ̂) ⊔ Z(ν̂)` and symmetry
   `checkMeasure μ = μ`, `checkMeasure ν = ν`.
6. `gabardo_lai_lem0`: sharp support bounds `1/(4r) ≤ a ≤ 1/(2r)` via Gauss–Chebyshev
   polynomial quadrature (uniformly for all `r ≥ 2`).
-/

namespace AlmostPerfect

open MeasureTheory Filter Topology Real Complex BigOperators Polynomial
open scoped ENNReal MeasureTheory

noncomputable section

/-! ### Fundamental Measures and Fourier Transform -/

/-- Normalized Lebesgue probability measure on `[0, 1]`. -/
def leb01 : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

/-- Normalized Lebesgue probability measure on `[-1/2, 1/2]`. -/
def lebHalf : Measure ℝ := volume.restrict (Set.Icc (-(1 / 2 : ℝ)) (1 / 2))

/-- Normalized Lebesgue probability measure on `[0, c]` (for `c > 0`). -/
def lebScaled (c : ℝ) : Measure ℝ := (ENNReal.ofReal c)⁻¹ • volume.restrict (Set.Icc (0 : ℝ) c)

/-- Discrete uniform probability measure `(1 / M) ∑_{j=0}^{M-1} δ_{j * step}`. -/
def unifDiscrete (M : ℕ) (step : ℝ) : Measure ℝ :=
  ((M : ℝ≥0∞))⁻¹ • ∑ j ∈ Finset.range M, Measure.dirac ((j : ℝ) * step)

/-- Reflected measure `checkMeasure μ = μ.map (-·)`. -/
def checkMeasure (μ : Measure ℝ) : Measure ℝ := μ.map (fun x => -x)

/-- Measure `μ` is supported in a set `s` (`μ sᶜ = 0`). -/
def IsSupportedIn (μ : Measure ℝ) (s : Set ℝ) : Prop := μ sᶜ = 0

/-- Fourier transform `μ̂(ξ) = ∫ exp(-2πi ξ x) dμ(x)` via Mathlib `charFun`. -/
def ft (μ : Measure ℝ) (ξ : ℝ) : ℂ := charFun μ (-2 * Real.pi * ξ)

instance instIsProbabilityMeasure_leb01 : IsProbabilityMeasure leb01 := by
  constructor
  simp [leb01, Real.volume_Icc]

instance instIsProbabilityMeasure_lebHalf : IsProbabilityMeasure lebHalf := by
  constructor
  rw [lebHalf, Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

lemma isProbabilityMeasure_lebScaled {c : ℝ} (hc : 0 < c) : IsProbabilityMeasure (lebScaled c) := by
  constructor
  rw [lebScaled, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top

lemma isProbabilityMeasure_unifDiscrete {M : ℕ} (hM : 0 < M) (step : ℝ) :
    IsProbabilityMeasure (unifDiscrete M step) := by
  constructor
  rw [unifDiscrete, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
  simp only [Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr (by omega)) (ENNReal.natCast_ne_top M)

instance instIsProbabilityMeasure_checkMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (checkMeasure μ) := by
  constructor
  rw [checkMeasure, Measure.map_apply measurable_neg MeasurableSet.univ, Set.preimage_univ, measure_univ]

lemma leb01_supported : IsSupportedIn leb01 (Set.Icc 0 1) := by
  unfold IsSupportedIn leb01
  rw [Measure.restrict_apply measurableSet_Icc.compl, Set.compl_inter_self, measure_empty]

lemma lebHalf_supported : IsSupportedIn lebHalf (Set.Icc (-(1 / 2)) (1 / 2)) := by
  unfold IsSupportedIn lebHalf
  rw [Measure.restrict_apply measurableSet_Icc.compl, Set.compl_inter_self, measure_empty]

lemma lebScaled_supported (c : ℝ) : IsSupportedIn (lebScaled c) (Set.Icc 0 c) := by
  unfold IsSupportedIn lebScaled
  rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Icc.compl, Set.compl_inter_self,
      measure_empty, smul_zero]

lemma leb01_map_sub_half : leb01.map (fun x : ℝ => x - 1 / 2) = lebHalf := by
  ext s hs
  rw [Measure.map_apply (measurable_sub_const _) hs, leb01, lebHalf,
      Measure.restrict_apply (hs.preimage (measurable_sub_const _)),
      Measure.restrict_apply hs]
  have hpre : (fun x : ℝ => x - 1 / 2) ⁻¹' s ∩ Set.Icc 0 1 =
      (fun x : ℝ => x + -(1 / 2 : ℝ)) ⁻¹' (s ∩ Set.Icc (-(1 / 2)) (1 / 2)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc]
    have hsub : x - 1 / 2 = x + -(1 / 2 : ℝ) := by ring
    rw [hsub]
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1, by linarith, by linarith⟩
  rw [hpre, measure_preimage_add_right]

lemma lebScaled_map_mul {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    (lebScaled c).map (fun x : ℝ => r * x) = lebScaled (r * c) := by
  ext s hs
  rw [Measure.map_apply (measurable_const_mul r) hs, lebScaled, lebScaled,
      Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
      Measure.restrict_apply (hs.preimage (measurable_const_mul r)), Measure.restrict_apply hs]
  have hpre : (fun x : ℝ => r * x) ⁻¹' s ∩ Set.Icc 0 c =
      (r * ·) ⁻¹' (s ∩ Set.Icc 0 (r * c)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc]
    constructor
    · rintro ⟨hx1, hx2, hx3⟩
      exact ⟨hx1, by positivity, by nlinarith⟩
    · rintro ⟨hy1, hy2, hy3⟩
      exact ⟨hy1, by nlinarith, by nlinarith⟩
  rw [hpre, Real.volume_preimage_mul_left hr.ne', abs_of_pos (inv_pos.mpr hr)]
  rw [ENNReal.ofReal_inv_of_pos hr, ← mul_assoc, ← ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr hc).ne') (Or.inl ENNReal.ofReal_ne_top)]
  rw [← ENNReal.ofReal_mul (le_of_lt hc), mul_comm c r]

lemma lebScaled_one : lebScaled 1 = leb01 := by
  simp [lebScaled, leb01]

lemma ft_apply (μ : Measure ℝ) (ξ : ℝ) :
    ft μ ξ = ∫ x, Complex.exp (-2 * Real.pi * ξ * x * Complex.I) ∂μ := by
  unfold ft
  rw [charFun_apply_real]
  congr 1; ext x; push_cast; ring_nf

lemma ft_conv {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ξ : ℝ) :
    ft (μ ∗ ν) ξ = ft μ ξ * ft ν ξ := charFun_conv (-2 * Real.pi * ξ)

lemma ft_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] : ft μ 0 = 1 := by
  unfold ft; simp

lemma ft_neg (μ : Measure ℝ) (ξ : ℝ) : ft μ (-ξ) = starRingEnd ℂ (ft μ ξ) := by
  unfold ft
  have : -2 * Real.pi * -ξ = -(-2 * Real.pi * ξ) := by ring
  rw [this, charFun_neg]

lemma ft_check (μ : Measure ℝ) (ξ : ℝ) : ft (checkMeasure μ) ξ = ft μ (-ξ) := by
  unfold ft checkMeasure
  have h1 : (fun x : ℝ => -x) = ((-1 : ℝ) * ·) := by ext x; ring
  rw [h1, charFun_map_mul]
  congr 1; ring

lemma ft_map_mul (μ : Measure ℝ) (r ξ : ℝ) : ft (μ.map (r * ·)) ξ = ft μ (r * ξ) := by
  unfold ft
  rw [charFun_map_mul]
  congr 1; ring

lemma ft_map_add_const (μ : Measure ℝ) (r ξ : ℝ) :
    ft (μ.map (· + r)) ξ = ft μ ξ * Complex.exp (-2 * Real.pi * ξ * r * Complex.I) := by
  unfold ft
  rw [charFun_map_add_const]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast; ring

lemma ft_dirac (x ξ : ℝ) :
    ft (Measure.dirac x) ξ = Complex.exp (-2 * Real.pi * ξ * x * Complex.I) := by
  unfold ft
  rw [charFun_dirac]
  congr 1
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast; ring

lemma ext_of_ft {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ ξ : ℝ, ft μ ξ = ft ν ξ) : μ = ν := by
  apply Measure.ext_of_charFun
  ext t
  have := h (-t / (2 * Real.pi))
  unfold ft at this
  have harg : -2 * Real.pi * (-t / (2 * Real.pi)) = t := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  rwa [harg] at this

lemma continuous_ft (μ : Measure ℝ) [IsFiniteMeasure μ] : Continuous (ft μ) := by
  have heq : ft μ = fun ξ : ℝ => ∫ x, Complex.exp (-2 * Real.pi * ξ * x * Complex.I) ∂μ :=
    funext (ft_apply μ)
  rw [heq]
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro ξ; exact (by fun_prop : Continuous fun x : ℝ => Complex.exp (-2 * Real.pi * ξ * x * Complex.I)).aestronglyMeasurable
  · intro ξ; apply ae_of_all; intro x
    have : ((-2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I = -2 * Real.pi * ξ * x * Complex.I := by
      push_cast; ring
    rw [← this, Complex.norm_exp_ofReal_mul_I]
  · exact integrable_const 1
  · apply ae_of_all; intro x; fun_prop

lemma ft_lebHalf (ξ : ℝ) :
    ft lebHalf ξ = if ξ = 0 then 1 else Complex.ofReal (Real.sin (Real.pi * ξ) / (Real.pi * ξ)) := by
  by_cases hξ : ξ = 0
  · subst hξ; simp [ft_zero]
  · simp only [hξ, ↓reduceIte]
    rw [ft_apply, lebHalf, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)]
    set c : ℂ := -2 * Real.pi * ξ * Complex.I
    have hc : c ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        (Complex.ofReal_ne_zero.mpr hξ)) Complex.I_ne_zero
    have hfun : (fun x : ℝ => Complex.exp (-2 * Real.pi * ξ * x * Complex.I)) =
        (fun x : ℝ => Complex.exp (c * x)) := by ext x; simp only [c]; ring_nf
    rw [hfun, integral_exp_mul_complex hc]
    have h1 : c * ((1 / 2 : ℝ) : ℂ) = -(Real.pi * ξ : ℂ) * Complex.I := by
      simp only [c]; push_cast; ring
    have h2 : c * ((-(1 / 2 : ℝ) : ℝ) : ℂ) = (Real.pi * ξ : ℂ) * Complex.I := by
      simp only [c]; push_cast; ring
    rw [h1, h2]
    have hsin : Complex.sin (Real.pi * ξ : ℂ) =
        (Complex.exp ((Real.pi * ξ : ℂ) * Complex.I) - Complex.exp (-(Real.pi * ξ : ℂ) * Complex.I)) /
        (2 * Complex.I) := by
      rw [Complex.sin, eq_div_iff (mul_ne_zero (by norm_num) Complex.I_ne_zero)]
      calc
        (Complex.exp (-(Real.pi * ξ : ℂ) * Complex.I) - Complex.exp ((Real.pi * ξ : ℂ) * Complex.I)) *
            Complex.I / 2 * (2 * Complex.I)
            = (Complex.exp (-(Real.pi * ξ : ℂ) * Complex.I) - Complex.exp ((Real.pi * ξ : ℂ) * Complex.I)) *
                Complex.I ^ 2 := by ring
        _ = Complex.exp ((Real.pi * ξ : ℂ) * Complex.I) - Complex.exp (-(Real.pi * ξ : ℂ) * Complex.I) := by
            rw [Complex.I_sq]; ring
    have hsin_real : Complex.ofReal (Real.sin (Real.pi * ξ)) = Complex.sin (Real.pi * ξ : ℂ) := by
      rw [Complex.ofReal_sin]; push_cast; rfl
    rw [Complex.ofReal_div, hsin_real, hsin]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hξc : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    simp only [c, Complex.ofReal_mul]
    field_simp
    ring

lemma ft_lebScaled {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    ft (lebScaled c) ξ =
      if ξ = 0 then 1
      else (Complex.exp (-2 * Real.pi * ξ * c * Complex.I) - 1) / (-2 * Real.pi * ξ * c * Complex.I) := by
  by_cases hξ : ξ = 0
  · subst hξ
    have := isProbabilityMeasure_lebScaled hc
    simp [ft_zero]
  · simp only [hξ, ↓reduceIte]
    rw [ft_apply, lebScaled, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal (le_of_lt hc),
        MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (le_of_lt hc)]
    set w : ℂ := -2 * Real.pi * ξ * Complex.I
    have hw : w ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        (Complex.ofReal_ne_zero.mpr hξ)) Complex.I_ne_zero
    have hfun : (fun x : ℝ => Complex.exp (-2 * Real.pi * ξ * x * Complex.I)) =
        (fun x : ℝ => Complex.exp (w * x)) := by ext x; simp only [w]; ring_nf
    rw [hfun, integral_exp_mul_complex hw, Complex.real_smul]
    simp only [w, Complex.ofReal_inv, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    have hcc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hξc : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    field_simp

lemma hasDerivAt_ft {μ : Measure ℝ} [IsFiniteMeasure μ] {M : ℝ} (_hM : 0 ≤ M)
    (hsupp : IsSupportedIn μ (Set.Icc (-M) M)) (ξ₀ : ℝ) :
    HasDerivAt (ft μ) (∫ x, (-2 * Real.pi * x * Complex.I) * Complex.exp (-2 * Real.pi * ξ₀ * x * Complex.I) ∂μ) ξ₀ := by
  have heq : ft μ = fun ξ : ℝ => ∫ x, Complex.exp (-2 * Real.pi * ξ * x * Complex.I) ∂μ :=
    funext (ft_apply μ)
  rw [heq]
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (ξ : ℝ) (x : ℝ) => Complex.exp (-2 * Real.pi * ξ * x * Complex.I))
    (F' := fun (ξ : ℝ) (x : ℝ) => (-2 * Real.pi * x * Complex.I) * Complex.exp (-2 * Real.pi * ξ * x * Complex.I))
    (bound := fun _ => 2 * Real.pi * M)
    (s := Set.univ) (x₀ := ξ₀)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun ξ => by fun_prop)
    ((integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun x => by
      have : ((-2 * Real.pi * ξ₀ * x : ℝ) : ℂ) * Complex.I = -2 * Real.pi * ξ₀ * x * Complex.I := by
        push_cast; ring
      rw [← this, Complex.norm_exp_ofReal_mul_I]))
    (by fun_prop)
    (by
      have hae : ∀ᵐ x ∂μ, x ∈ Set.Icc (-M) M := by
        rw [ae_iff]; exact hsupp
      filter_upwards [hae] with x hx ξ _
      have hexp : ‖Complex.exp (-2 * Real.pi * ξ * x * Complex.I)‖ = 1 := by
        have : ((-2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I = -2 * Real.pi * ξ * x * Complex.I := by
          push_cast; ring
        rw [← this, Complex.norm_exp_ofReal_mul_I]
      rw [norm_mul, hexp, mul_one]
      have hnorm : ‖(-2 * Real.pi * x * Complex.I : ℂ)‖ = 2 * Real.pi * |x| := by
        have : (-2 * Real.pi * x * Complex.I : ℂ) = ((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
            abs_of_pos Real.pi_pos]
      rw [hnorm]
      have hxabs : |x| ≤ M := abs_le.mpr hx
      nlinarith [Real.pi_pos])
    (integrable_const _)
    (ae_of_all _ fun x ξ _ => by
      have hlin : HasDerivAt (fun t : ℝ => (-2 * Real.pi * x * Complex.I) * (t : ℂ))
          (-2 * Real.pi * x * Complex.I) ξ := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := ξ)).const_mul (-2 * Real.pi * x * Complex.I)
      have hcomp := hlin.cexp
      have hfun : (fun t : ℝ => Complex.exp ((-2 * Real.pi * x * Complex.I) * (t : ℂ))) =
          (fun t : ℝ => Complex.exp (-2 * Real.pi * t * x * Complex.I)) := by ext t; congr 1; ring
      rw [hfun] at hcomp
      convert hcomp using 1; ring_nf)
  exact hres.2

/-! ### Circle Fourier Uniqueness and Periodicity Without Tempered Distributions -/

/-- Two finite Borel measures on `AddCircle 1` with identical Fourier coefficients coincide. -/
theorem addCircle_measure_ext_of_fourier {ρ₁ ρ₂ : Measure (AddCircle (1 : ℝ))}
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    (h : ∀ k : ℤ, ∫ z, fourier k z ∂ρ₁ = ∫ z, fourier k z ∂ρ₂) :
    ρ₁ = ρ₂ := by
  have : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩
  -- Equality on linear span of fourier k
  have hspan : ∀ g ∈ Submodule.span ℂ (Set.range (@fourier 1)),
      ∫ z, g z ∂ρ₁ = ∫ z, g z ∂ρ₂ := by
    intro g hg
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨k, rfl⟩; exact h k
    · simp
    · intro f₁ f₂ _ _ ih₁ ih₂
      have hf1_1 : Integrable f₁ ρ₁ := f₁.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hf2_1 : Integrable f₂ ρ₁ := f₂.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hf1_2 : Integrable f₁ ρ₂ := f₁.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hf2_2 : Integrable f₂ ρ₂ := f₂.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      change ∫ z, (f₁ z + f₂ z) ∂ρ₁ = ∫ z, (f₁ z + f₂ z) ∂ρ₂
      rw [integral_add hf1_1 hf2_1, integral_add hf1_2 hf2_2, ih₁, ih₂]
    · intro c f _ ih
      change ∫ z, c • f z ∂ρ₁ = ∫ z, c • f z ∂ρ₂
      rw [integral_smul, integral_smul, ih]
  -- By density of span(fourier) in C(AddCircle 1, ℂ), equality holds for all continuous functions
  have hcont : ∀ f : C(AddCircle (1 : ℝ), ℂ), ∫ z, f z ∂ρ₁ = ∫ z, f z ∂ρ₂ := by
    intro f
    have hdense : f ∈ closure (Submodule.span ℂ (Set.range (@fourier 1)) : Set C(AddCircle (1 : ℝ), ℂ)) := by
      change f ∈ (Submodule.span ℂ (Set.range (@fourier 1))).topologicalClosure
      rw [span_fourier_closure_eq_top]; trivial
    rw [Metric.mem_closure_iff] at hdense
    apply eq_of_forall_dist_le
    intro ε hε
    set M := (ρ₁ Set.univ).toReal + (ρ₂ Set.univ).toReal + 1
    have hMpos : 0 < M := by positivity
    obtain ⟨g, hg, hdist⟩ := hdense (ε / M) (div_pos hε hMpos)
    have hfg := hspan g hg
    have hf1 : Integrable f ρ₁ := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hg1 : Integrable g ρ₁ := g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hf2 : Integrable f ρ₂ := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hg2 : Integrable g ρ₂ := g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hb1 : ‖∫ z, f z ∂ρ₁ - ∫ z, g z ∂ρ₁‖ ≤ (ρ₁ Set.univ).toReal * (ε / M) := by
      rw [← integral_sub hf1 hg1]
      calc
        ‖∫ z, (f z - g z) ∂ρ₁‖ ≤ ∫ z, ‖f z - g z‖ ∂ρ₁ := norm_integral_le_integral_norm _
        _ ≤ ∫ _z, (ε / M) ∂ρ₁ := by
              apply integral_mono (hf1.sub hg1).norm (integrable_const _)
              intro z
              have hz : dist (f z) (g z) ≤ dist f g := ContinuousMap.dist_apply_le_dist z
              rw [dist_eq_norm] at hz
              exact le_trans hz (le_of_lt hdist)
        _ = (ρ₁ Set.univ).toReal * (ε / M) := by simp [Measure.real]
    have hb2 : ‖∫ z, f z ∂ρ₂ - ∫ z, g z ∂ρ₂‖ ≤ (ρ₂ Set.univ).toReal * (ε / M) := by
      rw [← integral_sub hf2 hg2]
      calc
        ‖∫ z, (f z - g z) ∂ρ₂‖ ≤ ∫ z, ‖f z - g z‖ ∂ρ₂ := norm_integral_le_integral_norm _
        _ ≤ ∫ _z, (ε / M) ∂ρ₂ := by
              apply integral_mono (hf2.sub hg2).norm (integrable_const _)
              intro z
              have hz : dist (f z) (g z) ≤ dist f g := ContinuousMap.dist_apply_le_dist z
              rw [dist_eq_norm] at hz
              exact le_trans hz (le_of_lt hdist)
        _ = (ρ₂ Set.univ).toReal * (ε / M) := by simp [Measure.real]
    rw [dist_eq_norm]
    calc
      ‖∫ z, f z ∂ρ₁ - ∫ z, f z ∂ρ₂‖
          = ‖(∫ z, f z ∂ρ₁ - ∫ z, g z ∂ρ₁) - (∫ z, f z ∂ρ₂ - ∫ z, g z ∂ρ₂)‖ := by rw [hfg]; ring_nf
      _ ≤ ‖∫ z, f z ∂ρ₁ - ∫ z, g z ∂ρ₁‖ + ‖∫ z, f z ∂ρ₂ - ∫ z, g z ∂ρ₂‖ := norm_sub_le _ _
      _ ≤ ((ρ₁ Set.univ).toReal + (ρ₂ Set.univ).toReal) * (ε / M) := by linarith
      _ ≤ M * (ε / M) := by
            apply mul_le_mul_of_nonneg_right (by linarith) (le_of_lt (div_pos hε hMpos))
      _ = ε := mul_div_cancel₀ ε hMpos.ne'
  -- Deduce ρ₁ = ρ₂ via ext_of_forall_integral_eq_of_IsFiniteMeasure
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let fc : C(AddCircle (1 : ℝ), ℂ) := ⟨fun z => Complex.ofReal (f z), Complex.continuous_ofReal.comp f.continuous⟩
  have hceq := hcont fc
  have h1 : ∫ z, fc z ∂ρ₁ = Complex.ofReal (∫ z, f z ∂ρ₁) := integral_ofReal
  have h2 : ∫ z, fc z ∂ρ₂ = Complex.ofReal (∫ z, f z ∂ρ₂) := integral_ofReal
  rw [h1, h2] at hceq
  exact Complex.ofReal_injective hceq

/-- Measurability of the section `AddCircle 1 → ℝ` landing in `[a, a + 1)`. -/
lemma measurable_coe_equivIco (a : ℝ) :
    Measurable (fun z : AddCircle (1 : ℝ) => (AddCircle.equivIco (1 : ℝ) a z : ℝ)) := by
  have : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩
  apply measurable_of_Iio
  intro t
  set f : AddCircle (1 : ℝ) → ℝ := fun z => (AddCircle.equivIco (1 : ℝ) a z : ℝ)
  by_cases ht1 : t ≤ a
  · have : f ⁻¹' Set.Iio t = ∅ := by
      ext z; simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
      exact le_trans ht1 (AddCircle.equivIco (1 : ℝ) a z).2.1
    rw [this]; exact MeasurableSet.empty
  · by_cases ht2 : a + 1 ≤ t
    · have : f ⁻¹' Set.Iio t = Set.univ := by
        ext z; simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_univ, iff_true]
        exact lt_of_lt_of_le (AddCircle.equivIco (1 : ℝ) a z).2.2 ht2
      rw [this]; exact MeasurableSet.univ
    · push Not at ht1 ht2
      have hpre : f ⁻¹' Set.Iio t = {(a : AddCircle (1 : ℝ))} ∪
          ((QuotientAddGroup.mk : ℝ → AddCircle (1 : ℝ)) '' Set.Ioo a t) := by
        ext z
        simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_union, Set.mem_singleton_iff,
          Set.mem_image, Set.mem_Ioo]
        constructor
        · intro hz
          set x : ℝ := (AddCircle.equivIco (1 : ℝ) a z : ℝ)
          have hx_mem : x ∈ Set.Ico a (a + 1) := (AddCircle.equivIco (1 : ℝ) a z).2
          have hzx : (x : AddCircle (1 : ℝ)) = z :=
            (AddCircle.equivIco (1 : ℝ) a).symm_apply_apply z
          rcases eq_or_lt_of_le hx_mem.1 with hxa | hxa
          · left; rw [← hzx, hxa]
          · right; exact ⟨x, ⟨hxa, hz⟩, hzx⟩
        · rintro (rfl | ⟨x, ⟨hx1, hx2⟩, rfl⟩)
          · have hmem : a ∈ Set.Ico a (a + 1) := ⟨le_rfl, by linarith⟩
            have heq : f (a : AddCircle (1 : ℝ)) = a := by
              simp only [f]; exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hmem)
            rw [heq]; exact ht1
          · have hmem : x ∈ Set.Ico a (a + 1) := ⟨le_of_lt hx1, lt_trans hx2 ht2⟩
            have heq : f (x : AddCircle (1 : ℝ)) = x := by
              simp only [f]; exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hmem)
            rw [heq]; exact hx2
      rw [hpre]
      apply MeasurableSet.union (measurableSet_singleton _)
      exact (QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo).measurableSet

/-- **Consequence 1a:** A probability measure supported on `[-1/2, 1/2]` whose integer Fourier
coefficients vanish for all `k ≠ 0` equals `lebHalf`. -/
theorem eq_lebHalf_of_ft_int {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hsupp : IsSupportedIn σ (Set.Icc (-(1 / 2)) (1 / 2)))
    (hzero : ∀ k : ℤ, k ≠ 0 → ft σ k = 0) : σ = lebHalf := by
  have : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩
  let q : ℝ → AddCircle (1 : ℝ) := QuotientAddGroup.mk
  have hq_meas : Measurable q := QuotientAddGroup.continuous_mk.measurable
  have hmap_eq : σ.map q = lebHalf.map q := by
    apply addCircle_measure_ext_of_fourier
    intro k
    have hint : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ],
        ∫ z, fourier k z ∂(ρ.map q) = ft ρ (-k) := by
      intro ρ _
      rw [integral_map hq_meas.aemeasurable (fourier k).continuous.aestronglyMeasurable,
          ft_apply]
      congr 1; ext x
      change fourier k (x : AddCircle (1 : ℝ)) = _
      rw [fourier_coe_apply]
      congr 1; push_cast; ring
    rw [hint σ, hint lebHalf]
    by_cases hk : k = 0
    · subst hk; simp [ft_zero]
    · have hnk : (-k : ℤ) ≠ 0 := neg_ne_zero.mpr hk
      have hcast_neg : -(k : ℝ) = ((-k : ℤ) : ℝ) := by push_cast; rfl
      rw [hcast_neg, hzero (-k) hnk, ft_lebHalf]
      have hne_r : ((-k : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hnk
      simp only [hne_r, ↓reduceIte]
      have hsin0 : Real.sin (Real.pi * ((-k : ℤ) : ℝ)) = 0 := by
        rw [mul_comm]; exact Real.sin_int_mul_pi (-k)
      rw [hsin0, zero_div, Complex.ofReal_zero]
  -- Both σ and lebHalf assign mass 0 to {1/2}, hence live on Ico (-1/2) (1/2)
  have hhalf_zero : σ {1 / 2} = 0 := by
    have hsub : ({1 / 2} : Set ℝ) ⊆ q ⁻¹' {q (1 / 2)} := fun x hx => by
      simp only [Set.mem_singleton_iff] at hx; subst hx; exact Set.mem_singleton _
    have h1 : (σ.map q) {q (1 / 2)} = (lebHalf.map q) {q (1 / 2)} := by rw [hmap_eq]
    rw [Measure.map_apply hq_meas (measurableSet_singleton _),
        Measure.map_apply hq_meas (measurableSet_singleton _)] at h1
    have hleb0 : lebHalf (q ⁻¹' {q (1 / 2)}) = 0 := by
      rw [lebHalf, Measure.restrict_apply (hq_meas (measurableSet_singleton _))]
      have hsub2 : q ⁻¹' {q (1 / 2)} ∩ Set.Icc (-(1 / 2)) (1 / 2) ⊆ {-(1 / 2), 1 / 2} := by
        intro x ⟨hxq, hx1, hx2⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff, q] at hxq
        rw [QuotientAddGroup.eq] at hxq
        simp only [AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul, mul_one] at hxq
        rcases hxq with ⟨m, hm⟩
        have hm_range : -1 ≤ m ∧ m ≤ 1 := by
          have : -(1 : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ 1 := by constructor <;> linarith
          exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        have : m = -1 ∨ m = 0 ∨ m = 1 := by omega
        rcases this with rfl | rfl | rfl <;> push_cast at hm
        · right; linarith
        · right; linarith
        · left; linarith
      exact measure_mono_null hsub2 (Set.Finite.measure_zero (Set.toFinite _) volume)
    exact measure_mono_null hsub (h1.trans hleb0)
  have hσ_Ico : σ (Set.Ico (-(1 / 2)) (-(1 / 2) + 1))ᶜ = 0 := by
    have hsub : (Set.Ico (-(1 / 2 : ℝ)) (-(1 / 2) + 1))ᶜ ⊆ (Set.Icc (-(1 / 2)) (1 / 2))ᶜ ∪ {1 / 2} := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_Ico, Set.mem_union, Set.mem_Icc, Set.mem_singleton_iff] at hx ⊢
      by_cases h1 : -(1 / 2 : ℝ) ≤ x ∧ x ≤ 1 / 2
      · right; have : ¬ x < 1 / 2 := fun hlt => hx ⟨h1.1, by linarith⟩; linarith
      · left; exact h1
    exact measure_mono_null hsub (measure_union_null hsupp hhalf_zero)
  have hleb_Ico : lebHalf (Set.Ico (-(1 / 2)) (-(1 / 2) + 1))ᶜ = 0 := by
    have hsub : (Set.Ico (-(1 / 2 : ℝ)) (-(1 / 2) + 1))ᶜ ⊆ (Set.Icc (-(1 / 2)) (1 / 2))ᶜ ∪ {1 / 2} := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_Ico, Set.mem_union, Set.mem_Icc, Set.mem_singleton_iff] at hx ⊢
      by_cases h1 : -(1 / 2 : ℝ) ≤ x ∧ x ≤ 1 / 2
      · right; have : ¬ x < 1 / 2 := fun hlt => hx ⟨h1.1, by linarith⟩; linarith
      · left; exact h1
    exact measure_mono_null hsub (measure_union_null lebHalf_supported
      (by rw [lebHalf, Measure.restrict_apply (measurableSet_singleton _)]; exact measure_mono_null Set.inter_subset_left (measure_singleton _)))
  -- Push back via equivIco 1 (-1/2)
  let ι : AddCircle (1 : ℝ) → ℝ := fun z => (AddCircle.equivIco (1 : ℝ) (-(1 / 2)) z : ℝ)
  have hι_meas : Measurable ι := measurable_coe_equivIco (-(1 / 2))
  have hpull : ∀ (ρ : Measure ℝ), ρ (Set.Ico (-(1 / 2)) (-(1 / 2) + 1))ᶜ = 0 →
      (ρ.map q).map ι = ρ := by
    intro ρ hρ
    rw [Measure.map_map hι_meas hq_meas]
    have hae : ι ∘ q =ᵐ[ρ] id := by
      have hmem : ∀ᵐ x ∂ρ, x ∈ Set.Ico (-(1 / 2 : ℝ)) (-(1 / 2) + 1) := by rw [ae_iff]; exact hρ
      filter_upwards [hmem] with x hx
      simp only [Function.comp_apply, id_eq, ι, q]
      exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hx)
    rw [Measure.map_congr hae, Measure.map_id]
  rw [← hpull σ hσ_Ico, ← hpull lebHalf hleb_Ico, hmap_eq]

/-- **Consequence 1b (Periodicity without tempered distributions):**
If a probability measure `μ` supported on `[0, 1)` satisfies `ft μ k = 0` whenever `¬ (N ∣ k)`
(with integer `N ≥ 2`), then `μ = unifDiscrete N (1 / N) ∗ α₁`, where
`α₁ = N • μ.restrict [0, 1 / N)` is a probability measure supported on `[0, 1 / N]`. -/
theorem periodic_decomp_of_ft_div {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 2 ≤ N)
    (hsupp : IsSupportedIn μ (Set.Ico (0 : ℝ) 1))
    (hdiv : ∀ k : ℤ, ¬ ((N : ℤ) ∣ k) → ft μ k = 0) :
    let α₁ : Measure ℝ := (N : ℝ≥0∞) • μ.restrict (Set.Ico (0 : ℝ) (1 / (N : ℝ)))
    IsProbabilityMeasure α₁ ∧
    IsSupportedIn α₁ (Set.Icc (0 : ℝ) (1 / (N : ℝ))) ∧
    μ = unifDiscrete N (1 / (N : ℝ)) ∗ α₁ := by
  intro α₁
  have : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  let q : ℝ → AddCircle (1 : ℝ) := QuotientAddGroup.mk
  have hq_meas : Measurable q := QuotientAddGroup.continuous_mk.measurable
  -- Show μ.map q is invariant under translation by q(j / N) for every j : ℕ
  have htrans : ∀ j : ℕ, (μ.map q).map (fun z => z + q ((j : ℝ) / (N : ℝ))) = μ.map q := by
    intro j
    apply addCircle_measure_ext_of_fourier
    intro k
    rw [integral_map (measurable_add_const _).aemeasurable (fourier k).continuous.aestronglyMeasurable]
    have hfun : (fun z : AddCircle (1 : ℝ) => fourier k (z + q ((j : ℝ) / (N : ℝ)))) =
        (fun z => fourier k (q ((j : ℝ) / (N : ℝ))) * fourier k z) := by
      ext z
      rw [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul, mul_comm]
      rfl
    rw [hfun, integral_const_mul]
    have hval : ∫ z, fourier k z ∂(μ.map q) = ft μ (-k) := by
      rw [integral_map hq_meas.aemeasurable (fourier k).continuous.aestronglyMeasurable, ft_apply]
      congr 1; ext x
      change fourier k (x : AddCircle (1 : ℝ)) = _
      rw [fourier_coe_apply]
      congr 1; push_cast; ring
    by_cases hd : (N : ℤ) ∣ k
    · rcases hd with ⟨m, rfl⟩
      have hphase : fourier ((N : ℤ) * m) (q ((j : ℝ) / (N : ℝ))) = 1 := by
        change fourier ((N : ℤ) * m) (((j : ℝ) / (N : ℝ) : ℝ) : AddCircle (1 : ℝ)) = 1
        rw [fourier_coe_apply]
        have harg : (2 * Real.pi * Complex.I * (((N : ℤ) * m : ℤ) : ℂ) * (((j : ℝ) / (N : ℝ) : ℝ) : ℂ) / (1 : ℝ)) =
            ((m * (j : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
          have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          push_cast; field_simp
        rw [harg, Complex.exp_int_mul_two_pi_mul_I]
      rw [hphase, one_mul]
    · have hnd : ¬ ((N : ℤ) ∣ -k) := fun h => hd (dvd_neg.mp h)
      have hcast_neg : -(k : ℝ) = ((-k : ℤ) : ℝ) := by push_cast; rfl
      rw [hval, hcast_neg, hdiv (-k) hnd, mul_zero]
  -- Translate equality on [0, 1) via equivIco 1 0
  let ι : AddCircle (1 : ℝ) → ℝ := fun z => (AddCircle.equivIco (1 : ℝ) 0 z : ℝ)
  have hι_meas : Measurable ι := measurable_coe_equivIco 0
  have hμ_pull : (μ.map q).map ι = μ := by
    rw [Measure.map_map hι_meas hq_meas]
    have hae : ι ∘ q =ᵐ[μ] id := by
      have hmem : ∀ᵐ x ∂μ, x ∈ Set.Ico (0 : ℝ) (0 + 1) := by rw [ae_iff, zero_add]; exact hsupp
      filter_upwards [hmem] with x hx
      simp only [Function.comp_apply, id_eq, ι, q]
      exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hx)
    rw [Measure.map_congr hae, Measure.map_id]
  -- For every j < N and measurable E ⊆ [0, 1/N), μ((· + j/N) '' E) = μ E
  have hshift_eq : ∀ j < N, ∀ s : Set ℝ, MeasurableSet s →
      μ ((fun x => x + (j : ℝ) * (1 / (N : ℝ))) ⁻¹' s ∩ Set.Ico 0 (1 / (N : ℝ))) =
      μ (s ∩ Set.Ico ((j : ℝ) * (1 / (N : ℝ))) (((j : ℕ) + 1 : ℝ) * (1 / (N : ℝ)))) := by
    intro j hj s hs
    have h1 := congrArg (fun ρ : Measure (AddCircle (1 : ℝ)) =>
      (ρ.map ι) (s ∩ Set.Ico ((j : ℝ) * (1 / (N : ℝ))) (((j : ℕ) + 1 : ℝ) * (1 / (N : ℝ)))))
      (htrans j)
    rw [hμ_pull] at h1
    rw [← h1]
    set Ij := Set.Ico ((j : ℝ) * (1 / (N : ℝ))) (((j : ℕ) + 1 : ℝ) * (1 / (N : ℝ)))
    have hIj_meas : MeasurableSet Ij := measurableSet_Ico
    rw [Measure.map_apply hι_meas (hs.inter hIj_meas),
        Measure.map_apply (measurable_add_const _) (hι_meas (hs.inter hIj_meas)),
        Measure.map_apply hq_meas ((measurable_add_const _).comp hq_meas (hι_meas (hs.inter hIj_meas)))]
    -- Compare preimages inside [0, 1)
    have hsymm : μ (q ⁻¹' ((fun z => z + q ((j : ℝ) / (N : ℝ))) ⁻¹' (ι ⁻¹' (s ∩ Ij)))) =
        μ (q ⁻¹' ((fun z => z + q ((j : ℝ) / (N : ℝ))) ⁻¹' (ι ⁻¹' (s ∩ Ij))) ∩ Set.Ico 0 1) := by
      have hsp := measure_inter_add_sdiff
        (q ⁻¹' ((fun z => z + q ((j : ℝ) / (N : ℝ))) ⁻¹' (ι ⁻¹' (s ∩ Ij))))
        (measurableSet_Ico : MeasurableSet (Set.Ico (0 : ℝ) 1)) (μ := μ)
      have hd : μ (q ⁻¹' ((fun z => z + q ((j : ℝ) / (N : ℝ))) ⁻¹' (ι ⁻¹' (s ∩ Ij))) \ Set.Ico 0 1) = 0 :=
        measure_mono_null (fun _ hx => hx.2) hsupp
      rw [hd, add_zero] at hsp
      exact hsp.symm
    rw [hsymm]
    congr 1; ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ico, Ij]
    constructor
    · rintro ⟨hx1, hx2, hx3⟩
      have hxj_mem : x + (j : ℝ) / (N : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1) := by
        simp only [Set.mem_Ico, zero_add]
        have hj_le : ((j : ℝ) + 1) ≤ (N : ℝ) := by exact_mod_cast (show j + 1 ≤ N by omega)
        constructor
        · positivity
        · have : (j : ℝ) / (N : ℝ) + 1 / (N : ℝ) ≤ 1 := by
            rw [← add_div, div_le_one hNpos]; linarith
          linarith
      have hι_eq : ι (q x + q ((j : ℝ) / (N : ℝ))) = x + (j : ℝ) / (N : ℝ) := by
        have hqadd : q x + q ((j : ℝ) / (N : ℝ)) = q (x + (j : ℝ) / (N : ℝ)) := rfl
        rw [hqadd]
        exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hxj_mem)
      rw [hι_eq]
      have hdiv_eq : (j : ℝ) * (1 / (N : ℝ)) = (j : ℝ) / (N : ℝ) := by ring
      have hdiv_eq2 : ((j : ℝ) + 1) * (1 / (N : ℝ)) = (j : ℝ) / (N : ℝ) + 1 / (N : ℝ) := by ring
      rw [hdiv_eq] at hx1
      refine ⟨⟨hx1, by rw [hdiv_eq]; linarith, by rw [hdiv_eq2]; linarith⟩, hx2, ?_⟩
      have : (1 : ℝ) / (N : ℝ) ≤ 1 := by rw [div_le_one hNpos]; exact_mod_cast (show 1 ≤ N by omega)
      linarith
    · rintro ⟨⟨hs_in, hlo, hhi⟩, hx0, hx1⟩
      -- Note: if x ∈ [0, 1) and ι(q(x + j/N)) ∈ [j/N, (j+1)/N), then x ∈ [0, 1/N) and x + j/N = ι(q(x + j/N))
      have hdiv_eq : (j : ℝ) * (1 / (N : ℝ)) = (j : ℝ) / (N : ℝ) := by ring
      have hdiv_eq2 : ((j : ℝ) + 1) * (1 / (N : ℝ)) = (j : ℝ) / (N : ℝ) + 1 / (N : ℝ) := by ring
      set y := ι (q x + q ((j : ℝ) / (N : ℝ)))
      have hy_mem : y ∈ Set.Ico (0 : ℝ) 1 := by
        have := (AddCircle.equivIco (1 : ℝ) 0 (q x + q ((j : ℝ) / (N : ℝ)))).2
        simpa [y, ι] using this
      have hqy : q y = q (x + (j : ℝ) / (N : ℝ)) :=
        (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply (q x + q ((j : ℝ) / (N : ℝ)))
      rw [QuotientAddGroup.eq] at hqy
      simp only [AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul, mul_one] at hqy
      rcases hqy with ⟨m, hm⟩
      -- x + j/N ∈ [0, 2) and y ∈ [j/N, (j+1)/N) ⊆ [0, 1)
      have hj_nn : (0 : ℝ) ≤ (j : ℝ) / (N : ℝ) := by positivity
      have hj_lt : (j : ℝ) / (N : ℝ) < 1 := by
        rw [div_lt_one hNpos]; exact_mod_cast hj
      have hy0 : 0 ≤ y := hy_mem.1
      have hy1 : y < 1 := hy_mem.2
      have hm_01 : m = 0 ∨ m = 1 := by
        have hlo_m : -(1 : ℝ) < (m : ℝ) := by linarith
        have hhi_m : (m : ℝ) < 2 := by linarith
        have h1 : (-1 : ℤ) < m := by exact_mod_cast hlo_m
        have h2 : m < (2 : ℤ) := by exact_mod_cast hhi_m
        omega
      rcases hm_01 with rfl | rfl
      · push_cast at hm
        have hy_eq : y = x + (j : ℝ) / (N : ℝ) := by linarith
        rw [hy_eq] at hs_in hlo hhi
        rw [hdiv_eq] at hlo ⊢
        rw [hdiv_eq2] at hhi
        exact ⟨hs_in, hx0, by linarith⟩
      · -- If m = 1, then x + j/N - y = 1, so x = 1 + y - j/N ≥ 1 + j/N - j/N = 1, contradicting x < 1!
        push_cast at hm
        rw [hdiv_eq] at hlo
        linarith
  -- Compute μ [0, 1/N) = 1 / N by summing over the N disjoint intervals [j/N, (j+1)/N)
  have hpart : ∀ s : Set ℝ, MeasurableSet s →
      μ s = ∑ j ∈ Finset.range N,
        μ (s ∩ Set.Ico ((j : ℝ) * (1 / (N : ℝ))) (((j : ℕ) + 1 : ℝ) * (1 / (N : ℝ)))) := by
    intro s hs
    have hdisj : Set.PairwiseDisjoint (↑(Finset.range N) : Set ℕ)
        (fun j => s ∩ Set.Ico ((j : ℝ) * (1 / (N : ℝ))) (((j : ℕ) + 1 : ℝ) * (1 / (N : ℝ)))) := by
      intro j₁ _ j₂ _ hne
      rw [Function.onFun, Set.disjoint_left]
      intro x hx1 hx2
      have hlt_or : j₁ < j₂ ∨ j₂ < j₁ := lt_or_gt_of_ne hne
      rcases hlt_or with hlt | hgt
      · have h1 : ((j₁ : ℝ) + 1) ≤ (j₂ : ℝ) := by exact_mod_cast (show j₁ + 1 ≤ j₂ by omega)
        have : ((j₁ : ℝ) + 1) * (1 / (N : ℝ)) ≤ (j₂ : ℝ) * (1 / (N : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        linarith [hx1.2.2, hx2.2.1]
      · have h1 : ((j₂ : ℝ) + 1) ≤ (j₁ : ℝ) := by exact_mod_cast (show j₂ + 1 ≤ j₁ by omega)
        have : ((j₂ : ℝ) + 1) * (1 / (N : ℝ)) ≤ (j₁ : ℝ) * (1 / (N : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        linarith [hx2.2.2, hx1.2.1]
    have hunion : (⋃ j ∈ Finset.range N,
        s ∩ Set.Ico ((j : ℝ) * (1 / (N : ℝ))) (((j : ℕ) + 1 : ℝ) * (1 / (N : ℝ)))) =
        s ∩ Set.Ico 0 1 := by
      ext x
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_inter_iff, Set.mem_Ico]
      constructor
      · rintro ⟨j, hj, hxs, h1, h2⟩
        have hjn : (0 : ℝ) ≤ (j : ℝ) * (1 / (N : ℝ)) := by positivity
        refine ⟨hxs, by linarith, ?_⟩
        have hj1 : ((j : ℝ) + 1) ≤ (N : ℝ) := by exact_mod_cast (show j + 1 ≤ N by omega)
        have : ((j : ℝ) + 1) * (1 / (N : ℝ)) ≤ 1 := by
          rw [mul_one_div, div_le_one hNpos]; exact hj1
        linarith
      · rintro ⟨hxs, hx0, hx1⟩
        set j := ⌊x * (N : ℝ)⌋₊
        have hj_lt : j < N := by
          rw [Nat.floor_lt (by positivity)]
          nlinarith
        have hlo : (j : ℝ) ≤ x * (N : ℝ) := Nat.floor_le (by positivity)
        have hhi : x * (N : ℝ) < (j : ℝ) + 1 := Nat.lt_floor_add_one _
        refine ⟨j, hj_lt, hxs, ?_, ?_⟩
        · rw [mul_one_div, div_le_iff₀ hNpos]; exact hlo
        · rw [mul_one_div, lt_div_iff₀ hNpos]; exact hhi
    rw [← measure_biUnion_finset hdisj (fun j _ => hs.inter measurableSet_Ico), hunion]
    have hsp := measure_inter_add_sdiff s (measurableSet_Ico : MeasurableSet (Set.Ico (0 : ℝ) 1)) (μ := μ)
    have hd : μ (s \ Set.Ico 0 1) = 0 := measure_mono_null (fun _ hx => hx.2) hsupp
    rw [hd, add_zero] at hsp
    exact hsp.symm
  have hprob_α1 : IsProbabilityMeasure α₁ := by
    constructor
    have h1 := hpart Set.univ MeasurableSet.univ
    simp only [measure_univ, Set.univ_inter] at h1
    have heach : ∀ j ∈ Finset.range N,
        μ (Set.Ico ((j : ℝ) * (1 / (N : ℝ))) (((j : ℕ) + 1 : ℝ) * (1 / (N : ℝ)))) =
        μ (Set.Ico 0 (1 / (N : ℝ))) := by
      intro j hj
      have := hshift_eq j (Finset.mem_range.mp hj) Set.univ MeasurableSet.univ
      simpa using this.symm
    rw [Finset.sum_congr rfl heach, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    rw [show α₁ Set.univ = (N : ℝ≥0∞) * μ (Set.Ico 0 (1 / (N : ℝ))) by simp [α₁]]
    exact h1.symm
  have hsupp_α1 : IsSupportedIn α₁ (Set.Icc 0 (1 / (N : ℝ))) := by
    unfold IsSupportedIn
    simp only [α₁, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply measurableSet_Icc.compl]
    have hsub : (Set.Icc (0 : ℝ) (1 / (N : ℝ)))ᶜ ∩ Set.Ico 0 (1 / (N : ℝ)) = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_Icc, Set.mem_Ico,
        Set.mem_empty_iff_false, iff_false]; rintro ⟨h1, h2, h3⟩; exact h1 ⟨h2, le_of_lt h3⟩
    rw [hsub, measure_empty, mul_zero]
  have hconv_eq : μ = unifDiscrete N (1 / (N : ℝ)) ∗ α₁ := by
    ext s hs
    rw [hpart s hs]
    unfold unifDiscrete
    rw [Measure.conv_smul_left, Measure.smul_apply, smul_eq_mul]
    have hsum_conv : (∑ j ∈ Finset.range N, Measure.dirac ((j : ℝ) * (1 / (N : ℝ)))) ∗ α₁ =
        ∑ j ∈ Finset.range N, Measure.dirac ((j : ℝ) * (1 / (N : ℝ))) ∗ α₁ := by
      clear hpart hshift_eq hprob_α1 hsupp_α1
      induction Finset.range N using Finset.induction_on with
      | empty => simp
      | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.add_conv, ih]
    rw [hsum_conv, Measure.finsetSum_apply]
    have hterm : ∀ j ∈ Finset.range N,
        (Measure.dirac ((j : ℝ) * (1 / (N : ℝ))) ∗ α₁) s =
        (N : ℝ≥0∞) * μ (s ∩ Set.Ico ((j : ℝ) * (1 / (N : ℝ))) (((j : ℕ) + 1 : ℝ) * (1 / (N : ℝ)))) := by
      intro j hj
      rw [Measure.dirac_conv, Measure.map_apply (measurable_const_add _) hs]
      simp only [α₁, Measure.smul_apply, smul_eq_mul,
        Measure.restrict_apply ((measurable_const_add _) hs)]
      congr 1
      have hcomm : (fun y : ℝ => (j : ℝ) * (1 / (N : ℝ)) + y) =
          (fun y : ℝ => y + (j : ℝ) * (1 / (N : ℝ))) := by ext y; ring
      rw [hcomm]
      exact hshift_eq j (Finset.mem_range.mp hj) s hs
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← mul_assoc,
        ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr (by omega)) (ENNReal.natCast_ne_top N), one_mul]
  exact ⟨hprob_α1, hsupp_α1, hconv_eq⟩

/-! ### Support Endpoints and Lemma `lem01` (Disjoint Zeros + Symmetry) -/

/-- Support endpoint addition for compactly supported probability measures convolving to `lebHalf`
(or any interval `[L, R]`). -/
lemma support_endpoints_of_conv_lebHalf {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hconv : μ ∗ ν = lebHalf) :
    BddBelow μ.support ∧ BddAbove μ.support ∧ BddBelow ν.support ∧ BddAbove ν.support ∧
    sInf μ.support + sInf ν.support = -(1 / 2) ∧
    sSup μ.support + sSup ν.support = 1 / 2 := by
  have hμne : μ.support.Nonempty := Measure.nonempty_support (IsProbabilityMeasure.ne_zero μ)
  have hνne : ν.support.Nonempty := Measure.nonempty_support (IsProbabilityMeasure.ne_zero ν)
  -- Every x ∈ μ.support and y ∈ ν.support satisfies x + y ∈ [-1/2, 1/2]
  have hsum_in : ∀ x ∈ μ.support, ∀ y ∈ ν.support, x + y ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    intro x hx y hy
    by_contra hnot
    have hopen : IsOpen (Set.Icc (-(1 / 2 : ℝ)) (1 / 2))ᶜ := isClosed_Icc.isOpen_compl
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen (x + y) hnot
    have hμpos : 0 < μ (Metric.ball x (ε / 2)) :=
      (Measure.mem_support_iff_forall x).mp hx _ (Metric.ball_mem_nhds x (half_pos hε))
    have hνpos : 0 < ν (Metric.ball y (ε / 2)) :=
      (Measure.mem_support_iff_forall y).mp hy _ (Metric.ball_mem_nhds y (half_pos hε))
    have hconv_pos : 0 < (μ ∗ ν) (Set.Icc (-(1 / 2 : ℝ)) (1 / 2))ᶜ := by
      rw [Measure.conv, Measure.map_apply measurable_add hopen.measurableSet]
      have hsub : Metric.ball x (ε / 2) ×ˢ Metric.ball y (ε / 2) ⊆
          (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' (Set.Icc (-(1 / 2 : ℝ)) (1 / 2))ᶜ := by
        rintro ⟨u, v⟩ ⟨hu, hv⟩
        apply hball
        rw [Metric.mem_ball, Real.dist_eq] at hu hv ⊢
        calc |u + v - (x + y)| = |(u - x) + (v - y)| := by ring_nf
          _ ≤ |u - x| + |v - y| := abs_add_le _ _
          _ < ε / 2 + ε / 2 := add_lt_add hu hv
          _ = ε := add_halves ε
      calc
        0 < μ (Metric.ball x (ε / 2)) * ν (Metric.ball y (ε / 2)) := ENNReal.mul_pos hμpos.ne' hνpos.ne'
        _ = (μ.prod ν) (Metric.ball x (ε / 2) ×ˢ Metric.ball y (ε / 2)) := (Measure.prod_prod _ _).symm
        _ ≤ (μ.prod ν) ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' (Set.Icc (-(1 / 2 : ℝ)) (1 / 2))ᶜ) :=
              measure_mono hsub
    rw [hconv] at hconv_pos
    have h0 : lebHalf (Set.Icc (-(1 / 2 : ℝ)) (1 / 2))ᶜ = 0 := lebHalf_supported
    rw [h0] at hconv_pos
    exact lt_irrefl 0 hconv_pos
  rcases hμne with ⟨x₀, hx₀⟩
  rcases hνne with ⟨y₀, hy₀⟩
  have hμ_bb : BddBelow μ.support := ⟨-(1 / 2) - y₀, fun x hx => by linarith [(hsum_in x hx y₀ hy₀).1]⟩
  have hμ_ba : BddAbove μ.support := ⟨1 / 2 - y₀, fun x hx => by linarith [(hsum_in x hx y₀ hy₀).2]⟩
  have hν_bb : BddBelow ν.support := ⟨-(1 / 2) - x₀, fun y hy => by linarith [(hsum_in x₀ hx₀ y hy).1]⟩
  have hν_ba : BddAbove ν.support := ⟨1 / 2 - x₀, fun y hy => by linarith [(hsum_in x₀ hx₀ y hy).2]⟩
  -- Since μ.support is closed and nonempty, inf/sup lie in the support!
  have hμ_inf_mem : sInf μ.support ∈ μ.support := Measure.isClosed_support.csInf_mem ⟨x₀, hx₀⟩ hμ_bb
  have hμ_sup_mem : sSup μ.support ∈ μ.support := Measure.isClosed_support.csSup_mem ⟨x₀, hx₀⟩ hμ_ba
  have hν_inf_mem : sInf ν.support ∈ ν.support := Measure.isClosed_support.csInf_mem ⟨y₀, hy₀⟩ hν_bb
  have hν_sup_mem : sSup ν.support ∈ ν.support := Measure.isClosed_support.csSup_mem ⟨y₀, hy₀⟩ hν_ba
  have hinf_ge : -(1 / 2 : ℝ) ≤ sInf μ.support + sInf ν.support := (hsum_in _ hμ_inf_mem _ hν_inf_mem).1
  have hsup_le : sSup μ.support + sSup ν.support ≤ 1 / 2 := (hsum_in _ hμ_sup_mem _ hν_sup_mem).2
  -- Conversely, μ∗ν is supported in [sInf μ + sInf ν, sSup μ + sSup ν]
  have hconv_supp : (μ ∗ ν) (Set.Icc (sInf μ.support + sInf ν.support) (sSup μ.support + sSup ν.support))ᶜ = 0 := by
    rw [Measure.conv, Measure.map_apply measurable_add measurableSet_Icc.compl]
    have hsub : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹'
        (Set.Icc (sInf μ.support + sInf ν.support) (sSup μ.support + sSup ν.support))ᶜ ⊆
        (μ.supportᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ ν.supportᶜ) := by
      rintro ⟨x, y⟩ hxy
      by_contra hnot
      simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff, Set.mem_univ, and_true, true_and,
        not_or, not_not] at hnot
      exact hxy ⟨add_le_add (csInf_le hμ_bb hnot.1) (csInf_le hν_bb hnot.2),
                 add_le_add (le_csSup hμ_ba hnot.1) (le_csSup hν_ba hnot.2)⟩
    apply measure_mono_null hsub
    refine measure_union_null ?_ ?_
    · rw [Measure.prod_prod, Measure.measure_compl_support, zero_mul]
    · rw [Measure.prod_prod, Measure.measure_compl_support, mul_zero]
  rw [hconv] at hconv_supp
  have hinf_le : sInf μ.support + sInf ν.support ≤ -(1 / 2) := by
    by_contra hgt; push Not at hgt
    have hsub : Set.Ioo (-(1 / 2 : ℝ)) (min (1 / 2) (sInf μ.support + sInf ν.support)) ⊆
        (Set.Icc (sInf μ.support + sInf ν.support) (sSup μ.support + sSup ν.support))ᶜ := by
      intro x hx; simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le]
      left; exact lt_of_lt_of_le hx.2 (min_le_right _ _)
    have hpos : 0 < lebHalf (Set.Ioo (-(1 / 2 : ℝ)) (min (1 / 2) (sInf μ.support + sInf ν.support))) := by
      rw [lebHalf, Measure.restrict_apply measurableSet_Ioo]
      have hinter : Set.Ioo (-(1 / 2 : ℝ)) (min (1 / 2) (sInf μ.support + sInf ν.support)) ∩ Set.Icc (-(1 / 2)) (1 / 2) =
          Set.Ioo (-(1 / 2 : ℝ)) (min (1 / 2) (sInf μ.support + sInf ν.support)) := by
        apply Set.inter_eq_left.mpr; intro x hx
        exact ⟨le_of_lt hx.1, le_of_lt (lt_of_lt_of_le hx.2 (min_le_left _ _))⟩
      rw [hinter, Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by rw [sub_pos, lt_min_iff]; exact ⟨by norm_num, hgt⟩)
    exact lt_irrefl 0 (hpos.trans_eq (measure_mono_null hsub hconv_supp))
  have hsup_ge : 1 / 2 ≤ sSup μ.support + sSup ν.support := by
    by_contra hlt; push Not at hlt
    have hsub : Set.Ioo (max (-(1 / 2 : ℝ)) (sSup μ.support + sSup ν.support)) (1 / 2) ⊆
        (Set.Icc (sInf μ.support + sInf ν.support) (sSup μ.support + sSup ν.support))ᶜ := by
      intro x hx; simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le]
      right; exact lt_of_le_of_lt (le_max_right _ _) hx.1
    have hpos : 0 < lebHalf (Set.Ioo (max (-(1 / 2 : ℝ)) (sSup μ.support + sSup ν.support)) (1 / 2)) := by
      rw [lebHalf, Measure.restrict_apply measurableSet_Ioo]
      have hinter : Set.Ioo (max (-(1 / 2 : ℝ)) (sSup μ.support + sSup ν.support)) (1 / 2) ∩ Set.Icc (-(1 / 2)) (1 / 2) =
          Set.Ioo (max (-(1 / 2 : ℝ)) (sSup μ.support + sSup ν.support)) (1 / 2) := by
        apply Set.inter_eq_left.mpr; intro x hx
        exact ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hx.1), le_of_lt hx.2⟩
      rw [hinter, Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by rw [sub_pos, max_lt_iff]; exact ⟨by norm_num, hlt⟩)
    exact lt_irrefl 0 (hpos.trans_eq (measure_mono_null hsub hconv_supp))
  exact ⟨hμ_bb, hμ_ba, hν_bb, hν_ba, le_antisymm hinf_le hinf_ge, le_antisymm hsup_le hsup_ge⟩

/-- **Gabardo–Lai Lemma 2.1 (`lem01`):**
If `μ ∗ ν = lebHalf` and the smallest closed interval containing `μ.support` is `[-a, a]`
with `0 ≤ a ≤ 1/2`, then:
1. For every `k : ℤ` with `k ≠ 0`, `ft μ k = 0` or `ft ν k = 0`, and NOT both;
2. The smallest closed interval containing `ν.support` is `[-b, b]` with `b = 1/2 - a`;
3. Both measures are symmetric: `checkMeasure μ = μ` and `checkMeasure ν = ν`. -/
theorem gabardo_lai_lem01 {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : ℝ} (ha0 : 0 ≤ a) (ha_half : a ≤ 1 / 2)
    (hconv : μ ∗ ν = lebHalf)
    (hinf_μ : sInf μ.support = -a) (hsup_μ : sSup μ.support = a) :
    (∀ k : ℤ, k ≠ 0 → (ft μ k = 0 ∨ ft ν k = 0) ∧ ¬ (ft μ k = 0 ∧ ft ν k = 0)) ∧
    sInf ν.support = -(1 / 2 - a) ∧ sSup ν.support = 1 / 2 - a ∧
    checkMeasure μ = μ ∧ checkMeasure ν = ν := by
  rcases support_endpoints_of_conv_lebHalf hconv with ⟨hμ_bb, hμ_ba, hν_bb, hν_ba, hinf_sum, hsup_sum⟩
  set b := 1 / 2 - a with hb_eq
  have hb0 : 0 ≤ b := by linarith
  have hinf_ν : sInf ν.support = -b := by linarith
  have hsup_ν : sSup ν.support = b := by linarith
  have hμ_supp : IsSupportedIn μ (Set.Icc (-a) a) := by
    have hsub : μ.support ⊆ Set.Icc (-a) a := fun x hx =>
      ⟨hinf_μ ▸ csInf_le hμ_bb hx, hsup_μ ▸ le_csSup hμ_ba hx⟩
    exact measure_mono_null (Set.compl_subset_compl.mpr hsub) Measure.measure_compl_support
  have hν_supp : IsSupportedIn ν (Set.Icc (-b) b) := by
    have hsub : ν.support ⊆ Set.Icc (-b) b := fun y hy =>
      ⟨hinf_ν ▸ csInf_le hν_bb hy, hsup_ν ▸ le_csSup hν_ba hy⟩
    exact measure_mono_null (Set.compl_subset_compl.mpr hsub) Measure.measure_compl_support
  -- Disjoint integer zeros by differentiating ft μ ξ * ft ν ξ = ft lebHalf ξ at ξ = k ≠ 0
  have hdisj : ∀ k : ℤ, k ≠ 0 → (ft μ k = 0 ∨ ft ν k = 0) ∧ ¬ (ft μ k = 0 ∧ ft ν k = 0) := by
    intro k hk
    have hprod_eq : ∀ ξ : ℝ, ft μ ξ * ft ν ξ = ft lebHalf ξ := fun ξ => by
      rw [← ft_conv, hconv]
    have hprod_k : ft μ k * ft ν k = 0 := by
      rw [hprod_eq k, ft_lebHalf]
      have hkr : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
      simp only [hkr, ↓reduceIte]
      have hsin0 : Real.sin (Real.pi * (k : ℝ)) = 0 := by rw [mul_comm]; exact Real.sin_int_mul_pi k
      simp [hsin0]
    refine ⟨mul_eq_zero.mp hprod_k, ?_⟩
    rintro ⟨hμk, hνk⟩
    have hdμ := hasDerivAt_ft ha0 hμ_supp (k : ℝ)
    have hdν := hasDerivAt_ft hb0 hν_supp (k : ℝ)
    have hd_prod := hdμ.mul hdν
    rw [hμk, hνk, zero_mul, mul_zero, add_zero] at hd_prod
    have hd_lhs : HasDerivAt (ft lebHalf) 0 (k : ℝ) := by
      convert hd_prod using 1; ext ξ; exact (hprod_eq ξ).symm
    -- Meanwhile, derivative of sin(πξ)/(πξ) at ξ = k ≠ 0 is cos(πk) / k ≠ 0
    have hkr : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have hsin_d : HasDerivAt (fun ξ : ℝ => Real.sin (Real.pi * ξ) / (Real.pi * ξ))
        (Real.cos (Real.pi * k) / (k : ℝ)) (k : ℝ) := by
      have h1 : HasDerivAt (fun ξ : ℝ => Real.pi * ξ) Real.pi (k : ℝ) := by
        simpa using (hasDerivAt_id (k : ℝ)).const_mul Real.pi
      have h2 : HasDerivAt (fun ξ : ℝ => Real.sin (Real.pi * ξ)) (Real.cos (Real.pi * k) * Real.pi) (k : ℝ) :=
        h1.sin
      have h3 := h2.div h1 (mul_ne_zero Real.pi_ne_zero hkr)
      have hsin0 : Real.sin (Real.pi * k) = 0 := by rw [mul_comm]; exact Real.sin_int_mul_pi k
      rw [hsin0, zero_mul, sub_zero] at h3
      convert h3 using 1
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
    have hd_rhs : HasDerivAt (ft lebHalf) (Complex.ofReal (Real.cos (Real.pi * k) / (k : ℝ))) (k : ℝ) := by
      have hloc : ft lebHalf =ᶠ[𝓝 (k : ℝ)] (fun ξ : ℝ => Complex.ofRealCLM (Real.sin (Real.pi * ξ) / (Real.pi * ξ))) := by
        filter_upwards [isOpen_ne.mem_nhds hkr] with ξ hξ
        simp only [ft_lebHalf, hξ, ↓reduceIte, Complex.ofRealCLM_apply]
      have hd_comp := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (k : ℝ) hsin_d
      exact hd_comp.congr_of_eventuallyEq hloc
    have heq0 : Complex.ofReal (Real.cos (Real.pi * k) / (k : ℝ)) = 0 :=
      hd_rhs.unique hd_lhs
    have heq0_r : Real.cos (Real.pi * k) / (k : ℝ) = 0 := Complex.ofReal_eq_zero.mp heq0
    have hcos0 : Real.cos (Real.pi * k) = 0 := (div_eq_zero_iff.mp heq0_r).resolve_right hkr
    have hsin0 : Real.sin (Real.pi * k) = 0 := by rw [mul_comm]; exact Real.sin_int_mul_pi k
    have hsq := Real.sin_sq_add_cos_sq (Real.pi * k)
    rw [hsin0, hcos0] at hsq
    norm_num at hsq
  -- Symmetry: checkMeasure μ ∗ ν = lebHalf = μ ∗ ν, hence checkMeasure μ = μ
  have hcheck_μ : checkMeasure μ = μ := by
    have hsupp_check : IsSupportedIn (checkMeasure μ ∗ ν) (Set.Icc (-(1 / 2)) (1 / 2)) := by
      unfold IsSupportedIn
      rw [Measure.conv, Measure.map_apply measurable_add measurableSet_Icc.compl]
      have hcm_supp : (checkMeasure μ) (Set.Icc (-a) a)ᶜ = 0 := by
        rw [checkMeasure, Measure.map_apply measurable_neg measurableSet_Icc.compl]
        have hpre : (fun x : ℝ => -x) ⁻¹' (Set.Icc (-a) a)ᶜ = (Set.Icc (-a) a)ᶜ := by
          ext x; simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc]
          constructor <;> intro h ⟨h1, h2⟩ <;> exact h ⟨by linarith, by linarith⟩
        rw [hpre]; exact hμ_supp
      have hsub : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' (Set.Icc (-(1 / 2 : ℝ)) (1 / 2))ᶜ ⊆
          ((Set.Icc (-a) a)ᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ (Set.Icc (-b) b)ᶜ) := by
        rintro ⟨x, y⟩ hxy
        by_contra hnot
        simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff, Set.mem_univ, and_true,
          true_and, not_or, not_not, Set.mem_Icc] at hnot
        exact hxy ⟨by linarith, by linarith⟩
      apply measure_mono_null hsub
      exact measure_union_null (by rw [Measure.prod_prod, hcm_supp, zero_mul])
        (by rw [Measure.prod_prod, hν_supp, mul_zero])
    have hcm_conv : checkMeasure μ ∗ ν = lebHalf := by
      apply eq_lebHalf_of_ft_int hsupp_check
      intro k hk
      rw [ft_conv, ft_check, ft_neg]
      rcases (hdisj k hk).1 with hμ0 | hν0
      · rw [hμ0, map_zero, zero_mul]
      · rw [hν0, mul_zero]
    apply ext_of_ft
    -- First prove equality on ℝ \ ℤ (dense), then everywhere by continuity
    have hdense : Dense {ξ : ℝ | ∀ k : ℤ, ξ ≠ (k : ℝ)} := by
      intro x
      rw [Metric.mem_closure_iff]
      intro ε hε
      -- Either x is not an integer or x + min(ε/2, 1/2) is not an integer
      by_cases hx : ∃ k : ℤ, x = k
      · rcases hx with ⟨k, rfl⟩
        refine ⟨(k : ℝ) + min (ε / 2) (1 / 2), ?_, ?_⟩
        · intro m hm
          have h1 : (0 : ℝ) < min (ε / 2) (1 / 2) := lt_min (half_pos hε) (by norm_num)
          have h2 : min (ε / 2) (1 / 2) < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
          have hm1 : (k : ℝ) < (m : ℝ) := by linarith
          have hm2 : (m : ℝ) < (k : ℝ) + 1 := by linarith
          have h1z : k < m := by exact_mod_cast hm1
          have h2z : m < k + 1 := by exact_mod_cast hm2
          omega
        · rw [Real.dist_eq, abs_sub_comm]
          have h1 : (0 : ℝ) < min (ε / 2) (1 / 2) := lt_min (half_pos hε) (by norm_num)
          rw [show (k : ℝ) + min (ε / 2) (1 / 2) - (k : ℝ) = min (ε / 2) (1 / 2) by ring,
              abs_of_pos h1]
          exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
      · push Not at hx
        exact ⟨x, hx, by simp [hε]⟩
    have hfun_eq : ft (checkMeasure μ) = ft μ := by
      apply Continuous.ext_on hdense (continuous_ft (checkMeasure μ)) (continuous_ft μ)
      intro ξ hξ
      have hν_ne : ft ν ξ ≠ 0 := by
        intro hν0
        have h1 : ft lebHalf ξ = 0 := by rw [← hconv, ft_conv, hν0, mul_zero]
        have hξ0 : ξ ≠ 0 := by simpa using hξ 0
        simp only [ft_lebHalf, hξ0, ↓reduceIte] at h1
        have hsin0 : Real.sin (Real.pi * ξ) = 0 := by
          have := Complex.ofReal_eq_zero.mp h1
          exact (div_eq_zero_iff.mp this).resolve_right (mul_ne_zero Real.pi_ne_zero hξ0)
        rcases Real.sin_eq_zero_iff.mp hsin0 with ⟨k, hk⟩
        have hξk : ξ = (k : ℝ) := by
          have : Real.pi * ξ = Real.pi * (k : ℝ) := by linarith
          exact mul_left_cancel₀ Real.pi_ne_zero this
        exact hξ k hξk
      have hprod : ft (checkMeasure μ) ξ * ft ν ξ = ft μ ξ * ft ν ξ := by
        rw [← ft_conv, ← ft_conv, hcm_conv, hconv]
      exact mul_right_cancel₀ hν_ne hprod
    exact congrFun hfun_eq
  have hcheck_ν : checkMeasure ν = ν := by
    have hconv_check : checkMeasure μ ∗ checkMeasure ν = lebHalf := by
      have h1 : checkMeasure (μ ∗ ν) = checkMeasure μ ∗ checkMeasure ν := by
        unfold checkMeasure
        let negHom : ℝ →+ ℝ := ⟨⟨fun x => -x, neg_zero⟩, neg_add⟩
        simpa [negHom] using Measure.map_conv_addMonoidHom (μ := μ) (ν := ν) negHom measurable_neg
      rw [← h1, hconv]
      ext s hs
      rw [checkMeasure, Measure.map_apply measurable_neg hs, lebHalf,
          Measure.restrict_apply (hs.preimage measurable_neg), Measure.restrict_apply hs]
      have hpre : (fun x : ℝ => -x) ⁻¹' s ∩ Set.Icc (-(1 / 2)) (1 / 2) =
          ((-1 : ℝ) * ·) ⁻¹' (s ∩ Set.Icc (-(1 / 2)) (1 / 2)) := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc, neg_one_mul]
        constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1, by linarith, by linarith⟩
      rw [hpre, Real.volume_preimage_mul_left (by norm_num : (-1 : ℝ) ≠ 0)]; simp
    rw [hcheck_μ] at hconv_check
    apply ext_of_ft
    have hdense : Dense {ξ : ℝ | ∀ k : ℤ, ξ ≠ (k : ℝ)} := by
      intro x
      rw [Metric.mem_closure_iff]
      intro ε hε
      by_cases hx : ∃ k : ℤ, x = k
      · rcases hx with ⟨k, rfl⟩
        refine ⟨(k : ℝ) + min (ε / 2) (1 / 2), ?_, ?_⟩
        · intro m hm
          have h1 : (0 : ℝ) < min (ε / 2) (1 / 2) := lt_min (half_pos hε) (by norm_num)
          have h2 : min (ε / 2) (1 / 2) < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
          have h1z : k < m := by exact_mod_cast (show (k : ℝ) < (m : ℝ) by linarith)
          have h2z : m < k + 1 := by exact_mod_cast (show (m : ℝ) < (k : ℝ) + 1 by linarith)
          omega
        · rw [Real.dist_eq, abs_sub_comm]
          have h1 : (0 : ℝ) < min (ε / 2) (1 / 2) := lt_min (half_pos hε) (by norm_num)
          rw [show (k : ℝ) + min (ε / 2) (1 / 2) - (k : ℝ) = min (ε / 2) (1 / 2) by ring, abs_of_pos h1]
          exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
      · push Not at hx; exact ⟨x, hx, by simp [hε]⟩
    have hfun_eq : ft (checkMeasure ν) = ft ν := by
      apply Continuous.ext_on hdense (continuous_ft (checkMeasure ν)) (continuous_ft ν)
      intro ξ hξ
      have hμ_ne : ft μ ξ ≠ 0 := by
        intro hμ0
        have h1 : ft lebHalf ξ = 0 := by rw [← hconv, ft_conv, hμ0, zero_mul]
        have hξ0 : ξ ≠ 0 := by simpa using hξ 0
        simp only [ft_lebHalf, hξ0, ↓reduceIte] at h1
        have hsin0 : Real.sin (Real.pi * ξ) = 0 :=
          (div_eq_zero_iff.mp (Complex.ofReal_eq_zero.mp h1)).resolve_right (mul_ne_zero Real.pi_ne_zero hξ0)
        rcases Real.sin_eq_zero_iff.mp hsin0 with ⟨k, hk⟩
        exact hξ k (mul_left_cancel₀ Real.pi_ne_zero (by linarith))
      have hprod : ft μ ξ * ft (checkMeasure ν) ξ = ft μ ξ * ft ν ξ := by
        rw [← ft_conv, ← ft_conv, hconv_check, hconv]
      exact mul_left_cancel₀ hμ_ne hprod
    exact congrFun hfun_eq
  exact ⟨hdisj, hinf_ν, hsup_ν, hcheck_μ, hcheck_ν⟩

/-! ### Lemma `lem0`: Sharp Support Bounds `1/(4r) ≤ a ≤ 1/(2r)` -/

/-- Every power `(cos θ)^d` is a linear combination of `cos (m * θ)` for `0 ≤ m ≤ d`. -/
private lemma cos_pow_eq_sum_cos (d : ℕ) :
    ∃ c : Fin (d + 1) → ℝ, ∀ θ : ℝ, Real.cos θ ^ d = ∑ m : Fin (d + 1), c m * Real.cos ((m : ℕ) * θ) := by
  induction d with
  | zero =>
    refine ⟨fun _ => 1, fun θ => by simp⟩
  | succ d ih =>
    rcases ih with ⟨c, hc⟩
    -- (cos θ)^(d+1) = ∑_{m ≤ d} c m * (cos(m θ) * cos θ)
    -- For m = 0: cos 0 * cos θ = cos(1 * θ)
    -- For m ≥ 1: cos(m θ) * cos θ = (cos((m+1) θ) + cos((m-1) θ)) / 2
    let step : Fin (d + 1) → Fin (d + 2) → ℝ := fun m k =>
      if (m : ℕ) = 0 then (if (k : ℕ) = 1 then c m else 0)
      else (if (k : ℕ) = (m : ℕ) + 1 then c m / 2 else 0) +
           (if (k : ℕ) = (m : ℕ) - 1 then c m / 2 else 0)
    refine ⟨fun k => ∑ m : Fin (d + 1), step m k, fun θ => ?_⟩
    rw [pow_succ, hc θ, Finset.sum_mul]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    by_cases hm0 : (m : ℕ) = 0
    · have h1 : (⟨1, by omega⟩ : Fin (d + 2)) ∈ Finset.univ := Finset.mem_univ _
      rw [Finset.sum_eq_single (⟨1, by omega⟩ : Fin (d + 2))]
      · simp only [step, hm0, ↓reduceIte]; simp
      · intro k _ hk
        have hne : (k : ℕ) ≠ 1 := fun h => hk (Fin.ext h)
        simp only [step, hm0, hne, ↓reduceIte, zero_mul]
      · intro h; exact absurd h1 h
    · have hplus : (⟨(m : ℕ) + 1, by omega⟩ : Fin (d + 2)) ∈ Finset.univ := Finset.mem_univ _
      have hminus : (⟨(m : ℕ) - 1, by omega⟩ : Fin (d + 2)) ∈ Finset.univ := Finset.mem_univ _
      have hne_pm : (⟨(m : ℕ) + 1, by omega⟩ : Fin (d + 2)) ≠ ⟨(m : ℕ) - 1, by omega⟩ := by
        intro heq; have := congrArg Fin.val heq; dsimp only at this; omega
      have hstep_sum : ∑ k : Fin (d + 2), step m k * Real.cos ((k : ℕ) * θ) =
          (c m / 2) * Real.cos (((m : ℕ) + 1 : ℕ) * θ) + (c m / 2) * Real.cos (((m : ℕ) - 1 : ℕ) * θ) := by
        have hsplit : ∀ k : Fin (d + 2), step m k * Real.cos ((k : ℕ) * θ) =
            (if (k : ℕ) = (m : ℕ) + 1 then (c m / 2) * Real.cos ((k : ℕ) * θ) else 0) +
            (if (k : ℕ) = (m : ℕ) - 1 then (c m / 2) * Real.cos ((k : ℕ) * θ) else 0) := by
          intro k; simp only [step, hm0, ↓reduceIte, add_mul, ite_mul, zero_mul]
        simp_rw [hsplit, Finset.sum_add_distrib]
        congr 1
        · rw [Finset.sum_eq_single (⟨(m : ℕ) + 1, by omega⟩ : Fin (d + 2))]
          · simp
          · intro k _ hk; have hne : (k : ℕ) ≠ (m : ℕ) + 1 := fun h => hk (Fin.ext h); simp [hne]
          · intro h; exact absurd hplus h
        · rw [Finset.sum_eq_single (⟨(m : ℕ) - 1, by omega⟩ : Fin (d + 2))]
          · simp
          · intro k _ hk; have hne : (k : ℕ) ≠ (m : ℕ) - 1 := fun h => hk (Fin.ext h); simp [hne]
          · intro h; exact absurd hminus h
      rw [hstep_sum]
      have htrig : 2 * (Real.cos ((m : ℕ) * θ) * Real.cos θ) =
          Real.cos ((m : ℕ) * θ + θ) + Real.cos ((m : ℕ) * θ - θ) := by
        linarith [Real.cos_add ((m : ℕ) * θ) θ, Real.cos_sub ((m : ℕ) * θ) θ]
      have hsub : (((m : ℕ) - 1 : ℕ) : ℝ) * θ = (m : ℕ) * θ - θ := by
        rw [Nat.cast_sub (by omega : 1 ≤ (m : ℕ))]; push_cast; ring
      have hadd : (((m : ℕ) + 1 : ℕ) : ℝ) * θ = (m : ℕ) * θ + θ := by push_cast; ring
      rw [hsub, hadd]
      linear_combination (c m / 2) * htrig

/-- Integral of `P(cos(2π x))` against a symmetric probability measure `ν` with `ft ν m = 0` for
`1 ≤ m < r` equals the discrete average over the `r` shifted roots `x_j = -(r-1)/(2r) + j/r`. -/
private lemma integral_poly_cos_eq_quadrature {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {r : ℕ} (hr : 2 ≤ r)
    (hzeros : ∀ m : ℕ, 1 ≤ m → m < r → ft ν m = 0)
    (P : ℝ[X]) (hdeg : P.natDegree < r) :
    ∫ x, P.eval (Real.cos (2 * Real.pi * x)) ∂ν =
      (1 / (r : ℝ)) * ∑ j ∈ Finset.range r,
        P.eval (Real.cos (2 * Real.pi * (-(r - 1 : ℝ) / (2 * (r : ℝ)) + (j : ℝ) / (r : ℝ)))) := by
  have hrpos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
  -- First prove for every 0 ≤ m < r: ∫ cos(2π m x) dν = (1/r) ∑_j cos(2π m x_j)
  have hcos_eq : ∀ m < r,
      ∫ x, Real.cos (2 * Real.pi * (m : ℝ) * x) ∂ν =
        (1 / (r : ℝ)) * ∑ j ∈ Finset.range r,
          Real.cos (2 * Real.pi * (m : ℝ) * (-(r - 1 : ℝ) / (2 * (r : ℝ)) + (j : ℝ) / (r : ℝ))) := by
    intro m hm
    by_cases hm0 : m = 0
    · subst hm0
      simp [hrpos.ne']
    · have hm1 : 1 ≤ m := by omega
      -- LHS = Re(ft ν m) = 0
      have hlhs : ∫ x, Real.cos (2 * Real.pi * (m : ℝ) * x) ∂ν = 0 := by
        have hft0 : ft ν m = 0 := hzeros m hm1 hm
        have hre : (ft ν m).re = ∫ x, Real.cos (2 * Real.pi * (m : ℝ) * x) ∂ν := by
          change RCLike.re (ft ν m) = _
          rw [ft_apply, ← integral_re]
          · congr 1; ext x
            have h1 : (-2 * Real.pi * (m : ℝ) * x * Complex.I : ℂ) =
                ((-2 * Real.pi * (m : ℝ) * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
            change (Complex.exp (-2 * Real.pi * (m : ℝ) * x * Complex.I)).re = _
            rw [h1, Complex.exp_ofReal_mul_I_re, show -2 * Real.pi * (m : ℝ) * x = -(2 * Real.pi * (m : ℝ) * x) by ring,
                Real.cos_neg]
          · exact (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun x => by
              have h1 : (-2 * Real.pi * (m : ℝ) * x * Complex.I : ℂ) =
                  ((-2 * Real.pi * (m : ℝ) * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
              rw [h1, Complex.norm_exp_ofReal_mul_I])
        rw [← hre, hft0, Complex.zero_re]
      -- RHS = (1/r) * Re(exp(...) * ∑_{j<r} ω^j) = 0
      have hrhs : ∑ j ∈ Finset.range r,
          Real.cos (2 * Real.pi * (m : ℝ) * (-(r - 1 : ℝ) / (2 * (r : ℝ)) + (j : ℝ) / (r : ℝ))) = 0 := by
        set θ₀ : ℝ := 2 * Real.pi * (m : ℝ) / (r : ℝ)
        set ω : ℂ := Complex.exp ((θ₀ : ℂ) * Complex.I)
        set α : ℂ := Complex.exp (((2 * Real.pi * (m : ℝ) * (-(r - 1 : ℝ) / (2 * (r : ℝ))) : ℝ) : ℂ) * Complex.I)
        have hω_pow : ω ^ r = 1 := by
          simp only [ω, ← Complex.exp_nat_mul]
          have harg : (r : ℂ) * ((θ₀ : ℂ) * Complex.I) =
              ((m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
            have hrc : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            simp only [θ₀]; push_cast; field_simp
          rw [harg, Complex.exp_int_mul_two_pi_mul_I]
        have hω_ne : ω ≠ 1 := by
          intro h1
          have hcos1 : Real.cos θ₀ = 1 := by
            have := congrArg Complex.re h1
            simp only [ω, Complex.exp_ofReal_mul_I_re, Complex.one_re] at this
            exact this
          have hsin0 : Real.sin θ₀ = 0 := by
            have := congrArg Complex.im h1
            simp only [ω, Complex.exp_ofReal_mul_I_im, Complex.one_im] at this
            exact this
          rcases Real.sin_eq_zero_iff.mp hsin0 with ⟨k, hk⟩
          have hpos : 0 < θ₀ := by simp only [θ₀]; positivity
          have hlt2pi : θ₀ < 2 * Real.pi := by
            simp only [θ₀]
            rw [div_lt_iff₀ hrpos]
            have hm_lt : (m : ℝ) < (r : ℝ) := by exact_mod_cast hm
            nlinarith [Real.pi_pos]
          have hk_gt0 : (0 : ℝ) < (k : ℝ) := by nlinarith [Real.pi_pos]
          have hk_lt2 : (k : ℝ) < 2 := by nlinarith [Real.pi_pos]
          have hk1 : k = 1 := by
            have : (0 : ℤ) < k := by exact_mod_cast hk_gt0
            have : k < (2 : ℤ) := by exact_mod_cast hk_lt2
            omega
          subst hk1
          rw [← hk] at hcos1
          norm_num [Real.cos_pi] at hcos1
        have hgeom : ∑ j ∈ Finset.range r, ω ^ j = 0 := by
          have hmul := geom_sum_mul ω r
          rw [hω_pow, sub_self] at hmul
          exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hω_ne)
        have hsum_c : (∑ j ∈ Finset.range r,
            Complex.exp ((2 * Real.pi * (m : ℝ) * (-(r - 1 : ℝ) / (2 * (r : ℝ)) + (j : ℝ) / (r : ℝ)) : ℝ) * Complex.I)) = 0 := by
          have hterm : ∀ j ∈ Finset.range r,
              Complex.exp ((2 * Real.pi * (m : ℝ) * (-(r - 1 : ℝ) / (2 * (r : ℝ)) + (j : ℝ) / (r : ℝ)) : ℝ) * Complex.I) =
              α * ω ^ j := by
            intro j _
            simp only [α, ω, θ₀, ← Complex.exp_nat_mul, ← Complex.exp_add]
            congr 1; push_cast; ring
          rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hgeom, mul_zero]
        have hre := congrArg Complex.re hsum_c
        rw [Complex.re_sum, Complex.zero_re] at hre
        convert hre using 1
        apply Finset.sum_congr rfl
        intro j _
        rw [Complex.exp_ofReal_mul_I_re]
      rw [hlhs, hrhs, mul_zero]
  -- Extend from cos(m θ) to (cos θ)^d for all d < r
  have hpow_eq : ∀ d < r,
      ∫ x, Real.cos (2 * Real.pi * x) ^ d ∂ν =
        (1 / (r : ℝ)) * ∑ j ∈ Finset.range r,
          Real.cos (2 * Real.pi * (-(r - 1 : ℝ) / (2 * (r : ℝ)) + (j : ℝ) / (r : ℝ))) ^ d := by
    intro d hd
    rcases cos_pow_eq_sum_cos d with ⟨c, hc⟩
    simp_rw [hc]
    rw [integral_finsetSum _ (fun m _ =>
      (integrable_const |c m|).mono' (by fun_prop) (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)))]
    simp_rw [integral_const_mul]
    have hcomm : (1 / (r : ℝ)) * ∑ j ∈ Finset.range r,
        ∑ m : Fin (d + 1), c m * Real.cos ((m : ℕ) * (2 * Real.pi * (-(r - 1 : ℝ) / (2 * (r : ℝ)) + (j : ℝ) / (r : ℝ)))) =
        ∑ m : Fin (d + 1), c m * ((1 / (r : ℝ)) * ∑ j ∈ Finset.range r,
          Real.cos (2 * Real.pi * (m : ℕ) * (-(r - 1 : ℝ) / (2 * (r : ℝ)) + (j : ℝ) / (r : ℝ)))) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro m _
      rw [← Finset.mul_sum]
      have harg : ∀ j ∈ Finset.range r,
          Real.cos ((m : ℕ) * (2 * Real.pi * (-(r - 1 : ℝ) / (2 * (r : ℝ)) + (j : ℝ) / (r : ℝ)))) =
          Real.cos (2 * Real.pi * (m : ℕ) * (-(r - 1 : ℝ) / (2 * (r : ℝ)) + (j : ℝ) / (r : ℝ))) := by
        intro j _; congr 1; ring
      rw [Finset.sum_congr rfl harg]; ring
    rw [hcomm]
    apply Finset.sum_congr rfl; intro m _
    congr 1
    have hmul : ∀ x : ℝ, (m : ℕ) * (2 * Real.pi * x) = 2 * Real.pi * ((m : ℕ) : ℝ) * x := fun x => by ring
    simp_rw [hmul]
    exact hcos_eq (m : ℕ) (by omega)
  -- Extend from powers to polynomial P of degree < r
  simp_rw [Polynomial.eval_eq_sum_range' hdeg]
  rw [integral_finsetSum _ (fun d _ =>
    (integrable_const |P.coeff d|).mono' (by fun_prop) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _))))]
  simp_rw [integral_const_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro d hd
  rw [← Finset.mul_sum, ← mul_assoc, mul_comm (1 / (r : ℝ)) (P.coeff d), mul_assoc,
      hpow_eq d (Finset.mem_range.mp hd)]

private lemma integrable_poly_cos {ν : Measure ℝ} [IsFiniteMeasure ν] (R : ℝ[X]) :
    Integrable (fun x => R.eval (Real.cos (2 * Real.pi * x))) ν := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn R.continuous.continuousOn
  exact (integrable_const M).mono' (R.continuous.comp (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun x => hM _ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)

private lemma poly_cos_contradiction {ν : Measure ℝ} [IsFiniteMeasure ν] {b c_k : ℝ}
    (hb_nn : 0 ≤ b) (hb_half : b ≤ 1 / 2) (hν_supp : IsSupportedIn ν (Set.Icc (-b) b))
    (hgap_cos : c_k < Real.cos (2 * Real.pi * b))
    (Q : ℝ[X])
    (hQ_nn : ∀ t : ℝ, t ≤ 1 → 0 ≤ Q.eval t)
    (hP_int : ∫ x, ((X - C c_k) * Q).eval (Real.cos (2 * Real.pi * x)) ∂ν = 0)
    (hQ_int_pos : 0 < ∫ x, Q.eval (Real.cos (2 * Real.pi * x)) ∂ν) : False := by
  have hae_le : ∀ᵐ x ∂ν, (Real.cos (2 * Real.pi * b) - c_k) * Q.eval (Real.cos (2 * Real.pi * x)) ≤
      ((X - C c_k) * Q).eval (Real.cos (2 * Real.pi * x)) := by
    have hmem : ∀ᵐ x ∂ν, x ∈ Set.Icc (-b) b := by rw [ae_iff]; exact hν_supp
    filter_upwards [hmem] with x hx
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    apply mul_le_mul_of_nonneg_right _ (hQ_nn _ (Real.cos_le_one _))
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    have hxabs : |x| ≤ b := abs_le.mpr hx
    have hcos_ge : Real.cos (2 * Real.pi * b) ≤ Real.cos (2 * Real.pi * x) := by
      rw [← Real.cos_abs (2 * Real.pi * x)]
      apply Real.strictAntiOn_cos.antitoneOn
      · exact ⟨abs_nonneg _, by rw [abs_mul, abs_of_pos h2pi]; nlinarith [Real.pi_pos]⟩
      · exact ⟨by positivity, by nlinarith [Real.pi_pos]⟩
      · rw [abs_mul, abs_of_pos h2pi]; nlinarith [h2pi]
    linarith
  have hineq := integral_mono_ae ((integrable_poly_cos Q).const_mul _) (integrable_poly_cos ((X - C c_k) * Q)) hae_le
  rw [integral_const_mul, hP_int] at hineq
  have hprod_pos : 0 < (Real.cos (2 * Real.pi * b) - c_k) * ∫ x, Q.eval (Real.cos (2 * Real.pi * x)) ∂ν :=
    mul_pos (sub_pos.mpr hgap_cos) hQ_int_pos
  linarith

private lemma gabardo_lai_lem0_lower {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : ℝ} (ha0 : 0 < a) (ha_half : a < 1 / 2)
    (hconv : μ ∗ ν = lebHalf)
    (hinf_μ : sInf μ.support = -a) (hsup_μ : sSup μ.support = a)
    {r : ℕ} (hr1 : 1 ≤ r) (hμr : ft μ r = 0) :
    1 / (4 * (r : ℝ)) ≤ a := by
  rcases support_endpoints_of_conv_lebHalf hconv with ⟨hμ_bb, hμ_ba, _, _, _, _⟩
  have hμ_supp : IsSupportedIn μ (Set.Icc (-a) a) := by
    have hsub : μ.support ⊆ Set.Icc (-a) a := fun x hx =>
      ⟨hinf_μ ▸ csInf_le hμ_bb hx, hsup_μ ▸ le_csSup hμ_ba hx⟩
    exact measure_mono_null (Set.compl_subset_compl.mpr hsub) Measure.measure_compl_support
  have hrpos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
  by_contra hlt
  push Not at hlt
  have hcos_int : ∫ x, Real.cos (2 * Real.pi * (r : ℝ) * x) ∂μ = 0 := by
    have hre : (ft μ r).re = ∫ x, Real.cos (2 * Real.pi * (r : ℝ) * x) ∂μ := by
      change RCLike.re (ft μ r) = _
      rw [ft_apply, ← integral_re]
      · congr 1; ext x
        have h1 : (-2 * Real.pi * (r : ℝ) * x * Complex.I : ℂ) =
            ((-2 * Real.pi * (r : ℝ) * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
        change (Complex.exp (-2 * Real.pi * (r : ℝ) * x * Complex.I)).re = _
        rw [h1, Complex.exp_ofReal_mul_I_re,
            show -2 * Real.pi * (r : ℝ) * x = -(2 * Real.pi * (r : ℝ) * x) by ring, Real.cos_neg]
      · exact (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun x => by
          have h1 : (-2 * Real.pi * (r : ℝ) * x * Complex.I : ℂ) =
              ((-2 * Real.pi * (r : ℝ) * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
          rw [h1, Complex.norm_exp_ofReal_mul_I])
    rw [← hre, hμr, Complex.zero_re]
  have h2pr : 0 < 2 * Real.pi * (r : ℝ) := by positivity
  have hcos_pos : 0 < Real.cos (2 * Real.pi * (r : ℝ) * a) := by
    apply Real.cos_pos_of_mem_Ioo
    have h1 : 2 * Real.pi * (r : ℝ) * a < Real.pi / 2 := by
      have hmul : 4 * (r : ℝ) * a < 1 := by
        rw [lt_div_iff₀ (by positivity)] at hlt; linarith
      nlinarith [Real.pi_pos]
    exact ⟨by nlinarith [Real.pi_pos, h2pr], h1⟩
  have hae : ∀ᵐ x ∂μ, Real.cos (2 * Real.pi * (r : ℝ) * a) ≤ Real.cos (2 * Real.pi * (r : ℝ) * x) := by
    have hmem : ∀ᵐ x ∂μ, x ∈ Set.Icc (-a) a := by rw [ae_iff]; exact hμ_supp
    filter_upwards [hmem] with x hx
    rw [← Real.cos_abs (2 * Real.pi * (r : ℝ) * x)]
    apply Real.strictAntiOn_cos.antitoneOn
    · exact ⟨abs_nonneg _, by
        have : |2 * Real.pi * (r : ℝ) * x| = 2 * Real.pi * (r : ℝ) * |x| := by
          rw [abs_mul, abs_of_pos h2pr]
        rw [this]
        have h1 : 2 * Real.pi * (r : ℝ) * a < Real.pi / 2 := by
          rw [lt_div_iff₀ (by positivity)] at hlt; nlinarith [Real.pi_pos]
        have h2 : |x| ≤ a := abs_le.mpr hx
        nlinarith [Real.pi_pos, h2pr]⟩
    · exact ⟨by positivity, by
        rw [lt_div_iff₀ (by positivity)] at hlt; nlinarith [Real.pi_pos]⟩
    · rw [abs_mul, abs_of_pos h2pr]
      have h2 : |x| ≤ a := abs_le.mpr hx
      nlinarith [h2pr]
  have hint_ge : Real.cos (2 * Real.pi * (r : ℝ) * a) ≤ ∫ x, Real.cos (2 * Real.pi * (r : ℝ) * x) ∂μ := by
    calc
      Real.cos (2 * Real.pi * (r : ℝ) * a)
          = ∫ _x, Real.cos (2 * Real.pi * (r : ℝ) * a) ∂μ := by simp
      _ ≤ ∫ x, Real.cos (2 * Real.pi * (r : ℝ) * x) ∂μ :=
            integral_mono_ae (integrable_const _)
              ((integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun x => by
                rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)) hae
  linarith

private lemma gabardo_lai_lem0_upper {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : ℝ} (ha0 : 0 < a) (ha_half : a < 1 / 2)
    (hconv : μ ∗ ν = lebHalf)
    (hinf_μ : sInf μ.support = -a) (hsup_μ : sSup μ.support = a)
    {r : ℕ} (hr1 : 1 ≤ r)
    (hr_min : ∀ m : ℕ, 1 ≤ m → m < r → ft μ m ≠ 0) :
    a ≤ 1 / (2 * (r : ℝ)) := by
  have h01 := gabardo_lai_lem01 (le_of_lt ha0) (le_of_lt ha_half) hconv hinf_μ hsup_μ
  rcases support_endpoints_of_conv_lebHalf hconv with ⟨_, _, hν_bb, hν_ba, _, _⟩
  set b := 1 / 2 - a with hb_eq
  have hν_supp : IsSupportedIn ν (Set.Icc (-b) b) := by
    have hsub : ν.support ⊆ Set.Icc (-b) b := fun y hy =>
      ⟨h01.2.1 ▸ csInf_le hν_bb hy, h01.2.2.1 ▸ le_csSup hν_ba hy⟩
    exact measure_mono_null (Set.compl_subset_compl.mpr hsub) Measure.measure_compl_support
  have hrpos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
  by_cases hr_eq1 : r = 1
  · subst hr_eq1; norm_num; exact le_of_lt ha_half
  · have hr2 : 2 ≤ r := by omega
    have hν_zeros : ∀ m : ℕ, 1 ≤ m → m < r → ft ν m = 0 := by
      intro m hm1 hmr
      have hne : (m : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (by omega)
      exact (h01.1 m hne).1.resolve_left (hr_min m hm1 hmr)
    by_contra hgt_a
    push Not at hgt_a
    have hb_lt : b < ((r : ℝ) - 1) / (2 * (r : ℝ)) := by
      have : (1 : ℝ) / 2 - 1 / (2 * (r : ℝ)) = ((r : ℝ) - 1) / (2 * (r : ℝ)) := by field_simp
      linarith
    have hb_nn : 0 ≤ b := by linarith
    have hb_le_half : b ≤ 1 / 2 := by linarith
    set c_k : ℝ := Real.cos (((r : ℝ) - 1) * Real.pi / (r : ℝ))
    set k : ℕ := r / 2
    set Q : ℝ[X] :=
      if Even r then
        ∏ l ∈ Finset.Ico 1 k, (X - C (Real.cos ((2 * (l : ℝ) - 1) * Real.pi / (r : ℝ)))) ^ 2
      else
        (1 - X) * ∏ l ∈ Finset.Ico 1 k, (X - C (Real.cos ((2 * (l : ℝ)) * Real.pi / (r : ℝ)))) ^ 2
    set P : ℝ[X] := (X - C c_k) * Q
    have hQ_deg : Q.natDegree ≤ r - 2 := by
      simp only [Q]
      split_ifs with hev
      · have hk2 : 2 * k = r := by rcases hev with ⟨m, rfl⟩; omega
        calc
          (∏ l ∈ Finset.Ico 1 k, (X - C (Real.cos ((2 * (l : ℝ) - 1) * Real.pi / (r : ℝ)))) ^ 2).natDegree
              ≤ ∑ l ∈ Finset.Ico 1 k, ((X - C (Real.cos ((2 * (l : ℝ) - 1) * Real.pi / (r : ℝ)))) ^ 2).natDegree :=
                Polynomial.natDegree_prod_le _ _
          _ ≤ ∑ _l ∈ Finset.Ico 1 k, 2 := by
                apply Finset.sum_le_sum; intro l _
                calc ((X - C _ : ℝ[X]) ^ 2).natDegree ≤ 2 * (X - C _ : ℝ[X]).natDegree := Polynomial.natDegree_pow_le
                  _ ≤ 2 * 1 := Nat.mul_le_mul_left 2 (Polynomial.natDegree_X_sub_C_le _)
                  _ = 2 := by norm_num
          _ = 2 * (k - 1) := by rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]; ring
          _ = r - 2 := by omega
      · have hk2 : 2 * k + 1 = r := by
          have hodd : r % 2 = 1 := by
            by_contra h0; exact hev (Nat.even_iff.mpr (by omega))
          omega
        calc
          ((1 - X) * ∏ l ∈ Finset.Ico 1 k, (X - C (Real.cos ((2 * (l : ℝ)) * Real.pi / (r : ℝ)))) ^ 2).natDegree
              ≤ (1 - X : ℝ[X]).natDegree + (∏ l ∈ Finset.Ico 1 k, (X - C (Real.cos ((2 * (l : ℝ)) * Real.pi / (r : ℝ)))) ^ 2).natDegree :=
                Polynomial.natDegree_mul_le
          _ ≤ 1 + ∑ l ∈ Finset.Ico 1 k, ((X - C (Real.cos ((2 * (l : ℝ)) * Real.pi / (r : ℝ)))) ^ 2).natDegree := by
                have h1 : (1 - X : ℝ[X]).natDegree ≤ 1 := by
                  calc (1 - X : ℝ[X]).natDegree ≤ max (1 : ℝ[X]).natDegree (X : ℝ[X]).natDegree := Polynomial.natDegree_sub_le _ _
                    _ = 1 := by simp
                exact add_le_add h1 (Polynomial.natDegree_prod_le _ _)
          _ ≤ 1 + ∑ _l ∈ Finset.Ico 1 k, 2 := by
                apply Nat.add_le_add_left; apply Finset.sum_le_sum; intro l _
                calc ((X - C _ : ℝ[X]) ^ 2).natDegree ≤ 2 * (X - C _ : ℝ[X]).natDegree := Polynomial.natDegree_pow_le
                  _ ≤ 2 * 1 := Nat.mul_le_mul_left 2 (Polynomial.natDegree_X_sub_C_le _)
                  _ = 2 := by norm_num
          _ = 1 + 2 * (k - 1) := by rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]; ring
          _ = r - 2 := by omega
    have hP_deg : P.natDegree < r := by
      calc
        P.natDegree ≤ (X - C c_k).natDegree + Q.natDegree := Polynomial.natDegree_mul_le
        _ ≤ 1 + (r - 2) := add_le_add (Polynomial.natDegree_X_sub_C_le _) hQ_deg
        _ < r := by omega
    have hQ_nn : ∀ t : ℝ, t ≤ 1 → 0 ≤ Q.eval t := by
      intro t ht
      simp only [Q]
      split_ifs
      · rw [Polynomial.eval_prod]
        exact Finset.prod_nonneg (fun _ _ => by simp only [Polynomial.eval_pow]; exact sq_nonneg _)
      · rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
            Polynomial.eval_prod]
        exact mul_nonneg (by linarith) (Finset.prod_nonneg (fun _ _ => by simp only [Polynomial.eval_pow]; exact sq_nonneg _))
    have hr1_pos : (0 : ℝ) < (r : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
      linarith
    have hQ_ck_pos : 0 < Q.eval c_k := by
      simp only [Q]
      split_ifs with hev
      · rw [Polynomial.eval_prod]
        apply Finset.prod_pos; intro l hl
        rw [Finset.mem_Ico] at hl
        simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        apply sq_pos_of_ne_zero
        have hlt_ang : (2 * (l : ℝ) - 1) * Real.pi / (r : ℝ) < ((r : ℝ) - 1) * Real.pi / (r : ℝ) := by
          have hk2 : 2 * k = r := by rcases hev with ⟨m, rfl⟩; omega
          have h1 : 2 * (l : ℝ) - 1 < (r : ℝ) - 1 := by
            have : 2 * l < r := by omega
            have : 2 * (l : ℝ) < (r : ℝ) := by exact_mod_cast this
            linarith
          exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right h1 Real.pi_pos) hrpos
        have h2l1_nn : (0 : ℝ) ≤ 2 * (l : ℝ) - 1 := by
          have : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl.1
          linarith
        have hcos_lt : c_k < Real.cos ((2 * (l : ℝ) - 1) * Real.pi / (r : ℝ)) := by
          apply Real.strictAntiOn_cos
          · exact ⟨by positivity,
                   by have : ((r : ℝ) - 1) * Real.pi / (r : ℝ) ≤ Real.pi := by
                        rw [div_le_iff₀ hrpos]; nlinarith [Real.pi_pos]
                      linarith⟩
          · exact ⟨by positivity,
                   by rw [div_le_iff₀ hrpos]; nlinarith [Real.pi_pos]⟩
          · exact hlt_ang
        linarith
      · rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
            Polynomial.eval_prod]
        have hck_lt1 : c_k < 1 := by
          have h1 : c_k < Real.cos 0 := by
            apply Real.strictAntiOn_cos
            · exact ⟨le_rfl, le_of_lt Real.pi_pos⟩
            · exact ⟨by positivity,
                     by rw [div_le_iff₀ hrpos]; nlinarith [Real.pi_pos]⟩
            · positivity
          simpa [Real.cos_zero] using h1
        apply mul_pos (by linarith)
        apply Finset.prod_pos; intro l hl
        rw [Finset.mem_Ico] at hl
        simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        apply sq_pos_of_ne_zero
        have hk2 : 2 * k + 1 = r := by
          have hodd : r % 2 = 1 := by by_contra h0; exact hev (Nat.even_iff.mpr (by omega))
          omega
        have hlt_ang : (2 * (l : ℝ)) * Real.pi / (r : ℝ) < ((r : ℝ) - 1) * Real.pi / (r : ℝ) := by
          have h1 : 2 * (l : ℝ) < (r : ℝ) - 1 := by
            have : 2 * l + 1 < r := by omega
            have : 2 * (l : ℝ) + 1 < (r : ℝ) := by exact_mod_cast this
            linarith
          exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right h1 Real.pi_pos) hrpos
        have hcos_lt : c_k < Real.cos ((2 * (l : ℝ)) * Real.pi / (r : ℝ)) := by
          apply Real.strictAntiOn_cos
          · exact ⟨by positivity,
                   by have : ((r : ℝ) - 1) * Real.pi / (r : ℝ) ≤ Real.pi := by
                        rw [div_le_iff₀ hrpos]; nlinarith [Real.pi_pos]
                      linarith⟩
          · exact ⟨by positivity,
                   by rw [div_le_iff₀ hrpos]; nlinarith [Real.pi_pos]⟩
          · exact hlt_ang
        linarith
    have hQ_inner_zero : ∀ j, 1 ≤ j → j < r - 1 →
        Q.eval (Real.cos (2 * Real.pi * (-(r - 1 : ℝ) / (2 * (r : ℝ)) + (j : ℝ) / (r : ℝ)))) = 0 := by
      intro j hj1 hj2
      set θ := 2 * Real.pi * (-(r - 1 : ℝ) / (2 * (r : ℝ)) + (j : ℝ) / (r : ℝ))
      have hθ_eq : θ = (2 * (j : ℝ) - ((r : ℝ) - 1)) * Real.pi / (r : ℝ) := by
        simp only [θ]; field_simp; ring
      simp only [Q]
      split_ifs with hev
      · rw [Polynomial.eval_prod]
        have hk2 : 2 * k = r := by rcases hev with ⟨m, rfl⟩; omega
        set d : ℕ := if j < k then k - j else j - k + 1
        have hd_mem : d ∈ Finset.Ico 1 k := by rw [Finset.mem_Ico]; simp only [d]; split_ifs <;> omega
        apply Finset.prod_eq_zero hd_mem
        simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        have hcos_eq : Real.cos θ = Real.cos ((2 * (d : ℝ) - 1) * Real.pi / (r : ℝ)) := by
          rw [hθ_eq]
          simp only [d]
          split_ifs with hjk
          · rw [← Real.cos_neg]
            congr 1
            rw [Nat.cast_sub (le_of_lt hjk)]
            have hk_r : (2 : ℝ) * (k : ℝ) = (r : ℝ) := by exact_mod_cast hk2
            field_simp; linarith
          · congr 1
            rw [Nat.cast_add, Nat.cast_sub (by omega : k ≤ j)]
            have hk_r : (2 : ℝ) * (k : ℝ) = (r : ℝ) := by exact_mod_cast hk2
            push_cast; field_simp; linarith
        rw [hcos_eq, sub_self, zero_pow (by norm_num)]
      · rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
            Polynomial.eval_prod]
        have hk2 : 2 * k + 1 = r := by
          have hodd : r % 2 = 1 := by by_contra h0; exact hev (Nat.even_iff.mpr (by omega))
          omega
        by_cases hjk : j = k
        · have hθ0 : θ = 0 := by
            rw [hθ_eq, hjk]
            have hk_r : 2 * (k : ℝ) + 1 = (r : ℝ) := by exact_mod_cast hk2
            have hnum : 2 * (k : ℝ) - ((r : ℝ) - 1) = 0 := by linarith
            rw [hnum, zero_mul, zero_div]
          rw [hθ0, Real.cos_zero, sub_self, zero_mul]
        · apply mul_eq_zero_of_right
          set d : ℕ := if j < k then k - j else j - k
          have hd_mem : d ∈ Finset.Ico 1 k := by rw [Finset.mem_Ico]; simp only [d]; split_ifs <;> omega
          apply Finset.prod_eq_zero hd_mem
          simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
          have hcos_eq : Real.cos θ = Real.cos ((2 * (d : ℝ)) * Real.pi / (r : ℝ)) := by
            rw [hθ_eq]; simp only [d]
            split_ifs with hlt
            · rw [← Real.cos_neg]; congr 1
              rw [Nat.cast_sub (le_of_lt hlt)]
              have hk_r : 2 * (k : ℝ) + 1 = (r : ℝ) := by exact_mod_cast hk2
              field_simp; linarith
            · congr 1
              rw [Nat.cast_sub (by omega : k ≤ j)]
              have hk_r : 2 * (k : ℝ) + 1 = (r : ℝ) := by exact_mod_cast hk2
              field_simp; linarith
          rw [hcos_eq, sub_self, zero_pow (by norm_num)]
    have hnode_0 : Real.cos (2 * Real.pi * (-(r - 1 : ℝ) / (2 * (r : ℝ)) + ((0 : ℕ) : ℝ) / (r : ℝ))) = c_k := by
      simp only [Nat.cast_zero, zero_div, add_zero]
      rw [show 2 * Real.pi * (-(r - 1 : ℝ) / (2 * (r : ℝ))) = -(((r : ℝ) - 1) * Real.pi / (r : ℝ)) by
        field_simp, Real.cos_neg]
    have hnode_end : Real.cos (2 * Real.pi * (-(r - 1 : ℝ) / (2 * (r : ℝ)) + ((r - 1 : ℕ) : ℝ) / (r : ℝ))) = c_k := by
      rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
      congr 1; field_simp; ring
    have hP_int : ∫ x, P.eval (Real.cos (2 * Real.pi * x)) ∂ν = 0 := by
      rw [integral_poly_cos_eq_quadrature hr2 hν_zeros P hP_deg]
      suffices ∑ j ∈ Finset.range r,
          P.eval (Real.cos (2 * Real.pi * (-(r - 1 : ℝ) / (2 * (r : ℝ)) + (j : ℝ) / (r : ℝ)))) = 0 by
        rw [this, mul_zero]
      apply Finset.sum_eq_zero; intro j hj
      have hj_lt := Finset.mem_range.mp hj
      simp only [P, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      by_cases hj0 : j = 0
      · subst hj0; rw [hnode_0, sub_self, zero_mul]
      · by_cases hje : j = r - 1
        · subst hje; rw [hnode_end, sub_self, zero_mul]
        · rw [hQ_inner_zero j (by omega) (by omega), mul_zero]
    have hQ_int_pos : 0 < ∫ x, Q.eval (Real.cos (2 * Real.pi * x)) ∂ν := by
      rw [integral_poly_cos_eq_quadrature hr2 hν_zeros Q (by omega)]
      apply mul_pos (by positivity)
      have h0mem : 0 ∈ Finset.range r := Finset.mem_range.mpr (by omega)
      have hnn : ∀ j ∈ Finset.range r,
          0 ≤ Q.eval (Real.cos (2 * Real.pi * (-(r - 1 : ℝ) / (2 * (r : ℝ)) + (j : ℝ) / (r : ℝ)))) :=
        fun j _ => hQ_nn _ (Real.cos_le_one _)
      have hle := Finset.single_le_sum hnn h0mem
      rw [hnode_0] at hle
      linarith
    have hgap_cos : c_k < Real.cos (2 * Real.pi * b) := by
      apply Real.strictAntiOn_cos
      · exact ⟨by positivity, by
          have h1 : 2 * Real.pi * b < ((r : ℝ) - 1) * Real.pi / (r : ℝ) := by
            have := mul_lt_mul_of_pos_left hb_lt (show (0 : ℝ) < 2 * Real.pi by positivity)
            convert this using 1; field_simp
          have h2 : ((r : ℝ) - 1) * Real.pi / (r : ℝ) ≤ Real.pi := by
            rw [div_le_iff₀ hrpos]; nlinarith [Real.pi_pos]
          linarith⟩
      · exact ⟨by positivity, by rw [div_le_iff₀ hrpos]; nlinarith [Real.pi_pos]⟩
      · have := mul_lt_mul_of_pos_left hb_lt (show (0 : ℝ) < 2 * Real.pi by positivity)
        convert this using 1; field_simp
    exact poly_cos_contradiction hb_nn hb_le_half hν_supp hgap_cos Q hQ_nn hP_int hQ_int_pos

/-- **Gabardo–Lai Lemma 2.2 (`lem0`):**
If `μ ∗ ν = lebHalf`, `sInf μ.support = -a`, `sSup μ.support = a` with `0 < a < 1/2`, and
`r ≥ 1` is the smallest positive integer with `ft μ r = 0`, then `1 / (4 r) ≤ a ≤ 1 / (2 r)`. -/
theorem gabardo_lai_lem0 {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : ℝ} (ha0 : 0 < a) (ha_half : a < 1 / 2)
    (hconv : μ ∗ ν = lebHalf)
    (hinf_μ : sInf μ.support = -a) (hsup_μ : sSup μ.support = a)
    {r : ℕ} (hr1 : 1 ≤ r) (hμr : ft μ r = 0)
    (hr_min : ∀ m : ℕ, 1 ≤ m → m < r → ft μ m ≠ 0) :
    1 / (4 * (r : ℝ)) ≤ a ∧ a ≤ 1 / (2 * (r : ℝ)) :=
  ⟨gabardo_lai_lem0_lower ha0 ha_half hconv hinf_μ hsup_μ hr1 hμr,
   gabardo_lai_lem0_upper ha0 ha_half hconv hinf_μ hsup_μ hr1 hr_min⟩

end

end AlmostPerfect
