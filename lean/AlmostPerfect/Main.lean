import AlmostPerfect.Basic
import AlmostPerfect.ModularLift
import AlmostPerfect.LimsupBounds
import AlmostPerfect.PolynomialInvariants
import AlmostPerfect.DifferenceDensity
import AlmostPerfect.ForwardDoubling
import AlmostPerfect.PolynomialRigidity
import AlmostPerfect.WeakLimit
import Mathlib.Tactic

/-!
# Section 7: Exact Classification Theorem, Conjecture 1.3, and Corollary 2

Assembles all preceding sections into the final theorems of the paper:
1. `main_classification` (**Main Theorem**): Every pair `(A, B)` of infinite almost perfect
   additive complements with `limsup A(x)B(x)/x < 8/5` is a modular lift (`IsModularLift A B`).
2. `conjecture_1_3` (**Corollary 1 / Conjecture 1.3 of van Doorn–Liu–Tang**): Every pair of
   infinite almost perfect additive complements satisfies either
   `limsup A(x)B(x)/x = 3/2` or `8/5 ≤ limsup A(x)B(x)/x ≤ 2`.
3. `no_repeated_sums_below_eight_fifths` (**Corollary 2**): Whenever `limsup A(x)B(x)/x < 8/5`,
   every nonnegative integer has at most one representation `a + b = n` (`repCount A B n ≤ 1`).
-/

namespace AlmostPerfect

open Polynomial BigOperators Filter

noncomputable section

/-! ### Symmetry Helpers -/

private lemma repCount_symm (A B : Set ℕ) (n : ℕ) : repCount A B n = repCount B A n := by
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

private lemma repTrunc_symm (A B : Set ℕ) (N n : ℕ) : repTrunc A B N n = repTrunc B A N n := by
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

private lemma crossExcess_symm (A B : Set ℕ) (N : ℕ) : crossExcess A B N = crossExcess B A N := by
  unfold crossExcess
  apply Finset.sum_congr rfl; intro m _; exact repTrunc_symm A B N _

private lemma VPoly_symm (A B : Set ℕ) (n₀ : ℕ) : VPoly A B n₀ = VPoly B A n₀ := by
  unfold VPoly
  congr 2; apply Finset.sum_congr rfl; intro n _; rw [repCount_symm]

private lemma WPoly_symm (A B : Set ℕ) (N : ℕ) : WPoly A B N = WPoly B A N := by
  unfold WPoly
  congr 2; apply Finset.sum_congr rfl; intro m _; rw [repTrunc_symm]

private lemma errSum_symm (A B : Set ℕ) (n₀ : ℕ) : errSum A B n₀ = errSum B A n₀ := by
  unfold errSum; apply Finset.sum_congr rfl; intro n _; rw [repCount_symm]

/-! ### Finite Truncations of `ABin` -/

private def ABinTrunc (i : ℕ) : Set ℕ := {m : ℕ | m ∈ ABin ∧ m < 4 ^ i}

private lemma ABinTrunc_zero (m : ℕ) : m ∈ ABinTrunc 0 ↔ m = 0 := by
  simp only [ABinTrunc, Set.mem_ofPred_eq, pow_zero]
  constructor
  · intro h; omega
  · rintro rfl; exact ⟨fun i => by simp, by norm_num⟩

private lemma ABinTrunc_succ (i m : ℕ) :
    m ∈ ABinTrunc (i + 1) ↔ m ∈ ABinTrunc i ∨ ∃ m' ∈ ABinTrunc i, m = 4 ^ i + m' := by
  have h4pos : 0 < 4 ^ i := Nat.pow_pos (by decide)
  constructor
  · intro ⟨hmA, hmlt⟩
    by_cases hlt : m < 4 ^ i
    · left; exact ⟨hmA, hlt⟩
    · right
      have hd_lt4 : m / 4 ^ i < 4 := by
        rw [Nat.div_lt_iff_lt_mul h4pos]
        simpa [pow_succ'] using hmlt
      have hd_ge1 : 1 ≤ m / 4 ^ i := (Nat.le_div_iff_mul_le h4pos).mpr (by omega)
      have hd_le1 : (m / 4 ^ i) % 4 ≤ 1 := hmA i
      have hd_eq1 : m / 4 ^ i = 1 := by omega
      have hm_lt2 : m < 2 * 4 ^ i := by
        have hdiv := Nat.div_add_mod m (4 ^ i)
        rw [hd_eq1] at hdiv
        have := Nat.mod_lt m h4pos
        omega
      refine ⟨m - 4 ^ i, ⟨?_, by omega⟩, by omega⟩
      intro j
      by_cases hji : j < i
      · have hdiv_eq : (m - 4 ^ i) / 4 ^ j + 4 ^ (i - j) = m / 4 ^ j := by
          have hpow : 4 ^ i = 4 ^ (i - j) * 4 ^ j := by
            rw [← pow_add, Nat.sub_add_cancel (le_of_lt hji)]
          have hpos_j : 0 < 4 ^ j := Nat.pow_pos (by decide)
          rw [← Nat.add_mul_div_right _ _ hpos_j, ← hpow, Nat.sub_add_cancel (by omega)]
        have h4dvd : 4 ∣ 4 ^ (i - j) := dvd_pow_self 4 (by omega)
        rcases h4dvd with ⟨q, hq⟩
        have hmod : (m - 4 ^ i) / 4 ^ j % 4 = m / 4 ^ j % 4 := by
          rw [← hdiv_eq, hq]; omega
        rw [hmod]; exact hmA j
      · have hlt_j : m - 4 ^ i < 4 ^ j := by
          have hpow : 4 ^ i ≤ 4 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
          omega
        rw [Nat.div_eq_of_lt hlt_j]; simp
  · rintro (⟨hmA, hmlt⟩ | ⟨m', ⟨hm'A, hm'lt⟩, rfl⟩)
    · exact ⟨hmA, lt_of_lt_of_le hmlt (Nat.pow_le_pow_right (by decide) (Nat.le_succ i))⟩
    · refine ⟨?_, ?_⟩
      · intro j
        by_cases hji : j < i
        · have hpow : 4 ^ i = 4 ^ (i - j) * 4 ^ j := by
            rw [← pow_add, Nat.sub_add_cancel (le_of_lt hji)]
          have hpos_j : 0 < 4 ^ j := Nat.pow_pos (by decide)
          have hdiv : (4 ^ i + m') / 4 ^ j = 4 ^ (i - j) + m' / 4 ^ j := by
            rw [add_comm, hpow, Nat.add_mul_div_right _ _ hpos_j, add_comm]
          have h4dvd : 4 ∣ 4 ^ (i - j) := dvd_pow_self 4 (by omega)
          rcases h4dvd with ⟨q, hq⟩
          rw [hdiv, hq]
          have hmod : (4 * q + m' / 4 ^ j) % 4 = (m' / 4 ^ j) % 4 := by omega
          rw [hmod]; exact hm'A j
        · by_cases hjeq : j = i
          · subst j
            have hdiv : (4 ^ i + m') / 4 ^ i = 1 := by
              have hrew : 4 ^ i + m' = m' + 1 * 4 ^ i := by omega
              rw [hrew, Nat.add_mul_div_right _ _ h4pos, Nat.div_eq_of_lt hm'lt, zero_add]
            rw [hdiv]
          · have hjgt : i + 1 ≤ j := by omega
            have hlt_j : 4 ^ i + m' < 4 ^ j := by
              have h1 : 4 ^ i + m' < 2 * 4 ^ i := by omega
              have h2 : 2 * 4 ^ i ≤ 4 ^ (i + 1) := by rw [pow_succ']; omega
              have h3 : 4 ^ (i + 1) ≤ 4 ^ j := Nat.pow_le_pow_right (by decide) hjgt
              omega
            rw [Nat.div_eq_of_lt hlt_j]; simp
      · rw [pow_succ']; omega

private lemma ABinTrunc_mul_three_le (i m : ℕ) (hm : m ∈ ABinTrunc i) :
    3 * m ≤ 4 ^ i - 1 := by
  induction i generalizing m with
  | zero =>
    rw [ABinTrunc_zero] at hm; subst hm; simp
  | succ i ih =>
    have h4pos : 1 ≤ 4 ^ i := Nat.one_le_pow i 4 (by decide)
    rw [ABinTrunc_succ] at hm
    rcases hm with h | ⟨m', hm', rfl⟩
    · have := ih m h; rw [pow_succ']; omega
    · have := ih m' hm'; rw [pow_succ']; omega

/-! ### Step 1: Polynomial Rigidity at Bounded-Crossing Levels -/

private lemma step1_rigidity {A B : Set ℕ} (hA_inf : A.Infinite) (hB_inf : B.Infinite)
    {n₀ K₀ N_star : ℕ} (hn0 : 1 ≤ n₀) (hstab : ∀ n ≥ n₀, repCount A B n = 1)
    (_hK₀_n0 : n₀ ≤ K₀) (_hK₀_E : errSum A B n₀ ≤ K₀)
    (hN_star : ∀ N ≥ N_star, crossExcess A B N ≤
        2 ^ (max n₀ (errSum A B n₀ + 2) + 1) * (K₀ + errSum A B n₀ + 2 * n₀) →
        LevelApprox A B n₀ (2 ^ (max n₀ (errSum A B n₀ + 2) + 1) * (K₀ + errSum A B n₀ + 2 * n₀)) N ∨
        LevelApprox B A n₀ (2 ^ (max n₀ (errSum A B n₀ + 2) + 1) * (K₀ + errSum A B n₀ + 2 * n₀)) N)
    {N₀ : ℕ} (hN₀_ge : N_star ≤ N₀) (hT₀ : crossExcess A B N₀ ≤ K₀) :
    stripPoly (WPoly A B N₀) = stripPoly (VPoly A B n₀) := by
  set E := errSum A B n₀
  set E' := E + 1
  set k := max n₀ (E' + 1) + 1
  set K_max := 2 ^ k * (K₀ + E + 2 * n₀)
  have hstab_sym : ∀ n ≥ n₀, repCount B A n = 1 := fun n hn => by
    rw [repCount_symm]; exact hstab n hn
  have hAne : A.Nonempty := hA_inf.nonempty
  have hBne : B.Nonempty := hB_inf.nonempty
  have hV_props := VPoly_strip_properties hAne hBne hstab
  -- Inductively construct N^(0), ..., N^(k) with quadratic recurrence on stripPoly W
  have hchain : ∀ j ≤ k, ∃ f : ℕ → ℕ,
      f 0 = N₀ ∧
      (∀ i ≤ j, N_star ≤ f i ∧ n₀ ≤ f i ∧
        crossExcess A B (f i) + (E + 2 * n₀) ≤ 2 ^ i * (K₀ + E + 2 * n₀)) ∧
      (∀ i < j, stripPoly (VPoly A B n₀) * stripPoly (WPoly A B (f (i + 1))) =
        (stripPoly (WPoly A B (f i))) ^ 2) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hK_le0 : crossExcess A B N₀ ≤ K_max := by
        have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        have : K₀ ≤ K_max := by
          calc K₀ ≤ 1 * (K₀ + E + 2 * n₀) := by omega
            _ ≤ 2 ^ k * (K₀ + E + 2 * n₀) := Nat.mul_le_mul_right _ hpow
        omega
      have hN₀_n0 : n₀ ≤ N₀ := by
        rcases hN_star N₀ hN₀_ge hK_le0 with hL | hL
        · have := hL.hN_large; nlinarith
        · have := hL.hN_large; nlinarith
      refine ⟨fun _ => N₀, rfl, ?_, fun i hi => by omega⟩
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      refine ⟨hN₀_ge, hN₀_n0, ?_⟩
      simp only [pow_zero, one_mul]; omega
    | succ j ih =>
      intro hjk
      obtain ⟨f, hf0, hf_bd, hf_rec⟩ := ih (by omega)
      have hj_bd := hf_bd j le_rfl
      have hTj_le : crossExcess A B (f j) ≤ K_max := by
        have hpow : 2 ^ j ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
        have hmul : 2 ^ j * (K₀ + E + 2 * n₀) ≤ 2 ^ k * (K₀ + E + 2 * n₀) :=
          Nat.mul_le_mul_right _ hpow
        omega
      -- Apply forward_doubling_step in whichever orientation holds at f j
      have hstep : ∃ N_next : ℕ, f j < N_next ∧
          crossExcess A B N_next ≤ 2 * crossExcess A B (f j) + E + 2 * n₀ ∧
          stripPoly (VPoly A B n₀) * stripPoly (WPoly A B N_next) =
            (stripPoly (WPoly A B (f j))) ^ 2 := by
        rcases hN_star (f j) hj_bd.1 hTj_le with hL | hL
        · obtain ⟨d⟩ := forward_doubling_step hA_inf hB_inf hn0 hstab hL
          exact ⟨d.N₁', d.hN₁'_gt, d.hT_bound, d.hstrip_quad⟩
        · obtain ⟨d⟩ := forward_doubling_step hB_inf hA_inf hn0 hstab_sym hL
          refine ⟨d.N₁', d.hN₁'_gt, ?_, ?_⟩
          · rw [crossExcess_symm A B d.N₁', crossExcess_symm A B (f j),
                show E = errSum B A n₀ from errSum_symm A B n₀]
            exact d.hT_bound
          · rw [VPoly_symm A B n₀, WPoly_symm A B d.N₁', WPoly_symm A B (f j)]
            exact d.hstrip_quad
      obtain ⟨N_next, hgt, hTnext, hquad⟩ := hstep
      let f' : ℕ → ℕ := fun i => if i = j + 1 then N_next else f i
      refine ⟨f', ?_, ?_, ?_⟩
      · have h0 : (0 : ℕ) ≠ j + 1 := by omega
        simp only [f', h0, ↓reduceIte, hf0]
      · intro i hi
        by_cases heq : i = j + 1
        · subst heq
          simp only [f', ↓reduceIte]
          refine ⟨le_trans hj_bd.1 (le_of_lt hgt), le_trans hj_bd.2.1 (le_of_lt hgt), ?_⟩
          have h2 : 2 ^ (j + 1) * (K₀ + E + 2 * n₀) = 2 * (2 ^ j * (K₀ + E + 2 * n₀)) := by
            rw [pow_succ']; ring
          omega
        · simp only [f', heq, ↓reduceIte]
          exact hf_bd i (by omega)
      · intro i hi
        by_cases heq : i = j
        · rw [heq]
          have hne : j ≠ j + 1 := by omega
          simp only [f', ↓reduceIte, hne]
          exact hquad
        · have hne1 : i + 1 ≠ j + 1 := by omega
          have hne2 : i ≠ j + 1 := by omega
          simp only [f', hne1, hne2, ↓reduceIte]
          exact hf_rec i (by omega)
  obtain ⟨f, hf0, hf_bd, hf_rec⟩ := hchain k le_rfl
  have hVbound : ∀ d : ℕ, |(stripPoly (VPoly A B n₀)).coeff d| ≤ (E' : ℤ) := by
    intro d
    cases d with
    | zero => rw [hV_props.2.1]; norm_num; omega
    | succ m =>
      have := hV_props.2.2.2.2.1 (m + 1) (Nat.succ_pos m)
      have hEE' : (E : ℤ) ≤ (E' : ℤ) := by simp only [E']; omega
      exact le_trans this hEE'
  have hW0 : (stripPoly (WPoly A B (f 0))).coeff 0 = 1 :=
    (WPoly_strip_properties hstab (hf_bd 0 (Nat.zero_le k)).2.1).1
  have hWbound : ∀ j ≤ k, ∀ d : ℕ, |(stripPoly (WPoly A B (f j))).coeff d| ≤ 1 :=
    fun j hj => (WPoly_strip_properties hstab (hf_bd j hj).2.1).2.2.1
  have hk_lt_pow : k < 2 ^ k := Nat.lt_two_pow_self
  have hk_deg : (stripPoly (VPoly A B n₀)).natDegree < 2 ^ k := by
    have := hV_props.2.2.2.1
    have : n₀ < k := by simp only [k]; omega
    omega
  have hk_E : E' + 1 < 2 ^ k := by
    have : E' + 1 < k := by simp only [k]; omega
    omega
  have hrig := polynomial_iteration_rigidity (stripPoly (VPoly A B n₀))
    (fun j => stripPoly (WPoly A B (f j))) k E'
    hV_props.2.1 hVbound hW0 hWbound hf_rec hk_deg hk_E 0 (Nat.zero_le k)
  rwa [hf0] at hrig

/-! ### Step 2 Helper: Single Exact Doubling Step under `W̃_N = Ṽ` -/

private lemma exact_doubling_step {A B : Set ℕ} (hA_inf : A.Infinite) (hB_inf : B.Infinite)
    {n₀ K_max N_star N : ℕ} (hn0 : 1 ≤ n₀) (hstab : ∀ n ≥ n₀, repCount A B n = 1)
    (hE_le_Kmax : errSum A B n₀ ≤ K_max)
    (hN_star : ∀ M ≥ N_star, crossExcess A B M ≤ K_max →
      LevelApprox A B n₀ K_max M ∨ LevelApprox B A n₀ K_max M)
    (hN_ge_star : N_star ≤ N)
    (hL : LevelApprox A B n₀ K_max N)
    (hW_eq : stripPoly (WPoly A B N) = stripPoly (VPoly A B n₀)) :
    let y := nextGt hA_inf N
    let D := y - minElem A
    let N₁ := 2 * D + min (minElem A) (minElem B) - 1
    N < N₁ ∧
    (∀ a ≤ N₁, a ∈ A ↔ (a ≤ N ∧ a ∈ A) ∨ (∃ a₀ ∈ A, a₀ ≤ N ∧ a = D + a₀)) ∧
    (∀ b ≤ N₁, b ∈ B ↔ b ≤ N ∧ b ∈ B) ∧
    stripPoly (WPoly A B N₁) = stripPoly (VPoly A B n₀) ∧
    crossExcess A B N₁ ≤ errSum A B n₀ ∧
    LevelApprox B A n₀ K_max N₁ ∧
    nextGt hB_inf N₁ = 2 * D + minElem B ∧
    X ^ (N + 1) * WPoly A B N = X ^ D * VPoly A B n₀ := by
  intro y D N₁
  have hAne : A.Nonempty := hA_inf.nonempty
  have hBne : B.Nonempty := hB_inf.nonempty
  have hV_props := VPoly_strip_properties hAne hBne hstab
  have hVstrip_ne : stripPoly (VPoly A B n₀) ≠ 0 := by
    intro h0; have := hV_props.2.1; rw [h0] at this; simp at this
  have hN_ge_n0 : n₀ ≤ N := by have := hL.hN_large; nlinarith
  have hm0_le : mZero A B ≤ n₀ := mZero_le_n0 hstab
  have hamin_le : minElem A ≤ n₀ := by unfold mZero at hm0_le; omega
  have hbmin_le : minElem B ≤ n₀ := by unfold mZero at hm0_le; omega
  have hy_spec := nextGt_spec hA_inf N
  have hy_51 := lemma_5_1 hA_inf hn0 hstab hL
  obtain ⟨d⟩ := forward_doubling_step hA_inf hB_inf hn0 hstab hL
  -- 1. Identify stripPoly d.U₁ = stripPoly (VPoly A B n₀)
  have hU1_strip : stripPoly d.U₁ = stripPoly (VPoly A B n₀) := by
    have hWN_fac : WPoly A B N = X ^ (y - (N + 1) + d.U₁.natTrailingDegree) * stripPoly d.U₁ := by
      rw [d.hWN_U1, pow_add, mul_assoc, X_pow_mul_stripPoly]
    have hst := (stripPoly_eq_of_X_pow_mul hWN_fac (by rw [d.hU₁_strip0]; norm_num)).2
    rw [← hst, hW_eq]
  -- 2. Cancel stripPoly V in d.hPA1_V to get shiftedTruncPoly * X^(mZero) = truncPoly * X^u₁
  have hcancel : shiftedTruncPoly A y d.T₁ * X ^ mZero A B = truncPoly A N * X ^ d.U₁.natTrailingDegree := by
    have hmul : (shiftedTruncPoly A y d.T₁ * X ^ mZero A B) * stripPoly (VPoly A B n₀) =
        (truncPoly A N * X ^ d.U₁.natTrailingDegree) * stripPoly (VPoly A B n₀) := by
      calc
        (shiftedTruncPoly A y d.T₁ * X ^ mZero A B) * stripPoly (VPoly A B n₀)
            = shiftedTruncPoly A y d.T₁ * (X ^ (VPoly A B n₀).natTrailingDegree * stripPoly (VPoly A B n₀)) := by
              rw [hV_props.1]; ring
        _ = shiftedTruncPoly A y d.T₁ * VPoly A B n₀ := by rw [X_pow_mul_stripPoly]
        _ = truncPoly A N * d.U₁ := d.hPA1_V
        _ = truncPoly A N * (X ^ d.U₁.natTrailingDegree * stripPoly d.U₁) := by rw [X_pow_mul_stripPoly]
        _ = (truncPoly A N * X ^ d.U₁.natTrailingDegree) * stripPoly (VPoly A B n₀) := by
              rw [hU1_strip]; ring
    exact mul_right_cancel₀ hVstrip_ne hmul
  -- 3. Compare natTrailingDegree to deduce d.U₁.natTrailingDegree = minElem B
  have hPA1_0 : (shiftedTruncPoly A y d.T₁).coeff 0 = 1 := by
    rw [shiftedTruncPoly_coeff]; simp only [Nat.zero_le, add_zero, true_and, y, hy_spec.2, ↓reduceIte]
  have hPA1_ne : shiftedTruncPoly A y d.T₁ ≠ 0 := by
    intro h0; rw [h0] at hPA1_0; simp at hPA1_0
  have hPA1_ord : (shiftedTruncPoly A y d.T₁).natTrailingDegree = 0 :=
    Nat.eq_zero_of_le_zero (Polynomial.natTrailingDegree_le_of_ne_zero (by rw [hPA1_0]; norm_num))
  have htrA_ord : (truncPoly A N).natTrailingDegree = minElem A := by
    have hcoeff_min : (truncPoly A N).coeff (minElem A) = 1 := by
      rw [truncPoly_coeff]; simp [show minElem A ≤ N by omega, minElem_mem hAne]
    have htrA_ne : truncPoly A N ≠ 0 := by
      intro h0; rw [h0] at hcoeff_min; simp at hcoeff_min
    apply le_antisymm
    · exact Polynomial.natTrailingDegree_le_of_ne_zero (by rw [hcoeff_min]; norm_num)
    · by_contra hlt; push Not at hlt
      have hnz : (truncPoly A N).coeff (truncPoly A N).natTrailingDegree ≠ 0 :=
        Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr htrA_ne
      rw [truncPoly_coeff] at hnz
      split_ifs at hnz with hmem
      · have := minElem_le hmem.2; omega
      · exact hnz rfl
  have htrA_ne : truncPoly A N ≠ 0 := by
    intro h0
    have hcoeff_min : (truncPoly A N).coeff (minElem A) = 1 := by
      rw [truncPoly_coeff]; simp [show minElem A ≤ N by omega, minElem_mem hAne]
    rw [h0] at hcoeff_min; simp at hcoeff_min
  have hu1_eq : d.U₁.natTrailingDegree = minElem B := by
    have h1 := Polynomial.natTrailingDegree_mul hPA1_ne (pow_ne_zero (mZero A B) X_ne_zero)
    have h2 := Polynomial.natTrailingDegree_mul htrA_ne (pow_ne_zero d.U₁.natTrailingDegree X_ne_zero)
    rw [hcancel, h2, hPA1_ord, htrA_ord, Polynomial.natTrailingDegree_X_pow,
        Polynomial.natTrailingDegree_X_pow] at h1
    unfold mZero at h1; omega
  -- 4. Exact shift polynomial identity X^y * PA1 = X^D * truncPoly A N
  have hshift_poly : X ^ y * shiftedTruncPoly A y d.T₁ = X ^ D * truncPoly A N := by
    have hcancel2 : shiftedTruncPoly A y d.T₁ * X ^ minElem A = truncPoly A N := by
      have hmul : (shiftedTruncPoly A y d.T₁ * X ^ minElem A) * X ^ minElem B =
          truncPoly A N * X ^ minElem B := by
        calc
          (shiftedTruncPoly A y d.T₁ * X ^ minElem A) * X ^ minElem B
              = shiftedTruncPoly A y d.T₁ * X ^ mZero A B := by unfold mZero; rw [pow_add]; ring
          _ = truncPoly A N * X ^ minElem B := by rw [hcancel, hu1_eq]
      exact mul_right_cancel₀ (pow_ne_zero _ X_ne_zero) hmul
    calc
      X ^ y * shiftedTruncPoly A y d.T₁
          = X ^ D * (shiftedTruncPoly A y d.T₁ * X ^ minElem A) := by
            have hy_eq : y = D + minElem A := by omega
            rw [hy_eq, pow_add]; ring
      _ = X ^ D * truncPoly A N := by rw [hcancel2]
  -- 5. Exact identity X^(N+1) * WPoly A B N = X^D * VPoly A B n₀
  have hXW_V : X ^ (N + 1) * WPoly A B N = X ^ D * VPoly A B n₀ := by
    calc
      X ^ (N + 1) * WPoly A B N
          = X ^ (N + 1) * (X ^ (y - (N + 1)) * (X ^ d.U₁.natTrailingDegree * stripPoly d.U₁)) := by
            rw [d.hWN_U1, X_pow_mul_stripPoly]
      _ = X ^ (y + minElem B) * stripPoly (VPoly A B n₀) := by
            rw [hu1_eq, hU1_strip, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
            congr 2; omega
      _ = X ^ D * (X ^ (VPoly A B n₀).natTrailingDegree * stripPoly (VPoly A B n₀)) := by
            rw [hV_props.1, ← mul_assoc, ← pow_add]
            congr 2; unfold mZero; omega
      _ = X ^ D * VPoly A B n₀ := by rw [X_pow_mul_stripPoly]
  -- 6. Identify d.N₁' = N₁
  have hN1_eq : d.N₁' = N₁ := by
    rw [d.hN₁'_formula, hu1_eq]
    unfold mZero N₁ D y
    omega
  -- 7. Exact truncation of A and B up to N₁
  have hA_trunc1 : ∀ a ≤ N₁, a ∈ A ↔ (a ≤ N ∧ a ∈ A) ∨ (∃ a₀ ∈ A, a₀ ≤ N ∧ a = D + a₀) := by
    intro a ha
    rw [← hN1_eq] at ha
    have hA_d := d.hA_trunc a ha
    have hcoeff := congrArg (fun P => P.coeff a) hshift_poly
    rw [coeff_X_pow_mul', coeff_X_pow_mul'] at hcoeff
    have hsecond : (y ≤ a ∧ a ≤ y + d.T₁ ∧ a ∈ A) ↔ (∃ a₀ ∈ A, a₀ ≤ N ∧ a = D + a₀) := by
      constructor
      · intro ⟨hya, haT, haA⟩
        have hlhs : (if y ≤ a then (shiftedTruncPoly A y d.T₁).coeff (a - y) else 0) = 1 := by
          simp only [hya, ↓reduceIte, shiftedTruncPoly_coeff]
          have hadd : y + (a - y) = a := by omega
          simp [hadd, show a - y ≤ d.T₁ by omega, haA]
        rw [hlhs] at hcoeff
        split_ifs at hcoeff with hDa
        · rw [truncPoly_coeff] at hcoeff
          split_ifs at hcoeff with hmem
          · exact ⟨a - D, hmem.2, hmem.1, by omega⟩
          · norm_num at hcoeff
        · norm_num at hcoeff
      · rintro ⟨a₀, ha₀A, ha₀N, rfl⟩
        have hrhs : (if D ≤ D + a₀ then (truncPoly A N).coeff (D + a₀ - D) else 0) = 1 := by
          simp only [Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left, truncPoly_coeff, ha₀N, ha₀A, and_self]
        rw [hrhs] at hcoeff
        split_ifs at hcoeff with hya
        · rw [shiftedTruncPoly_coeff] at hcoeff
          split_ifs at hcoeff with hmem
          · have hadd : y + (D + a₀ - y) = D + a₀ := by omega
            rw [hadd] at hmem
            exact ⟨hya, by omega, hmem.2⟩
          · norm_num at hcoeff
        · norm_num at hcoeff
    exact hA_d.trans ⟨fun h => h.imp id hsecond.mp, fun h => h.imp id hsecond.mpr⟩
  have hB_trunc1 : ∀ b ≤ N₁, b ∈ B ↔ b ≤ N ∧ b ∈ B := fun b hb =>
    d.hB_trunc b (by rw [hN1_eq]; exact hb)
  -- 8. Exact WPoly at N₁ and crossExcess A B N₁ ≤ E
  have hW_strip1 : stripPoly (WPoly A B N₁) = stripPoly (VPoly A B n₀) := by
    have hq := d.hstrip_quad
    rw [hN1_eq, hW_eq, sq] at hq
    exact mul_left_cancel₀ hVstrip_ne hq
  have hW_exact1 : WPoly A B N₁ = X ^ max (minElem A) (minElem B) * stripPoly (VPoly A B n₀) := by
    rw [← hW_strip1, ← hN1_eq, ← d.hW_ord, X_pow_mul_stripPoly]
  have hT_N1 : crossExcess A B N₁ ≤ errSum A B n₀ := by
    have hd_V := congrArg (fun P => (Polynomial.derivative P).eval 1) (X_pow_mul_stripPoly (VPoly A B n₀))
    simp only [derivative_mul, derivative_pow, derivative_X, mul_one, eval_add, eval_mul, eval_pow,
      eval_X, eval_C, one_pow, hV_props.1, hV_props.2.2.1, hV_props.2.2.2.2.2] at hd_V
    have hd_W := congrArg (fun P => (Polynomial.derivative P).eval 1) hW_exact1
    simp only [derivative_mul, derivative_pow, derivative_X, mul_one, eval_add, eval_mul, eval_pow,
      eval_X, eval_C, one_pow, hV_props.2.2.1, WPoly_deriv_eval_one] at hd_W
    have hc_ge : -(errSum A B n₀ : ℤ) ≤ errSigned A B n₀ := (abs_le.mp (abs_errSigned_le_errSum A B n₀)).1
    have hmin_le : ((max (minElem A) (minElem B) : ℕ) : ℤ) ≤ (mZero A B : ℤ) := by
      have hnat : max (minElem A) (minElem B) ≤ mZero A B := by unfold mZero; omega
      exact_mod_cast hnat
    have hT_z : (crossExcess A B N₁ : ℤ) ≤ (errSum A B n₀ : ℤ) := by linarith
    exact_mod_cast hT_z
  -- 9. Orientation flips: LevelApprox B A n₀ K_max N₁ MUST hold
  have hN1_gt : N < N₁ := by rw [← hN1_eq]; exact d.hN₁'_gt
  have hL_next : LevelApprox B A n₀ K_max N₁ := by
    rcases hN_star N₁ (le_trans hN_ge_star (le_of_lt hN1_gt)) (le_trans hT_N1 hE_le_Kmax) with hbad | hgood
    · exfalso
      -- Witness a_big = D + maxLe A N ∈ A ∩ [0, N₁] exceeds (1/3 + 1/1000) * N₁!
      obtain ⟨a₀, ha₀A, ha₀N, ha₀_lo⟩ := hL.hx₀_lo
      have ha₀_hi : (a₀ : ℝ) ≤ (1 / 3 + 1 / 1000 : ℝ) * (N : ℝ) := hL.hx₀_hi a₀ ha₀A ha₀N
      have hN_lin : (10 ^ 7 : ℝ) * ((n₀ : ℝ) + 1) ≤ (N : ℝ) := by
        have hnat : 10 ^ 7 * (n₀ + 1) ≤ N := by have := hL.hN_large; nlinarith
        exact_mod_cast hnat
      have hD_le : (D : ℝ) ≤ (1 + 8 / 1000 : ℝ) * (N : ℝ) := by
        have h1 : D ≤ y := Nat.sub_le _ _
        have h2 : (D : ℝ) ≤ (y : ℝ) := by exact_mod_cast h1
        linarith [hy_51.2]
      have hD_ge : (N : ℝ) - (n₀ : ℝ) ≤ (D : ℝ) := by
        have : N ≤ D + n₀ := by omega
        have : (N : ℝ) ≤ (D : ℝ) + (n₀ : ℝ) := by exact_mod_cast this
        linarith
      have hN1_lo_r : 2 * (N : ℝ) - 2 * (n₀ : ℝ) ≤ (N₁ : ℝ) := by
        have h1 : 2 * N - 2 * n₀ ≤ N₁ := by rw [← hN1_eq]; exact d.hN₁'_lo
        have h2 : ((2 * N - 2 * n₀ : ℕ) : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast h1
        rw [Nat.cast_sub (by omega)] at h2; push_cast at h2; linarith
      have hN1_hi_r : (N₁ : ℝ) ≤ (2 + 17 / 1000 : ℝ) * (N : ℝ) := by
        rw [← hN1_eq]; exact d.hN₁'_hi
      have hbig_le_N1 : D + a₀ ≤ N₁ := by
        have : ((D + a₀ : ℕ) : ℝ) ≤ (N₁ : ℝ) := by push_cast; linarith
        exact_mod_cast this
      have hbig_mem : D + a₀ ∈ A := (hA_trunc1 (D + a₀) hbig_le_N1).mpr (Or.inr ⟨a₀, ha₀A, ha₀N, rfl⟩)
      have hbad_hi := hbad.hx₀_hi (D + a₀) hbig_mem hbig_le_N1
      push_cast at hbad_hi
      linarith
    · exact hgood
  -- 10. Exact value of nextGt hB_inf N₁ = 2 * D + minElem B
  have hw_eq : nextGt hB_inf N₁ = 2 * D + minElem B := by
    have hstab_sym : ∀ n ≥ n₀, repCount B A n = 1 := fun n hn => by
      rw [repCount_symm]; exact hstab n hn
    obtain ⟨d2⟩ := forward_doubling_step hB_inf hA_inf hn0 hstab_sym hL_next
    set w := nextGt hB_inf N₁
    have hw_spec := nextGt_spec hB_inf N₁
    have hW_sym : stripPoly (WPoly B A N₁) = stripPoly (VPoly B A n₀) := by
      rw [WPoly_symm B A N₁, VPoly_symm B A n₀]; exact hW_strip1
    have hU2_strip : stripPoly d2.U₁ = stripPoly (VPoly B A n₀) := by
      have hWN_fac : WPoly B A N₁ = X ^ (w - (N₁ + 1) + d2.U₁.natTrailingDegree) * stripPoly d2.U₁ := by
        rw [d2.hWN_U1, pow_add, mul_assoc, X_pow_mul_stripPoly]
      have hst := (stripPoly_eq_of_X_pow_mul hWN_fac (by rw [d2.hU₁_strip0]; norm_num)).2
      rw [← hst, hW_sym]
    have hVsym_ne : stripPoly (VPoly B A n₀) ≠ 0 := by
      rw [VPoly_symm B A n₀]; exact hVstrip_ne
    have hcancel2 : shiftedTruncPoly B w d2.T₁ * X ^ mZero B A = truncPoly B N₁ * X ^ d2.U₁.natTrailingDegree := by
      have hV_props2 := VPoly_strip_properties hBne hAne hstab_sym
      have hmul : (shiftedTruncPoly B w d2.T₁ * X ^ mZero B A) * stripPoly (VPoly B A n₀) =
          (truncPoly B N₁ * X ^ d2.U₁.natTrailingDegree) * stripPoly (VPoly B A n₀) := by
        calc
          (shiftedTruncPoly B w d2.T₁ * X ^ mZero B A) * stripPoly (VPoly B A n₀)
              = shiftedTruncPoly B w d2.T₁ * (X ^ (VPoly B A n₀).natTrailingDegree * stripPoly (VPoly B A n₀)) := by
                rw [hV_props2.1]; ring
          _ = shiftedTruncPoly B w d2.T₁ * VPoly B A n₀ := by rw [X_pow_mul_stripPoly]
          _ = truncPoly B N₁ * d2.U₁ := d2.hPA1_V
          _ = truncPoly B N₁ * (X ^ d2.U₁.natTrailingDegree * stripPoly d2.U₁) := by rw [X_pow_mul_stripPoly]
          _ = (truncPoly B N₁ * X ^ d2.U₁.natTrailingDegree) * stripPoly (VPoly B A n₀) := by
                rw [hU2_strip]; ring
      exact mul_right_cancel₀ hVsym_ne hmul
    have hPB1_0 : (shiftedTruncPoly B w d2.T₁).coeff 0 = 1 := by
      rw [shiftedTruncPoly_coeff]; simp only [Nat.zero_le, add_zero, true_and, w, hw_spec.2, ↓reduceIte]
    have hPB1_ne : shiftedTruncPoly B w d2.T₁ ≠ 0 := by
      intro h0; rw [h0] at hPB1_0; simp at hPB1_0
    have hPB1_ord : (shiftedTruncPoly B w d2.T₁).natTrailingDegree = 0 :=
      Nat.eq_zero_of_le_zero (Polynomial.natTrailingDegree_le_of_ne_zero (by rw [hPB1_0]; norm_num))
    have htrB_ne : truncPoly B N₁ ≠ 0 := by
      intro h0
      have hcoeff_min : (truncPoly B N₁).coeff (minElem B) = 1 := by
        rw [truncPoly_coeff]; simp [show minElem B ≤ N₁ by omega, minElem_mem hBne]
      rw [h0] at hcoeff_min; simp at hcoeff_min
    have htrB_ord : (truncPoly B N₁).natTrailingDegree = minElem B := by
      have hcoeff_min : (truncPoly B N₁).coeff (minElem B) = 1 := by
        rw [truncPoly_coeff]; simp [show minElem B ≤ N₁ by omega, minElem_mem hBne]
      apply le_antisymm
      · exact Polynomial.natTrailingDegree_le_of_ne_zero (by rw [hcoeff_min]; norm_num)
      · by_contra hlt; push Not at hlt
        have hnz : (truncPoly B N₁).coeff (truncPoly B N₁).natTrailingDegree ≠ 0 :=
          Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr htrB_ne
        rw [truncPoly_coeff] at hnz
        split_ifs at hnz with hmem
        · have := minElem_le hmem.2; omega
        · exact hnz rfl
    have hu2_eq : d2.U₁.natTrailingDegree = minElem A := by
      have h1 := Polynomial.natTrailingDegree_mul hPB1_ne (pow_ne_zero (mZero B A) X_ne_zero)
      have h2 := Polynomial.natTrailingDegree_mul htrB_ne (pow_ne_zero d2.U₁.natTrailingDegree X_ne_zero)
      rw [hcancel2, h2, hPB1_ord, htrB_ord, Polynomial.natTrailingDegree_X_pow,
          Polynomial.natTrailingDegree_X_pow] at h1
      unfold mZero at h1; omega
    have hU2_ne : d2.U₁ ≠ 0 := by
      intro h0; have := d2.hU₁_eval; rw [h0] at this; simp at this
    have hord_W : (WPoly B A N₁).natTrailingDegree = (w - (N₁ + 1)) + minElem A := by
      rw [d2.hWN_U1, Polynomial.natTrailingDegree_mul (pow_ne_zero _ X_ne_zero) hU2_ne,
          Polynomial.natTrailingDegree_X_pow, hu2_eq]
    have hord_W2 : (WPoly B A N₁).natTrailingDegree = max (minElem A) (minElem B) := by
      rw [WPoly_symm B A N₁, ← hN1_eq]; exact d.hW_ord
    have hD_pos : 1 ≤ D := by omega
    have hN1_add1 : N₁ + 1 = 2 * D + min (minElem A) (minElem B) := by
      simp only [N₁]; omega
    omega
  exact ⟨hN1_gt, hA_trunc1, hB_trunc1, hW_strip1, hT_N1, hL_next, hw_eq, hXW_V⟩

/-! ### Step 3 Helper: Bijection Modulo `D₀` from Equation (7.3) -/

private lemma residue_bijection_of_poly_identity {A B : Set ℕ} {n₀ N₀ D₀ : ℕ}
    (hD₀ : 1 ≤ D₀)
    (hA₀_lt : ∀ a ∈ A, a ≤ N₀ → a < D₀)
    (hB₀_lt : ∀ b ∈ B, b ≤ N₀ → b < D₀)
    (hpoly : (1 - X) * (truncPoly A N₀ * truncPoly B N₀) = VPoly A B n₀ * (1 - X ^ D₀)) :
    letI := Classical.decPred (· ∈ A)
    letI := Classical.decPred (· ∈ B)
    let A₀ := (Finset.range (N₀ + 1)).filter (· ∈ A)
    let B₀ := (Finset.range (N₀ + 1)).filter (· ∈ B)
    ∀ r < D₀, ∃! p : ℕ × ℕ, p.1 ∈ A₀ ∧ p.2 ∈ B₀ ∧ (p.1 + p.2) % D₀ = r := by
  classical
  set A₀ := (Finset.range (N₀ + 1)).filter (· ∈ A)
  set B₀ := (Finset.range (N₀ + 1)).filter (· ∈ B)
  -- Divide by (1 - X) in ℤ[X]: P_{A₀} * P_{B₀} = (∑_{j < D₀} X^j) + (1 - X^{D₀}) * Δ
  set Δ : ℤ[X] := ∑ n ∈ Finset.range n₀, C ((repCount A B n : ℤ) - 1) * (X : ℤ[X]) ^ n
  set G : ℤ[X] := ∑ j ∈ Finset.range D₀, (X : ℤ[X]) ^ j
  have hgeom : (1 - X) * G = (1 - X ^ D₀ : ℤ[X]) := by
    have h := geom_sum_mul (X : ℤ[X]) D₀
    change (∑ j ∈ Finset.range D₀, (X : ℤ[X]) ^ j) * (X - 1) = X ^ D₀ - 1 at h
    linear_combination -h
  have h1subX_ne : (1 - X : ℤ[X]) ≠ 0 := by
    intro h0
    have := congrArg (fun P : ℤ[X] => P.eval 0) h0
    simp at this
  have hprod_eq : truncPoly A N₀ * truncPoly B N₀ = G + (1 - X ^ D₀) * Δ := by
    apply mul_left_cancel₀ h1subX_ne
    calc
      (1 - X) * (truncPoly A N₀ * truncPoly B N₀)
          = VPoly A B n₀ * (1 - X ^ D₀) := hpoly
      _ = (1 + (1 - X) * Δ) * (1 - X ^ D₀) := rfl
      _ = (1 - X ^ D₀) + (1 - X) * ((1 - X ^ D₀) * Δ) := by ring
      _ = (1 - X) * G + (1 - X) * ((1 - X ^ D₀) * Δ) := by rw [← hgeom]
      _ = (1 - X) * (G + (1 - X ^ D₀) * Δ) := by ring
  -- For any r < D₀, sum coeff (r + q * D₀) over q < K where K = max 2 (Δ.natDegree + 2)
  dsimp only
  intro r hr
  set K := max 2 (Δ.natDegree + 2)
  -- 1. Telescoping sum for (1 - X^{D₀}) * Δ vanishes
  have hsum_Δ : ∑ q ∈ Finset.range K, ((1 - X ^ D₀) * Δ).coeff (r + q * D₀) = 0 := by
    have htele : ∀ m : ℕ,
        ∑ q ∈ Finset.range (m + 1), ((1 - X ^ D₀) * Δ).coeff (r + q * D₀) =
          Δ.coeff (r + m * D₀) := by
      intro m
      induction m with
      | zero =>
        simp only [zero_mul, add_zero, sub_mul, one_mul, coeff_sub,
          coeff_X_pow_mul']
        have hnot : ¬ (D₀ ≤ r) := by omega
        simp [hnot]
      | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        rw [sub_mul, one_mul, coeff_sub, coeff_X_pow_mul']
        have hge : D₀ ≤ r + (m + 1) * D₀ := by
          have : D₀ ≤ (m + 1) * D₀ := Nat.le_mul_of_pos_left D₀ (Nat.succ_pos m)
          omega
        have hsub : r + (m + 1) * D₀ - D₀ = r + m * D₀ := by
          have : (m + 1) * D₀ = m * D₀ + D₀ := by ring
          omega
        simp only [hge, ↓reduceIte, hsub]
        ring
    have hK_pos : 1 ≤ K := by simp only [K]; omega
    have hK_eq : K = (K - 1) + 1 := (Nat.sub_add_cancel hK_pos).symm
    rw [hK_eq, htele]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have h1 : Δ.natDegree + 1 ≤ K - 1 := by simp only [K]; omega
    have h2 : K - 1 ≤ (K - 1) * D₀ := Nat.le_mul_of_pos_right (K - 1) hD₀
    omega
  -- 2. Sum for G = ∑_{j < D₀} X^j equals 1
  have hsum_G : ∑ q ∈ Finset.range K, G.coeff (r + q * D₀) = 1 := by
    have hG_coeff : ∀ n, G.coeff n = if n < D₀ then 1 else 0 := by
      intro n
      simp only [G, finsetSum_coeff, coeff_X_pow]
      by_cases hn : n < D₀
      · rw [Finset.sum_eq_single n]
        · simp [hn]
        · intro b _ hbn; simp [hbn.symm]
        · intro hnot; exact absurd (Finset.mem_range.mpr hn) hnot
      · simp only [hn, ↓reduceIte]
        apply Finset.sum_eq_zero; intro b hb
        have : n ≠ b := by have := Finset.mem_range.mp hb; omega
        simp [this]
    have h0mem : 0 ∈ Finset.range K := Finset.mem_range.mpr (by simp only [K]; omega)
    rw [Finset.sum_eq_single 0]
    · simp [hG_coeff, hr]
    · intro q _ hq0
      rw [hG_coeff]
      have hge : D₀ ≤ r + q * D₀ := by
        have : 1 ≤ q := Nat.pos_of_ne_zero hq0
        have : D₀ ≤ q * D₀ := Nat.le_mul_of_pos_left D₀ this
        omega
      simp [show ¬ (r + q * D₀ < D₀) by omega]
    · intro hnot; exact absurd h0mem hnot
  -- 3. Sum for truncPoly A N₀ * truncPoly B N₀ equals #{(a, b) ∈ A₀ × B₀ : (a + b) % D₀ = r}
  have hsum_P : ∑ q ∈ Finset.range K, (truncPoly A N₀ * truncPoly B N₀).coeff (r + q * D₀) =
      (((A₀ ×ˢ B₀).filter (fun p => (p.1 + p.2) % D₀ = r)).card : ℤ) := by
    have hK2 : 2 ≤ K := le_max_left _ _
    have hsplit : ∑ q ∈ Finset.range K, (truncPoly A N₀ * truncPoly B N₀).coeff (r + q * D₀) =
        (truncPoly A N₀ * truncPoly B N₀).coeff r + (truncPoly A N₀ * truncPoly B N₀).coeff (r + D₀) := by
      have hsub : Finset.range 2 ⊆ Finset.range K := Finset.range_mono hK2
      rw [← Finset.sum_subset hsub]
      · simp [Finset.sum_range_succ]
      · intro q _ hq2
        have hq_ge2 : 2 ≤ q := by simp only [Finset.mem_range] at hq2; omega
        rw [truncPoly_mul_coeff]
        have hzero : repTrunc A B N₀ (r + q * D₀) = 0 := by
          unfold repTrunc
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro a ha ⟨haA, hale, hbN, hbB⟩
          have haN : a ≤ N₀ := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
          have ha_lt := hA₀_lt a haA haN
          have hb_lt := hB₀_lt (r + q * D₀ - a) hbB hbN
          have : 2 * D₀ ≤ q * D₀ := Nat.mul_le_mul_right D₀ hq_ge2
          omega
        simp [hzero]
    rw [hsplit, truncPoly_mul_coeff, truncPoly_mul_coeff]
    -- Count pairs in A₀ × B₀ with sum = r and sum = r + D₀
    have hrep_eq : ∀ n : ℕ, repTrunc A B N₀ n = ((A₀ ×ˢ B₀).filter (fun p => p.1 + p.2 = n)).card := by
      intro n
      unfold repTrunc
      apply Finset.card_bij (fun a _ => (a, n - a))
      · intro a ha; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_product, A₀, B₀] at ha ⊢
        exact ⟨⟨⟨by omega, ha.2.1⟩, ⟨by omega, ha.2.2.2.2⟩⟩, by omega⟩
      · intro a₁ _ a₂ _ heq; exact congrArg Prod.fst heq
      · rintro ⟨a, b⟩ hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, A₀, B₀] at hp
        refine ⟨a, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_range]
          refine ⟨hp.1.1.1, hp.1.1.2, by omega, by omega, ?_⟩
          have : n - a = b := by omega
          rw [this]; exact hp.1.2.2
        · ext
          · rfl
          · dsimp; omega
    rw [hrep_eq r, hrep_eq (r + D₀)]
    have hdisj : Disjoint
        ((A₀ ×ˢ B₀).filter (fun p => p.1 + p.2 = r))
        ((A₀ ×ˢ B₀).filter (fun p => p.1 + p.2 = r + D₀)) := by
      rw [Finset.disjoint_left]; intro p h1 h2
      simp only [Finset.mem_filter] at h1 h2; omega
    have hunion : ((A₀ ×ˢ B₀).filter (fun p => p.1 + p.2 = r)) ∪
        ((A₀ ×ˢ B₀).filter (fun p => p.1 + p.2 = r + D₀)) =
        (A₀ ×ˢ B₀).filter (fun p => (p.1 + p.2) % D₀ = r) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_range, A₀, B₀]
      constructor
      · rintro (⟨hmem, hsum⟩ | ⟨hmem, hsum⟩)
        · exact ⟨hmem, by rw [hsum, Nat.mod_eq_of_lt hr]⟩
        · exact ⟨hmem, by rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hr]⟩
      · rintro ⟨⟨⟨haN, haA⟩, ⟨hbN, hbB⟩⟩, hmod⟩
        have ha_lt := hA₀_lt a haA (by omega)
        have hb_lt := hB₀_lt b hbB (by omega)
        have hdiv_lt : (a + b) / D₀ < 2 := (Nat.div_lt_iff_lt_mul hD₀).mpr (by omega)
        have hd := Nat.div_add_mod (a + b) D₀
        have hq01 : (a + b) / D₀ = 0 ∨ (a + b) / D₀ = 1 := by
          generalize (a + b) / D₀ = q at hdiv_lt ⊢; omega
        rcases hq01 with hq0 | hq1
        · left; exact ⟨⟨⟨haN, haA⟩, ⟨hbN, hbB⟩⟩, by rw [hq0, hmod] at hd; omega⟩
        · right; exact ⟨⟨⟨haN, haA⟩, ⟨hbN, hbB⟩⟩, by rw [hq1, hmod] at hd; omega⟩
    have hcard := Finset.card_union_of_disjoint hdisj
    rw [hunion] at hcard
    exact_mod_cast hcard.symm
  -- 4. Equate the sums to get card = 1, hence unique pair!
  have hcard1_z : (((A₀ ×ˢ B₀).filter (fun p => (p.1 + p.2) % D₀ = r)).card : ℤ) = 1 := by
    rw [← hsum_P, hprod_eq]
    have hadd : ∑ q ∈ Finset.range K, (G + (1 - X ^ D₀) * Δ).coeff (r + q * D₀) =
        (∑ q ∈ Finset.range K, G.coeff (r + q * D₀)) +
        ∑ q ∈ Finset.range K, ((1 - X ^ D₀) * Δ).coeff (r + q * D₀) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro q _; rw [coeff_add]
    rw [hadd, hsum_G, hsum_Δ, add_zero]
  have hcard1 : ((A₀ ×ˢ B₀).filter (fun p => (p.1 + p.2) % D₀ = r)).card = 1 := by
    exact_mod_cast hcard1_z
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard1
  have hpmem : p ∈ (A₀ ×ˢ B₀).filter (fun q => (q.1 + q.2) % D₀ = r) := by rw [hp]; simp
  simp only [Finset.mem_filter, Finset.mem_product] at hpmem
  refine ⟨p, ⟨hpmem.1.1, hpmem.1.2, hpmem.2⟩, fun q hq => ?_⟩
  have hqmem : q ∈ (A₀ ×ˢ B₀).filter (fun x => (x.1 + x.2) % D₀ = r) :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hq.1, hq.2.1⟩, hq.2.2⟩
  rw [hp, Finset.mem_singleton] at hqmem
  exact hqmem

/-! ### Main Theorem, Conjecture 1.3, and Corollary 2 -/

/-- Oriented core of the Main Theorem assuming `LevelApprox A B n₀ K_max N₀` at the initial level. -/
private lemma main_classification_oriented {A B : Set ℕ} (hA_inf : A.Infinite) (hB_inf : B.Infinite)
    {n₀ K₀ N_star N₀ : ℕ} (hn0 : 1 ≤ n₀) (hstab : ∀ n ≥ n₀, repCount A B n = 1)
    (hK₀_n0 : n₀ ≤ K₀) (hK₀_E : errSum A B n₀ ≤ K₀)
    (hN_star : ∀ N ≥ N_star, crossExcess A B N ≤
        2 ^ (max n₀ (errSum A B n₀ + 2) + 1) * (K₀ + errSum A B n₀ + 2 * n₀) →
        LevelApprox A B n₀ (2 ^ (max n₀ (errSum A B n₀ + 2) + 1) * (K₀ + errSum A B n₀ + 2 * n₀)) N ∨
        LevelApprox B A n₀ (2 ^ (max n₀ (errSum A B n₀ + 2) + 1) * (K₀ + errSum A B n₀ + 2 * n₀)) N)
    (hN₀_ge : N_star ≤ N₀) (hT₀ : crossExcess A B N₀ ≤ K₀)
    (hL₀ : LevelApprox A B n₀ (2 ^ (max n₀ (errSum A B n₀ + 2) + 1) * (K₀ + errSum A B n₀ + 2 * n₀)) N₀) :
    IsModularLift A B := by
  classical
  set E := errSum A B n₀
  set k := max n₀ (E + 2) + 1
  set K_max := 2 ^ k * (K₀ + E + 2 * n₀)
  have hE_le_Kmax : E ≤ K_max := by
    have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    calc E ≤ K₀ := hK₀_E
      _ ≤ 1 * (K₀ + E + 2 * n₀) := by omega
      _ ≤ 2 ^ k * (K₀ + E + 2 * n₀) := Nat.mul_le_mul_right _ hpow
  have hstab_sym : ∀ n ≥ n₀, repCount B A n = 1 := fun n hn => by
    rw [repCount_symm]; exact hstab n hn
  have hN_star_sym : ∀ M ≥ N_star, crossExcess B A M ≤ K_max →
      LevelApprox B A n₀ K_max M ∨ LevelApprox A B n₀ K_max M := by
    intro M hM hTM
    rw [crossExcess_symm B A M] at hTM
    exact (hN_star M hM hTM).symm
  -- Step 1: Rigidity at N₀
  have hW₀ : stripPoly (WPoly A B N₀) = stripPoly (VPoly A B n₀) :=
    step1_rigidity hA_inf hB_inf hn0 hstab hK₀_n0 hK₀_E hN_star hN₀_ge hT₀
  -- Define A₀, B₀, D₀
  set A₀ := (Finset.range (N₀ + 1)).filter (· ∈ A)
  set B₀ := (Finset.range (N₀ + 1)).filter (· ∈ B)
  set y₀ := nextGt hA_inf N₀
  set D₀ := y₀ - minElem A
  have hN₀_ge_n0 : n₀ ≤ N₀ := by have := hL₀.hN_large; nlinarith
  have hm0_le : mZero A B ≤ n₀ := mZero_le_n0 hstab
  have hamin_le : minElem A ≤ n₀ := by unfold mZero at hm0_le; omega
  have hbmin_le : minElem B ≤ n₀ := by unfold mZero at hm0_le; omega
  have hy₀_spec := nextGt_spec hA_inf N₀
  have hN₀_lin : (10 ^ 7 : ℝ) * ((n₀ : ℝ) + 1) ≤ (N₀ : ℝ) := by
    have hnat : 10 ^ 7 * (n₀ + 1) ≤ N₀ := by have := hL₀.hN_large; nlinarith
    exact_mod_cast hnat
  have hD₀_ge_N0 : (N₀ : ℝ) - (n₀ : ℝ) ≤ (D₀ : ℝ) := by
    have : N₀ ≤ D₀ + n₀ := by omega
    have : (N₀ : ℝ) ≤ (D₀ : ℝ) + (n₀ : ℝ) := by exact_mod_cast this
    linarith
  have hD₀_pos : 1 ≤ D₀ := by omega
  have hA₀_lt : ∀ a ∈ A, a ≤ N₀ → a < D₀ := by
    intro a haA haN
    have hhi := hL₀.hx₀_hi a haA haN
    have : (a : ℝ) < (D₀ : ℝ) := by linarith
    exact_mod_cast this
  have hB₀_lt : ∀ b ∈ B, b ≤ N₀ → b < D₀ := by
    intro b hbB hbN
    have hhi := hL₀.hz₀_hi b hbB hbN
    have : (b : ℝ) < (D₀ : ℝ) := by linarith
    exact_mod_cast this
  -- Step 2: Infinite doubling induction for all j : ℕ
  have htower : ∀ j : ℕ, ∃ N_j : ℕ,
      N_star ≤ N_j ∧
      (1 ≤ j → N_j = 2 ^ j * D₀ + min (minElem A) (minElem B) - 1) ∧
      crossExcess A B N_j ≤ K₀ ∧
      stripPoly (WPoly A B N_j) = stripPoly (VPoly A B n₀) ∧
      (Even j →
        LevelApprox A B n₀ K_max N_j ∧
        nextGt hA_inf N_j = 2 ^ j * D₀ + minElem A ∧
        (∀ a ≤ N_j, a ∈ A ↔ ∃ a₀ ∈ A₀, ∃ m ∈ ABinTrunc (j / 2), a = a₀ + D₀ * m) ∧
        (∀ b ≤ N_j, b ∈ B ↔ ∃ b₀ ∈ B₀, ∃ m ∈ ABinTrunc (j / 2), b = b₀ + D₀ * (2 * m))) ∧
      (¬ Even j →
        LevelApprox B A n₀ K_max N_j ∧
        nextGt hB_inf N_j = 2 ^ j * D₀ + minElem B ∧
        (∀ a ≤ N_j, a ∈ A ↔ ∃ a₀ ∈ A₀, ∃ m ∈ ABinTrunc (j / 2 + 1), a = a₀ + D₀ * m) ∧
        (∀ b ≤ N_j, b ∈ B ↔ ∃ b₀ ∈ B₀, ∃ m ∈ ABinTrunc (j / 2), b = b₀ + D₀ * (2 * m))) := by
    intro j
    induction j with
    | zero =>
      refine ⟨N₀, hN₀_ge, fun h => by omega, hT₀, hW₀, ?_, fun h => absurd Even.zero h⟩
      intro _
      refine ⟨hL₀, by simp only [pow_zero, one_mul, D₀, y₀]; omega, ?_, ?_⟩
      · intro a ha
        simp only [Nat.zero_div, ABinTrunc_zero, exists_eq_left, mul_zero, add_zero,
          A₀, Finset.mem_filter, Finset.mem_range]
        constructor
        · intro haA; exact ⟨a, ⟨by omega, haA⟩, rfl⟩
        · rintro ⟨a₀, ⟨_, haA⟩, rfl⟩; exact haA
      · intro b hb
        simp only [Nat.zero_div, ABinTrunc_zero, exists_eq_left, mul_zero, add_zero,
          B₀, Finset.mem_filter, Finset.mem_range]
        constructor
        · intro hbB; exact ⟨b, ⟨by omega, hbB⟩, rfl⟩
        · rintro ⟨b₀, ⟨_, hbB⟩, rfl⟩; exact hbB
    | succ j ih =>
      obtain ⟨Nj, hNj_star, hNj_form, hTj, hWj, hEv, hOdd⟩ := ih
      by_cases hj_ev : Even j
      · -- Even j = 2i -> Odd j + 1 = 2i + 1
        obtain ⟨hLj, hyj, hAj, hBj⟩ := hEv hj_ev
        have hstep := exact_doubling_step hA_inf hB_inf hn0 hstab hE_le_Kmax hN_star hNj_star hLj hWj
        rcases hstep with ⟨hgt, hA_tr, hB_tr, hW_next, hT_next, hL_next, hw_next, _⟩
        set i := j / 2
        have hj_eq : j = 2 * i := by
          rcases hj_ev with ⟨k, rfl⟩; simp only [i]; omega
        have h2j_eq : 2 ^ j = 4 ^ i := by
          rw [hj_eq, pow_mul]; norm_num
        have hDj : nextGt hA_inf Nj - minElem A = 2 ^ j * D₀ := by
          rw [hyj]; omega
        set Nnext := 2 * (nextGt hA_inf Nj - minElem A) + min (minElem A) (minElem B) - 1
        have hNnext_form : Nnext = 2 ^ (j + 1) * D₀ + min (minElem A) (minElem B) - 1 := by
          simp only [Nnext, hDj, pow_succ']; congr 1; ring
        have hodd1 : ¬ Even (j + 1) := by
          intro ⟨m, hm⟩; omega
        refine ⟨Nnext, le_trans hNj_star (le_of_lt hgt), fun _ => hNnext_form,
          le_trans hT_next hK₀_E, hW_next, fun h => absurd h hodd1, fun _ => ?_⟩
        refine ⟨hL_next, ?_, ?_, ?_⟩
        · rw [hw_next, hDj, pow_succ']; ring
        · intro a ha
          rw [hA_tr a ha, hDj, h2j_eq]
          have hdiv1 : (j + 1) / 2 + 1 = i + 1 := by omega
          rw [hdiv1]
          constructor
          · rintro (⟨haN, haA⟩ | ⟨a₁, ha₁A, ha₁N, rfl⟩)
            · obtain ⟨a₀, ha₀, m, hm, rfl⟩ := (hAj a haN).mp haA
              exact ⟨a₀, ha₀, m, (ABinTrunc_succ i m).mpr (Or.inl hm), rfl⟩
            · obtain ⟨a₀, ha₀, m, hm, rfl⟩ := (hAj a₁ ha₁N).mp ha₁A
              refine ⟨a₀, ha₀, 4 ^ i + m, (ABinTrunc_succ i _).mpr (Or.inr ⟨m, hm, rfl⟩), ?_⟩
              ring
          · rintro ⟨a₀, ha₀, m, hm, rfl⟩
            have ha₀_mem : a₀ ≤ N₀ ∧ a₀ ∈ A := by
              simp only [A₀, Finset.mem_filter, Finset.mem_range] at ha₀; exact ⟨by omega, ha₀.2⟩
            have ha₀_ltD : a₀ < D₀ := hA₀_lt a₀ ha₀_mem.2 ha₀_mem.1
            have hle_Nj : ∀ m' ∈ ABinTrunc i, a₀ + D₀ * m' ≤ Nj := by
              intro m' hm'
              by_cases hi0 : i = 0
              · rw [hi0, ABinTrunc_zero] at hm'; subst hm'
                have hj0 : j = 0 := by omega
                have hy_eq0 : nextGt hA_inf Nj = D₀ + minElem A := by rw [hyj, hj0]; simp
                have hlt_y : a₀ < nextGt hA_inf Nj := by omega
                have hle_N : a₀ ≤ Nj := by
                  by_contra hgtN; have := nextGt_le hA_inf (N := Nj) ha₀_mem.2 (by omega); omega
                omega
              · have hj1 : 1 ≤ j := by omega
                have hNj_eq := hNj_form hj1
                have hm'3 := ABinTrunc_mul_three_le i m' hm'
                have h4pos : 1 ≤ 4 ^ i := Nat.one_le_pow i 4 (by decide)
                have hm'_le : m' + 1 ≤ 4 ^ i := by omega
                have hprod_le : D₀ * (m' + 1) ≤ 4 ^ i * D₀ := by
                  rw [mul_comm]; exact Nat.mul_le_mul_right D₀ hm'_le
                rw [h2j_eq] at hNj_eq
                have : a₀ + D₀ * m' < D₀ * (m' + 1) := by rw [mul_add, mul_one]; omega
                omega
            rcases (ABinTrunc_succ i m).mp hm with hm_i | ⟨m', hm'_i, rfl⟩
            · left
              have hle := hle_Nj m hm_i
              exact ⟨hle, (hAj _ hle).mpr ⟨a₀, ha₀, m, hm_i, rfl⟩⟩
            · right
              have hle := hle_Nj m' hm'_i
              refine ⟨a₀ + D₀ * m', (hAj _ hle).mpr ⟨a₀, ha₀, m', hm'_i, rfl⟩, hle, ?_⟩
              ring
        · intro b hb
          rw [hB_tr b hb]
          have hdiv1 : (j + 1) / 2 = i := by omega
          rw [hdiv1]
          constructor
          · rintro ⟨hbN, hbB⟩; exact (hBj b hbN).mp hbB
          · rintro ⟨b₀, hb₀, m, hm, rfl⟩
            have hb₀_mem : b₀ ≤ N₀ ∧ b₀ ∈ B := by
              simp only [B₀, Finset.mem_filter, Finset.mem_range] at hb₀; exact ⟨by omega, hb₀.2⟩
            have hb₀_ltD : b₀ < D₀ := hB₀_lt b₀ hb₀_mem.2 hb₀_mem.1
            have hle_Nj : b₀ + D₀ * (2 * m) ≤ Nj := by
              by_cases hi0 : i = 0
              · rw [hi0, ABinTrunc_zero] at hm; subst hm
                simp only [mul_zero, add_zero]
                have hj0 : j = 0 := by omega
                have hy_51 := lemma_5_1 hA_inf hn0 hstab hLj
                have hb_hi : (b₀ : ℝ) ≤ (2 / 3 + 1 / 1000 : ℝ) * (N₀ : ℝ) := hL₀.hz₀_hi b₀ hb₀_mem.2 hb₀_mem.1
                have hy_eq0 : nextGt hA_inf Nj = D₀ + minElem A := by rw [hyj, hj0]; simp
                have hD_le_y : (D₀ : ℝ) ≤ (nextGt hA_inf Nj : ℝ) := by exact_mod_cast (by omega : D₀ ≤ nextGt hA_inf Nj)
                have : (b₀ : ℝ) ≤ (Nj : ℝ) := by linarith [hy_51.2]
                exact_mod_cast this
              · have hj1 : 1 ≤ j := by omega
                have hNj_eq := hNj_form hj1
                have hm3 := ABinTrunc_mul_three_le i m hm
                have h4pos : 1 ≤ 4 ^ i := Nat.one_le_pow i 4 (by decide)
                have hm_le : 2 * m + 1 ≤ 4 ^ i := by omega
                have hprod_le : D₀ * (2 * m + 1) ≤ 4 ^ i * D₀ := by
                  rw [mul_comm]; exact Nat.mul_le_mul_right D₀ hm_le
                rw [h2j_eq] at hNj_eq
                have : b₀ + D₀ * (2 * m) < D₀ * (2 * m + 1) := by rw [mul_add, mul_one]; omega
                omega
            exact ⟨hle_Nj, (hBj _ hle_Nj).mpr ⟨b₀, hb₀, m, hm, rfl⟩⟩
      · -- Odd j = 2i + 1 -> Even j + 1 = 2(i + 1)
        obtain ⟨hLj, hwj, hAj, hBj⟩ := hOdd hj_ev
        have hWj_sym : stripPoly (WPoly B A Nj) = stripPoly (VPoly B A n₀) := by
          rw [WPoly_symm B A Nj, VPoly_symm B A n₀]; exact hWj
        have hE_sym : errSum B A n₀ ≤ K_max := by rw [errSum_symm]; exact hE_le_Kmax
        have hstep := exact_doubling_step hB_inf hA_inf hn0 hstab_sym hE_sym hN_star_sym hNj_star hLj hWj_sym
        rcases hstep with ⟨hgt, hB_tr, hA_tr, hW_next, hT_next, hL_next, hy_next, _⟩
        set i := j / 2
        have hj_eq : j = 2 * i + 1 := by
          have : j % 2 = 1 := by by_contra h0; exact hj_ev (Nat.even_iff.mpr (by omega))
          omega
        have h2j_eq : 2 ^ j = 2 * 4 ^ i := by
          rw [hj_eq, pow_succ', pow_mul]; norm_num
        have hDj : nextGt hB_inf Nj - minElem B = 2 ^ j * D₀ := by
          rw [hwj]; omega
        set Nnext := 2 * (nextGt hB_inf Nj - minElem B) + min (minElem B) (minElem A) - 1
        have hNnext_form : Nnext = 2 ^ (j + 1) * D₀ + min (minElem A) (minElem B) - 1 := by
          simp only [Nnext, hDj, pow_succ', min_comm]; congr 1; ring
        have hev1 : Even (j + 1) := ⟨i + 1, by omega⟩
        have hW_next' : stripPoly (WPoly A B Nnext) = stripPoly (VPoly A B n₀) := by
          rw [WPoly_symm A B Nnext, VPoly_symm A B n₀]; exact hW_next
        have hT_next' : crossExcess A B Nnext ≤ K₀ := by
          rw [crossExcess_symm A B Nnext]
          exact le_trans hT_next (by rw [errSum_symm]; exact hK₀_E)
        have hj1 : 1 ≤ j := by omega
        have hNj_eq := hNj_form hj1
        refine ⟨Nnext, le_trans hNj_star (le_of_lt hgt), fun _ => hNnext_form,
          hT_next', hW_next', fun _ => ?_, fun h => absurd hev1 h⟩
        refine ⟨hL_next, ?_, ?_, ?_⟩
        · rw [hy_next, hDj, pow_succ']; ring
        · intro a ha
          rw [hA_tr a ha]
          have hdiv1 : (j + 1) / 2 = i + 1 := by omega
          rw [hdiv1]
          constructor
          · rintro ⟨haN, haA⟩; exact (hAj a haN).mp haA
          · rintro ⟨a₀, ha₀, m, hm, rfl⟩
            have ha₀_mem : a₀ ≤ N₀ ∧ a₀ ∈ A := by
              simp only [A₀, Finset.mem_filter, Finset.mem_range] at ha₀; exact ⟨by omega, ha₀.2⟩
            have ha₀_ltD : a₀ < D₀ := hA₀_lt a₀ ha₀_mem.2 ha₀_mem.1
            have hm3 := ABinTrunc_mul_three_le (i + 1) m hm
            have h4pos : 1 ≤ 4 ^ i := Nat.one_le_pow i 4 (by decide)
            have hm_le : m + 1 ≤ 2 * 4 ^ i := by
              rw [pow_succ'] at hm3; omega
            have hprod_le : D₀ * (m + 1) ≤ 2 * 4 ^ i * D₀ := by
              rw [mul_comm]; exact Nat.mul_le_mul_right D₀ hm_le
            rw [h2j_eq] at hNj_eq
            have hle_Nj : a₀ + D₀ * m ≤ Nj := by
              have : a₀ + D₀ * m < D₀ * (m + 1) := by rw [mul_add, mul_one]; omega
              omega
            exact ⟨hle_Nj, (hAj _ hle_Nj).mpr ⟨a₀, ha₀, m, hm, rfl⟩⟩
        · intro b hb
          rw [hB_tr b hb, hDj, h2j_eq]
          have hdiv1 : (j + 1) / 2 = i + 1 := by omega
          rw [hdiv1]
          constructor
          · rintro (⟨hbN, hbB⟩ | ⟨b₁, hb₁B, hb₁N, rfl⟩)
            · obtain ⟨b₀, hb₀, m, hm, rfl⟩ := (hBj b hbN).mp hbB
              exact ⟨b₀, hb₀, m, (ABinTrunc_succ i m).mpr (Or.inl hm), rfl⟩
            · obtain ⟨b₀, hb₀, m, hm, rfl⟩ := (hBj b₁ hb₁N).mp hb₁B
              refine ⟨b₀, hb₀, 4 ^ i + m, (ABinTrunc_succ i _).mpr (Or.inr ⟨m, hm, rfl⟩), ?_⟩
              ring
          · rintro ⟨b₀, hb₀, m, hm, rfl⟩
            have hb₀_mem : b₀ ≤ N₀ ∧ b₀ ∈ B := by
              simp only [B₀, Finset.mem_filter, Finset.mem_range] at hb₀; exact ⟨by omega, hb₀.2⟩
            have hb₀_ltD : b₀ < D₀ := hB₀_lt b₀ hb₀_mem.2 hb₀_mem.1
            have hle_Nj : ∀ m' ∈ ABinTrunc i, b₀ + D₀ * (2 * m') ≤ Nj := by
              intro m' hm'
              have hm'3 := ABinTrunc_mul_three_le i m' hm'
              have h4pos : 1 ≤ 4 ^ i := Nat.one_le_pow i 4 (by decide)
              have hm'_le : 2 * m' + 1 ≤ 2 * 4 ^ i := by omega
              have hprod_le : D₀ * (2 * m' + 1) ≤ 2 * 4 ^ i * D₀ := by
                rw [mul_comm]; exact Nat.mul_le_mul_right D₀ hm'_le
              rw [h2j_eq] at hNj_eq
              have : b₀ + D₀ * (2 * m') < D₀ * (2 * m' + 1) := by rw [mul_add, mul_one]; omega
              omega
            rcases (ABinTrunc_succ i m).mp hm with hm_i | ⟨m', hm'_i, rfl⟩
            · left
              have hle := hle_Nj m hm_i
              exact ⟨hle, (hBj _ hle).mpr ⟨b₀, hb₀, m, hm_i, rfl⟩⟩
            · right
              have hle := hle_Nj m' hm'_i
              refine ⟨b₀ + D₀ * (2 * m'), (hBj _ hle).mpr ⟨b₀, hb₀, m', hm'_i, rfl⟩, hle, ?_⟩
              ring
  -- Step 3a: Global identities A = A₀ + D₀ · ABin and B = B₀ + D₀ · (2 ABin)
  have hA_global : A = {n : ℕ | ∃ a₀ ∈ A₀, ∃ m ∈ ABin, n = a₀ + D₀ * m} := by
    ext n
    simp only [Set.mem_ofPred_eq]
    obtain ⟨Nj, _, hNj_form, _, _, hEv, _⟩ := htower (2 * (n + 1))
    have hNj_eq := hNj_form (by omega)
    have hpow_gt : n + 1 < 2 ^ (2 * (n + 1)) := by
      have : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
      have : 2 ^ (n + 1) ≤ 2 ^ (2 * (n + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hn_le : n ≤ Nj := by
      have : 2 ^ (2 * (n + 1)) ≤ 2 ^ (2 * (n + 1)) * D₀ := Nat.le_mul_of_pos_right _ hD₀_pos
      omega
    have hAj := (hEv ⟨n + 1, by ring⟩).2.2.1 n hn_le
    rw [hAj]
    have hdiv : 2 * (n + 1) / 2 = n + 1 := by omega
    rw [hdiv]
    constructor
    · rintro ⟨a₀, ha₀, m, ⟨hmA, _⟩, rfl⟩; exact ⟨a₀, ha₀, m, hmA, rfl⟩
    · rintro ⟨a₀, ha₀, m, hmA, hn_eq⟩
      have hm_lt : m < 4 ^ (n + 1) := by
        have h1 : m ≤ a₀ + D₀ * m := by
          have : m ≤ D₀ * m := Nat.le_mul_of_pos_left m hD₀_pos
          omega
        have h2 : n < 4 ^ (n + 1) := by
          have : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
          have : 2 ^ (n + 1) ≤ 4 ^ (n + 1) := Nat.pow_le_pow_left (by decide) _
          omega
        omega
      exact ⟨a₀, ha₀, m, ⟨hmA, hm_lt⟩, hn_eq⟩
  have hB_global : B = {n : ℕ | ∃ b₀ ∈ B₀, ∃ m ∈ ABin, n = b₀ + D₀ * (2 * m)} := by
    ext n
    simp only [Set.mem_ofPred_eq]
    obtain ⟨Nj, _, hNj_form, _, _, hEv, _⟩ := htower (2 * (n + 1))
    have hNj_eq := hNj_form (by omega)
    have hpow_gt : n + 1 < 2 ^ (2 * (n + 1)) := by
      have : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
      have : 2 ^ (n + 1) ≤ 2 ^ (2 * (n + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hn_le : n ≤ Nj := by
      have : 2 ^ (2 * (n + 1)) ≤ 2 ^ (2 * (n + 1)) * D₀ := Nat.le_mul_of_pos_right _ hD₀_pos
      omega
    have hBj := (hEv ⟨n + 1, by ring⟩).2.2.2 n hn_le
    rw [hBj]
    have hdiv : 2 * (n + 1) / 2 = n + 1 := by omega
    rw [hdiv]
    constructor
    · rintro ⟨b₀, hb₀, m, ⟨hmA, _⟩, rfl⟩; exact ⟨b₀, hb₀, m, hmA, rfl⟩
    · rintro ⟨b₀, hb₀, m, hmA, hn_eq⟩
      have hm_lt : m < 4 ^ (n + 1) := by
        have h1 : m ≤ b₀ + D₀ * (2 * m) := by
          have : m ≤ D₀ * (2 * m) := by
            have : 1 ≤ D₀ := hD₀_pos; nlinarith
          omega
        have h2 : n < 4 ^ (n + 1) := by
          have : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
          have : 2 ^ (n + 1) ≤ 4 ^ (n + 1) := Nat.pow_le_pow_left (by decide) _
          omega
        omega
      exact ⟨b₀, hb₀, m, ⟨hmA, hm_lt⟩, hn_eq⟩
  -- Step 3b: Bijection modulo D₀ from (7.3)
  have hstep0 := exact_doubling_step hA_inf hB_inf hn0 hstab hE_le_Kmax hN_star hN₀_ge hL₀ hW₀
  have hXW₀ : X ^ (N₀ + 1) * WPoly A B N₀ = X ^ D₀ * VPoly A B n₀ := hstep0.2.2.2.2.2.2.2
  have hpoly73 : (1 - X) * (truncPoly A N₀ * truncPoly B N₀) = VPoly A B n₀ * (1 - X ^ D₀) := by
    rw [truncPoly_exact_identity hstab hN₀_ge_n0, hXW₀]
    ring
  have hbij := residue_bijection_of_poly_identity hD₀_pos hA₀_lt hB₀_lt hpoly73
  refine ⟨D₀, A₀, B₀, hD₀_pos, ?_, ?_, hbij, Or.inl ⟨hA_global, hB_global⟩⟩
  · intro a ha; simp only [A₀, Finset.mem_filter, Finset.mem_range] at ha; exact hA₀_lt a ha.2 (by omega)
  · intro b hb; simp only [B₀, Finset.mem_filter, Finset.mem_range] at hb; exact hB₀_lt b hb.2 (by omega)

/-- **Main Theorem (Exact Classification below `8 / 5`):**
Every pair `(A, B)` of infinite almost perfect additive complements satisfying
`limsup_{x → ∞} A(x) B(x) / x < 8 / 5` has the modular-lift form `IsModularLift A B`. -/
theorem main_classification {A B : Set ℕ} (hAP : IsAlmostPerfect A B)
    (hlim : Filter.limsup (ratioEReal A B) Filter.atTop < ((8 / 5 : ℝ) : EReal)) :
    IsModularLift A B := by
  have hA_inf : A.Infinite := hAP.1
  have hB_inf : B.Infinite := hAP.2.1
  obtain ⟨n₀, hn0, hstab⟩ := exists_repCount_eq_one_eventually hAP
  obtain ⟨T_min, hT_freq⟩ := exists_crossExcess_frequently_le hAP hstab
  set E := errSum A B n₀
  set K₀ := max T_min (max n₀ E)
  have hK₀_n0 : n₀ ≤ K₀ := le_trans (le_max_left n₀ E) (le_max_right _ _)
  have hK₀_E : E ≤ K₀ := le_trans (le_max_right n₀ E) (le_max_right _ _)
  have hK₀_T : T_min ≤ K₀ := le_max_left _ _
  set k := max n₀ (E + 2) + 1
  set K_max := 2 ^ k * (K₀ + E + 2 * n₀)
  have hK_max_n0 : n₀ ≤ K_max := by
    have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    calc n₀ ≤ K₀ := hK₀_n0
      _ ≤ 1 * (K₀ + E + 2 * n₀) := by omega
      _ ≤ 2 ^ k * (K₀ + E + 2 * n₀) := Nat.mul_le_mul_right _ hpow
  obtain ⟨N_star, hN_star⟩ := exists_levelApprox hAP hlim hn0 hstab K_max hK_max_n0
  obtain ⟨N₀, hN₀_ge, hT₀_le⟩ := hT_freq N_star
  have hT₀ : crossExcess A B N₀ ≤ K₀ := le_trans hT₀_le hK₀_T
  have hT₀_max : crossExcess A B N₀ ≤ K_max := by
    have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    calc crossExcess A B N₀ ≤ K₀ := hT₀
      _ ≤ 1 * (K₀ + E + 2 * n₀) := by omega
      _ ≤ 2 ^ k * (K₀ + E + 2 * n₀) := Nat.mul_le_mul_right _ hpow
  rcases hN_star N₀ hN₀_ge hT₀_max with hL₀ | hL₀
  · exact main_classification_oriented hA_inf hB_inf hn0 hstab hK₀_n0 hK₀_E hN_star hN₀_ge hT₀ hL₀
  · -- Swap A and B once, apply oriented theorem, and swap back!
    have hstab_sym : ∀ n ≥ n₀, repCount B A n = 1 := fun n hn => by
      rw [repCount_symm]; exact hstab n hn
    have hE_sym : errSum B A n₀ = E := errSum_symm B A n₀
    have hK₀_Esym : errSum B A n₀ ≤ K₀ := by rw [hE_sym]; exact hK₀_E
    have hT₀_sym : crossExcess B A N₀ ≤ K₀ := by rw [crossExcess_symm]; exact hT₀
    have hN_star_sym : ∀ N ≥ N_star, crossExcess B A N ≤
        2 ^ (max n₀ (errSum B A n₀ + 2) + 1) * (K₀ + errSum B A n₀ + 2 * n₀) →
        LevelApprox B A n₀ (2 ^ (max n₀ (errSum B A n₀ + 2) + 1) * (K₀ + errSum B A n₀ + 2 * n₀)) N ∨
        LevelApprox A B n₀ (2 ^ (max n₀ (errSum B A n₀ + 2) + 1) * (K₀ + errSum B A n₀ + 2 * n₀)) N := by
      intro N hN hTN
      rw [hE_sym, crossExcess_symm] at hTN
      rw [hE_sym]
      exact (hN_star N hN hTN).symm
    have hL₀' : LevelApprox B A n₀
        (2 ^ (max n₀ (errSum B A n₀ + 2) + 1) * (K₀ + errSum B A n₀ + 2 * n₀)) N₀ := by
      rw [hE_sym]; exact hL₀
    have hlift_BA := main_classification_oriented hB_inf hA_inf hn0 hstab_sym hK₀_n0 hK₀_Esym
      hN_star_sym hN₀_ge hT₀_sym hL₀'
    rcases hlift_BA with ⟨D₀, A₀, B₀, hD₀, hA₀, hB₀, hbij, hor⟩
    exact ⟨D₀, A₀, B₀, hD₀, hA₀, hB₀, hbij, hor.symm⟩

/-- **Corollary 1 (Resolution of Conjecture 1.3 of van Doorn–Liu–Tang, `arXiv:2610.35027v1`):**
For every pair `(A, B)` of infinite almost perfect additive complements,
either `limsup A(x) B(x) / x = 3 / 2` or `8 / 5 ≤ limsup A(x) B(x) / x ≤ 2`. -/
theorem conjecture_1_3 {A B : Set ℕ} (hAP : IsAlmostPerfect A B) :
    Filter.limsup (ratioEReal A B) Filter.atTop = (3 / 2 : EReal) ∨
      (((8 / 5 : ℝ) : EReal) ≤ Filter.limsup (ratioEReal A B) Filter.atTop ∧
       Filter.limsup (ratioEReal A B) Filter.atTop ≤ (2 : EReal)) := by
  by_cases hlt : Filter.limsup (ratioEReal A B) Filter.atTop < ((8 / 5 : ℝ) : EReal)
  · left
    exact modularLift_limsup_eq_three_halves (main_classification hAP hlt)
  · right
    exact ⟨le_of_not_gt hlt, almostPerfect_limsup_le_two hAP⟩

/-- **Corollary 2 (No Repeated Sums below `8 / 5`):**
Every pair `(A, B)` of infinite almost perfect additive complements with
`limsup A(x) B(x) / x < 8 / 5` has `repCount A B n ≤ 1` for every `n : ℕ`. -/
theorem no_repeated_sums_below_eight_fifths {A B : Set ℕ} (hAP : IsAlmostPerfect A B)
    (hlim : Filter.limsup (ratioEReal A B) Filter.atTop < ((8 / 5 : ℝ) : EReal)) :
    ∀ n : ℕ, repCount A B n ≤ 1 :=
  modularLift_repCount_le_one (main_classification hAP hlim)

end

end AlmostPerfect
