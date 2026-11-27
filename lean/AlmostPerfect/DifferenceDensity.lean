import AlmostPerfect.Basic
import AlmostPerfect.PolynomialInvariants
import AlmostPerfect.ZhangGap
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-!
# Section 3 (Part 2): Stripped Polynomials, Basic Invariants, and Modular Difference Density

Completes Section 3 of `PROOF.md`:
- Lemma 3.1(2)-(5): `aMin`, `bMin`, `mZero`, `errSum` (`E`), `errSigned` (`c`), `repPairSum` (`S₂`),
  product identity `A(N)B(N) = N + 1 + c + T(N)`, upper bound `A(u)B(v) ≤ u + v + 1 + E`,
  `T_min < ∞`, and stripped polynomials `stripPoly P` (`Ṽ`, `W̃_N`, `Ũ₁`, `F̃`).
- Lemma 3.3(3)-(4): Derivative at `1` (`W_N'(1) = T(N)`) and stripped properties for any
  polynomial of the form `1 - (1 - X) * E` with `{0, 1}`-valued coefficients of `E`.
- Lemma 3.4: Quantitative modular difference density (`C₁(K)` bound on missing elements of
  `B₀ - A₀` and `A₀ - B₀`).
-/

namespace AlmostPerfect

open Polynomial BigOperators Filter

noncomputable section

/-! ### Minimal Elements and Error Invariants (Lemma 3.1(2)–(4)) -/

/-- Minimal element of `S ⊆ ℕ` (equals `0` if empty). -/
def minElem (S : Set ℕ) : ℕ := sInf S

/-- Minimal sum `m₀ = min A + min B`. -/
def mZero (A B : Set ℕ) : ℕ := minElem A + minElem B

/-- Total absolute error `E = ∑_{n < n₀} |r(n) - 1|`. -/
def errSum (A B : Set ℕ) (n₀ : ℕ) : ℕ :=
  ∑ n ∈ Finset.range n₀, Int.natAbs ((repCount A B n : ℤ) - 1)

/-- Signed error `c = ∑_{n < n₀} (r(n) - 1)`. -/
def errSigned (A B : Set ℕ) (n₀ : ℕ) : ℤ :=
  ∑ n ∈ Finset.range n₀, ((repCount A B n : ℤ) - 1)

/-- Pair excess `S₂ = ∑_{n < n₀} r(n) * (r(n) - 1)`. -/
def repPairSum (A B : Set ℕ) (n₀ : ℕ) : ℕ :=
  ∑ n ∈ Finset.range n₀, repCount A B n * (repCount A B n - 1)

/-- Constant `C₁(K) = E + S₂ + 2(1 + E)(1 + K)` from Lemma 3.4. -/
def C1Const (A B : Set ℕ) (n₀ K : ℕ) : ℕ :=
  errSum A B n₀ + repPairSum A B n₀ + 2 * (1 + errSum A B n₀) * (1 + K)

lemma minElem_mem {S : Set ℕ} (hS : S.Nonempty) : minElem S ∈ S :=
  Nat.sInf_mem hS

lemma minElem_le {S : Set ℕ} {x : ℕ} (hx : x ∈ S) : minElem S ≤ x :=
  Nat.sInf_le hx

lemma repCount_eq_zero_of_lt_mZero {A B : Set ℕ} {n : ℕ} (hn : n < mZero A B) :
    repCount A B n = 0 := by
  classical
  unfold repCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a ha
  simp only [Finset.mem_range] at ha
  rintro ⟨haA, hbB⟩
  have h1 : minElem A ≤ a := minElem_le haA
  have h2 : minElem B ≤ n - a := minElem_le hbB
  unfold mZero at hn
  omega

lemma repCount_mZero {A B : Set ℕ} (hA : A.Nonempty) (hB : B.Nonempty) :
    repCount A B (mZero A B) = 1 := by
  classical
  unfold repCount
  have hfilt :
      (Finset.range (mZero A B + 1)).filter (fun a => a ∈ A ∧ mZero A B - a ∈ B) = {minElem A} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨ha_lt, haA, hbB⟩
      have h1 : minElem A ≤ a := minElem_le haA
      have h2 : minElem B ≤ mZero A B - a := minElem_le hbB
      unfold mZero at ha_lt h2
      omega
    · rintro rfl
      refine ⟨by unfold mZero; omega, minElem_mem hA, ?_⟩
      have : mZero A B - minElem A = minElem B := by unfold mZero; omega
      rw [this]
      exact minElem_mem hB
  rw [hfilt, Finset.card_singleton]

lemma mZero_le_n0 {A B : Set ℕ} {n₀ : ℕ} (hstab : ∀ n ≥ n₀, repCount A B n = 1) :
    mZero A B ≤ n₀ := by
  by_contra hgt
  push Not at hgt
  have h0 : repCount A B n₀ = 0 := repCount_eq_zero_of_lt_mZero hgt
  have h1 : repCount A B n₀ = 1 := hstab n₀ le_rfl
  omega

lemma abs_errSigned_le_errSum (A B : Set ℕ) (n₀ : ℕ) :
    |errSigned A B n₀| ≤ (errSum A B n₀ : ℤ) := by
  unfold errSigned errSum
  calc
    |∑ n ∈ Finset.range n₀, ((repCount A B n : ℤ) - 1)|
        ≤ ∑ n ∈ Finset.range n₀, |((repCount A B n : ℤ) - 1)| := Finset.abs_sum_le_sum_abs _ _
    _ = ((∑ n ∈ Finset.range n₀, Int.natAbs ((repCount A B n : ℤ) - 1) : ℕ) : ℤ) := by
          push_cast; rfl

lemma repCount_le_one_add_errSum {A B : Set ℕ} {n₀ : ℕ}
    (hstab : ∀ n ≥ n₀, repCount A B n = 1) (n : ℕ) :
    repCount A B n ≤ 1 + errSum A B n₀ := by
  by_cases hn : n < n₀
  · have hterm : Int.natAbs ((repCount A B n : ℤ) - 1) ≤ errSum A B n₀ := by
      unfold errSum
      exact Finset.single_le_sum (f := fun k => Int.natAbs ((repCount A B k : ℤ) - 1))
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hn)
    omega
  · have := hstab n (Nat.le_of_not_lt hn)
    omega

/-- **Lemma 3.1(2) / Equation (3.2):**
For every `N ≥ n₀`, `A(N) * B(N) = N + 1 + c + T(N)` in `ℤ`. -/
lemma countNat_mul_eq_N_add_c_add_T {A B : Set ℕ} {n₀ N : ℕ}
    (hstab : ∀ n ≥ n₀, repCount A B n = 1) (hN : n₀ ≤ N) :
    (countNat A N : ℤ) * (countNat B N : ℤ) =
      (N : ℤ) + 1 + errSigned A B n₀ + (crossExcess A B N : ℤ) := by
  have hprod := countNat_mul_eq_sum_repCount_add_crossExcess A B N
  have hcast : (countNat A N : ℤ) * (countNat B N : ℤ) =
      (∑ n ∈ Finset.range (N + 1), (repCount A B n : ℤ)) + (crossExcess A B N : ℤ) := by
    exact_mod_cast hprod
  rw [hcast]
  have hsplit : N + 1 = n₀ + (N + 1 - n₀) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hhead : ∑ n ∈ Finset.range n₀, (repCount A B n : ℤ) = (n₀ : ℤ) + errSigned A B n₀ := by
    unfold errSigned
    have hsum : ∑ n ∈ Finset.range n₀, ((repCount A B n : ℤ) - 1) =
        (∑ n ∈ Finset.range n₀, (repCount A B n : ℤ)) - (n₀ : ℤ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    linarith
  have htail : ∑ m ∈ Finset.range (N + 1 - n₀), (repCount A B (n₀ + m) : ℤ) =
      ((N + 1 - n₀ : ℕ) : ℤ) := by
    calc
      ∑ m ∈ Finset.range (N + 1 - n₀), (repCount A B (n₀ + m) : ℤ)
          = ∑ _m ∈ Finset.range (N + 1 - n₀), (1 : ℤ) := by
            apply Finset.sum_congr rfl
            intro m _
            simp [hstab (n₀ + m) (by omega)]
      _ = ((N + 1 - n₀ : ℕ) : ℤ) := by simp
  rw [hhead, htail]
  have hsub : ((N + 1 - n₀ : ℕ) : ℤ) = (N : ℤ) + 1 - (n₀ : ℤ) := by omega
  linarith

/-- **Lemma 3.1(3):** For all `u, v : ℕ`, `A(u) * B(v) ≤ u + v + 1 + E`. -/
lemma countNat_mul_le_add_errSum {A B : Set ℕ} {n₀ : ℕ}
    (hstab : ∀ n ≥ n₀, repCount A B n = 1) (u v : ℕ) :
    countNat A u * countNat B v ≤ u + v + 1 + errSum A B n₀ := by
  classical
  have hsum_ge : countNat A u * countNat B v ≤ ∑ n ∈ Finset.range (u + v + 1), repCount A B n := by
    unfold countNat
    rw [← Finset.card_product]
    have hmap : ∀ p ∈ ((Finset.range (u + 1)).filter (· ∈ A)) ×ˢ ((Finset.range (v + 1)).filter (· ∈ B)),
        p.1 + p.2 ∈ Finset.range (u + v + 1) := by
      intro p hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hp ⊢
      omega
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    apply Finset.sum_le_sum
    intro n hn
    unfold repCount
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
      refine ⟨by omega, hp.1.1.2, ?_⟩
      have : n - p.1 = p.2 := by omega
      rw [this]
      exact hp.1.2.2
    · rintro ⟨a₁, b₁⟩ h1 ⟨a₂, b₂⟩ h2 heq
      simp only [Finset.mem_coe, Finset.mem_filter] at h1 h2
      dsimp only at heq
      subst heq
      have hb : b₁ = b₂ := by omega
      rw [hb]
  have hsum_le : (∑ n ∈ Finset.range (u + v + 1), (repCount A B n : ℤ)) ≤
      (u + v + 1 : ℤ) + (errSum A B n₀ : ℤ) := by
    have hdiff : (∑ n ∈ Finset.range (u + v + 1), (repCount A B n : ℤ)) - (u + v + 1 : ℤ) =
        ∑ n ∈ Finset.range (u + v + 1), ((repCount A B n : ℤ) - 1) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      push_cast; ring
    have hbound : ∑ n ∈ Finset.range (u + v + 1), ((repCount A B n : ℤ) - 1) ≤ (errSum A B n₀ : ℤ) := by
      calc
        ∑ n ∈ Finset.range (u + v + 1), ((repCount A B n : ℤ) - 1)
            ≤ ∑ n ∈ Finset.range (u + v + 1), |((repCount A B n : ℤ) - 1)| :=
              Finset.sum_le_sum (fun n _ => le_abs_self _)
        _ ≤ ∑ n ∈ Finset.range n₀, |((repCount A B n : ℤ) - 1)| := by
              by_cases hle : u + v + 1 ≤ n₀
              · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hle)
                  (fun _ _ _ => abs_nonneg _)
              · have hsplit : u + v + 1 = n₀ + (u + v + 1 - n₀) := by omega
                rw [hsplit, Finset.sum_range_add]
                have hzero : ∑ m ∈ Finset.range (u + v + 1 - n₀),
                    |((repCount A B (n₀ + m) : ℤ) - 1)| = 0 := by
                  apply Finset.sum_eq_zero
                  intro m _
                  simp [hstab (n₀ + m) (by omega)]
                rw [hzero, add_zero]
        _ = (errSum A B n₀ : ℤ) := by
              unfold errSum
              push_cast; rfl
    linarith
  have hcast : ((countNat A u * countNat B v : ℕ) : ℤ) ≤
      ((u + v + 1 + errSum A B n₀ : ℕ) : ℤ) := by
    have h1 : ((countNat A u * countNat B v : ℕ) : ℤ) ≤
        ∑ n ∈ Finset.range (u + v + 1), (repCount A B n : ℤ) := by exact_mod_cast hsum_ge
    push_cast at h1 ⊢
    linarith
  exact_mod_cast hcast

/-- **Lemma 3.1(2) (`T_min < ∞`):**
There exists `K₀ : ℕ` such that `crossExcess A B N ≤ K₀` for arbitrarily large `N`. -/
lemma exists_crossExcess_frequently_le {A B : Set ℕ} (hAP : IsAlmostPerfect A B)
    {n₀ : ℕ} (hstab : ∀ n ≥ n₀, repCount A B n = 1) :
    ∃ K₀ : ℕ, ∀ M : ℕ, ∃ N ≥ M, crossExcess A B N ≤ K₀ := by
  rcases hAP with ⟨_, _, _, hnot⟩
  rw [Filter.tendsto_atTop_atTop] at hnot
  push Not at hnot
  rcases hnot with ⟨C, hC⟩
  obtain ⟨K, hK⟩ := exists_nat_gt (max C 0 + 2 + (errSum A B n₀ : ℝ))
  refine ⟨K, fun M => ?_⟩
  rcases hC (max (max (M : ℝ) (n₀ : ℝ)) 1) with ⟨x, hx_ge, hx_lt⟩
  have hx_nonneg : 0 ≤ x := by
    linarith [le_max_right (max (M : ℝ) (n₀ : ℝ)) 1]
  set N := ⌊x⌋₊
  have hN_ge_M : M ≤ N :=
    Nat.le_floor (le_trans (le_trans (le_max_left (M : ℝ) (n₀ : ℝ)) (le_max_left _ _)) hx_ge)
  have hN_ge_n0 : n₀ ≤ N :=
    Nat.le_floor (le_trans (le_trans (le_max_right (M : ℝ) (n₀ : ℝ)) (le_max_left _ _)) hx_ge)
  have hcrA : countReal A x = countNat A N := by
    unfold countReal; exact ite_eq_right_iff.mpr (fun hlt => absurd hlt (not_lt.mpr hx_nonneg))
  have hcrB : countReal B x = countNat B N := by
    unfold countReal; exact ite_eq_right_iff.mpr (fun hlt => absurd hlt (not_lt.mpr hx_nonneg))
  rw [hcrA, hcrB] at hx_lt
  have hx_lt_succ : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have heq := countNat_mul_eq_N_add_c_add_T hstab hN_ge_n0
  have heq_real : (countNat A N : ℝ) * (countNat B N : ℝ) =
      (N : ℝ) + 1 + (errSigned A B n₀ : ℝ) + (crossExcess A B N : ℝ) := by
    exact_mod_cast heq
  have hc_abs : |(errSigned A B n₀ : ℝ)| ≤ (errSum A B n₀ : ℝ) := by
    exact_mod_cast abs_errSigned_le_errSum A B n₀
  have hc_ge : -(errSum A B n₀ : ℝ) ≤ (errSigned A B n₀ : ℝ) := (abs_le.mp hc_abs).1
  have hT_lt : (crossExcess A B N : ℝ) < (K : ℝ) := by
    have hC_le : C ≤ max C 0 := le_max_left C 0
    linarith
  exact ⟨N, hN_ge_M, Nat.le_of_lt (by exact_mod_cast hT_lt)⟩

/-! ### Stripped Polynomials and Derivatives (Lemma 3.1(5) and Lemma 3.3(3)–(4)) -/

/-- Strip the maximal power of `X` dividing `P`: `stripPoly P = P / X^(natTrailingDegree P)`. -/
def stripPoly (P : ℤ[X]) : ℤ[X] :=
  ∑ d ∈ Finset.range (P.natDegree + 1),
    C (P.coeff (P.natTrailingDegree + d)) * (X : ℤ[X]) ^ d

lemma stripPoly_coeff (P : ℤ[X]) (d : ℕ) :
    (stripPoly P).coeff d = P.coeff (P.natTrailingDegree + d) := by
  unfold stripPoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  by_cases hd : d < P.natDegree + 1
  · rw [Finset.sum_eq_single d]
    · simp
    · intro b _ hbd; simp [hbd.symm]
    · intro hnot; exact absurd (Finset.mem_range.mpr hd) hnot
  · have hsum0 :
        ∑ x ∈ Finset.range (P.natDegree + 1),
          P.coeff (P.natTrailingDegree + x) * (if d = x then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      have hbd : d ≠ b := by intro h; subst h; exact hd (Finset.mem_range.mp hb)
      simp [hbd]
    rw [hsum0]
    symm
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

lemma X_pow_mul_stripPoly (P : ℤ[X]) :
    X ^ P.natTrailingDegree * stripPoly P = P := by
  ext n
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [stripPoly_coeff]
    congr 1
    omega
  · symm
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (Nat.lt_of_not_ge h)

lemma stripPoly_eval_one (P : ℤ[X]) :
    (stripPoly P).eval 1 = P.eval 1 := by
  have h := congrArg (eval 1) (X_pow_mul_stripPoly P)
  simp only [eval_mul, eval_pow, eval_X, one_pow, one_mul] at h
  exact h

lemma stripPoly_eq_of_X_pow_mul {P Q : ℤ[X]} {k : ℕ}
    (hPQ : P = X ^ k * Q) (hQ0 : Q.coeff 0 ≠ 0) :
    P.natTrailingDegree = k ∧ stripPoly P = Q := by
  have hQne : Q ≠ 0 := by intro h0; rw [h0] at hQ0; simp at hQ0
  have hPne : P ≠ 0 := by
    rw [hPQ]
    exact mul_ne_zero (pow_ne_zero k X_ne_zero) hQne
  have hk : P.natTrailingDegree = k := by
    apply le_antisymm
    · apply Polynomial.natTrailingDegree_le_of_ne_zero
      rw [hPQ, coeff_X_pow_mul']
      simpa using hQ0
    · by_contra hlt
      push Not at hlt
      set m := P.natTrailingDegree
      have hnz : P.coeff m ≠ 0 :=
        Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hPne
      have hnot : ¬ (k ≤ m) := by omega
      rw [hPQ, coeff_X_pow_mul', ite_eq_right_iff.mpr (fun hh => absurd hh hnot)] at hnz
      exact hnz rfl
  refine ⟨hk, ?_⟩
  have hmul : X ^ k * stripPoly P = X ^ k * Q :=
    calc
      X ^ k * stripPoly P = X ^ P.natTrailingDegree * stripPoly P := by rw [hk]
      _ = P := X_pow_mul_stripPoly P
      _ = X ^ k * Q := hPQ
  exact mul_left_cancel₀ (pow_ne_zero k X_ne_zero) hmul

lemma stripPoly_natDegree_le (P : ℤ[X]) :
    (stripPoly P).natDegree ≤ P.natDegree := by
  unfold stripPoly
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun d hd => ?_)
  have hd_lt := Finset.mem_range.mp hd
  calc
    (C (P.coeff (P.natTrailingDegree + d)) * (X : ℤ[X]) ^ d).natDegree
        ≤ (C (P.coeff (P.natTrailingDegree + d))).natDegree + ((X : ℤ[X]) ^ d).natDegree :=
          natDegree_mul_le
    _ = 0 + d := by rw [natDegree_C, natDegree_X_pow]
    _ ≤ P.natDegree := by omega

/-- **Lemma 3.1(5):** Exact properties of `V(X)` and `Ṽ(X) = stripPoly (VPoly A B n₀)`. -/
lemma VPoly_strip_properties {A B : Set ℕ} (hA : A.Nonempty) (hB : B.Nonempty)
    {n₀ : ℕ} (hstab : ∀ n ≥ n₀, repCount A B n = 1) :
    (VPoly A B n₀).natTrailingDegree = mZero A B ∧
    (stripPoly (VPoly A B n₀)).coeff 0 = 1 ∧
    (stripPoly (VPoly A B n₀)).eval 1 = 1 ∧
    (stripPoly (VPoly A B n₀)).natDegree ≤ n₀ ∧
    (∀ d ≥ 1, |(stripPoly (VPoly A B n₀)).coeff d| ≤ (errSum A B n₀ : ℤ)) ∧
    (Polynomial.derivative (VPoly A B n₀)).eval 1 = -errSigned A B n₀ := by
  have hVne : VPoly A B n₀ ≠ 0 := by
    intro h0
    have := VPoly_eval_one A B n₀
    rw [h0] at this
    simp at this
  have hcoeff_m0 : (VPoly A B n₀).coeff (mZero A B) = 1 := by
    rw [VPoly_coeff hstab]
    split_ifs with h0
    · rw [← h0, repCount_mZero hA hB]; norm_num
    · rw [repCount_mZero hA hB, repCount_eq_zero_of_lt_mZero (by omega)]; norm_num
  have hcoeff_lt : ∀ k < mZero A B, (VPoly A B n₀).coeff k = 0 := by
    intro k hk
    rw [VPoly_coeff hstab]
    split_ifs with h0
    · subst h0; rw [repCount_eq_zero_of_lt_mZero hk]; norm_num
    · rw [repCount_eq_zero_of_lt_mZero hk, repCount_eq_zero_of_lt_mZero (by omega)]; norm_num
  have hord : (VPoly A B n₀).natTrailingDegree = mZero A B := by
    apply le_antisymm
    · apply Polynomial.natTrailingDegree_le_of_ne_zero
      rw [hcoeff_m0]; norm_num
    · by_contra hlt
      push Not at hlt
      have hnz : (VPoly A B n₀).coeff (VPoly A B n₀).natTrailingDegree ≠ 0 :=
        Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hVne
      exact hnz (hcoeff_lt _ hlt)
  have hdegV : (VPoly A B n₀).natDegree ≤ n₀ := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun k hk => ?_)
    rw [VPoly_coeff hstab]
    have hne : k ≠ 0 := by omega
    simp only [hne, ↓reduceIte]
    rw [hstab k (by omega), hstab (k - 1) (by omega)]
    ring
  have hderiv : (Polynomial.derivative (VPoly A B n₀)).eval 1 = -errSigned A B n₀ := by
    unfold VPoly errSigned
    set Δ : ℤ[X] := ∑ n ∈ Finset.range n₀, C ((repCount A B n : ℤ) - 1) * (X : ℤ[X]) ^ n
    have hΔ1 : Δ.eval 1 = ∑ n ∈ Finset.range n₀, ((repCount A B n : ℤ) - 1) := by
      simp [Δ, eval_finsetSum]
    rw [derivative_add, derivative_one, zero_add, derivative_mul, derivative_sub,
        derivative_one, derivative_X]
    simp [eval_add, eval_mul, eval_sub, hΔ1]
  refine ⟨hord, ?_, ?_, ?_, ?_, hderiv⟩
  · rw [stripPoly_coeff, hord, add_zero, hcoeff_m0]
  · rw [stripPoly_eval_one, VPoly_eval_one]
  · exact le_trans (stripPoly_natDegree_le _) hdegV
  · intro d hd
    rw [stripPoly_coeff, hord, VPoly_coeff hstab]
    have hne : mZero A B + d ≠ 0 := by omega
    simp only [hne, ↓reduceIte]
    have hrew : (repCount A B (mZero A B + d) : ℤ) - (repCount A B (mZero A B + d - 1) : ℤ) =
        ((repCount A B (mZero A B + d) : ℤ) - 1) - ((repCount A B (mZero A B + d - 1) : ℤ) - 1) := by
      ring
    rw [hrew]
    set k₁ := mZero A B + d
    set k₂ := mZero A B + d - 1
    have hne12 : k₁ ≠ k₂ := by omega
    have hsum_abs : |((repCount A B k₁ : ℤ) - 1)| + |((repCount A B k₂ : ℤ) - 1)| ≤
        (errSum A B n₀ : ℤ) := by
      unfold errSum
      push_cast
      by_cases h1 : k₁ < n₀
      · by_cases h2 : k₂ < n₀
        · have hpair : ({k₁, k₂} : Finset ℕ) ⊆ Finset.range n₀ := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact Finset.mem_range.mpr h1
            · exact Finset.mem_range.mpr h2
          have hle := Finset.sum_le_sum_of_subset_of_nonneg hpair
            (f := fun k => |((repCount A B k : ℤ) - 1)|) (fun _ _ _ => abs_nonneg _)
          rw [Finset.sum_pair hne12] at hle
          exact hle
        · have hz2 : |((repCount A B k₂ : ℤ) - 1)| = 0 := by
            simp [hstab k₂ (Nat.le_of_not_lt h2)]
          rw [hz2, add_zero]
          exact Finset.single_le_sum
            (f := fun k => |((repCount A B k : ℤ) - 1)|)
            (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr h1)
      · have hz1 : |((repCount A B k₁ : ℤ) - 1)| = 0 := by
          simp [hstab k₁ (Nat.le_of_not_lt h1)]
        rw [hz1, zero_add]
        by_cases h2 : k₂ < n₀
        · exact Finset.single_le_sum
            (f := fun k => |((repCount A B k : ℤ) - 1)|)
            (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr h2)
        · have hz2 : |((repCount A B k₂ : ℤ) - 1)| = 0 := by
            simp [hstab k₂ (Nat.le_of_not_lt h2)]
          rw [hz2]
          exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    calc
      |((repCount A B k₁ : ℤ) - 1) - ((repCount A B k₂ : ℤ) - 1)|
          ≤ |((repCount A B k₁ : ℤ) - 1)| + |((repCount A B k₂ : ℤ) - 1)| := abs_sub _ _
      _ ≤ (errSum A B n₀ : ℤ) := hsum_abs

/-- **Generic Lemma 3.3(3)–(4):**
For any polynomial `P = 1 - (1 - X) * E` where `E : ℤ[X]` has every coefficient in `{0, 1}`:
1. `P.eval 1 = 1` and `(derivative P).eval 1 = E.eval 1`;
2. every coefficient of `P` and `stripPoly P` lies in `{-1, 0, +1}`;
3. `E.coeff m = 1` for all `m < P.natTrailingDegree`, `E.coeff P.natTrailingDegree = 0`;
4. `(stripPoly P).coeff 0 = 1` and `(stripPoly P).eval 1 = 1`;
5. `P.natTrailingDegree ≤ E.eval 1`. -/
lemma one_sub_one_sub_X_mul_properties {E : ℤ[X]}
    (hE : ∀ m, E.coeff m = 0 ∨ E.coeff m = 1) :
    let P := (1 : ℤ[X]) - (1 - X) * E
    P.eval 1 = 1 ∧
    (Polynomial.derivative P).eval 1 = E.eval 1 ∧
    (∀ m, |P.coeff m| ≤ 1) ∧
    (∀ m < P.natTrailingDegree, E.coeff m = 1) ∧
    E.coeff P.natTrailingDegree = 0 ∧
    (stripPoly P).coeff 0 = 1 ∧
    (stripPoly P).eval 1 = 1 ∧
    (∀ d, |(stripPoly P).coeff d| ≤ 1) ∧
    (P.natTrailingDegree : ℤ) ≤ E.eval 1 := by
  intro P
  have hP_eval : P.eval 1 = 1 := by simp [P]
  have hP_ne : P ≠ 0 := by intro h0; rw [h0] at hP_eval; simp at hP_eval
  have hP_deriv : (Polynomial.derivative P).eval 1 = E.eval 1 := by
    simp only [P, derivative_sub, derivative_one, zero_sub, derivative_mul, derivative_X]
    simp
  have hP_coeff : ∀ m, P.coeff m =
      if m = 0 then 1 - E.coeff 0 else E.coeff (m - 1) - E.coeff m := by
    intro m
    simp only [P, coeff_sub, coeff_one_sub_X_mul]
    cases m with
    | zero => simp
    | succ j => simp [Polynomial.coeff_one]
  have hP_abs : ∀ m, |P.coeff m| ≤ 1 := by
    intro m
    rw [hP_coeff]
    split_ifs with h0
    · rcases hE 0 with h | h <;> rw [h] <;> norm_num
    · rcases hE (m - 1) with h1 | h1 <;> rcases hE m with h2 | h2 <;> rw [h1, h2] <;> norm_num
  have hE_ones : ∀ m < P.natTrailingDegree, E.coeff m = 1 := by
    intro m
    induction m with
    | zero =>
      intro hm
      have h0 : P.coeff 0 = 0 := Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hm
      rw [hP_coeff 0] at h0
      simp only [↓reduceIte] at h0
      linarith
    | succ j ih =>
      intro hm
      have hj : E.coeff j = 1 := ih (by omega)
      have h0 : P.coeff (j + 1) = 0 := Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hm
      rw [hP_coeff (j + 1)] at h0
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hj] at h0
      linarith
  have hE_ord_zero : E.coeff P.natTrailingDegree = 0 := by
    have hnz : P.coeff P.natTrailingDegree ≠ 0 :=
      Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hP_ne
    rw [hP_coeff] at hnz
    cases hord : P.natTrailingDegree with
    | zero =>
      rw [hord] at hnz
      simp only [↓reduceIte] at hnz
      rcases hE 0 with h | h
      · exact h
      · omega
    | succ j =>
      rw [hord] at hnz
      have hj : E.coeff j = 1 := hE_ones j (by omega)
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hj] at hnz
      rcases hE (j + 1) with h | h
      · exact h
      · omega
  have hstrip0 : (stripPoly P).coeff 0 = 1 := by
    rw [stripPoly_coeff, add_zero, hP_coeff]
    cases hord : P.natTrailingDegree with
    | zero =>
      have h0 : E.coeff 0 = 0 := by rwa [hord] at hE_ord_zero
      simp [h0]
    | succ j =>
      have hj : E.coeff j = 1 := hE_ones j (by omega)
      have hj1 : E.coeff (j + 1) = 0 := by rwa [hord] at hE_ord_zero
      simp [hj, hj1]
  have hord_le_E : (P.natTrailingDegree : ℤ) ≤ E.eval 1 := by
    by_cases hE0 : E = 0
    · have hP1 : P = 1 := by simp [P, hE0]
      have hord0 : P.natTrailingDegree = 0 := by rw [hP1]; simp
      rw [hord0, hE0]; simp
    · have hord_le_deg : P.natTrailingDegree ≤ E.natDegree + 1 := by
        by_contra hgt
        push Not at hgt
        have h1 : E.coeff (E.natDegree + 1) = 1 := hE_ones (E.natDegree + 1) (by omega)
        have h0 : E.coeff (E.natDegree + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        omega
      have hevalE : E.eval 1 = ∑ m ∈ Finset.range (E.natDegree + 1), E.coeff m := by
        rw [eval_eq_sum_range' (Nat.lt_succ_self _)]
        simp
      rw [hevalE]
      calc
        (P.natTrailingDegree : ℤ)
            = ∑ _m ∈ Finset.range P.natTrailingDegree, (1 : ℤ) := by simp
        _ = ∑ m ∈ Finset.range P.natTrailingDegree, E.coeff m := by
              apply Finset.sum_congr rfl
              intro m hm
              exact (hE_ones m (Finset.mem_range.mp hm)).symm
        _ ≤ ∑ m ∈ Finset.range (E.natDegree + 1), E.coeff m := by
              apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hord_le_deg)
              intro m _ _
              rcases hE m with h | h <;> omega
  refine ⟨hP_eval, hP_deriv, hP_abs, hE_ones, hE_ord_zero, hstrip0, ?_, ?_, hord_le_E⟩
  · rw [stripPoly_eval_one, hP_eval]
  · intro d; rw [stripPoly_coeff]; exact hP_abs _

/-- Derivative of `WPoly A B N` at `1` equals `crossExcess A B N`. -/
lemma WPoly_deriv_eval_one (A B : Set ℕ) (N : ℕ) :
    (Polynomial.derivative (WPoly A B N)).eval 1 = (crossExcess A B N : ℤ) := by
  unfold WPoly crossExcess
  set E : ℤ[X] := ∑ m ∈ Finset.range N, C (repTrunc A B N (N + 1 + m) : ℤ) * (X : ℤ[X]) ^ m
  have hE1 : E.eval 1 = (∑ m ∈ Finset.range N, (repTrunc A B N (N + 1 + m) : ℤ)) := by
    simp [E, eval_finsetSum]
  have hderiv : (Polynomial.derivative ((1 : ℤ[X]) - (1 - X) * E)).eval 1 = E.eval 1 := by
    simp [derivative_sub, derivative_one, derivative_mul, derivative_X]
  rw [hderiv, hE1]
  push_cast
  rfl

/-- Stripped `WPoly` properties for any `N ≥ n₀`. -/
lemma WPoly_strip_properties {A B : Set ℕ} {n₀ N : ℕ}
    (hstab : ∀ n ≥ n₀, repCount A B n = 1) (hN : n₀ ≤ N) :
    (stripPoly (WPoly A B N)).coeff 0 = 1 ∧
    (stripPoly (WPoly A B N)).eval 1 = 1 ∧
    (∀ d, |(stripPoly (WPoly A B N)).coeff d| ≤ 1) ∧
    (WPoly A B N).natTrailingDegree ≤ crossExcess A B N := by
  set E : ℤ[X] := ∑ m ∈ Finset.range N, C (repTrunc A B N (N + 1 + m) : ℤ) * (X : ℤ[X]) ^ m
  have hE_coeff : ∀ m, E.coeff m = 0 ∨ E.coeff m = 1 := by
    intro m
    rw [finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow]
    by_cases hm : m < N
    · rw [Finset.sum_eq_single m]
      · simp only [↓reduceIte, mul_one]
        have hle1 : repTrunc A B N (N + 1 + m) ≤ 1 :=
          (repTrunc_le_repCount A B N (N + 1 + m)).trans (by rw [hstab _ (by omega)])
        omega
      · intro b _ hbm; simp [hbm.symm]
      · intro hnot; exact absurd (Finset.mem_range.mpr hm) hnot
    · left
      apply Finset.sum_eq_zero
      intro b hb
      have hbm : m ≠ b := by intro h; subst h; exact hm (Finset.mem_range.mp hb)
      simp [hbm]
  have hP := one_sub_one_sub_X_mul_properties hE_coeff
  have hW_eq : WPoly A B N = 1 - (1 - X) * E := rfl
  have hE1 : E.eval 1 = (crossExcess A B N : ℤ) := by
    unfold crossExcess
    simp [E, eval_finsetSum]
  rw [← hW_eq, hE1] at hP
  exact ⟨hP.2.2.2.2.2.1, hP.2.2.2.2.2.2.1, hP.2.2.2.2.2.2.2.1, by exact_mod_cast hP.2.2.2.2.2.2.2.2⟩

/-! ### Lemma 3.4: Quantitative Modular Difference Density -/

private lemma sum_sq_card_fiber_eq {α : Type*} [DecidableEq α] (s : Finset α)
    (N : ℕ) (f : α → ℕ) (hf : ∀ x ∈ s, f x < N) :
    ∑ n ∈ Finset.range N, ((s.filter (fun x => f x = n)).card) ^ 2 =
      ((s ×ˢ s).filter (fun pq => f pq.1 = f pq.2)).card := by
  have h1 : ∀ n ∈ Finset.range N,
      ((s.filter (fun x => f x = n)).card) ^ 2 =
      (((s ×ˢ s).filter (fun pq => f pq.1 = f pq.2)).filter (fun pq => f pq.1 = n)).card := by
    intro n _
    rw [sq, ← Finset.card_product]
    congr 1
    ext ⟨x, y⟩
    simp only [Finset.mem_product, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx, hfx⟩, ⟨hy, hfy⟩⟩; exact ⟨⟨⟨hx, hy⟩, hfx.trans hfy.symm⟩, hfx⟩
    · rintro ⟨⟨⟨hx, hy⟩, heq⟩, hfx⟩; exact ⟨⟨hx, hfx⟩, ⟨hy, heq.symm.trans hfx⟩⟩
  rw [Finset.sum_congr rfl h1]
  symm
  apply Finset.card_eq_sum_card_fiberwise
  intro pq hpq
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hpq
  exact Finset.mem_coe.mpr (Finset.mem_range.mpr (hf pq.1 hpq.1.1))

/-- **Lemma 3.4 (Quantitative Modular Difference Density):**
For any `N ≥ n₀` with `N ∉ A`, `N ∉ B`, `crossExcess A B N ≤ K`, letting
`A₀ = (Finset.range N).filter (· ∈ A)` and `B₀ = (Finset.range N).filter (· ∈ B)`
with upper bounds `x₀` on `A₀` and `z₀` on `B₀`:
1. `#{d ∈ [0, N - 1 - x₀] : d ∉ B₀ - A₀} ≤ C₁(K)` (with `[0, N - 1 - x₀]` represented as `range (N - x₀)` when `x₀ < N`),
2. `#{d ∈ [1, N - 1 - z₀] : d ∉ A₀ - B₀} ≤ C₁(K)`. -/
theorem modular_difference_density {A B : Set ℕ} {n₀ N K x₀ z₀ : ℕ}
    (hstab : ∀ n ≥ n₀, repCount A B n = 1)
    (hN_ge : n₀ ≤ N) (hN_pos : 1 ≤ N)
    (hNA : N ∉ A) (hNB : N ∉ B)
    (hT : crossExcess A B N ≤ K)
    (hx₀ : ∀ a ∈ A, a < N → a ≤ x₀)
    (hz₀ : ∀ b ∈ B, b < N → b ≤ z₀) :
    letI := Classical.decPred (· ∈ A)
    letI := Classical.decPred (· ∈ B)
    let A₀ := (Finset.range N).filter (· ∈ A)
    let B₀ := (Finset.range N).filter (· ∈ B)
    ((Finset.range (N - x₀)).filter (fun d => ¬ ∃ a ∈ A₀, ∃ b ∈ B₀, b = a + d)).card ≤
      C1Const A B n₀ K ∧
    ((Finset.Icc 1 (N - 1 - z₀)).filter (fun d => ¬ ∃ a ∈ A₀, ∃ b ∈ B₀, a = b + d)).card ≤
      C1Const A B n₀ K := by
  classical
  set A₀ := (Finset.range N).filter (· ∈ A)
  set B₀ := (Finset.range N).filter (· ∈ B)
  have hA₀_card : A₀.card = countNat A N := by
    unfold countNat
    congr 1
    ext a
    simp only [A₀, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      by_contra hge
      have heq : a = N := by omega
      subst heq
      exact hNA h2
  have hB₀_card : B₀.card = countNat B N := by
    unfold countNat
    congr 1
    ext b
    simp only [B₀, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      by_contra hge
      have heq : b = N := by omega
      subst heq
      exact hNB h2
  set R : ℕ → ℕ := fun n => ((A₀ ×ˢ B₀).filter (fun p => (p.1 + p.2) % N = n)).card
  set D : ℕ → ℕ := fun n => ((A₀ ×ˢ B₀).filter (fun p => (p.2 + N - p.1) % N = n)).card
  have hsumR : ∑ n ∈ Finset.range N, R n = A₀.card * B₀.card := by
    rw [← Finset.card_product]
    symm
    exact Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_range.mpr (Nat.mod_lt _ hN_pos))
  have hsumD : ∑ n ∈ Finset.range N, D n = A₀.card * B₀.card := by
    rw [← Finset.card_product]
    symm
    exact Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_range.mpr (Nat.mod_lt _ hN_pos))
  have hsumSq : ∑ n ∈ Finset.range N, (R n) ^ 2 = ∑ n ∈ Finset.range N, (D n) ^ 2 := by
    rw [sum_sq_card_fiber_eq (A₀ ×ˢ B₀) N (fun p => (p.1 + p.2) % N) (fun _ _ => Nat.mod_lt _ hN_pos)]
    rw [sum_sq_card_fiber_eq (A₀ ×ˢ B₀) N (fun p => (p.2 + N - p.1) % N) (fun _ _ => Nat.mod_lt _ hN_pos)]
    apply Finset.card_bij (fun pq _ => ((pq.2.1, pq.1.2), (pq.1.1, pq.2.2)))
    · intro pq hpq
      simp only [Finset.mem_filter, Finset.mem_product] at hpq ⊢
      rcases hpq with ⟨⟨⟨ha1, hb1⟩, ⟨ha2, hb2⟩⟩, hmod⟩
      refine ⟨⟨⟨ha2, hb1⟩, ⟨ha1, hb2⟩⟩, ?_⟩
      have ha1_lt : pq.1.1 < N := (Finset.mem_range.mp (Finset.mem_filter.mp ha1).1)
      have ha2_lt : pq.2.1 < N := (Finset.mem_range.mp (Finset.mem_filter.mp ha2).1)
      have h1 : (pq.1.2 + N - pq.2.1 + (pq.1.1 + pq.2.1)) % N = (pq.1.1 + pq.1.2) % N := by
        have : pq.1.2 + N - pq.2.1 + (pq.1.1 + pq.2.1) = (pq.1.1 + pq.1.2) + N := by omega
        rw [this, Nat.add_mod_right]
      have h2 : (pq.2.2 + N - pq.1.1 + (pq.1.1 + pq.2.1)) % N = (pq.2.1 + pq.2.2) % N := by
        have : pq.2.2 + N - pq.1.1 + (pq.1.1 + pq.2.1) = (pq.2.1 + pq.2.2) + N := by omega
        rw [this, Nat.add_mod_right]
      have heq_add : (pq.1.2 + N - pq.2.1 + (pq.1.1 + pq.2.1)) % N =
          (pq.2.2 + N - pq.1.1 + (pq.1.1 + pq.2.1)) % N := by rw [h1, h2, hmod]
      -- Cancel +(pq.1.1 + pq.2.1) mod N via ZMod or direct Nat arithmetic
      have hsub1 : (pq.1.2 + N - pq.2.1) % N = (pq.2.2 + N - pq.1.1) % N := by
        have hz : ((pq.1.2 + N - pq.2.1 : ℕ) : ℤ) ≡ ((pq.2.2 + N - pq.1.1 : ℕ) : ℤ) [ZMOD (N : ℤ)] := by
          have hz1 : ((pq.1.2 + N - pq.2.1 + (pq.1.1 + pq.2.1) : ℕ) : ℤ) ≡
              ((pq.2.2 + N - pq.1.1 + (pq.1.1 + pq.2.1) : ℕ) : ℤ) [ZMOD (N : ℤ)] := by
            rw [Int.ModEq]; exact_mod_cast heq_add
          push_cast at hz1
          exact Int.ModEq.add_right_cancel' _ hz1
        rw [Int.ModEq] at hz
        exact_mod_cast hz
      exact hsub1
    · rintro ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩ _ ⟨⟨a1', b1'⟩, ⟨a2', b2'⟩⟩ _ heq
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
      rfl
    · rintro ⟨⟨a2, b1⟩, ⟨a1, b2⟩⟩ hpq
      simp only [Finset.mem_filter, Finset.mem_product] at hpq
      rcases hpq with ⟨⟨⟨ha2, hb1⟩, ⟨ha1, hb2⟩⟩, hmod⟩
      refine ⟨((a1, b1), (a2, b2)), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨⟨ha1, hb1⟩, ⟨ha2, hb2⟩⟩, ?_⟩
      have ha1_lt : a1 < N := (Finset.mem_range.mp (Finset.mem_filter.mp ha1).1)
      have ha2_lt : a2 < N := (Finset.mem_range.mp (Finset.mem_filter.mp ha2).1)
      have h1 : (b1 + N - a2 + (a1 + a2)) % N = (a1 + b1) % N := by
        have : b1 + N - a2 + (a1 + a2) = (a1 + b1) + N := by omega
        rw [this, Nat.add_mod_right]
      have h2 : (b2 + N - a1 + (a1 + a2)) % N = (a2 + b2) % N := by
        have : b2 + N - a1 + (a1 + a2) = (a2 + b2) + N := by omega
        rw [this, Nat.add_mod_right]
      rw [← h1, ← h2]
      rw [Nat.add_mod, hmod, ← Nat.add_mod]
  -- Express R(n) = repCount A B n + repTrunc A B N (n + N) for n < N
  have hR_eq : ∀ n < N, R n = repCount A B n + repTrunc A B N (n + N) := by
    intro n hn
    have hdisj : Disjoint
        ((A₀ ×ˢ B₀).filter (fun p => p.1 + p.2 = n))
        ((A₀ ×ˢ B₀).filter (fun p => p.1 + p.2 = n + N)) := by
      rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [Finset.mem_filter] at h1 h2
      omega
    have hunion : (A₀ ×ˢ B₀).filter (fun p => (p.1 + p.2) % N = n) =
        ((A₀ ×ˢ B₀).filter (fun p => p.1 + p.2 = n)) ∪
        ((A₀ ×ˢ B₀).filter (fun p => p.1 + p.2 = n + N)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product, A₀, B₀, Finset.mem_range]
      constructor
      · rintro ⟨⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩, hmod⟩
        have hlt2 : a + b < 2 * N := by omega
        have hq_lt : (a + b) / N < 2 := (Nat.div_lt_iff_lt_mul hN_pos).mpr (by omega)
        have hdm := Nat.div_add_mod (a + b) N
        match hq : (a + b) / N with
        | 0 =>
          rw [hq, mul_zero, zero_add] at hdm
          left; exact ⟨⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩, by omega⟩
        | 1 =>
          rw [hq, mul_one] at hdm
          right; exact ⟨⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩, by omega⟩
        | k + 2 => omega
      · rintro (⟨⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩, heq⟩ | ⟨⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩, heq⟩)
        · exact ⟨⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩, by rw [heq, Nat.mod_eq_of_lt hn]⟩
        · exact ⟨⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩, by rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hn]⟩
    have hc1 : ((A₀ ×ˢ B₀).filter (fun p => p.1 + p.2 = n)).card = repCount A B n := by
      unfold repCount
      apply Finset.card_bij (fun p _ => p.1)
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, A₀, B₀, Finset.mem_range] at hp ⊢
        refine ⟨by omega, hp.1.1.2, ?_⟩
        have : n - p.1 = p.2 := by omega
        rw [this]; exact hp.1.2.2
      · rintro ⟨a1, b1⟩ h1 ⟨a2, b2⟩ h2 heq
        simp only [Finset.mem_filter] at h1 h2
        dsimp only at heq
        subst heq
        have hb : b1 = b2 := by omega
        rw [hb]
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_range] at ha
        refine ⟨(a, n - a), ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_product, A₀, B₀, Finset.mem_range]
        exact ⟨⟨⟨by omega, ha.2.1⟩, ⟨by omega, ha.2.2⟩⟩, by omega⟩
    have hc2 : ((A₀ ×ˢ B₀).filter (fun p => p.1 + p.2 = n + N)).card = repTrunc A B N (n + N) := by
      unfold repTrunc
      apply Finset.card_bij (fun p _ => p.1)
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, A₀, B₀, Finset.mem_range] at hp ⊢
        refine ⟨by omega, hp.1.1.2, by omega, by omega, ?_⟩
        have : n + N - p.1 = p.2 := by omega
        rw [this]; exact hp.1.2.2
      · rintro ⟨a1, b1⟩ h1 ⟨a2, b2⟩ h2 heq
        simp only [Finset.mem_filter] at h1 h2
        dsimp only at heq
        subst heq
        have hb : b1 = b2 := by omega
        rw [hb]
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_range] at ha
        have ha_lt : a < N := by
          by_contra hge
          have heq : a = N := by omega
          subst heq
          exact hNA ha.2.1
        have hb_lt : n + N - a < N := by
          by_contra hge
          have heq : n + N - a = N := by omega
          rw [heq] at ha
          exact hNB ha.2.2.2.2
        refine ⟨(a, n + N - a), ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_product, A₀, B₀, Finset.mem_range]
        exact ⟨⟨⟨ha_lt, ha.2.1⟩, ⟨hb_lt, ha.2.2.2.2⟩⟩, by omega⟩
    show ((A₀ ×ˢ B₀).filter (fun p => (p.1 + p.2) % N = n)).card = _
    rw [hunion, Finset.card_union_of_disjoint hdisj, hc1, hc2]
  -- Bound ∑ R(n)(R(n)-1) ≤ S₂ + 2(1 + E)(1 + K)
  have hsum_R_pair :
      ∑ n ∈ Finset.range N, (R n : ℤ) * ((R n : ℤ) - 1) ≤
        (repPairSum A B n₀ : ℤ) + 2 * (1 + (errSum A B n₀ : ℤ)) * (1 + (K : ℤ)) := by
    have hterm : ∀ n ∈ Finset.range N,
        (R n : ℤ) * ((R n : ℤ) - 1) =
          (repCount A B n : ℤ) * ((repCount A B n : ℤ) - 1) +
          2 * (repCount A B n : ℤ) * (repTrunc A B N (n + N) : ℤ) := by
      intro n hn
      have hn_lt := Finset.mem_range.mp hn
      rw [hR_eq n hn_lt]
      have he_le1 : repTrunc A B N (n + N) ≤ 1 :=
        (repTrunc_le_repCount A B N (n + N)).trans (by rw [hstab _ (by omega)])
      have he_quad : (repTrunc A B N (n + N) : ℤ) * ((repTrunc A B N (n + N) : ℤ) - 1) = 0 := by
        have : repTrunc A B N (n + N) = 0 ∨ repTrunc A B N (n + N) = 1 := by omega
        rcases this with h | h <;> simp [h]
      push_cast
      linarith
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    have hpart1 : ∑ n ∈ Finset.range N, (repCount A B n : ℤ) * ((repCount A B n : ℤ) - 1) =
        (repPairSum A B n₀ : ℤ) := by
      have hsplit : N = n₀ + (N - n₀) := by omega
      rw [hsplit, Finset.sum_range_add]
      have htail : ∑ m ∈ Finset.range (N - n₀),
          (repCount A B (n₀ + m) : ℤ) * ((repCount A B (n₀ + m) : ℤ) - 1) = 0 := by
        apply Finset.sum_eq_zero
        intro m _
        simp [hstab (n₀ + m) (by omega)]
      rw [htail, add_zero]
      unfold repPairSum
      push_cast
      apply Finset.sum_congr rfl
      intro n _
      cases hr : repCount A B n with
      | zero => simp
      | succ k => push_cast; ring
    have hpart2 :
        ∑ n ∈ Finset.range N, 2 * (repCount A B n : ℤ) * (repTrunc A B N (n + N) : ℤ) ≤
          2 * (1 + (errSum A B n₀ : ℤ)) * (1 + (K : ℤ)) := by
      have hsum_e : ∑ n ∈ Finset.range N, (repTrunc A B N (n + N) : ℤ) ≤ 1 + (K : ℤ) := by
        have hrg : Finset.range N = Finset.range (1 + (N - 1)) := by congr 1; omega
        rw [hrg, Finset.sum_range_add]
        simp only [Finset.range_one, Finset.sum_singleton, zero_add]
        have h0 : repTrunc A B N N ≤ 1 :=
          (repTrunc_le_repCount A B N N).trans (by rw [hstab N hN_ge])
        have htail : ∑ x ∈ Finset.range (N - 1), repTrunc A B N (1 + x + N) ≤ crossExcess A B N := by
          unfold crossExcess
          have hsub : Finset.range (N - 1) ⊆ Finset.range N := Finset.range_mono (by omega)
          calc
            ∑ x ∈ Finset.range (N - 1), repTrunc A B N (1 + x + N)
                = ∑ x ∈ Finset.range (N - 1), repTrunc A B N (N + 1 + x) := by
                  apply Finset.sum_congr rfl; intro x _; congr 1; omega
            _ ≤ ∑ x ∈ Finset.range N, repTrunc A B N (N + 1 + x) :=
                  Finset.sum_le_sum_of_subset hsub
        have htail_z : ∑ x ∈ Finset.range (N - 1), (repTrunc A B N (1 + x + N) : ℤ) ≤ (K : ℤ) := by
          have : ∑ x ∈ Finset.range (N - 1), repTrunc A B N (1 + x + N) ≤ K := le_trans htail hT
          exact_mod_cast this
        have h0_z : (repTrunc A B N N : ℤ) ≤ 1 := by exact_mod_cast h0
        linarith
      calc
        ∑ n ∈ Finset.range N, 2 * (repCount A B n : ℤ) * (repTrunc A B N (n + N) : ℤ)
            ≤ ∑ n ∈ Finset.range N, 2 * (1 + (errSum A B n₀ : ℤ)) * (repTrunc A B N (n + N) : ℤ) := by
              apply Finset.sum_le_sum
              intro n _
              have hr : (repCount A B n : ℤ) ≤ 1 + (errSum A B n₀ : ℤ) := by
                exact_mod_cast repCount_le_one_add_errSum hstab n
              have he_nn : (0 : ℤ) ≤ (repTrunc A B N (n + N) : ℤ) := Nat.cast_nonneg _
              nlinarith
        _ = 2 * (1 + (errSum A B n₀ : ℤ)) * ∑ n ∈ Finset.range N, (repTrunc A B N (n + N) : ℤ) := by
              rw [Finset.mul_sum]
        _ ≤ 2 * (1 + (errSum A B n₀ : ℤ)) * (1 + (K : ℤ)) := by
              have hpos : (0 : ℤ) ≤ 2 * (1 + (errSum A B n₀ : ℤ)) := by positivity
              exact mul_le_mul_of_nonneg_left hsum_e hpos
    linarith
  -- Main bound: #{0 ≤ n < N : D(n) = 0} ≤ C₁(K)
  have hzero_D : ((Finset.range N).filter (fun n => D n = 0)).card ≤ C1Const A B n₀ K := by
    have hcast : (((Finset.range N).filter (fun n => D n = 0)).card : ℤ) ≤ (C1Const A B n₀ K : ℤ) := by
      have hcard_sum : (((Finset.range N).filter (fun n => D n = 0)).card : ℤ) =
          ∑ n ∈ Finset.range N, (if D n = 0 then (1 : ℤ) else 0) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [hcard_sum]
      have hquad : ∑ n ∈ Finset.range N, (if D n = 0 then (1 : ℤ) else 0) ≤
          ∑ n ∈ Finset.range N, (1 - (D n : ℤ)) +
          ∑ n ∈ Finset.range N, (D n : ℤ) * ((D n : ℤ) - 1) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_le_sum (fun n _ => indicator_zero_le_quad (D n))
      have hpair_eq : ∑ n ∈ Finset.range N, (D n : ℤ) * ((D n : ℤ) - 1) =
          ∑ n ∈ Finset.range N, (R n : ℤ) * ((R n : ℤ) - 1) := by
        have h1 : ∀ f : ℕ → ℕ, ∑ n ∈ Finset.range N, (f n : ℤ) * ((f n : ℤ) - 1) =
            (∑ n ∈ Finset.range N, ((f n : ℤ) ^ 2)) - ∑ n ∈ Finset.range N, (f n : ℤ) := by
          intro f
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro n _; ring
        rw [h1 D, h1 R]
        have hsD : ∑ n ∈ Finset.range N, (D n : ℤ) = ∑ n ∈ Finset.range N, (R n : ℤ) := by
          exact_mod_cast (hsumD.trans hsumR.symm)
        have hsq : ∑ n ∈ Finset.range N, ((D n : ℤ) ^ 2) = ∑ n ∈ Finset.range N, ((R n : ℤ) ^ 2) := by
          exact_mod_cast hsumSq.symm
        rw [hsD, hsq]
      have hlin : ∑ n ∈ Finset.range N, (1 - (D n : ℤ)) =
          (N : ℤ) - (countNat A N : ℤ) * (countNat B N : ℤ) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        have hD_cast : ∑ n ∈ Finset.range N, (D n : ℤ) = (countNat A N : ℤ) * (countNat B N : ℤ) := by
          rw [← hA₀_card, ← hB₀_card]; exact_mod_cast hsumD
        linarith
      have hprod := countNat_mul_eq_N_add_c_add_T hstab hN_ge
      have hc_ge : -(errSum A B n₀ : ℤ) ≤ errSigned A B n₀ := (abs_le.mp (abs_errSigned_le_errSum A B n₀)).1
      have hT_nn : (0 : ℤ) ≤ (crossExcess A B N : ℤ) := Nat.cast_nonneg _
      unfold C1Const
      push_cast
      linarith
    exact_mod_cast hcast
  -- Deduce (1) and (2)
  constructor
  · calc
      ((Finset.range (N - x₀)).filter (fun d => ¬ ∃ a ∈ A₀, ∃ b ∈ B₀, b = a + d)).card
          ≤ ((Finset.range N).filter (fun n => D n = 0)).card := by
            apply Finset.card_le_card
            intro d hd
            simp only [Finset.mem_filter, Finset.mem_range] at hd ⊢
            refine ⟨by omega, ?_⟩
            by_contra hne
            have hpos : 0 < D d := Nat.pos_of_ne_zero hne
            obtain ⟨⟨a, b⟩, hp⟩ := Finset.card_pos.mp hpos
            simp only [Finset.mem_filter, Finset.mem_product] at hp
            have ha_le : a ≤ x₀ := hx₀ a (Finset.mem_filter.mp hp.1.1).2 (Finset.mem_range.mp (Finset.mem_filter.mp hp.1.1).1)
            have hb_lt : b < N := Finset.mem_range.mp (Finset.mem_filter.mp hp.1.2).1
            have ha_lt : a < N := Finset.mem_range.mp (Finset.mem_filter.mp hp.1.1).1
            -- Since b + N - a ∈ [N - x₀, 2N - 1] and d < N - x₀, (b + N - a) % N = d forces b + N - a = d + N, i.e., b = a + d
            have hmod := hp.2
            have hq_lt : (b + N - a) / N < 2 := (Nat.div_lt_iff_lt_mul hN_pos).mpr (by omega)
            have hdm := Nat.div_add_mod (b + N - a) N
            match hq : (b + N - a) / N with
            | 0 => rw [hq, mul_zero, zero_add] at hdm; omega
            | 1 => rw [hq, mul_one] at hdm; exact hd.2 ⟨a, hp.1.1, b, hp.1.2, by omega⟩
            | k + 2 => omega
      _ ≤ C1Const A B n₀ K := hzero_D
  · calc
      ((Finset.Icc 1 (N - 1 - z₀)).filter (fun d => ¬ ∃ a ∈ A₀, ∃ b ∈ B₀, a = b + d)).card
          ≤ ((Finset.range N).filter (fun n => D n = 0)).card := by
            apply Finset.card_le_card_of_injOn (fun d => N - d)
            · intro d hd
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hd ⊢
              refine ⟨by omega, ?_⟩
              by_contra hne
              have hpos : 0 < D (N - d) := Nat.pos_of_ne_zero hne
              obtain ⟨⟨a, b⟩, hp⟩ := Finset.card_pos.mp hpos
              simp only [Finset.mem_filter, Finset.mem_product] at hp
              have hb_le : b ≤ z₀ := hz₀ b (Finset.mem_filter.mp hp.1.2).2 (Finset.mem_range.mp (Finset.mem_filter.mp hp.1.2).1)
              have ha_lt : a < N := Finset.mem_range.mp (Finset.mem_filter.mp hp.1.1).1
              have hb_lt : b < N := Finset.mem_range.mp (Finset.mem_filter.mp hp.1.2).1
              have hmod := hp.2
              have hq_lt : (b + N - a) / N < 2 := (Nat.div_lt_iff_lt_mul hN_pos).mpr (by omega)
              have hdm := Nat.div_add_mod (b + N - a) N
              match hq : (b + N - a) / N with
              | 0 => rw [hq, mul_zero, zero_add] at hdm; exact hd.2 ⟨a, hp.1.1, b, hp.1.2, by omega⟩
              | 1 => rw [hq, mul_one] at hdm; omega
              | k + 2 => omega
            · intro d₁ h1 d₂ h2 heq
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at h1 h2
              dsimp only at heq
              omega
      _ ≤ C1Const A B n₀ K := hzero_D

end

end AlmostPerfect
