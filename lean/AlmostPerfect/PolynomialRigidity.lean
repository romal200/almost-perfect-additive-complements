import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Tactic

/-!
# Section 6: Polynomial Iteration Rigidity (Lemma 6.1)

Proves the UFD rigidity theorem in `ℤ[X]`: if `V, W₀, ..., W_k ∈ ℤ[X]` satisfy
`V(0) = 1`, `W_j(0) = 1`, `|coeff_d(W_j)| ≤ 1`, `V · W_{j+1} = W_j²` for `0 ≤ j < k`,
and `2^k > max (natDegree V) (E + 1)` where `|coeff_d(V)| ≤ E`, then `W_j = V` for all `j ≤ k`.
-/

namespace AlmostPerfect

open Polynomial

/-- Inductive identity `V ^ (2 ^ j - 1) * W j = (W 0) ^ (2 ^ j)` from the quadratic recurrence. -/
lemma poly_iter_identity (V : ℤ[X]) (W : ℕ → ℤ[X]) (k : ℕ)
    (hrec : ∀ j < k, V * W (j + 1) = (W j) ^ 2) :
    ∀ j ≤ k, V ^ (2 ^ j - 1) * W j = (W 0) ^ (2 ^ j) := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    have hj_lt : j < k := Nat.lt_of_succ_le hj
    have ih' := ih (Nat.le_of_lt hj_lt)
    have hpos : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have hexp : 2 ^ (j + 1) - 1 = 2 * (2 ^ j - 1) + 1 := by omega
    calc
      V ^ (2 ^ (j + 1) - 1) * W (j + 1)
          = V ^ (2 * (2 ^ j - 1)) * (V * W (j + 1)) := by
              rw [hexp, pow_succ]; ring
      _ = (V ^ (2 ^ j - 1)) ^ 2 * (W j) ^ 2 := by
              rw [hrec j hj_lt, pow_mul']
      _ = (V ^ (2 ^ j - 1) * W j) ^ 2 := by ring
      _ = ((W 0) ^ (2 ^ j)) ^ 2 := by rw [ih']
      _ = (W 0) ^ (2 ^ (j + 1)) := by rw [← pow_mul, pow_succ]

/-- Any irreducible polynomial dividing `V` with `V.coeff 0 = 1` has degree at least `1`. -/
lemma irred_natDegree_pos_of_dvd_coeff_zero_one {V q : ℤ[X]}
    (hV0 : V.coeff 0 = 1) (hq : Irreducible q) (hdvd : q ∣ V) :
    1 ≤ q.natDegree := by
  by_contra h
  push Not at h
  have hdeg0 : q.natDegree = 0 := Nat.lt_one_iff.mp h
  have hqC : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero hdeg0
  rcases hdvd with ⟨u, hu⟩
  have h0 : q.coeff 0 * u.coeff 0 = 1 := by
    have := congrArg (fun p : ℤ[X] => p.coeff 0) hu
    simpa [mul_coeff_zero, hV0] using this.symm
  have hunit_c : IsUnit (q.coeff 0) := isUnit_iff_exists_inv.mpr ⟨u.coeff 0, h0⟩
  have hunit_q : IsUnit q := by
    rw [hqC]
    exact hunit_c.map C
  exact hq.not_isUnit hunit_q

/-- Every irreducible factor of `V` with `V.coeff 0 = 1` has multiplicity at most `V.natDegree`. -/
lemma count_normalizedFactors_le_natDegree {V q : ℤ[X]}
    (hV0 : V.coeff 0 = 1) (hq : q ∈ UniqueFactorizationMonoid.normalizedFactors V) :
    (UniqueFactorizationMonoid.normalizedFactors V).count q ≤ V.natDegree := by
  have hVne : V ≠ 0 := by
    intro h0; rw [h0, coeff_zero] at hV0; exact zero_ne_one hV0
  have hprod : Associated (UniqueFactorizationMonoid.normalizedFactors V).prod V :=
    UniqueFactorizationMonoid.prod_normalizedFactors hVne
  have hdeg_prod : (UniqueFactorizationMonoid.normalizedFactors V).prod.natDegree = V.natDegree := by
    rcases hprod with ⟨u, hu⟩
    have hu_deg : (u : ℤ[X]).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit u.isUnit
    have hne_p : (UniqueFactorizationMonoid.normalizedFactors V).prod ≠ 0 := by
      intro hp
      rw [hp, zero_mul] at hu
      exact hVne hu.symm
    conv_rhs => rw [← hu]
    rw [Polynomial.natDegree_mul hne_p u.ne_zero, hu_deg, add_zero]
  have hnz : (0 : ℤ[X]) ∉ UniqueFactorizationMonoid.normalizedFactors V := fun h0 =>
    (UniqueFactorizationMonoid.irreducible_of_normalized_factor 0 h0).ne_zero rfl
  have hsum :
      ((UniqueFactorizationMonoid.normalizedFactors V).map Polynomial.natDegree).sum =
        (UniqueFactorizationMonoid.normalizedFactors V).prod.natDegree := by
    exact (Polynomial.natDegree_multiset_prod _ hnz).symm
  have hq_irred : Irreducible q := UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq
  have hq_dvd : q ∣ V := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq
  have hq_deg : 1 ≤ q.natDegree := irred_natDegree_pos_of_dvd_coeff_zero_one hV0 hq_irred hq_dvd
  have hle : Multiset.replicate ((UniqueFactorizationMonoid.normalizedFactors V).count q) q ≤
      UniqueFactorizationMonoid.normalizedFactors V :=
    Multiset.le_count_iff_replicate_le.mp le_rfl
  have hmap_le :
      (Multiset.replicate ((UniqueFactorizationMonoid.normalizedFactors V).count q) q).map
          Polynomial.natDegree ≤
        (UniqueFactorizationMonoid.normalizedFactors V).map Polynomial.natDegree :=
    Multiset.map_le_map hle
  have hsum_le :
      ((Multiset.replicate ((UniqueFactorizationMonoid.normalizedFactors V).count q) q).map
          Polynomial.natDegree).sum ≤
        ((UniqueFactorizationMonoid.normalizedFactors V).map Polynomial.natDegree).sum := by
    rcases Multiset.le_iff_exists_add.mp hmap_le with ⟨t, ht⟩
    rw [ht, Multiset.sum_add]
    exact Nat.le_add_right _ _
  rw [Multiset.map_replicate, Multiset.sum_replicate, smul_eq_mul, hsum, hdeg_prod] at hsum_le
  calc
    (UniqueFactorizationMonoid.normalizedFactors V).count q
        ≤ (UniqueFactorizationMonoid.normalizedFactors V).count q * q.natDegree :=
          Nat.le_mul_of_pos_right _ hq_deg
    _ ≤ V.natDegree := hsum_le

/-- Divisibility step in `ℤ[X]`: if `V^(2^k - 1) ∣ W₀^(2^k)` with `V(0) = W₀(0) = 1`
and `V.natDegree < 2^k`, then `V ∣ W₀`. -/
lemma dvd_of_pow_dvd_pow_coeff_zero_one {V W₀ : ℤ[X]} {k : ℕ}
    (hV0 : V.coeff 0 = 1) (hW0 : W₀.coeff 0 = 1)
    (hk : V.natDegree < 2 ^ k)
    (hdvd : V ^ (2 ^ k - 1) ∣ W₀ ^ (2 ^ k)) :
    V ∣ W₀ := by
  have hVne : V ≠ 0 := by intro h; rw [h, coeff_zero] at hV0; exact zero_ne_one hV0
  have hWne : W₀ ≠ 0 := by intro h; rw [h, coeff_zero] at hW0; exact zero_ne_one hW0
  have hWpow_ne : W₀ ^ (2 ^ k) ≠ 0 := pow_ne_zero _ hWne
  rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hVne hWne]
  have hfac_dvd :
      UniqueFactorizationMonoid.normalizedFactors (V ^ (2 ^ k - 1)) ≤
        UniqueFactorizationMonoid.normalizedFactors (W₀ ^ (2 ^ k)) :=
    (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
      (pow_ne_zero _ hVne) hWpow_ne).mp hdvd
  rw [UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_pow] at hfac_dvd
  rw [Multiset.le_iff_count] at hfac_dvd ⊢
  intro q
  by_cases hq : q ∈ UniqueFactorizationMonoid.normalizedFactors V
  · have hq_le : (UniqueFactorizationMonoid.normalizedFactors V).count q ≤ V.natDegree :=
      count_normalizedFactors_le_natDegree hV0 hq
    have hc := hfac_dvd q
    simp only [Multiset.count_nsmul] at hc
    set a := (UniqueFactorizationMonoid.normalizedFactors V).count q
    set b := (UniqueFactorizationMonoid.normalizedFactors W₀).count q
    have ha_lt : a < 2 ^ k := lt_of_le_of_lt hq_le hk
    by_contra hab
    push Not at hab
    have h1 : b + 1 ≤ a := hab
    have h2 : 2 ^ k * b + 2 ^ k ≤ 2 ^ k * a := by
      calc
        2 ^ k * b + 2 ^ k = 2 ^ k * (b + 1) := by ring
        _ ≤ 2 ^ k * a := Nat.mul_le_mul_left _ h1
    have h3 : (2 ^ k - 1) * a + a = 2 ^ k * a := by
      have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      calc
        (2 ^ k - 1) * a + a = (2 ^ k - 1 + 1) * a := by ring
        _ = 2 ^ k * a := by rw [Nat.sub_add_cancel hpos]
    omega
  · rw [Multiset.count_eq_zero_of_notMem hq]
    exact Nat.zero_le _

/-- Lowest nonzero coefficient above `0` scales linearly under taking `M`-th powers:
if `R(0) = 1` and `coeff_i(R) = 0` for `0 < i < d`, then
`(R^M)(0) = 1`, `coeff_i(R^M) = 0` for `0 < i < d`, and `coeff_d(R^M) = M * coeff_d(R)`. -/
lemma pow_lowest_coeff (R : ℤ[X]) (d : ℕ) (hd : 1 ≤ d)
    (hR0 : R.coeff 0 = 1) (hzero : ∀ i, 0 < i → i < d → R.coeff i = 0) :
    ∀ M : ℕ,
      (R ^ M).coeff 0 = 1 ∧
      (∀ i, 0 < i → i < d → (R ^ M).coeff i = 0) ∧
      (R ^ M).coeff d = (M : ℤ) * R.coeff d := by
  intro M
  induction M with
  | zero =>
    refine ⟨by simp, fun i hi _ => ?_, ?_⟩
    · simp [Polynomial.coeff_one, Nat.ne_of_gt hi]
    · simp [Polynomial.coeff_one]; omega
  | succ M ih =>
    rcases ih with ⟨hM0, hMzero, hMd⟩
    have hpow : R ^ (M + 1) = R ^ M * R := pow_succ R M
    refine ⟨?_, ?_, ?_⟩
    · rw [hpow, mul_coeff_zero, hM0, hR0, mul_one]
    · intro i hi hilt
      rw [hpow, coeff_mul]
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.mem_antidiagonal] at hp
      by_cases hp1 : p.1 = 0
      · have hp2_pos : 0 < p.2 := by omega
        have hp2_lt : p.2 < d := by omega
        rw [hzero p.2 hp2_pos hp2_lt, mul_zero]
      · have hp1_pos : 0 < p.1 := Nat.pos_of_ne_zero hp1
        have hp1_lt : p.1 < d := by omega
        rw [hMzero p.1 hp1_pos hp1_lt, zero_mul]
    · rw [hpow, coeff_mul]
      have h0mem : (0, d) ∈ Finset.antidiagonal d := Finset.mem_antidiagonal.mpr (zero_add d)
      have hdmem : (d, 0) ∈ Finset.antidiagonal d := Finset.mem_antidiagonal.mpr (add_zero d)
      have hne : (0, d) ≠ (d, 0) := by
        intro heq
        have := congrArg Prod.fst heq
        omega
      have hsum :
          ∑ p ∈ Finset.antidiagonal d, (R ^ M).coeff p.1 * R.coeff p.2 =
            (R ^ M).coeff 0 * R.coeff d + (R ^ M).coeff d * R.coeff 0 := by
        rw [← Finset.sum_subset (s₁ := {(0, d), (d, 0)})]
        · rw [Finset.sum_pair hne]
        · intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl <;> assumption
        · intro p hp hnot
          rw [Finset.mem_antidiagonal] at hp
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
          have hp1_ne0 : p.1 ≠ 0 := by
            intro h; apply hnot.1; ext <;> omega
          have hp2_ne0 : p.2 ≠ 0 := by
            intro h; apply hnot.2; ext <;> omega
          have hp1_pos : 0 < p.1 := Nat.pos_of_ne_zero hp1_ne0
          have hp1_lt : p.1 < d := by omega
          rw [hMzero p.1 hp1_pos hp1_lt, zero_mul]
      rw [hsum, hM0, hMd, hR0]
      push_cast
      ring

/-- **Lemma 6.1 (Polynomial Iteration Rigidity).**
If `V, W₀, ..., W_k ∈ ℤ[X]` satisfy `V(0) = 1`, `W_j(0) = 1`, `|coeff_d(W_j)| ≤ 1`,
`|coeff_d(V)| ≤ E`, `V * W_{j+1} = W_j^2` for `0 ≤ j < k`, and
`2^k > max V.natDegree (E + 1)`, then `W_j = V` for every `j ≤ k`. -/
theorem polynomial_iteration_rigidity (V : ℤ[X]) (W : ℕ → ℤ[X]) (k E : ℕ)
    (hV0 : V.coeff 0 = 1)
    (hVbound : ∀ d, |V.coeff d| ≤ (E : ℤ))
    (hW0 : (W 0).coeff 0 = 1)
    (hWbound : ∀ j ≤ k, ∀ d, |(W j).coeff d| ≤ 1)
    (hrec : ∀ j < k, V * W (j + 1) = (W j) ^ 2)
    (hk_deg : V.natDegree < 2 ^ k)
    (hk_E : E + 1 < 2 ^ k) :
    ∀ j ≤ k, W j = V := by
  have hVne : V ≠ 0 := by intro h; rw [h, coeff_zero] at hV0; exact zero_ne_one hV0
  have hiter := poly_iter_identity V W k hrec
  have hdvd_pow : V ^ (2 ^ k - 1) ∣ (W 0) ^ (2 ^ k) :=
    ⟨W k, (hiter k le_rfl).symm⟩
  have hV_dvd_W0 : V ∣ W 0 := dvd_of_pow_dvd_pow_coeff_zero_one hV0 hW0 hk_deg hdvd_pow
  rcases hV_dvd_W0 with ⟨R, hR⟩
  have hR0 : R.coeff 0 = 1 := by
    have := congrArg (fun p : ℤ[X] => p.coeff 0) hR
    simpa [mul_coeff_zero, hV0, hW0] using this.symm
  have hWj_eq : ∀ j ≤ k, W j = V * R ^ (2 ^ j) := by
    intro j hj
    have h1 := hiter j hj
    rw [hR, mul_pow] at h1
    have hpos : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have h2 : V ^ (2 ^ j) = V ^ (2 ^ j - 1) * V := by
      rw [← pow_succ, Nat.sub_add_cancel hpos]
    rw [h2, mul_assoc] at h1
    exact mul_left_cancel₀ (pow_ne_zero _ hVne) h1
  have hR_eq_one : R = 1 := by
    by_contra hRne1
    -- There exists a smallest d ≥ 1 with R.coeff d ≠ 0
    have hex : ∃ d : ℕ, 1 ≤ d ∧ R.coeff d ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hRne1
      ext n
      cases n with
      | zero => simp [hR0]
      | succ m =>
        have := hall (m + 1) (Nat.succ_pos m)
        simp [Polynomial.coeff_one, this]
    let d := Nat.find hex
    have hd_spec : 1 ≤ d ∧ R.coeff d ≠ 0 := Nat.find_spec hex
    have hd_pos : 1 ≤ d := hd_spec.1
    have hRd_ne : R.coeff d ≠ 0 := hd_spec.2
    have hzero : ∀ i, 0 < i → i < d → R.coeff i = 0 := by
      intro i hi hilt
      by_contra hne
      exact Nat.find_min hex hilt ⟨hi, hne⟩
    set M := 2 ^ k
    have hRM := pow_lowest_coeff R d hd_pos hR0 hzero M
    rcases hRM with ⟨hRM0, hRMzero, hRMd⟩
    have hWk : W k = V * R ^ M := hWj_eq k le_rfl
    have hcoeff_d : (W k).coeff d = (M : ℤ) * R.coeff d + V.coeff d := by
      rw [hWk, coeff_mul]
      have h0mem : (0, d) ∈ Finset.antidiagonal d := Finset.mem_antidiagonal.mpr (zero_add d)
      have hdmem : (d, 0) ∈ Finset.antidiagonal d := Finset.mem_antidiagonal.mpr (add_zero d)
      have hne : (0, d) ≠ (d, 0) := by
        intro heq; have := congrArg Prod.fst heq; omega
      have hsum :
          ∑ p ∈ Finset.antidiagonal d, V.coeff p.1 * (R ^ M).coeff p.2 =
            V.coeff 0 * (R ^ M).coeff d + V.coeff d * (R ^ M).coeff 0 := by
        rw [← Finset.sum_subset (s₁ := {(0, d), (d, 0)})]
        · rw [Finset.sum_pair hne]
        · intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl <;> assumption
        · intro p hp hnot
          rw [Finset.mem_antidiagonal] at hp
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
          have hp1_ne0 : p.1 ≠ 0 := by intro h; apply hnot.1; ext <;> omega
          have hp2_ne0 : p.2 ≠ 0 := by intro h; apply hnot.2; ext <;> omega
          have hp2_pos : 0 < p.2 := Nat.pos_of_ne_zero hp2_ne0
          have hp2_lt : p.2 < d := by omega
          rw [hRMzero p.2 hp2_pos hp2_lt, mul_zero]
      rw [hsum, hV0, hRMd, hRM0, one_mul, mul_one]
    have habs_Rd : 1 ≤ |R.coeff d| := Int.one_le_abs hRd_ne
    have habs_M : (M : ℤ) ≤ |(M : ℤ) * R.coeff d| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg M)]
      calc
        (M : ℤ) = (M : ℤ) * 1 := (mul_one _).symm
        _ ≤ (M : ℤ) * |R.coeff d| := mul_le_mul_of_nonneg_left habs_Rd (Nat.cast_nonneg M)
    have hV_d := hVbound d
    have hW_d := hWbound k le_rfl d
    have htri : |(M : ℤ) * R.coeff d| - |V.coeff d| ≤ |(M : ℤ) * R.coeff d + V.coeff d| := by
      have := abs_add_le ((M : ℤ) * R.coeff d + V.coeff d) (-V.coeff d)
      simp only [add_neg_cancel_right, abs_neg] at this
      linarith
    rw [← hcoeff_d] at htri
    have hM_gt : (E : ℤ) + 1 < (M : ℤ) := by exact_mod_cast hk_E
    linarith
  intro j hj
  rw [hWj_eq j hj, hR_eq_one, one_pow, mul_one]

end AlmostPerfect
