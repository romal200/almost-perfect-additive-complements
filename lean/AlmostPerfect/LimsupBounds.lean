import AlmostPerfect.ModularLift
import AlmostPerfect.PolynomialInvariants
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

/-!
# Limsup Bounds: Upper Bound `≤ 2` and Exact Modular-Lift Value `3 / 2`

Proves:
1. `almostPerfect_limsup_le_two`: for every pair of infinite almost perfect additive complements,
   `Filter.limsup (ratioEReal A B) Filter.atTop ≤ 2`.
2. `ABin_count_prod_le`: for all `m : ℕ`,
   `2 * (countNat ABin m * countNat {n | ∃ k ∈ ABin, n = 2 * k} m) ≤ 3 * m + 2`.
3. `modularLift_limsup_eq_three_halves`: every `IsModularLift A B` satisfies
   `Filter.limsup (ratioEReal A B) Filter.atTop = 3 / 2`.
-/

namespace AlmostPerfect

open Filter BigOperators

noncomputable section

/-- The doubled binary Cantor set `2 · ABin`. -/
def twoABin : Set ℕ := {n : ℕ | ∃ m ∈ ABin, n = 2 * m}

lemma countNat_twoABin_eq (x : ℕ) : countNat twoABin x = countNat ABin (x / 2) := by
  classical
  unfold countNat twoABin
  apply Finset.card_bij (fun n _ => n / 2)
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_ofPred_eq] at hn ⊢
    rcases hn.2 with ⟨m, hm, rfl⟩
    refine ⟨by omega, ?_⟩
    have hdiv : 2 * m / 2 = m := by omega
    rw [hdiv]; exact hm
  · intro n₁ hn₁ n₂ hn₂ heq
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_ofPred_eq] at hn₁ hn₂
    rcases hn₁.2 with ⟨m₁, _, rfl⟩
    rcases hn₂.2 with ⟨m₂, _, rfl⟩
    omega
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    refine ⟨2 * m, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_ofPred_eq]
    exact ⟨by omega, m, hm.2, rfl⟩

/-- `countNat ABin x` equals the number of `k` with `binElem k ≤ x`. -/
lemma countNat_ABin_eq_card_binElem (x : ℕ) :
    countNat ABin x = ((Finset.range (x + 1)).filter (fun k => binElem k ≤ x)).card := by
  classical
  unfold countNat
  apply Finset.card_bij (fun n _ => binIndex n)
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    have hbin : binElem (binIndex n) = n := binElem_binIndex hn.2
    have hle : binIndex n ≤ n := by
      have h1 : ∀ k, k ≤ binElem k := by
        intro k
        have hsq := sq_add_two_mul_le_three_mul_binElem k
        nlinarith
      calc binIndex n ≤ binElem (binIndex n) := h1 (binIndex n)
        _ = n := hbin
    exact ⟨by omega, by omega⟩
  · intro n₁ hn₁ n₂ hn₂ heq
    simp only [Finset.mem_filter, Finset.mem_range] at hn₁ hn₂
    have h1 := binElem_binIndex hn₁.2
    have h2 := binElem_binIndex hn₂.2
    rw [← h1, ← h2, heq]
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    refine ⟨binElem k, ?_, binIndex_binElem k⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, binElem_mem_ABin k⟩

/-- If `countNat ABin x = k` with `k ≥ 1`, then `binElem (k - 1) ≤ x`. -/
lemma binElem_pred_countNat_le (x : ℕ) :
    binElem (countNat ABin x - 1) ≤ x := by
  have hpos : 1 ≤ countNat ABin x := by
    classical
    unfold countNat
    apply Finset.card_pos.mpr
    refine ⟨0, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.succ_pos x, by intro i; simp⟩
  set k := countNat ABin x
  by_contra hgt
  push Not at hgt
  -- Then every m with binElem m ≤ x satisfies m < k - 1
  have hsub : (Finset.range (x + 1)).filter (fun m => binElem m ≤ x) ⊆ Finset.range (k - 1) := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
    by_contra hge
    push Not at hge
    have := binElem_strictMono.monotone hge
    omega
  have hcard_le : k ≤ k - 1 := by
    calc k = ((Finset.range (x + 1)).filter (fun m => binElem m ≤ x)).card :=
            countNat_ABin_eq_card_binElem x
      _ ≤ (Finset.range (k - 1)).card := Finset.card_le_card hsub
      _ = k - 1 := Finset.card_range (k - 1)
  omega

/-- Immediate quadratic bound: `(countNat ABin x)^2 ≤ 3 * x + 1` for every `x : ℕ`. -/
lemma sq_countNat_ABin_le (x : ℕ) : (countNat ABin x) ^ 2 ≤ 3 * x + 1 := by
  have hpos : 1 ≤ countNat ABin x := by
    classical
    unfold countNat
    apply Finset.card_pos.mpr
    refine ⟨0, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.succ_pos x, by intro i; simp⟩
  have h1 := sq_add_two_mul_le_three_mul_binElem (countNat ABin x - 1)
  have h2 := binElem_pred_countNat_le x
  set k := countNat ABin x
  have hsq : k ^ 2 = (k - 1) ^ 2 + 2 * (k - 1) + 1 := by
    have : k = (k - 1) + 1 := (Nat.sub_add_cancel hpos).symm
    conv_lhs => rw [this]
    ring
  omega

/-- Exact count of `ABin` below `4^t`: `countNat ABin (4^t - 1) = 2^t`. -/
lemma countNat_ABin_pow_four_sub_one (t : ℕ) :
    countNat ABin (4 ^ t - 1) = 2 ^ t := by
  rw [countNat_ABin_eq_card_binElem]
  have hfilt : (Finset.range (4 ^ t - 1 + 1)).filter (fun k => binElem k ≤ 4 ^ t - 1) =
      Finset.range (2 ^ t) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    have h4pos : 1 ≤ 4 ^ t := Nat.one_le_pow t 4 (by decide)
    constructor
    · intro ⟨_, hle⟩
      by_contra hge
      push Not at hge
      have hmono := binElem_strictMono.monotone hge
      rw [binElem_pow_two] at hmono
      omega
    · intro hlt
      have hmono : binElem k < binElem (2 ^ t) := binElem_strictMono hlt
      rw [binElem_pow_two] at hmono
      have hk_le : k ≤ binElem k := by
        have := sq_add_two_mul_le_three_mul_binElem k
        nlinarith
      exact ⟨by omega, by omega⟩
  rw [hfilt, Finset.card_range]

/-- Self-similarity of `ABin` on `[4^t, 2*4^t - 1]`:
for `x < 4^t`, `countNat ABin (4^t + x) = 2^t + countNat ABin x`. -/
lemma countNat_ABin_add_pow_four {t x : ℕ} (hx : x < 4 ^ t) :
    countNat ABin (4 ^ t + x) = 2 ^ t + countNat ABin x := by
  classical
  have h4pos : 1 ≤ 4 ^ t := Nat.one_le_pow t 4 (by decide)
  rw [← countNat_ABin_pow_four_sub_one t]
  unfold countNat
  have hdisj : Disjoint
      ((Finset.range (4 ^ t - 1 + 1)).filter (· ∈ ABin))
      ((Finset.Ico (4 ^ t) (4 ^ t + x + 1)).filter (· ∈ ABin)) := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at ha1 ha2
    omega
  have hunion :
      (Finset.range (4 ^ t + x + 1)).filter (· ∈ ABin) =
      (Finset.range (4 ^ t - 1 + 1)).filter (· ∈ ABin) ∪
      (Finset.Ico (4 ^ t) (4 ^ t + x + 1)).filter (· ∈ ABin) := by
    ext a
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨ha1, ha2⟩
      by_cases hlt : a < 4 ^ t
      · exact Or.inl ⟨by omega, ha2⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, ha2⟩
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩) <;> exact ⟨by omega, by assumption⟩
  rw [hunion, Finset.card_union_of_disjoint hdisj]
  congr 1
  apply Finset.card_bij (fun a _ => a - 4 ^ t)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at ha ⊢
    refine ⟨by omega, ?_⟩
    intro i
    by_cases hit : i < t
    · have hdiv_eq : (a - 4 ^ t) / 4 ^ i + 4 ^ (t - i) = a / 4 ^ i := by
        have hpow : 4 ^ t = 4 ^ (t - i) * 4 ^ i := by rw [← pow_add, Nat.sub_add_cancel (le_of_lt hit)]
        have hpos_i : 0 < 4 ^ i := Nat.pow_pos (by decide)
        rw [← Nat.add_mul_div_right _ _ hpos_i, ← hpow, Nat.sub_add_cancel ha.1.1]
      have h4dvd : 4 ∣ 4 ^ (t - i) := dvd_pow_self 4 (by omega)
      have hmod : (a - 4 ^ t) / 4 ^ i % 4 = a / 4 ^ i % 4 := by
        rw [← hdiv_eq]
        rcases h4dvd with ⟨q, hq⟩
        rw [hq]
        omega
      rw [hmod]
      exact ha.2 i
    · have hlt_i : a - 4 ^ t < 4 ^ i := by
        have hpow : 4 ^ t ≤ 4 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      rw [Nat.div_eq_of_lt hlt_i]
      simp
  · intro a₁ ha₁ a₂ ha₂ heq
    simp only [Finset.mem_filter, Finset.mem_Ico] at ha₁ ha₂
    omega
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_range] at hb
    refine ⟨4 ^ t + b, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro i
    by_cases hit : i < t
    · have hpow : 4 ^ t = 4 ^ (t - i) * 4 ^ i := by rw [← pow_add, Nat.sub_add_cancel (le_of_lt hit)]
      have hpos_i : 0 < 4 ^ i := Nat.pow_pos (by decide)
      have hdiv : (4 ^ t + b) / 4 ^ i = 4 ^ (t - i) + b / 4 ^ i := by
        rw [hpow, mul_comm (4 ^ (t - i)) (4 ^ i), Nat.mul_add_div hpos_i]
      have h4dvd : 4 ∣ 4 ^ (t - i) := dvd_pow_self 4 (by omega)
      rw [hdiv]
      rcases h4dvd with ⟨q, hq⟩
      rw [hq]
      have : (4 * q + b / 4 ^ i) % 4 = b / 4 ^ i % 4 := by omega
      rw [this]
      exact hb.2 i
    · by_cases heqi : i = t
      · subst i
        have hdiv : (4 ^ t + b) / 4 ^ t = 1 := by
          have hb_lt : b < 4 ^ t := by omega
          rw [Nat.add_div_of_dvd_right (dvd_refl _), Nat.div_self h4pos, Nat.div_eq_of_lt hb_lt, add_zero]
        rw [hdiv]
      · have hgt_i : t + 1 ≤ i := by omega
        have hpow : 4 ^ (t + 1) ≤ 4 ^ i := Nat.pow_le_pow_right (by decide) hgt_i
        have hlt_i : 4 ^ t + b < 4 ^ i := by
          have : 4 ^ (t + 1) = 4 * 4 ^ t := by rw [pow_succ']
          omega
        rw [Nat.div_eq_of_lt hlt_i]; simp

/-- No element of `ABin` lies in `[2 * 4^t, 4^(t+1) - 1]`. -/
lemma ABin_not_mem_gap {t a : ℕ} (ha1 : 2 * 4 ^ t ≤ a) (ha2 : a < 4 ^ (t + 1)) :
    a ∉ ABin := by
  intro hmem
  have hdig := hmem t
  have h4pos : 0 < 4 ^ t := Nat.pow_pos (by decide)
  have hpow : 4 ^ (t + 1) = 4 * 4 ^ t := by rw [pow_succ']
  have hq1 : 2 ≤ a / 4 ^ t := (Nat.le_div_iff_mul_le h4pos).mpr ha1
  have hq2 : a / 4 ^ t < 4 := (Nat.div_lt_iff_lt_mul h4pos).mpr (by omega)
  omega

/-- **Exact Sharp Counting Bound for `(ABin, 2 · ABin)`:**
For every `x : ℕ`, `2 * (countNat ABin x * countNat twoABin x) ≤ 3 * x + 2`. -/
theorem ABin_count_prod_le (x : ℕ) :
    2 * (countNat ABin x * countNat twoABin x) ≤ 3 * x + 2 := by
  by_cases hx0 : x = 0
  · subst hx0
    have h1 : countNat ABin 0 = 1 := by
      simpa using countNat_ABin_pow_four_sub_one 0
    rw [countNat_twoABin_eq, Nat.zero_div, h1]
  · -- Pick unique t with 4^t ≤ x < 4^(t+1)
    have hex : ∃ t : ℕ, x < 4 ^ (t + 1) := by
      refine ⟨x, ?_⟩
      have h1 : x < 4 ^ x := Nat.lt_pow_self (by decide : 1 < 4)
      have h2 : 4 ^ x < 4 ^ (x + 1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self x)
      exact lt_trans h1 h2
    let t := Nat.find hex
    have hlt : x < 4 ^ (t + 1) := Nat.find_spec hex
    have hge : 4 ^ t ≤ x := by
      cases ht : t with
      | zero => omega
      | succ s =>
        have hnot := Nat.find_min hex (show s < t by omega)
        push Not at hnot
        exact hnot
    have h4pos : 1 ≤ 4 ^ t := Nat.one_le_pow t 4 (by decide)
    have hsq2 : (2 ^ t) ^ 2 = 4 ^ t := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    by_cases hmid : x < 2 * 4 ^ t
    · -- Case 1: 4^t ≤ x < 2 * 4^t.
      -- Then x / 2 < 4^t so countNat twoABin x = countNat ABin (x/2) ≤ 2^t,
      -- and countNat ABin x = 2^t + countNat ABin (x - 4^t).
      have hv_le : countNat twoABin x ≤ 2 ^ t := by
        rw [countNat_twoABin_eq, ← countNat_ABin_pow_four_sub_one t]
        classical
        unfold countNat
        apply Finset.card_le_card
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
        exact ⟨by omega, ha.2⟩
      set y := x - 4 ^ t
      have hy : y < 4 ^ t := by omega
      have hu : countNat ABin x = 2 ^ t + countNat ABin y := by
        have hx_eq : x = 4 ^ t + y := by omega
        conv_lhs => rw [hx_eq]
        exact countNat_ABin_add_pow_four hy
      set k := countNat ABin y
      have hk2 : k ^ 2 ≤ 3 * y + 1 := sq_countNat_ABin_le y
      -- AM-GM in ℕ: 2 * k * 2^t ≤ (2^t)^2 + k^2 = 4^t + k^2
      have hamgm : 2 * (k * 2 ^ t) ≤ 4 ^ t + k ^ 2 := by
        have hsq_nn : 0 ≤ ((2 ^ t : ℤ) - (k : ℤ)) ^ 2 := sq_nonneg _
        have : (2 : ℤ) * ((k : ℤ) * (2 ^ t : ℤ)) ≤ (2 ^ t : ℤ) ^ 2 + (k : ℤ) ^ 2 := by nlinarith
        have hcast : ((2 ^ t : ℤ) ^ 2) = (4 ^ t : ℤ) := by exact_mod_cast hsq2
        rw [hcast] at this
        exact_mod_cast this
      calc
        2 * (countNat ABin x * countNat twoABin x)
            ≤ 2 * ((2 ^ t + k) * 2 ^ t) := by
              rw [hu]
              exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hv_le)
        _ = 2 * (2 ^ t) ^ 2 + 2 * (k * 2 ^ t) := by ring
        _ ≤ 2 * 4 ^ t + (4 ^ t + k ^ 2) := by rw [hsq2]; omega
        _ ≤ 3 * 4 ^ t + (3 * y + 1) := by omega
        _ ≤ 3 * x + 2 := by omega
    · -- Case 2: 2 * 4^t ≤ x < 4^(t+1).
      -- Then ABin has no elements in [2 * 4^t, x], so countNat ABin x = 2^(t+1),
      -- and x / 2 = 4^t + y with y = x/2 - 4^t < 4^t, so countNat twoABin x = 2^t + countNat ABin y.
      have hge2 : 2 * 4 ^ t ≤ x := by omega
      have hu : countNat ABin x = 2 ^ (t + 1) := by
        have hcount_eq : countNat ABin x = countNat ABin (2 * 4 ^ t - 1) := by
          classical
          unfold countNat
          congr 1
          ext a
          simp only [Finset.mem_filter, Finset.mem_range]
          constructor
          · rintro ⟨ha1, ha2⟩
            refine ⟨?_, ha2⟩
            by_contra hge_a
            push Not at hge_a
            exact ABin_not_mem_gap (t := t) (by omega) (by omega) ha2
          · rintro ⟨ha1, ha2⟩
            exact ⟨by omega, ha2⟩
        rw [hcount_eq]
        have hrew : 2 * 4 ^ t - 1 = 4 ^ t + (4 ^ t - 1) := by omega
        rw [hrew, countNat_ABin_add_pow_four (by omega : 4 ^ t - 1 < 4 ^ t),
            countNat_ABin_pow_four_sub_one t]
        ring
      set y := x / 2 - 4 ^ t
      have hy : y < 4 ^ t := by
        have : 4 ^ (t + 1) = 4 * 4 ^ t := by rw [pow_succ']
        omega
      have hv : countNat twoABin x = 2 ^ t + countNat ABin y := by
        rw [countNat_twoABin_eq]
        have hdiv_eq : x / 2 = 4 ^ t + y := by omega
        rw [hdiv_eq]
        exact countNat_ABin_add_pow_four hy
      set k := countNat ABin y
      have hk2 : k ^ 2 ≤ 3 * y + 1 := sq_countNat_ABin_le y
      have hamgm : 2 * (k * 2 ^ t) ≤ 4 ^ t + k ^ 2 := by
        have hsq_nn : 0 ≤ ((2 ^ t : ℤ) - (k : ℤ)) ^ 2 := sq_nonneg _
        have : (2 : ℤ) * ((k : ℤ) * (2 ^ t : ℤ)) ≤ (2 ^ t : ℤ) ^ 2 + (k : ℤ) ^ 2 := by nlinarith
        have hcast : ((2 ^ t : ℤ) ^ 2) = (4 ^ t : ℤ) := by exact_mod_cast hsq2
        rw [hcast] at this
        exact_mod_cast this
      calc
        2 * (countNat ABin x * countNat twoABin x)
            = 2 * (2 ^ (t + 1) * (2 ^ t + k)) := by rw [hu, hv]
        _ = 4 * (2 ^ t) ^ 2 + 2 * (2 * (k * 2 ^ t)) := by rw [pow_succ']; ring
        _ ≤ 4 * 4 ^ t + 2 * (4 ^ t + k ^ 2) := by rw [hsq2]; omega
        _ ≤ 6 * 4 ^ t + 2 * (3 * y + 1) := by omega
        _ ≤ 3 * x + 2 := by omega

/-- **Unconditional Upper Bound (`limsup ≤ 2`):**
For every pair of infinite almost perfect additive complements `A, B`,
`Filter.limsup (ratioEReal A B) Filter.atTop ≤ 2`. -/
theorem almostPerfect_limsup_le_two {A B : Set ℕ} (hAP : IsAlmostPerfect A B) :
    Filter.limsup (ratioEReal A B) Filter.atTop ≤ (2 : EReal) := by
  rcases exists_repCount_eq_one_eventually hAP with ⟨n₀, hn₀, hstab⟩
  set S₀ := ∑ m ∈ Finset.range n₀, repCount A B m
  -- For every N ≥ n₀, A(N) * B(N) ≤ 2 * N + 1 + S₀
  have hprod_le : ∀ N ≥ n₀, countNat A N * countNat B N ≤ 2 * N + 1 + S₀ := by
    intro N hN
    have hprod := countNat_mul_eq_sum_repCount_add_crossExcess A B N
    have hT_le : crossExcess A B N ≤ N := by
      unfold crossExcess
      calc
        ∑ m ∈ Finset.range N, repTrunc A B N (N + 1 + m)
            ≤ ∑ _m ∈ Finset.range N, 1 := by
              apply Finset.sum_le_sum
              intro m _
              calc
                repTrunc A B N (N + 1 + m) ≤ repCount A B (N + 1 + m) := repTrunc_le_repCount _ _ _ _
                _ = 1 := hstab _ (by omega)
        _ = N := by simp
    have hsum_le : ∑ m ∈ Finset.range (N + 1), repCount A B m ≤ S₀ + (N + 1) := by
      have hsplit : N + 1 = n₀ + (N + 1 - n₀) := by omega
      rw [hsplit, Finset.sum_range_add]
      have htail : ∑ m ∈ Finset.range (N + 1 - n₀), repCount A B (n₀ + m) = N + 1 - n₀ := by
        calc
          ∑ m ∈ Finset.range (N + 1 - n₀), repCount A B (n₀ + m)
              = ∑ _m ∈ Finset.range (N + 1 - n₀), 1 := by
                apply Finset.sum_congr rfl; intro m _; exact hstab _ (by omega)
          _ = N + 1 - n₀ := by simp
      rw [htail]
      omega
    omega
  -- Show limsup ≤ 2 via real upper bounds c > 2
  have hreal_bound : ∀ c : ℝ, (2 : ℝ) < c → Filter.limsup (ratioEReal A B) Filter.atTop ≤ (c : EReal) := by
    intro c hc
    apply Filter.limsup_le_of_le
    · exact isCoboundedUnder_le_of_le _ (fun _ => bot_le)
    · rw [Filter.eventually_atTop]
      refine ⟨max ((n₀ : ℝ) + 1) (((S₀ : ℝ) + 2) / (c - 2) + 1), fun x hx => ?_⟩
      have hx_pos : (0 : ℝ) < x := by linarith [le_max_left ((n₀ : ℝ) + 1) (((S₀ : ℝ) + 2) / (c - 2) + 1)]
      have hx_n0 : (n₀ : ℝ) + 1 ≤ x := le_trans (le_max_left _ _) hx
      have hx_c : ((S₀ : ℝ) + 2) / (c - 2) + 1 ≤ x := le_trans (le_max_right _ _) hx
      set N := ⌊x⌋₊
      have hN_ge : n₀ ≤ N := Nat.le_floor (by linarith)
      have hN_le : (N : ℝ) ≤ x := Nat.floor_le (le_of_lt hx_pos)
      have hcrA : countReal A x = countNat A N := by
        unfold countReal; exact ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (le_of_lt hx_pos)))
      have hcrB : countReal B x = countNat B N := by
        unfold countReal; exact ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (le_of_lt hx_pos)))
      unfold ratioEReal
      rw [hcrA, hcrB]
      rw [EReal.coe_le_coe_iff, div_le_iff₀ hx_pos]
      have hnat := hprod_le N hN_ge
      have hcast : (countNat A N : ℝ) * (countNat B N : ℝ) ≤ 2 * (N : ℝ) + 1 + (S₀ : ℝ) := by
        exact_mod_cast hnat
      have hc2 : (0 : ℝ) < c - 2 := by linarith
      have hx_mul : (S₀ : ℝ) + 2 < (c - 2) * x := by
        have h1 : ((S₀ : ℝ) + 2) / (c - 2) < x := by linarith
        linarith [(div_lt_iff₀ hc2).mp h1]
      linarith
  by_contra hgt
  push Not at hgt
  rcases EReal.exists_between_coe_real hgt with ⟨c, hc1, hc2⟩
  have h2lt : (2 : ℝ) < c := by
    have hcoe : ((2 : ℝ) : EReal) = (2 : EReal) := rfl
    rw [← hcoe] at hc1
    exact EReal.coe_lt_coe_iff.mp hc1
  exact not_lt_of_ge (hreal_bound c h2lt) hc2

/-- Counting function of a modular lift `{a₀ + D₀ * m | a₀ ∈ A₀, m ∈ S}` lies within `|A₀|` of
`|A₀| * countNat S (N / D₀)`. -/
lemma countNat_modularLift_bounds {D₀ : ℕ} (hD₀ : 1 ≤ D₀) {A₀ : Finset ℕ}
    (hA₀ : ∀ a ∈ A₀, a < D₀) (S : Set ℕ) (N : ℕ) :
    A₀.card * countNat S (N / D₀) ≤ countNat {n | ∃ a₀ ∈ A₀, ∃ m ∈ S, n = a₀ + D₀ * m} N + A₀.card ∧
    countNat {n | ∃ a₀ ∈ A₀, ∃ m ∈ S, n = a₀ + D₀ * m} N ≤ A₀.card * countNat S (N / D₀) := by
  classical
  set L : Set ℕ := {n | ∃ a₀ ∈ A₀, ∃ m ∈ S, n = a₀ + D₀ * m}
  have hinj : ∀ a₁ ∈ A₀, ∀ a₂ ∈ A₀, ∀ m₁ m₂ : ℕ, a₁ + D₀ * m₁ = a₂ + D₀ * m₂ → a₁ = a₂ ∧ m₁ = m₂ := by
    intro a₁ ha₁ a₂ ha₂ m₁ m₂ heq
    have h1 := hA₀ a₁ ha₁
    have h2 := hA₀ a₂ ha₂
    have hmod : a₁ = a₂ := by
      have hm1 : (a₁ + D₀ * m₁) % D₀ = a₁ := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
      have hm2 : (a₂ + D₀ * m₂) % D₀ = a₂ := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
      rw [← hm1, ← hm2, heq]
    have hm : m₁ = m₂ := Nat.eq_of_mul_eq_mul_left hD₀ (by omega)
    exact ⟨hmod, hm⟩
  constructor
  · -- Lower bound: every (a₀, m) ∈ A₀ × (S ∩ [0, N/D₀ - 1]) lands in L ∩ [0, N]
    by_cases hq0 : N / D₀ = 0
    · have hle1 : countNat S 0 ≤ 1 := by
        unfold countNat
        calc ((Finset.range 1).filter (· ∈ S)).card ≤ (Finset.range 1).card := Finset.card_filter_le _ _
          _ = 1 := Finset.card_range 1
      rw [hq0]
      nlinarith
    · have hq_pos : 1 ≤ N / D₀ := Nat.pos_of_ne_zero hq0
      have hsub : A₀.card * countNat S (N / D₀ - 1) ≤ countNat L N := by
        unfold countNat
        rw [← Finset.card_product]
        apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1 + D₀ * p.2)
        · intro p hp
          simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hp ⊢
          have ha_lt := hA₀ p.1 hp.1
          have hmul : D₀ * p.2 + D₀ ≤ N := by
            have h1 : p.2 + 1 ≤ N / D₀ := by omega
            have h2 := Nat.mul_le_mul_left D₀ h1
            have h3 := Nat.mul_div_le N D₀
            linarith
          refine ⟨by omega, p.1, hp.1, p.2, hp.2.2, rfl⟩
        · rintro ⟨a₁, m₁⟩ h1 ⟨a₂, m₂⟩ h2 heq
          simp only [Finset.mem_coe, Finset.mem_product] at h1 h2
          rcases hinj a₁ h1.1 a₂ h2.1 m₁ m₂ heq with ⟨rfl, rfl⟩
          rfl
      have hstep : countNat S (N / D₀) ≤ countNat S (N / D₀ - 1) + 1 := by
        unfold countNat
        have hrew : N / D₀ + 1 = (N / D₀ - 1 + 1) + 1 := by omega
        rw [hrew, Finset.range_add_one, Finset.filter_insert]
        split_ifs
        · rw [Finset.card_insert_of_notMem]
          simp [Finset.mem_filter, Finset.mem_range]
        · omega
      nlinarith
  · -- Upper bound: every n ∈ L ∩ [0, N] maps injectively into A₀ × (S ∩ [0, N/D₀])
    unfold countNat
    rw [← Finset.card_product]
    apply Finset.card_le_card_of_injOn (fun n => (n % D₀, n / D₀))
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Finset.mem_product] at hn ⊢
      rcases hn.2 with ⟨a₀, ha₀, m, hm, rfl⟩
      have hlt := hA₀ a₀ ha₀
      have hmod : (a₀ + D₀ * m) % D₀ = a₀ := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
      have hdiv : (a₀ + D₀ * m) / D₀ = m := by
        rw [mul_comm, Nat.add_mul_div_right _ _ hD₀, Nat.div_eq_of_lt hlt, zero_add]
      rw [hmod, hdiv]
      refine ⟨ha₀, ?_, hm⟩
      have hle : D₀ * m ≤ N := by omega
      have : m ≤ N / D₀ := (Nat.le_div_iff_mul_le hD₀).mpr (by rw [mul_comm]; exact hle)
      omega
    · intro n₁ _ n₂ _ heq
      have h1 : n₁ % D₀ = n₂ % D₀ := congrArg Prod.fst heq
      have h2 : n₁ / D₀ = n₂ / D₀ := congrArg Prod.snd heq
      have hd1 := Nat.div_add_mod n₁ D₀
      have hd2 := Nat.div_add_mod n₂ D₀
      rw [h1, h2] at hd1
      linarith

/-- Exact lower witness at `m_t = 4^t + (4^t - 1) / 3`: `ABin` has `2^(t+1)` elements
and `twoABin` has `2^t` elements below `m_t`. -/
lemma ABin_peak_counts (t : ℕ) :
    countNat ABin (4 ^ t + (4 ^ t - 1) / 3) = 2 ^ (t + 1) ∧
    countNat twoABin (4 ^ t + (4 ^ t - 1) / 3) = 2 ^ t := by
  have hdvd : 3 ∣ 4 ^ t - 1 := by
    induction t with
    | zero => simp
    | succ s ih =>
      rcases ih with ⟨q, hq⟩
      have h4pos : 1 ≤ 4 ^ s := Nat.one_le_pow s 4 (by decide)
      refine ⟨4 * q + 1, ?_⟩
      rw [pow_succ']
      omega
  have hmax_ABin : ∀ k < 2 ^ t, binElem k ≤ (4 ^ t - 1) / 3 := by
    intro k hk
    -- Every element of ABin < 4^t has base-4 digits in {0, 1}, so ≤ ∑_{i<t} 4^i = (4^t - 1)/3
    have hlt_all : ∀ s, ∀ j < 2 ^ s, 3 * binElem j ≤ 4 ^ s - 1 := by
      intro s
      induction s with
      | zero =>
        intro j hj
        have hj0 : j = 0 := by omega
        subst hj0
        simp [binElem_zero]
      | succ s ih =>
        intro j hj
        have hdiv : j / 2 < 2 ^ s := by rw [pow_succ'] at hj; omega
        have ih' := ih (j / 2) hdiv
        rw [binElem_eq, pow_succ']
        have h4pos : 1 ≤ 4 ^ s := Nat.one_le_pow s 4 (by decide)
        omega
    have h3 := hlt_all t k hk
    rcases hdvd with ⟨q, hq⟩
    omega
  have h4pos : 1 ≤ 4 ^ t := Nat.one_le_pow t 4 (by decide)
  have hq_lt : (4 ^ t - 1) / 3 < 4 ^ t := by omega
  have hcnt1 : countNat ABin ((4 ^ t - 1) / 3) = 2 ^ t := by
    apply le_antisymm
    · rw [← countNat_ABin_pow_four_sub_one t]
      classical
      unfold countNat
      apply Finset.card_le_card
      intro a ha; simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢; exact ⟨by omega, ha.2⟩
    · rw [countNat_ABin_eq_card_binElem]
      have hsub : Finset.range (2 ^ t) ⊆
          (Finset.range ((4 ^ t - 1) / 3 + 1)).filter (fun k => binElem k ≤ (4 ^ t - 1) / 3) := by
        intro k hk
        simp only [Finset.mem_range, Finset.mem_filter] at hk ⊢
        have hb := hmax_ABin k hk
        have hk_le : k ≤ binElem k := by have := sq_add_two_mul_le_three_mul_binElem k; nlinarith
        exact ⟨by omega, hb⟩
      calc 2 ^ t = (Finset.range (2 ^ t)).card := (Finset.card_range _).symm
        _ ≤ _ := Finset.card_le_card hsub
  constructor
  · rw [countNat_ABin_add_pow_four hq_lt, hcnt1]; ring
  · rw [countNat_twoABin_eq]
    have hhalf_ge : (4 ^ t - 1) / 3 ≤ (4 ^ t + (4 ^ t - 1) / 3) / 2 := by
      rcases hdvd with ⟨q, hq⟩
      omega
    have hhalf_lt : (4 ^ t + (4 ^ t - 1) / 3) / 2 < 4 ^ t := by omega
    apply le_antisymm
    · rw [← countNat_ABin_pow_four_sub_one t]
      classical
      unfold countNat
      apply Finset.card_le_card
      intro a ha; simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢; exact ⟨by omega, ha.2⟩
    · rw [← hcnt1]
      classical
      unfold countNat
      apply Finset.card_le_card
      intro a ha; simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢; exact ⟨by omega, ha.2⟩

/-- **Corollary 1 (Modular-lift direction):**
Every modular lift `IsModularLift A B` satisfies
`Filter.limsup (ratioEReal A B) Filter.atTop = 3 / 2`. -/
theorem modularLift_limsup_eq_three_halves {A B : Set ℕ} (h : IsModularLift A B) :
    Filter.limsup (ratioEReal A B) Filter.atTop = (3 / 2 : EReal) := by
  have haux : ∀ (D₀ : ℕ) (A₀ B₀ : Finset ℕ),
      1 ≤ D₀ →
      (∀ a ∈ A₀, a < D₀) →
      (∀ b ∈ B₀, b < D₀) →
      (∀ r < D₀, ∃! p : ℕ × ℕ, p.1 ∈ A₀ ∧ p.2 ∈ B₀ ∧ (p.1 + p.2) % D₀ = r) →
      Filter.limsup (ratioEReal
        {n | ∃ a₀ ∈ A₀, ∃ m ∈ ABin, n = a₀ + D₀ * m}
        {n | ∃ b₀ ∈ B₀, ∃ m ∈ ABin, n = b₀ + D₀ * (2 * m)}) Filter.atTop = (3 / 2 : EReal) := by
    intro D₀ A₀ B₀ hD₀ hA₀ hB₀ hbij
    set LA : Set ℕ := {n | ∃ a₀ ∈ A₀, ∃ m ∈ ABin, n = a₀ + D₀ * m}
    set LB : Set ℕ := {n | ∃ b₀ ∈ B₀, ∃ m ∈ ABin, n = b₀ + D₀ * (2 * m)}
    have hLB_eq : LB = {n | ∃ b₀ ∈ B₀, ∃ m ∈ twoABin, n = b₀ + D₀ * m} := by
      ext n; simp only [LB, twoABin, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨b₀, hb₀, m, hm, rfl⟩; exact ⟨b₀, hb₀, 2 * m, ⟨m, hm, rfl⟩, rfl⟩
      · rintro ⟨b₀, hb₀, k, ⟨m, hm, rfl⟩, rfl⟩; exact ⟨b₀, hb₀, m, hm, rfl⟩
    -- Bijection implies A₀.card * B₀.card = D₀
    have hcard_prod : A₀.card * B₀.card = D₀ := by
      rw [← Finset.card_product, ← Finset.card_range D₀]
      apply Finset.card_bij (fun p _ => (p.1 + p.2) % D₀)
      · intro p _; exact Finset.mem_range.mpr (Nat.mod_lt _ hD₀)
      · intro p₁ hp₁ p₂ hp₂ heq
        simp only [Finset.mem_product] at hp₁ hp₂
        rcases hbij ((p₁.1 + p₁.2) % D₀) (Nat.mod_lt _ hD₀) with ⟨q, _, hq_uniq⟩
        have h1 := hq_uniq p₁ ⟨hp₁.1, hp₁.2, rfl⟩
        have h2 := hq_uniq p₂ ⟨hp₂.1, hp₂.2, heq.symm⟩
        exact h1.trans h2.symm
      · intro r hr
        rcases hbij r (Finset.mem_range.mp hr) with ⟨p, ⟨hp1, hp2, hmod⟩, _⟩
        exact ⟨p, Finset.mem_product.mpr ⟨hp1, hp2⟩, hmod⟩
    apply le_antisymm
    · -- Upper bound: limsup ≤ 3/2
      have hreal_ub : ∀ c : ℝ, (3 / 2 : ℝ) < c →
          Filter.limsup (ratioEReal LA LB) Filter.atTop ≤ (c : EReal) := by
        intro c hc
        apply Filter.limsup_le_of_le
        · exact isCoboundedUnder_le_of_le _ (fun _ => bot_le)
        · rw [Filter.eventually_atTop]
          refine ⟨max 1 (((D₀ : ℝ) + 1) / (c - 3 / 2) + 1), fun x hx => ?_⟩
          have hx_pos : (0 : ℝ) < x := by linarith [le_max_left (1 : ℝ) (((D₀ : ℝ) + 1) / (c - 3 / 2) + 1)]
          set N := ⌊x⌋₊
          have hN_le : (N : ℝ) ≤ x := Nat.floor_le (le_of_lt hx_pos)
          have hcrA : countReal LA x = countNat LA N := by
            unfold countReal; exact ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (le_of_lt hx_pos)))
          have hcrB : countReal LB x = countNat LB N := by
            unfold countReal; exact ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (le_of_lt hx_pos)))
          unfold ratioEReal
          rw [hcrA, hcrB, EReal.coe_le_coe_iff, div_le_iff₀ hx_pos]
          have hLA_ub := (countNat_modularLift_bounds hD₀ hA₀ ABin N).2
          have hLB_ub : countNat LB N ≤ B₀.card * countNat twoABin (N / D₀) := by
            rw [hLB_eq]; exact (countNat_modularLift_bounds hD₀ hB₀ twoABin N).2
          have hprod_nat : 2 * (countNat LA N * countNat LB N) ≤ 3 * N + 2 * D₀ := by
            have h1 := ABin_count_prod_le (N / D₀)
            have h2 := Nat.mul_div_le N D₀
            calc
              2 * (countNat LA N * countNat LB N)
                  ≤ 2 * ((A₀.card * countNat ABin (N / D₀)) * (B₀.card * countNat twoABin (N / D₀))) :=
                    Nat.mul_le_mul_left 2 (Nat.mul_le_mul hLA_ub hLB_ub)
              _ = (A₀.card * B₀.card) * (2 * (countNat ABin (N / D₀) * countNat twoABin (N / D₀))) := by ring
              _ = D₀ * (2 * (countNat ABin (N / D₀) * countNat twoABin (N / D₀))) := by rw [hcard_prod]
              _ ≤ D₀ * (3 * (N / D₀) + 2) := Nat.mul_le_mul_left D₀ h1
              _ = 3 * (D₀ * (N / D₀)) + 2 * D₀ := by ring
              _ ≤ 3 * N + 2 * D₀ := by omega
          have hcast : 2 * ((countNat LA N : ℝ) * (countNat LB N : ℝ)) ≤ 3 * (N : ℝ) + 2 * (D₀ : ℝ) := by
            exact_mod_cast hprod_nat
          have hc32 : (0 : ℝ) < c - 3 / 2 := by linarith
          have hx_c : ((D₀ : ℝ) + 1) / (c - 3 / 2) < x := by
            linarith [le_max_right (1 : ℝ) (((D₀ : ℝ) + 1) / (c - 3 / 2) + 1)]
          have hmul : (D₀ : ℝ) + 1 < (c - 3 / 2) * x := by linarith [(div_lt_iff₀ hc32).mp hx_c]
          linarith
      by_contra hgt
      push Not at hgt
      rcases EReal.exists_between_coe_real hgt with ⟨c, hc1, hc2⟩
      have h32 : (3 / 2 : ℝ) < c := by
        have hcoe : ((3 / 2 : ℝ) : EReal) = (3 / 2 : EReal) := by
          rw [EReal.coe_div]; rfl
        rw [← hcoe] at hc1
        exact EReal.coe_lt_coe_iff.mp hc1
      exact not_lt_of_ge (hreal_ub c h32) hc2
    · -- Lower bound: limsup ≥ 3/2 via sequence x_t = D₀ * (4^t + (4^t - 1)/3 + 1)
      have hreal_lb : ∀ c : ℝ, c < (3 / 2 : ℝ) →
          (c : EReal) ≤ Filter.limsup (ratioEReal LA LB) Filter.atTop := by
        intro c hc
        refine Filter.le_limsup_of_frequently_le ?_ (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
        rw [Filter.frequently_atTop]
        intro M
        -- Choose t large enough so x_t ≥ M and ratio ≥ c
        have hgap : (0 : ℝ) < 3 / 2 - c := by linarith
        obtain ⟨t, ht⟩ := exists_nat_gt (max (max M 1) ((6 * (D₀ : ℝ) + 12) / (3 / 2 - c) + 4))
        have h2t : (t : ℝ) < (2 ^ t : ℝ) := by exact_mod_cast Nat.lt_two_pow_self
        have h4pos : 1 ≤ 4 ^ t := Nat.one_le_pow t 4 (by decide)
        have h2pos : 1 ≤ 2 ^ t := Nat.one_le_two_pow
        set m := 4 ^ t + (4 ^ t - 1) / 3
        set N := D₀ * (m + 1)
        have hN_ge_M : M ≤ (N : ℝ) := by
          have hM_le : M ≤ (t : ℝ) := le_trans (le_trans (le_max_left M 1) (le_max_left _ _)) (le_of_lt ht)
          have ht_le_N : t ≤ N := by
            have h1 : t < 2 ^ t := Nat.lt_two_pow_self
            have h2 : 2 ^ t ≤ 4 ^ t := Nat.pow_le_pow_left (by decide) t
            have h3 : 4 ^ t ≤ m + 1 := by omega
            have h4 : m + 1 ≤ D₀ * (m + 1) := Nat.le_mul_of_pos_left _ hD₀
            omega
          exact le_trans hM_le (by exact_mod_cast ht_le_N)
        refine ⟨(N : ℝ), hN_ge_M, ?_⟩
        have hN_pos : (0 : ℝ) < (N : ℝ) := by
          have : 0 < N := by positivity
          exact_mod_cast this
        have hcrA : countReal LA (N : ℝ) = countNat LA N := by
          unfold countReal
          rw [ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (le_of_lt hN_pos))), Nat.floor_natCast]
        have hcrB : countReal LB (N : ℝ) = countNat LB N := by
          unfold countReal
          rw [ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (le_of_lt hN_pos))), Nat.floor_natCast]
        unfold ratioEReal
        rw [hcrA, hcrB, EReal.coe_le_coe_iff, le_div_iff₀ hN_pos]
        -- Lower bound countNat LA N ≥ A₀.card * countNat ABin m and countNat LB N ≥ B₀.card * countNat twoABin m
        have hLA_ge : A₀.card * countNat ABin m ≤ countNat LA N := by
          classical
          unfold countNat
          rw [← Finset.card_product]
          apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1 + D₀ * p.2)
          · intro p hp
            simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hp ⊢
            have ha_lt := hA₀ p.1 hp.1
            have hmul : D₀ * p.2 ≤ D₀ * m := Nat.mul_le_mul_left D₀ (by omega)
            have hN_eq : N = D₀ * (m + 1) := rfl
            refine ⟨by nlinarith, p.1, hp.1, p.2, hp.2.2, rfl⟩
          · rintro ⟨a₁, u₁⟩ h1 ⟨a₂, u₂⟩ h2 heq
            simp only [Finset.mem_coe, Finset.mem_product] at h1 h2
            dsimp only at heq
            have ha1 := hA₀ a₁ h1.1; have ha2 := hA₀ a₂ h2.1
            have hmod : a₁ = a₂ := by
              have hm1 : (a₁ + D₀ * u₁) % D₀ = a₁ := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha1]
              have hm2 : (a₂ + D₀ * u₂) % D₀ = a₂ := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha2]
              rw [← hm1, ← hm2, heq]
            have hu : u₁ = u₂ := Nat.eq_of_mul_eq_mul_left hD₀ (by omega)
            rw [hmod, hu]
        have hLB_ge : B₀.card * countNat twoABin m ≤ countNat LB N := by
          rw [hLB_eq]
          classical
          unfold countNat
          rw [← Finset.card_product]
          apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1 + D₀ * p.2)
          · intro p hp
            simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hp ⊢
            have hb_lt := hB₀ p.1 hp.1
            have hmul : D₀ * p.2 ≤ D₀ * m := Nat.mul_le_mul_left D₀ (by omega)
            have hN_eq : N = D₀ * (m + 1) := rfl
            refine ⟨by nlinarith, p.1, hp.1, p.2, hp.2.2, rfl⟩
          · rintro ⟨b₁, v₁⟩ h1 ⟨b₂, v₂⟩ h2 heq
            simp only [Finset.mem_coe, Finset.mem_product] at h1 h2
            dsimp only at heq
            have hb1 := hB₀ b₁ h1.1; have hb2 := hB₀ b₂ h2.1
            have hmod : b₁ = b₂ := by
              have hm1 : (b₁ + D₀ * v₁) % D₀ = b₁ := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb1]
              have hm2 : (b₂ + D₀ * v₂) % D₀ = b₂ := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb2]
              rw [← hm1, ← hm2, heq]
            have hv : v₁ = v₂ := Nat.eq_of_mul_eq_mul_left hD₀ (by omega)
            rw [hmod, hv]
        by_cases hc_nn : c ≤ 0
        · have hprod_nn : (0 : ℝ) ≤ (countNat LA N : ℝ) * (countNat LB N : ℝ) := by positivity
          have hcN : c * (N : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc_nn (le_of_lt hN_pos)
          linarith
        · push Not at hc_nn
          rcases ABin_peak_counts t with ⟨hpeakA, hpeakB⟩
          rw [hpeakA] at hLA_ge
          rw [hpeakB] at hLB_ge
          have hsq2 : (2 ^ t) ^ 2 = 4 ^ t := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
          have hprod_ge : 2 * D₀ * 4 ^ t ≤ countNat LA N * countNat LB N := by
            calc
              2 * D₀ * 4 ^ t
                  = (A₀.card * B₀.card) * (2 ^ (t + 1) * 2 ^ t) := by
                    rw [hcard_prod, pow_succ']; nlinarith [hsq2]
              _ = (A₀.card * 2 ^ (t + 1)) * (B₀.card * 2 ^ t) := by ring
              _ ≤ countNat LA N * countNat LB N := Nat.mul_le_mul hLA_ge hLB_ge
          have hm_le : 3 * (m + 1) ≤ 4 * 4 ^ t + 3 := by omega
          have hN_le_3 : 3 * N ≤ D₀ * (4 * 4 ^ t + 3) := by
            calc 3 * N = D₀ * (3 * (m + 1)) := by ring
              _ ≤ D₀ * (4 * 4 ^ t + 3) := Nat.mul_le_mul_left D₀ hm_le
          have hcast_prod : (2 * (D₀ : ℝ) * (4 ^ t : ℝ)) ≤ (countNat LA N : ℝ) * (countNat LB N : ℝ) := by
            exact_mod_cast hprod_ge
          have hcast_N : 3 * (N : ℝ) ≤ (D₀ : ℝ) * (4 * (4 ^ t : ℝ) + 3) := by
            exact_mod_cast hN_le_3
          have h4t_ge : (6 * (D₀ : ℝ) + 12) / (3 / 2 - c) < (4 ^ t : ℝ) := by
            have h1 : (6 * (D₀ : ℝ) + 12) / (3 / 2 - c) < (t : ℝ) := by
              linarith [le_max_right (max M 1) ((6 * (D₀ : ℝ) + 12) / (3 / 2 - c) + 4)]
            have h2 : (t : ℝ) ≤ (4 ^ t : ℝ) := by
              have : t ≤ 4 ^ t := le_of_lt (Nat.lt_pow_self (by decide : 1 < 4))
              exact_mod_cast this
            linarith
          have h4t_mul : 6 * (D₀ : ℝ) + 12 < (3 / 2 - c) * (4 ^ t : ℝ) := by
            linarith [(div_lt_iff₀ hgap).mp h4t_ge]
          have hD0_real : (1 : ℝ) ≤ (D₀ : ℝ) := by exact_mod_cast hD₀
          nlinarith [mul_le_mul_of_nonneg_left hcast_N (le_of_lt hc_nn),
                     mul_le_mul_of_nonneg_left (le_of_lt h4t_mul) (show (0 : ℝ) ≤ (D₀ : ℝ) by linarith)]
      by_contra hlt
      push Not at hlt
      rcases EReal.exists_between_coe_real hlt with ⟨c, hc1, hc2⟩
      have hc32 : c < (3 / 2 : ℝ) := by
        have hcoe : ((3 / 2 : ℝ) : EReal) = (3 / 2 : EReal) := by
          rw [EReal.coe_div]; rfl
        rw [← hcoe] at hc2
        exact EReal.coe_lt_coe_iff.mp hc2
      exact not_lt_of_ge (hreal_lb c hc32) hc1
  rcases h with ⟨D₀, A₀, B₀, hD₀, hA₀, hB₀, hbij, ⟨hAeq, hBeq⟩ | ⟨hAeq, hBeq⟩⟩
  · rw [hAeq, hBeq]
    exact haux D₀ A₀ B₀ hD₀ hA₀ hB₀ hbij
  · have hswap : ratioEReal A B = ratioEReal B A := by
      funext x; unfold ratioEReal; ring_nf
    rw [hswap, hAeq, hBeq]
    exact haux D₀ A₀ B₀ hD₀ hA₀ hB₀ hbij

end

end AlmostPerfect

