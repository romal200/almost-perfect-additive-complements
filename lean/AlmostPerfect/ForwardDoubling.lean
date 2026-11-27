import AlmostPerfect.Basic
import AlmostPerfect.PolynomialInvariants
import AlmostPerfect.ZhangGap
import AlmostPerfect.DifferenceDensity
import Mathlib.Tactic

/-!
# Section 5: Exact Forward Doubling and Quadratic Polynomial Recurrence

Formalizes Section 5 of `PROOF.md`:
- `LevelApprox`: concrete quantitative approximation hypotheses at a bounded-crossing level `N`
  supplied by Corollary 4.4 (`ε = 1 / 1000`).
- `lemma_5_1`: `N < y₀ ≤ (1 + 8ε) N` where `y₀ = min(A ∩ (N, ∞))`.
- `lemma_5_2`: `w₀ > y₀ + (5/8) N` where `w₀ = min(B ∩ (N, ∞))`.
- `forward_doubling_step` (Proposition 5.3): exact polynomial identities
  `P_{A₁'} * V = P_{A₀} * U₁`, `W_N = X^(y₀ - (N+1)) * U₁`,
  `X^(N₁'+1) * V * W_{N₁'} = X^(2(N+1)) * W_N^2`,
  stripped quadratic recurrence `Ṽ * W̃_{N₁'} = W̃_N^2`,
  exact truncations `A ∩ [0, N₁'] = A₀ ∪ A₁'`, `B ∩ [0, N₁'] = B₀`,
  order `ord₀(W_{N₁'}) = max(a_min, b_min)`, and crossing bound `T(N₁') ≤ 2 T(N) + E + 2 n₀`.
-/

namespace AlmostPerfect

open Polynomial BigOperators Filter

noncomputable section

/-- Concrete quantitative approximation properties at level `N` (with `ε = 1 / 1000`) supplied by
Corollary 4.4 when `A` approximates `ν₀` (supported on `[0, 1/3]`) and `B` approximates `μ₀`
(supported on `[0, 2/3]`). -/
structure LevelApprox (A B : Set ℕ) (n₀ K N : ℕ) : Prop where
  hK_ge_n0 : n₀ ≤ K
  hN_large : 10 ^ 7 * (K + errSum A B n₀ + n₀ + 1) * (errSum A B n₀ + n₀ + 1) ≤ N
  hT_le : crossExcess A B N ≤ K
  hprod_le : ∀ t ≥ N, (countNat A t : ℝ) * (countNat B t : ℝ) ≤ (8 / 5 : ℝ) * (t : ℝ)
  hA_large : 10 ^ 7 * (C1Const A B n₀ K + K + errSum A B n₀ + n₀ + 1) ≤ countNat A N
  hB_large : 10 ^ 7 * (C1Const A B n₀ K + K + errSum A B n₀ + n₀ + 1) ≤ countNat B N
  hx₀_lo : ∃ a ∈ A, a ≤ N ∧ (1 / 3 - 1 / 1000 : ℝ) * (N : ℝ) ≤ (a : ℝ)
  hx₀_hi : ∀ a ∈ A, a ≤ N → (a : ℝ) ≤ (1 / 3 + 1 / 1000 : ℝ) * (N : ℝ)
  hz₀_lo : ∃ b ∈ B, b ≤ N ∧ (2 / 3 - 1 / 1000 : ℝ) * (N : ℝ) ≤ (b : ℝ)
  hz₀_hi : ∀ b ∈ B, b ≤ N → (b : ℝ) ≤ (2 / 3 + 1 / 1000 : ℝ) * (N : ℝ)
  hMaxAtAny : ∀ M ≥ N, crossExcess A B M ≤ K →
    ∃ a ∈ A, a ≤ M ∧ (1 / 3 - 1 / 1000 : ℝ) * (M : ℝ) ≤ (a : ℝ)
  hgap_A : ((countNat A ⌊(1 / 4 - 2 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) -
            (countNat A ⌊(1 / 12 + 3 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ)) ≤
            (2 / 1000 : ℝ) * (countNat A N : ℝ)
  hblock1_A : (248 / 1000 : ℝ) * (countNat A N : ℝ) ≤
              ((countNat A ⌊(1 / 12 + 1 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) -
               (countNat A ⌊(1 / 16 - 1 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ))
  hblock2_A : (248 / 1000 : ℝ) * (countNat A N : ℝ) ≤
              ((countNat A ⌊(1 / 3 + 1 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) -
               (countNat A ⌊(5 / 16 - 1 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ))

/-- Maximum element of `S ∩ [0, N]` (defined via `Finset.sup`). -/
def maxLe (S : Set ℕ) (N : ℕ) : ℕ :=
  letI := Classical.decPred (· ∈ S)
  ((Finset.range (N + 1)).filter (· ∈ S)).sup id

/-- Next element of an infinite set `S` strictly greater than `N`. -/
def nextGt {S : Set ℕ} (hS : S.Infinite) (N : ℕ) : ℕ :=
  letI := Classical.decPred (fun n => n ∈ S ∧ N < n)
  Nat.find (hS.exists_gt N)

lemma maxLe_mem {S : Set ℕ} {N : ℕ} (hne : ∃ a ∈ S, a ≤ N) :
    maxLe S N ∈ S ∧ maxLe S N ≤ N := by
  classical
  unfold maxLe
  set F := (Finset.range (N + 1)).filter (· ∈ S)
  have hFne : F.Nonempty := by
    rcases hne with ⟨a, haS, haN⟩
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), haS⟩⟩
  obtain ⟨m, hmF, hm_eq⟩ := Finset.exists_mem_eq_sup F hFne id
  have hm_eq' : F.sup id = m := hm_eq
  rw [hm_eq']
  simp only [F, Finset.mem_filter, Finset.mem_range] at hmF
  exact ⟨hmF.2, by omega⟩

lemma le_maxLe {S : Set ℕ} {N a : ℕ} (haS : a ∈ S) (haN : a ≤ N) :
    a ≤ maxLe S N := by
  classical
  unfold maxLe
  have hmem : a ∈ (Finset.range (N + 1)).filter (· ∈ S) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), haS⟩
  exact Finset.le_sup (f := id) hmem

lemma nextGt_spec {S : Set ℕ} (hS : S.Infinite) (N : ℕ) :
    N < nextGt hS N ∧ nextGt hS N ∈ S := by
  unfold nextGt
  let _ := Classical.decPred (fun n => n ∈ S ∧ N < n)
  have h := Nat.find_spec (hS.exists_gt N)
  exact ⟨h.2, h.1⟩

lemma nextGt_le {S : Set ℕ} (hS : S.Infinite) {N a : ℕ} (haS : a ∈ S) (haGt : N < a) :
    nextGt hS N ≤ a := by
  unfold nextGt
  let _ := Classical.decPred (fun n => n ∈ S ∧ N < n)
  exact Nat.find_min' (hS.exists_gt N) ⟨haS, haGt⟩

lemma not_mem_Ioo_maxLe_nextGt {S : Set ℕ} (hS : S.Infinite) {N a : ℕ}
    (haS : a ∈ S) (h1 : maxLe S N < a) : nextGt hS N ≤ a := by
  by_cases hle : a ≤ N
  · have := le_maxLe haS hle; omega
  · exact nextGt_le hS (N := N) haS (by omega)

/-! ### Helper: Pigeonhole Zero-Run Lemma (Step 1 of Proposition 5.3) -/

private lemma pigeonhole_zero_run {S f : ℕ → ℤ} {T₀ L₁ A₀c E n₀ : ℕ}
    (hf01 : ∀ t, T₀ < t → t ≤ L₁ → f t = 0 ∨ f t = 1)
    (hstep : ∀ t, T₀ ≤ t → t < L₁ → S (t + 1) = S t + f (t + 1))
    (hbd : ∀ t, T₀ ≤ t → t ≤ L₁ → (A₀c : ℤ) - (E : ℤ) ≤ S t ∧ S t ≤ (A₀c : ℤ) + (E : ℤ))
    (hrun : ∀ u, T₀ + n₀ ≤ u → u ≤ L₁ → (∀ j < n₀, f (u - j) = 0) → S u = (A₀c : ℤ))
    (hn0 : 1 ≤ n₀)
    (hgap : T₀ + 2 * (E + 1) * (n₀ + 1) ≤ L₁) :
    let T₁ := T₀ + (E + 1) * (n₀ + 1)
    let T₂ := L₁ - (E + 1) * (n₀ + 1)
    (∀ t, T₁ ≤ t → t ≤ T₂ → S t = (A₀c : ℤ)) ∧
    (∀ t, T₁ + 1 ≤ t → t ≤ T₂ → f t = 0) := by
  intro T₁ T₂
  have hS_mono : ∀ a b, T₀ ≤ a → a ≤ b → b ≤ L₁ → S a ≤ S b := by
    intro a b ha hab hb
    induction b with
    | zero =>
      have ha0 : a = 0 := by omega
      subst ha0; exact le_rfl
    | succ k ih =>
      by_cases hlt : a ≤ k
      · have ih' := ih hlt (by omega)
        have hst := hstep k (by omega) (by omega)
        rcases hf01 (k + 1) (by omega) (by omega) with h0 | h1 <;> linarith
      · have hak : a = k + 1 := by omega
        subst hak; exact le_rfl
  have hS_diff : ∀ a b, T₀ ≤ a → a ≤ b → b ≤ L₁ →
      S b - S a = ∑ i ∈ Finset.Ioc a b, f i := by
    intro a b ha hab hb
    induction b with
    | zero =>
      have ha0 : a = 0 := by omega
      subst ha0; simp
    | succ k ih =>
      by_cases hlt : a ≤ k
      · have ih' := ih hlt (by omega)
        have hst := hstep k (by omega) (by omega)
        have hIoc : Finset.Ioc a (k + 1) = insert (k + 1) (Finset.Ioc a k) := by
          ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
        have hnot : k + 1 ∉ Finset.Ioc a k := by simp [Finset.mem_Ioc]
        rw [hIoc, Finset.sum_insert hnot]
        linarith
      · have hak : a = k + 1 := by omega
        subst hak; simp
  have hexists_run : ∀ start, T₀ ≤ start → start + (E + 1) * (n₀ + 1) ≤ L₁ →
      S (start + (E + 1) * (n₀ + 1)) - S start ≤ (E : ℤ) →
      ∃ u, start + n₀ ≤ u ∧ u ≤ start + (E + 1) * (n₀ + 1) ∧ ∀ j < n₀, f (u - j) = 0 := by
    intro start hs_ge hs_le hinc
    by_contra hno
    push Not at hno
    have hblock : ∀ k ∈ Finset.range (E + 1),
        (1 : ℤ) ≤ ∑ i ∈ Finset.Ioc (start + k * (n₀ + 1)) (start + (k + 1) * (n₀ + 1)), f i := by
      intro k hk
      have hk_le : k ≤ E := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      set u := start + (k + 1) * (n₀ + 1)
      have hu_eq : u = start + (k + 1) * (n₀ + 1) := rfl
      have hu1 : start + n₀ ≤ u := by
        have : n₀ ≤ (k + 1) * (n₀ + 1) := by nlinarith
        omega
      have hu2 : u ≤ start + (E + 1) * (n₀ + 1) := by
        have : (k + 1) * (n₀ + 1) ≤ (E + 1) * (n₀ + 1) := Nat.mul_le_mul_right _ (by omega)
        omega
      obtain ⟨j, hj_lt, hfj_ne⟩ := hno u hu1 hu2
      have hsub_ge : start + k * (n₀ + 1) < u - j := by
        have h1 : (k + 1) * (n₀ + 1) = k * (n₀ + 1) + (n₀ + 1) := by ring
        omega
      have hmem : u - j ∈ Finset.Ioc (start + k * (n₀ + 1)) u := by
        rw [Finset.mem_Ioc]; exact ⟨hsub_ge, by omega⟩
      have hfj1 : f (u - j) = 1 := by
        rcases hf01 (u - j) (by omega) (by omega) with h0 | h1
        · exact absurd h0 hfj_ne
        · exact h1
      have hnn : ∀ i ∈ Finset.Ioc (start + k * (n₀ + 1)) u, (0 : ℤ) ≤ f i := by
        intro i hi
        rw [Finset.mem_Ioc] at hi
        rcases hf01 i (by omega) (by omega) with h0 | h1 <;> omega
      calc
        (1 : ℤ) = f (u - j) := hfj1.symm
        _ ≤ ∑ i ∈ Finset.Ioc (start + k * (n₀ + 1)) u, f i :=
              Finset.single_le_sum hnn hmem
    have hsum_blocks :
        ∑ k ∈ Finset.range (E + 1),
          ∑ i ∈ Finset.Ioc (start + k * (n₀ + 1)) (start + (k + 1) * (n₀ + 1)), f i =
        ∑ i ∈ Finset.Ioc start (start + (E + 1) * (n₀ + 1)), f i := by
      clear hinc hblock hno
      have haux : ∀ m,
          ∑ k ∈ Finset.range m,
            ∑ i ∈ Finset.Ioc (start + k * (n₀ + 1)) (start + (k + 1) * (n₀ + 1)), f i =
          ∑ i ∈ Finset.Ioc start (start + m * (n₀ + 1)), f i := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          rw [Finset.sum_range_succ, ih]
          have hdisj : Disjoint (Finset.Ioc start (start + m * (n₀ + 1)))
              (Finset.Ioc (start + m * (n₀ + 1)) (start + (m + 1) * (n₀ + 1))) := by
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            rw [Finset.mem_Ioc] at hx1 hx2
            omega
          have hunion : Finset.Ioc start (start + m * (n₀ + 1)) ∪
              Finset.Ioc (start + m * (n₀ + 1)) (start + (m + 1) * (n₀ + 1)) =
              Finset.Ioc start (start + (m + 1) * (n₀ + 1)) := by
            ext x
            simp only [Finset.mem_union, Finset.mem_Ioc]
            have hstep_m : (m + 1) * (n₀ + 1) = m * (n₀ + 1) + (n₀ + 1) := by ring
            constructor
            · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> omega
            · rintro ⟨h1, h2⟩
              by_cases hle : x ≤ start + m * (n₀ + 1)
              · left; exact ⟨h1, hle⟩
              · right; exact ⟨by omega, h2⟩
          rw [← Finset.sum_union hdisj, hunion]
      exact haux (E + 1)
    have hge_E1 : ((E + 1 : ℕ) : ℤ) ≤ S (start + (E + 1) * (n₀ + 1)) - S start := by
      rw [hS_diff start (start + (E + 1) * (n₀ + 1)) hs_ge (by omega) hs_le, ← hsum_blocks]
      calc
        ((E + 1 : ℕ) : ℤ) = ∑ _k ∈ Finset.range (E + 1), (1 : ℤ) := by simp
        _ ≤ _ := Finset.sum_le_sum hblock
    push_cast at hge_E1
    linarith
  have hSeq : ∀ t, T₁ ≤ t → t ≤ T₂ → S t = (A₀c : ℤ) := by
    intro t ht1 ht2
    have h2 : 2 * (E + 1) * (n₀ + 1) = (E + 1) * (n₀ + 1) + (E + 1) * (n₀ + 1) := by ring
    have hge : (A₀c : ℤ) ≤ S t := by
      by_contra hlt
      push Not at hlt
      have hT0_ge : (A₀c : ℤ) - (E : ℤ) ≤ S T₀ := (hbd T₀ le_rfl (by omega)).1
      have hT1_le : S T₁ ≤ S t := hS_mono T₁ t (by omega) ht1 (by omega)
      have hinc : S (T₀ + (E + 1) * (n₀ + 1)) - S T₀ ≤ (E : ℤ) := by
        change S T₁ - S T₀ ≤ (E : ℤ); linarith
      obtain ⟨u, hu1, hu2, hzeros⟩ := hexists_run T₀ le_rfl (by omega) hinc
      have hSu : S u = (A₀c : ℤ) := hrun u hu1 (by omega) hzeros
      have hSu_le : S u ≤ S t := hS_mono u t (by omega) (by omega) (by omega)
      linarith
    have hle : S t ≤ (A₀c : ℤ) := by
      by_contra hgt
      push Not at hgt
      have hL1_le : S L₁ ≤ (A₀c : ℤ) + (E : ℤ) := (hbd L₁ (by omega) le_rfl).2
      have hst_le : S (t + (E + 1) * (n₀ + 1)) ≤ S L₁ :=
        hS_mono (t + (E + 1) * (n₀ + 1)) L₁ (by omega) (by omega) le_rfl
      have hinc : S (t + (E + 1) * (n₀ + 1)) - S t ≤ (E : ℤ) := by linarith
      obtain ⟨u, hu1, hu2, hzeros⟩ := hexists_run t (by omega) (by omega) hinc
      have hSu : S u = (A₀c : ℤ) := hrun u (by omega) (by omega) hzeros
      have hSt_le : S t ≤ S u := hS_mono t u (by omega) (by omega) (by omega)
      linarith
    linarith
  refine ⟨hSeq, fun t ht1 ht2 => ?_⟩
  have h1 := hSeq (t - 1) (by omega) (by omega)
  have h2 := hSeq t (by omega) ht2
  have hst := hstep (t - 1) (by omega) (by omega)
  have heq : t - 1 + 1 = t := by omega
  rw [heq] at hst
  linarith

/-! ### Lemma 5.1: Location of `y₀` -/

/-- **Lemma 5.1:** `N < y₀ ≤ (1 + 8ε) N` (with `ε = 1 / 1000`). -/
theorem lemma_5_1 {A B : Set ℕ} (hA_inf : A.Infinite) {n₀ K N : ℕ}
    (hn0 : 1 ≤ n₀) (hstab : ∀ n ≥ n₀, repCount A B n = 1)
    (hL : LevelApprox A B n₀ K N) :
    N < nextGt hA_inf N ∧ (nextGt hA_inf N : ℝ) ≤ (1 + 8 / 1000 : ℝ) * (N : ℝ) := by
  set y₀ := nextGt hA_inf N
  set x₀ := maxLe A N
  have hy₀ := nextGt_spec hA_inf N
  have hx₀_mem := maxLe_mem (by rcases hL.hx₀_lo with ⟨a, haA, haN, _⟩; exact ⟨a, haA, haN⟩)
  have hx₀_lo : (1 / 3 - 1 / 1000 : ℝ) * (N : ℝ) ≤ (x₀ : ℝ) := by
    rcases hL.hx₀_lo with ⟨a, haA, haN, ha_lo⟩
    have hle : a ≤ x₀ := le_maxLe haA haN
    have : (a : ℝ) ≤ (x₀ : ℝ) := by exact_mod_cast hle
    linarith
  have hx₀_hi : (x₀ : ℝ) ≤ (1 / 3 + 1 / 1000 : ℝ) * (N : ℝ) := hL.hx₀_hi x₀ hx₀_mem.1 hx₀_mem.2
  have hN_ge_107 : (10 ^ 7 : ℝ) * ((n₀ : ℝ) + 1) ≤ (N : ℝ) := by
    have hnat : 10 ^ 7 * (n₀ + 1) ≤ N := by
      have := hL.hN_large
      nlinarith
    exact_mod_cast hnat
  refine ⟨hy₀.1, ?_⟩
  by_cases hlt : y₀ < 3 * x₀ + n₀
  · have hcast : (y₀ : ℝ) < 3 * (x₀ : ℝ) + (n₀ : ℝ) := by exact_mod_cast hlt
    linarith
  · push Not at hlt
    have hx₀_2n0 : 2 * n₀ ≤ x₀ := by
      have : (2 * (n₀ : ℝ)) ≤ (x₀ : ℝ) := by linarith
      exact_mod_cast this
    have hE_le : (∑ m ∈ Finset.range n₀, |(repCount A B m : ℤ) - 1|) ≤ (errSum A B n₀ : ℤ) := by
      unfold errSum; push_cast; exact le_rfl
    have hgap_z := zhang_gap_lemma hn0 hstab hE_le hx₀_mem.1 hy₀.2
      (fun a haA hgt => not_mem_Ioo_maxLe_nextGt hA_inf haA hgt) hx₀_2n0 hlt
    have hT_y0 : crossExcess A B (y₀ - 1) ≤ K := le_trans hgap_z.2.1 hL.hK_ge_n0
    obtain ⟨a, haA, ha_le, ha_lo⟩ := hL.hMaxAtAny (y₀ - 1) (by omega) hT_y0
    have ha_le_x0 : a ≤ x₀ := by
      by_cases hleN : a ≤ N
      · exact le_maxLe haA hleN
      · have := nextGt_le hA_inf (N := N) haA (by omega); omega
    have hcast_a : (a : ℝ) ≤ (x₀ : ℝ) := by exact_mod_cast ha_le_x0
    have hcast_y1 : ((y₀ - 1 : ℕ) : ℝ) = (y₀ : ℝ) - 1 := by
      have : 1 ≤ y₀ := by omega
      rw [Nat.cast_sub this]; simp
    rw [hcast_y1] at ha_lo
    linarith

/-! ### Lemma 5.2: Location of `w₀` -/

/-- Step 1 of Lemma 5.2: every integer `d ∈ [n₀, N - 2 x₀]` lies in `B₀ - A₀`. -/
lemma diff_interval_in_B0_sub_A0 {A B : Set ℕ} {n₀ N : ℕ}
    (hstab : ∀ n ≥ n₀, repCount A B n = 1)
    {x₀ : ℕ} (hx₀A : x₀ ∈ A) (_hx₀_le : x₀ ≤ N)
    (hx₀_max : ∀ a ∈ A, a ≤ N → a ≤ x₀)
    {d : ℕ} (hd1 : n₀ ≤ d) (hd2 : d + 2 * x₀ ≤ N) :
    ∃ a ∈ A, a ≤ x₀ ∧ ∃ b ∈ B, b ≤ N ∧ b = a + d := by
  classical
  set f₀ : ℕ → ℤ := fun n => if n ≤ x₀ ∧ n ∈ A then 1 else 0
  set g₀ : ℕ → ℤ := fun n => if n ≤ N ∧ n ∈ B then 1 else 0
  set f₀r : ℕ → ℤ := fun n => if n ≤ x₀ then f₀ (x₀ - n) else 0
  set h : ℕ → ℤ := fun _ => 1
  set δ : ℕ → ℤ := fun n => (repCount A B n : ℤ) - 1
  set D : ℕ → ℤ := fun n => 1 - dconv f₀r g₀ n
  have hfg : ∀ n ≤ N, dconv f₀ g₀ n = h n + δ n := by
    intro n hn
    unfold dconv h δ
    have hsum : ∑ i ∈ Finset.range (n + 1), f₀ i * g₀ (n - i) = (repCount A B n : ℤ) := by
      unfold repCount
      have hterm : ∀ i ∈ Finset.range (n + 1),
          f₀ i * g₀ (n - i) = if i ∈ A ∧ n - i ∈ B then (1 : ℤ) else 0 := by
        intro i hi
        have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        simp only [f₀, g₀]
        by_cases ha : i ∈ A
        · have hi_x0 : i ≤ x₀ := hx₀_max i ha (by omega)
          have hni_N : n - i ≤ N := by omega
          by_cases hb : n - i ∈ B <;> simp [ha, hb, hi_x0, hni_N]
        · simp [ha]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hsum]; ring
  have hfD_zero : ∀ n, x₀ + n₀ ≤ n → n ≤ N → dconv f₀ D n = 0 := by
    intro n hn1 hn2
    have h1 : dconv f₀ D n = dconv f₀ h n - dconv f₀ (dconv f₀r g₀) n :=
      dconv_sub_right f₀ h (dconv f₀r g₀) n
    rw [h1]
    have hassoc : dconv f₀ (dconv f₀r g₀) n = dconv f₀r (dconv f₀ g₀) n := by
      rw [← dconv_assoc, dconv_comm_fun f₀ f₀r, dconv_assoc]
    rw [hassoc]
    have hsub : dconv f₀r (dconv f₀ g₀) n = dconv f₀r h n + dconv f₀r δ n := by
      rw [dconv_congr_right (fun k hk => hfg k (by omega)), dconv_add_right]
    rw [hsub]
    have hfh : dconv f₀ h n = dconv f₀r h n := by
      unfold dconv h
      have hleft : ∑ i ∈ Finset.range (n + 1), f₀ i * 1 = ∑ i ∈ Finset.range (x₀ + 1), f₀ i := by
        have hsplit : n + 1 = (x₀ + 1) + (n - x₀) := by omega
        rw [hsplit, Finset.sum_range_add]
        have hz : ∑ m ∈ Finset.range (n - x₀), f₀ (x₀ + 1 + m) * 1 = 0 := by
          apply Finset.sum_eq_zero; intro m _; simp [f₀]; omega
        rw [hz, add_zero]
        apply Finset.sum_congr rfl; intro i _; ring
      have hright : ∑ i ∈ Finset.range (n + 1), f₀r i * 1 = ∑ i ∈ Finset.range (x₀ + 1), f₀ (x₀ - i) := by
        have hsplit : n + 1 = (x₀ + 1) + (n - x₀) := by omega
        rw [hsplit, Finset.sum_range_add]
        have hz : ∑ m ∈ Finset.range (n - x₀), f₀r (x₀ + 1 + m) * 1 = 0 := by
          apply Finset.sum_eq_zero; intro m _; simp [f₀r]; omega
        rw [hz, add_zero]
        apply Finset.sum_congr rfl
        intro i hi; have : i ≤ x₀ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi); simp [f₀r, this]
      rw [hleft, hright]
      symm
      apply Finset.sum_bij (fun i _ => x₀ - i)
      · intro i hi; rw [Finset.mem_range] at hi ⊢; omega
      · intro i₁ h1 i₂ h2 heq; rw [Finset.mem_range] at h1 h2; omega
      · intro j hj; rw [Finset.mem_range] at hj; exact ⟨x₀ - j, Finset.mem_range.mpr (by omega), by omega⟩
      · intro i _; rfl
    have hfδ : dconv f₀r δ n = 0 := by
      unfold dconv
      apply Finset.sum_eq_zero
      intro i _
      by_cases hix : i ≤ x₀
      · have hge : n₀ ≤ n - i := by omega
        simp [δ, hstab (n - i) hge]
      · simp [f₀r, hix]
    linarith
  have hD_nn : ∀ n, x₀ + n₀ ≤ n → 0 ≤ D n := by
    intro n hn
    unfold D dconv
    have hle1 : ∑ i ∈ Finset.range (n + 1), f₀r i * g₀ (n - i) ≤ 1 := by
      have hterm : ∀ i ∈ Finset.range (n + 1),
          f₀r i * g₀ (n - i) =
            if i ≤ x₀ ∧ x₀ - i ∈ A ∧ n - i ≤ N ∧ n - i ∈ B then (1 : ℤ) else 0 := by
        intro i _
        simp only [f₀r, f₀, g₀]
        by_cases h1 : i ≤ x₀
        · have hsub : x₀ - i ≤ x₀ := by omega
          by_cases h2 : x₀ - i ∈ A <;> by_cases h3 : n - i ≤ N <;> by_cases h4 : n - i ∈ B <;>
            simp [h1, hsub, h2, h3, h4]
        · simp [h1]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hcard : ((Finset.range (n + 1)).filter (fun i => i ≤ x₀ ∧ x₀ - i ∈ A ∧ n - i ≤ N ∧ n - i ∈ B)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro i₁ h1 i₂ h2
        simp only [Finset.mem_filter, Finset.mem_range] at h1 h2
        by_contra hne
        have hdiff : (n - i₁) + (x₀ - i₂) = (n - i₂) + (x₀ - i₁) := by omega
        have hpair_ne : x₀ - i₁ ≠ x₀ - i₂ ∨ n - i₁ ≠ n - i₂ := Or.inl (by omega)
        have hsmall := unique_large_diff hstab h1.2.2.1 h2.2.2.1 h1.2.2.2.2 h2.2.2.2.2 hdiff hpair_ne
        omega
      exact_mod_cast hcard
    linarith
  set u := x₀ + d
  have hu_eq : dconv f₀ D (u + x₀) = 0 := hfD_zero (u + x₀) (by omega) (by omega)
  have hDu_zero : D u = 0 := by
    unfold dconv at hu_eq
    have hnn : ∀ i ∈ Finset.range (u + x₀ + 1), 0 ≤ f₀ i * D (u + x₀ - i) := by
      intro i _
      by_cases hcond : i ≤ x₀ ∧ i ∈ A
      · have : f₀ i = 1 := by simp [f₀, hcond]
        rw [this, one_mul]
        exact hD_nn (u + x₀ - i) (by omega)
      · have : f₀ i = 0 := by simp [f₀, hcond]
        rw [this, zero_mul]
    have hx₀_mem : x₀ ∈ Finset.range (u + x₀ + 1) := Finset.mem_range.mpr (by omega)
    have hterm_le : f₀ x₀ * D (u + x₀ - x₀) ≤ ∑ i ∈ Finset.range (u + x₀ + 1), f₀ i * D (u + x₀ - i) :=
      Finset.single_le_sum hnn hx₀_mem
    have hfx0 : f₀ x₀ = 1 := by simp [f₀, hx₀A]
    have hDu_nn : 0 ≤ D u := hD_nn u (by omega)
    have hsub : u + x₀ - x₀ = u := by omega
    rw [hfx0, one_mul, hsub, hu_eq] at hterm_le
    linarith
  have hconv1 : dconv f₀r g₀ u = 1 := by unfold D at hDu_zero; linarith
  unfold dconv at hconv1
  have hex : ∃ i ∈ Finset.range (u + 1), f₀r i * g₀ (u - i) ≠ 0 := by
    by_contra hno
    push Not at hno
    have := Finset.sum_eq_zero hno
    omega
  rcases hex with ⟨i, hi, hnz⟩
  have hi_le : i ≤ u := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 : i ≤ x₀ := by by_contra hgt; simp [f₀r, hgt] at hnz
  have h2 : x₀ - i ∈ A := by by_contra hnot; simp [f₀r, f₀, h1, hnot] at hnz
  have h3 : u - i ≤ N ∧ u - i ∈ B := by
    by_contra hnot
    have hg0 : g₀ (u - i) = 0 := by simp only [g₀, hnot, ↓reduceIte]
    rw [hg0, mul_zero] at hnz
    exact hnz rfl
  exact ⟨x₀ - i, h2, by omega, u - i, h3.2, h3.1, by omega⟩

open Classical in
/-- Shared convolution identity `(5.4)–(5.5)` on `[0, t]` whenever `t ≤ N` and `y₀ + t < w₀`. -/
private lemma conv_identity_55 {A B : Set ℕ} (hA_inf : A.Infinite) (hB_inf : B.Infinite)
    {n₀ N : ℕ} (hstab : ∀ n ≥ n₀, repCount A B n = 1) (hN_ge : n₀ ≤ N)
    {t : ℕ} (htN : t ≤ N) (htw : nextGt hA_inf N + t < nextGt hB_inf N) :
    let x₀ := maxLe A N
    let y₀ := nextGt hA_inf N
    let f₀ : ℕ → ℤ := fun n => if n ≤ x₀ ∧ n ∈ A then 1 else 0
    let f₁ : ℕ → ℤ := fun n => if y₀ + n ∈ A then 1 else 0
    let h : ℕ → ℤ := fun _ => 1
    let δ : ℕ → ℤ := fun n => (repCount A B n : ℤ) - 1
    let η₁ : ℕ → ℤ := fun n => (repTrunc A B N (y₀ + n) : ℤ)
    dconv f₁ h t - dconv f₀ h t = - dconv f₁ δ t - dconv f₀ η₁ t := by
  intro x₀ y₀ f₀ f₁ h δ η₁
  set g₀ : ℕ → ℤ := fun n => if n ≤ N ∧ n ∈ B then 1 else 0
  have hy₀_spec := nextGt_spec hA_inf N
  have hf0g0 : ∀ n ≤ N, dconv f₀ g₀ n = h n + δ n := by
    intro n hn
    unfold dconv h δ
    have hsum : ∑ i ∈ Finset.range (n + 1), f₀ i * g₀ (n - i) = (repCount A B n : ℤ) := by
      unfold repCount
      have hterm : ∀ i ∈ Finset.range (n + 1),
          f₀ i * g₀ (n - i) = if i ∈ A ∧ n - i ∈ B then (1 : ℤ) else 0 := by
        intro i hi
        have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        simp only [f₀, g₀]
        by_cases ha : i ∈ A
        · have hi_x0 : i ≤ x₀ := le_maxLe ha (by omega)
          have hni_N : n - i ≤ N := by omega
          by_cases hb : n - i ∈ B <;> simp [ha, hb, hi_x0, hni_N]
        · simp [ha]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hsum]; ring
  have hf1g0 : ∀ n ≤ t, dconv f₁ g₀ n = h n - η₁ n := by
    intro n hn
    unfold dconv h η₁
    have hsum : ∑ i ∈ Finset.range (n + 1), f₁ i * g₀ (n - i) + (repTrunc A B N (y₀ + n) : ℤ) =
        (repCount A B (y₀ + n) : ℤ) := by
      have hpart1 : ∑ i ∈ Finset.range (n + 1), f₁ i * g₀ (n - i) =
          (((Finset.range (y₀ + n + 1)).filter (fun a => y₀ ≤ a ∧ a ∈ A ∧ y₀ + n - a ∈ B)).card : ℤ) := by
        have hterm : ∀ i ∈ Finset.range (n + 1),
            f₁ i * g₀ (n - i) = if y₀ + i ∈ A ∧ n - i ∈ B then (1 : ℤ) else 0 := by
          intro i hi
          have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          simp only [f₁, g₀]
          have hni_N : n - i ≤ N := by omega
          by_cases ha : y₀ + i ∈ A <;> by_cases hb : n - i ∈ B <;> simp [ha, hb, hni_N]
        rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        congr 1
        apply Finset.card_bij (fun i _ => y₀ + i)
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
          refine ⟨by omega, by omega, hi.2.1, ?_⟩
          have : y₀ + n - (y₀ + i) = n - i := by omega
          rw [this]; exact hi.2.2
        · intro i₁ _ i₂ _ heq; omega
        · intro a ha
          simp only [Finset.mem_filter, Finset.mem_range] at ha
          refine ⟨a - y₀, ?_, by omega⟩
          simp only [Finset.mem_filter, Finset.mem_range]
          refine ⟨by omega, ?_, ?_⟩
          · have hadd : y₀ + (a - y₀) = a := by omega
            rw [hadd]; exact ha.2.2.1
          · have hsub : n - (a - y₀) = y₀ + n - a := by omega
            rw [hsub]; exact ha.2.2.2
      have hpart2 : repTrunc A B N (y₀ + n) =
          ((Finset.range (y₀ + n + 1)).filter (fun a => a < y₀ ∧ a ∈ A ∧ y₀ + n - a ∈ B)).card := by
        unfold repTrunc
        congr 1; ext a
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨by omega, by omega, h2, h5⟩
        · rintro ⟨h1, h2, h3, h4⟩
          have haN : a ≤ N := by
            by_contra hgt
            have := nextGt_le hA_inf (N := N) h3 (by omega)
            omega
          have hbN : y₀ + n - a ≤ N := by
            by_contra hgt
            have := nextGt_le hB_inf (N := N) h4 (by omega)
            omega
          exact ⟨by omega, h3, by omega, hbN, h4⟩
      rw [hpart1, hpart2]
      have hdisj : Disjoint
          ((Finset.range (y₀ + n + 1)).filter (fun a => y₀ ≤ a ∧ a ∈ A ∧ y₀ + n - a ∈ B))
          ((Finset.range (y₀ + n + 1)).filter (fun a => a < y₀ ∧ a ∈ A ∧ y₀ + n - a ∈ B)) := by
        rw [Finset.disjoint_left]; intro a h1 h2; simp only [Finset.mem_filter] at h1 h2; omega
      have hunion :
          ((Finset.range (y₀ + n + 1)).filter (fun a => y₀ ≤ a ∧ a ∈ A ∧ y₀ + n - a ∈ B)) ∪
          ((Finset.range (y₀ + n + 1)).filter (fun a => a < y₀ ∧ a ∈ A ∧ y₀ + n - a ∈ B)) =
          (Finset.range (y₀ + n + 1)).filter (fun a => a ∈ A ∧ y₀ + n - a ∈ B) := by
        ext a; simp only [Finset.mem_union, Finset.mem_filter]; have := le_or_gt y₀ a; tauto
      have hcard := Finset.card_union_of_disjoint hdisj
      rw [hunion] at hcard
      unfold repCount
      exact_mod_cast hcard.symm
    have hr1 : repCount A B (y₀ + n) = 1 := hstab (y₀ + n) (by omega)
    rw [hr1] at hsum; push_cast at hsum; linarith
  have hlhs : dconv f₀ (dconv f₁ g₀) t = dconv f₀ h t - dconv f₀ η₁ t := by
    rw [dconv_congr_right (fun k hk => hf1g0 k hk), dconv_sub_right]
  have hrhs : dconv f₁ (dconv f₀ g₀) t = dconv f₁ h t + dconv f₁ δ t := by
    rw [dconv_congr_right (fun k hk => hf0g0 k (by omega)), dconv_add_right]
  have heq : dconv f₀ (dconv f₁ g₀) t = dconv f₁ (dconv f₀ g₀) t := by
    rw [← dconv_assoc, dconv_comm_fun f₀ f₁, dconv_assoc]
  linarith

/-- Step 2 of Lemma 5.2: `y₀ + n₀ ≤ w₀`, hence `y₀ + (N - 2 x₀) < w₀`. -/
private lemma lemma_5_2_step2 {A B : Set ℕ} (hA_inf : A.Infinite) (hB_inf : B.Infinite)
    {n₀ K N : ℕ} (hn0 : 1 ≤ n₀) (hstab : ∀ n ≥ n₀, repCount A B n = 1)
    (hL : LevelApprox A B n₀ K N)
    (hforbid : ∀ a ∈ A, N < a → ∀ b ∈ B, ¬ (a + n₀ ≤ b ∧ b + 2 * maxLe A N ≤ a + N)) :
    nextGt hA_inf N + n₀ ≤ nextGt hB_inf N := by
  classical
  set x₀ := maxLe A N
  set z₀ := maxLe B N
  set y₀ := nextGt hA_inf N
  set w₀ := nextGt hB_inf N
  have hy₀_spec := nextGt_spec hA_inf N
  have hw₀_spec := nextGt_spec hB_inf N
  have hy₀_51 := lemma_5_1 hA_inf hn0 hstab hL
  have hx₀_mem := maxLe_mem (by rcases hL.hx₀_lo with ⟨a, haA, haN, _⟩; exact ⟨a, haA, haN⟩)
  have hz₀_mem := maxLe_mem (by rcases hL.hz₀_lo with ⟨b, hbB, hbN, _⟩; exact ⟨b, hbB, hbN⟩)
  have hx₀_hi : (x₀ : ℝ) ≤ (1 / 3 + 1 / 1000 : ℝ) * (N : ℝ) := hL.hx₀_hi x₀ hx₀_mem.1 hx₀_mem.2
  have hz₀_hi : (z₀ : ℝ) ≤ (2 / 3 + 1 / 1000 : ℝ) * (N : ℝ) := hL.hz₀_hi z₀ hz₀_mem.1 hz₀_mem.2
  have hN_big : (10 ^ 7 : ℝ) * ((K : ℝ) + (errSum A B n₀ : ℝ) + (n₀ : ℝ) + 1) ≤ (N : ℝ) := by
    have hnat : 10 ^ 7 * (K + errSum A B n₀ + n₀ + 1) ≤ N := by
      have := hL.hN_large; nlinarith
    exact_mod_cast hnat
  have hN_ge_n0 : n₀ ≤ N := by
    have : (n₀ : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast this
  have hN_pos : 1 ≤ N := by omega
  have hNA : N ∉ A := fun h => by have := hL.hx₀_hi N h le_rfl; linarith
  have hNB : N ∉ B := fun h => by have := hL.hz₀_hi N h le_rfl; linarith
  by_contra hlt_w0
  push Not at hlt_w0
  set M_hi := ⌊(1 / 4 - 2 / 1000 : ℝ) * (N : ℝ)⌋₊
  set M_lo := ⌊(1 / 12 + 13 / 1000 : ℝ) * (N : ℝ)⌋₊
  set I_kill := Finset.Icc (N + M_lo) (N + M_hi)
  have hMhi_le : (M_hi : ℝ) ≤ (1 / 4 - 2 / 1000 : ℝ) * (N : ℝ) := Nat.floor_le (by linarith)
  have hMhi_gt : (1 / 4 - 2 / 1000 : ℝ) * (N : ℝ) - 1 < (M_hi : ℝ) := by
    have h1 := Nat.lt_floor_add_one ((1 / 4 - 2 / 1000 : ℝ) * (N : ℝ))
    change (1 / 4 - 2 / 1000 : ℝ) * (N : ℝ) < (M_hi : ℝ) + 1 at h1
    linarith
  have hMlo_le : (M_lo : ℝ) ≤ (1 / 12 + 13 / 1000 : ℝ) * (N : ℝ) := Nat.floor_le (by linarith)
  have hMlo_gt : (1 / 12 + 13 / 1000 : ℝ) * (N : ℝ) - 1 < (M_lo : ℝ) := by
    have h1 := Nat.lt_floor_add_one ((1 / 12 + 13 / 1000 : ℝ) * (N : ℝ))
    change (1 / 12 + 13 / 1000 : ℝ) * (N : ℝ) < (M_lo : ℝ) + 1 at h1
    linarith
  have hIkill_card : (15 / 100 : ℝ) * (N : ℝ) < (I_kill.card : ℝ) := by
    have hc : I_kill.card = N + M_hi + 1 - (N + M_lo) := Nat.card_Icc _ _
    have hle_M : M_lo ≤ M_hi := by
      have : (M_lo : ℝ) ≤ (M_hi : ℝ) := by linarith
      exact_mod_cast this
    have hc' : (I_kill.card : ℝ) = (M_hi : ℝ) + 1 - (M_lo : ℝ) := by
      rw [hc]
      have : N + M_hi + 1 - (N + M_lo) = M_hi + 1 - M_lo := by omega
      rw [this, Nat.cast_sub (by omega)]
      push_cast; ring
    linarith
  have hB_in_W : ∀ b ∈ B, N < b → b ≤ N + M_hi → b < y₀ + n₀ := by
    intro b hbB hb1 hb2
    by_contra hge
    push Not at hge
    have hbad : b + 2 * x₀ ≤ y₀ + N := by
      have hb_r : (b : ℝ) ≤ (N : ℝ) + (M_hi : ℝ) := by exact_mod_cast hb2
      have hy_r : (N : ℝ) < (y₀ : ℝ) := by exact_mod_cast hy₀_spec.1
      have : ((b + 2 * x₀ : ℕ) : ℝ) ≤ ((y₀ + N : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    exact hforbid y₀ hy₀_spec.2 hy₀_spec.1 b hbB ⟨by omega, hbad⟩
  set A_high := (Finset.Ioc N (N + M_hi)).filter (· ∈ A)
  have hA_high_card : A_high.card ≤ 2 * n₀ + C1Const A B n₀ K := by
    set A₀ := (Finset.range N).filter (· ∈ A)
    set B₀ := (Finset.range N).filter (· ∈ B)
    have hmd := (modular_difference_density hstab hN_ge_n0 hN_pos hNA hNB hL.hT_le
      (x₀ := x₀) (z₀ := z₀)
      (fun a ha haN => le_maxLe ha (le_of_lt haN))
      (fun b hb hbN => le_maxLe hb (le_of_lt hbN))).2
    set A_h1 := A_high.filter (fun a => a < w₀ + n₀)
    set A_h2 := A_high.filter (fun a => w₀ + n₀ ≤ a)
    have hsplit_card : A_high.card = A_h1.card + A_h2.card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext a; simp only [A_h1, A_h2, Finset.mem_union, Finset.mem_filter]
        have := lt_or_ge a (w₀ + n₀); tauto
      · rw [Finset.disjoint_left]; intro a h1 h2; simp only [A_h1, A_h2, Finset.mem_filter] at h1 h2; omega
    have hc1 : A_h1.card ≤ 2 * n₀ := by
      calc
        A_h1.card ≤ (Finset.Ico y₀ (y₀ + 2 * n₀)).card := by
          apply Finset.card_le_card
          intro a ha
          simp only [A_h1, A_high, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico] at ha ⊢
          have hy_le : y₀ ≤ a := nextGt_le hA_inf (N := N) ha.1.2 ha.1.1.1
          omega
        _ = 2 * n₀ := by rw [Nat.card_Ico]; omega
    have hc2 : A_h2.card ≤ C1Const A B n₀ K := by
      calc
        A_h2.card ≤ ((Finset.Icc 1 (N - 1 - z₀)).filter (fun d => ¬ ∃ a ∈ A₀, ∃ b ∈ B₀, a = b + d)).card := by
          apply Finset.card_le_card_of_injOn (fun a => a - w₀)
          · intro a ha
            simp only [A_h2, A_high, Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at ha ⊢
            have ha_le : a - w₀ ≤ N - 1 - z₀ := by
              have ha_r : (a : ℝ) ≤ (N : ℝ) + (M_hi : ℝ) := by exact_mod_cast ha.1.1.2
              have hw_r : (N : ℝ) < (w₀ : ℝ) := by exact_mod_cast hw₀_spec.1
              have hz_lt : z₀ + 1 ≤ N := by
                have : (z₀ : ℝ) + 1 ≤ (N : ℝ) := by linarith
                exact_mod_cast this
              have ha_ge_w : w₀ ≤ a := by omega
              have : ((a - w₀ : ℕ) : ℝ) ≤ ((N - 1 - z₀ : ℕ) : ℝ) := by
                rw [Nat.cast_sub ha_ge_w, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
                push_cast; linarith
              exact_mod_cast this
            refine ⟨⟨by omega, ha_le⟩, ?_⟩
            rintro ⟨a₀, ha₀, b₀, hb₀, heq⟩
            simp only [A₀, B₀, Finset.mem_filter, Finset.mem_range] at ha₀ hb₀
            have hdiff : w₀ + a₀ = b₀ + a := by omega
            have hne : a ≠ a₀ ∨ w₀ ≠ b₀ := Or.inl (by omega)
            have hsmall := unique_large_diff hstab ha.1.2 ha₀.2 hw₀_spec.2 hb₀.2 hdiff hne
            omega
          · intro a₁ h1 a₂ h2 heq
            simp only [A_h2, Finset.mem_coe, Finset.mem_filter] at h1 h2
            dsimp only at heq; omega
        _ ≤ C1Const A B n₀ K := hmd
    omega
  -- Bound |W| ≤ 4 * countNat B N
  set W := (Finset.Ioc N (y₀ + n₀)).filter (· ∈ B)
  have hW_card : (W.card : ℝ) ≤ 4 * (countNat B N : ℝ) := by
    have hW_le : W.card ≤ countNat B (y₀ + n₀) := by
      unfold countNat; apply Finset.card_le_card
      intro b hb; simp only [W, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hb ⊢
      exact ⟨by omega, hb.2⟩
    have hprod_y0 := hL.hprod_le (y₀ + n₀) (by omega)
    have hA_mono : countNat A N ≤ countNat A (y₀ + n₀) := by
      unfold countNat; apply Finset.card_le_card
      intro a ha; simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢; exact ⟨by omega, ha.2⟩
    have hprod_N_real : (N : ℝ) / 2 ≤ (countNat A N : ℝ) * (countNat B N : ℝ) := by
      have hprod_N := countNat_mul_eq_N_add_c_add_T hstab hN_ge_n0
      have hcast : (countNat A N : ℝ) * (countNat B N : ℝ) =
          (N : ℝ) + 1 + (errSigned A B n₀ : ℝ) + (crossExcess A B N : ℝ) := by exact_mod_cast hprod_N
      have hc : -(errSum A B n₀ : ℝ) ≤ (errSigned A B n₀ : ℝ) := by
        exact_mod_cast (abs_le.mp (abs_errSigned_le_errSum A B n₀)).1
      have hT_nn : (0 : ℝ) ≤ (crossExcess A B N : ℝ) := Nat.cast_nonneg _
      linarith
    have hA_pos : (0 : ℝ) < (countNat A N : ℝ) := by
      have h1 : 1 ≤ countNat A N := by have := hL.hA_large; omega
      have : (1 : ℝ) ≤ (countNat A N : ℝ) := by exact_mod_cast h1
      linarith
    have hA_mono_r : (countNat A N : ℝ) ≤ (countNat A (y₀ + n₀) : ℝ) := by exact_mod_cast hA_mono
    have hB_y0_le : (countNat A N : ℝ) * (countNat B (y₀ + n₀) : ℝ) ≤ 2 * (N : ℝ) := by
      have hy_r : ((y₀ + n₀ : ℕ) : ℝ) ≤ (1 + 9 / 1000 : ℝ) * (N : ℝ) := by push_cast; linarith
      have hmul1 : (countNat A N : ℝ) * (countNat B (y₀ + n₀) : ℝ) ≤
          (countNat A (y₀ + n₀) : ℝ) * (countNat B (y₀ + n₀) : ℝ) :=
        mul_le_mul_of_nonneg_right hA_mono_r (Nat.cast_nonneg _)
      linarith
    have h4 : (countNat A N : ℝ) * (countNat B (y₀ + n₀) : ℝ) ≤
        (countNat A N : ℝ) * (4 * (countNat B N : ℝ)) := by linarith
    have hB_le4 : (countNat B (y₀ + n₀) : ℝ) ≤ 4 * (countNat B N : ℝ) :=
      le_of_mul_le_mul_left h4 hA_pos
    have hW_r : (W.card : ℝ) ≤ (countNat B (y₀ + n₀) : ℝ) := by exact_mod_cast hW_le
    linarith
  -- Cover I_kill by S1 ∪ S2 ∪ S3
  set A₀_fin := (Finset.range (N + 1)).filter (· ∈ A)
  set B₀_fin := (Finset.range (N + 1)).filter (· ∈ B)
  set A_gap := (Finset.Ioc ⌊(1 / 12 + 3 / 1000 : ℝ) * (N : ℝ)⌋₊ M_hi).filter (· ∈ A)
  set S1 := ((A₀_fin ×ˢ B₀_fin).filter (fun p => N < p.1 + p.2)).image (fun p => p.1 + p.2)
  set S2 := (A_high ×ˢ B₀_fin).image (fun p => p.1 + p.2)
  set S3 := (A_gap ×ˢ W).image (fun p => p.1 + p.2)
  have hMlo_pos : 1 ≤ M_lo := by
    have : (1 : ℝ) ≤ (M_lo : ℝ) := by linarith
    exact_mod_cast this
  have hcover : I_kill ⊆ S1 ∪ S2 ∪ S3 := by
    intro n hn
    simp only [I_kill, Finset.mem_Icc] at hn
    have hr1 : repCount A B n = 1 := hstab n (by omega)
    have hpos : 0 < repCount A B n := by omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    set b := n - a
    have haA : a ∈ A := ha.2.1
    have hbB : b ∈ B := ha.2.2
    have hab : a + b = n := by omega
    by_cases haN : a ≤ N
    · by_cases hbN : b ≤ N
      · apply Finset.mem_union_left; apply Finset.mem_union_left
        rw [Finset.mem_image]
        refine ⟨(a, b), ?_, hab⟩
        simp only [Finset.mem_filter, Finset.mem_product, A₀_fin, B₀_fin, Finset.mem_range]
        exact ⟨⟨⟨by omega, haA⟩, ⟨by omega, hbB⟩⟩, by omega⟩
      · apply Finset.mem_union_right
        rw [Finset.mem_image]
        refine ⟨(a, b), ?_, hab⟩
        have hb_gt : N < b := by omega
        have hb_le : b ≤ N + M_hi := by omega
        have hb_W : b < y₀ + n₀ := hB_in_W b hbB hb_gt hb_le
        have ha_gt_lo : ⌊(1 / 12 + 3 / 1000 : ℝ) * (N : ℝ)⌋₊ < a := by
          have hfl : (⌊(1 / 12 + 3 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) ≤ (1 / 12 + 3 / 1000 : ℝ) * (N : ℝ) :=
            Nat.floor_le (by linarith)
          have hab_r : (a : ℝ) + (b : ℝ) = (n : ℝ) := by exact_mod_cast hab
          have hn_ge : (N : ℝ) + (M_lo : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
          have hb_r : (b : ℝ) < (y₀ : ℝ) + (n₀ : ℝ) := by exact_mod_cast hb_W
          have : (⌊(1 / 12 + 3 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) < (a : ℝ) := by linarith
          exact_mod_cast this
        simp only [Finset.mem_product, A_gap, W, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨⟨ha_gt_lo, by omega⟩, haA⟩, ⟨⟨hb_gt, by omega⟩, hbB⟩⟩
    · have hbN : b ≤ N := by
        by_contra hbgt
        have h2N : 2 * N + 2 ≤ n := by omega
        have hcast : 2 * (N : ℝ) + 2 ≤ (N : ℝ) + (M_hi : ℝ) := by exact_mod_cast (le_trans h2N hn.2)
        linarith
      apply Finset.mem_union_left; apply Finset.mem_union_right
      rw [Finset.mem_image]
      refine ⟨(a, b), ?_, hab⟩
      simp only [Finset.mem_product, A_high, B₀_fin, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
      exact ⟨⟨⟨by omega, by omega⟩, haA⟩, ⟨by omega, hbB⟩⟩
  have hS1_card : S1.card ≤ K := by
    have hle_T : ((A₀_fin ×ˢ B₀_fin).filter (fun p => N < p.1 + p.2)).card ≤ crossExcess A B N := by
      have hmap : ∀ p ∈ (A₀_fin ×ˢ B₀_fin).filter (fun p => N < p.1 + p.2),
          p.1 + p.2 - (N + 1) ∈ Finset.range N := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, A₀_fin, B₀_fin, Finset.mem_range] at hp ⊢
        omega
      rw [Finset.card_eq_sum_card_fiberwise hmap]
      unfold crossExcess
      apply Finset.sum_le_sum
      intro m _
      unfold repTrunc
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, A₀_fin, B₀_fin, Finset.mem_range] at hp ⊢
        refine ⟨hp.1.1.1.1, hp.1.1.1.2, by omega, by omega, ?_⟩
        have : N + 1 + m - p.1 = p.2 := by omega
        rw [this]; exact hp.1.1.2.2
      · rintro ⟨a1, b1⟩ h1 ⟨a2, b2⟩ h2 heq
        simp only [Finset.mem_coe, Finset.mem_filter] at h1 h2
        dsimp only at heq; subst heq
        have hb : b1 = b2 := by omega
        rw [hb]
    exact le_trans Finset.card_image_le (le_trans hle_T hL.hT_le)
  have hS2_real : (S2.card : ℝ) ≤ (1 / 1000 : ℝ) * (N : ℝ) := by
    have hS2_card : S2.card ≤ (2 * n₀ + C1Const A B n₀ K) * countNat B N := by
      calc S2.card ≤ (A_high ×ˢ B₀_fin).card := Finset.card_image_le
        _ = A_high.card * countNat B N := by rw [Finset.card_product]; rfl
        _ ≤ _ := Nat.mul_le_mul_right _ hA_high_card
    have hprod_N := hL.hprod_le N le_rfl
    have hAl : (10 ^ 7 : ℝ) * ((C1Const A B n₀ K : ℝ) + (K : ℝ) + (errSum A B n₀ : ℝ) + (n₀ : ℝ) + 1) ≤
        (countNat A N : ℝ) := by exact_mod_cast hL.hA_large
    have hS2_r : (S2.card : ℝ) ≤ (2 * (n₀ : ℝ) + (C1Const A B n₀ K : ℝ)) * (countNat B N : ℝ) := by
      exact_mod_cast hS2_card
    have hmul : (10 ^ 7 : ℝ) * ((C1Const A B n₀ K : ℝ) + (K : ℝ) + (errSum A B n₀ : ℝ) + (n₀ : ℝ) + 1) *
        (countNat B N : ℝ) ≤ (countNat A N : ℝ) * (countNat B N : ℝ) :=
      mul_le_mul_of_nonneg_right hAl (Nat.cast_nonneg _)
    have hcoef : (2 * (n₀ : ℝ) + (C1Const A B n₀ K : ℝ)) * (countNat B N : ℝ) ≤
        2 * ((C1Const A B n₀ K : ℝ) + (K : ℝ) + (errSum A B n₀ : ℝ) + (n₀ : ℝ) + 1) * (countNat B N : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _); linarith
    linarith
  have hS3_card : (S3.card : ℝ) ≤ (13 / 1000 : ℝ) * (N : ℝ) := by
    set L := ⌊(1 / 12 + 3 / 1000 : ℝ) * (N : ℝ)⌋₊
    have hAgap_card : (A_gap.card : ℝ) ≤ (2 / 1000 : ℝ) * (countNat A N : ℝ) := by
      have hL_le : L ≤ M_hi := by
        have h1 : (L : ℝ) ≤ (1 / 12 + 3 / 1000 : ℝ) * (N : ℝ) := Nat.floor_le (by linarith)
        have : (L : ℝ) ≤ (M_hi : ℝ) := by linarith
        exact_mod_cast this
      have hdiff_eq : A_gap.card + countNat A L = countNat A M_hi := by
        unfold countNat
        rw [← Finset.card_union_of_disjoint]
        · congr 1; ext a
          simp only [A_gap, Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
          constructor
          · rintro (⟨⟨h1, h2⟩, hA⟩ | ⟨h1, hA⟩)
            · exact ⟨by omega, hA⟩
            · exact ⟨by omega, hA⟩
          · rintro ⟨h1, hA⟩
            by_cases hgt : L < a
            · left; exact ⟨⟨hgt, by omega⟩, hA⟩
            · right; exact ⟨by omega, hA⟩
        · rw [Finset.disjoint_left]; intro a h1 h2
          simp only [A_gap, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at h1 h2; omega
      have hcast : (A_gap.card : ℝ) = (countNat A M_hi : ℝ) - (countNat A L : ℝ) := by
        have : (A_gap.card : ℝ) + (countNat A L : ℝ) = (countNat A M_hi : ℝ) := by exact_mod_cast hdiff_eq
        linarith
      rw [hcast]; exact hL.hgap_A
    have h1 : S3.card ≤ A_gap.card * W.card := by
      calc S3.card ≤ (A_gap ×ˢ W).card := Finset.card_image_le
        _ = A_gap.card * W.card := Finset.card_product _ _
    have h1r : (S3.card : ℝ) ≤ (A_gap.card : ℝ) * (W.card : ℝ) := by exact_mod_cast h1
    have hmul := mul_le_mul hAgap_card hW_card (Nat.cast_nonneg _) (by positivity)
    have hprod_N := hL.hprod_le N le_rfl
    linarith
  have hcov_card : I_kill.card ≤ S1.card + S2.card + S3.card := by
    calc I_kill.card ≤ (S1 ∪ S2 ∪ S3).card := Finset.card_le_card hcover
      _ ≤ (S1 ∪ S2).card + S3.card := Finset.card_union_le _ _
      _ ≤ S1.card + S2.card + S3.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hcov_r : (I_kill.card : ℝ) ≤ (S1.card : ℝ) + (S2.card : ℝ) + (S3.card : ℝ) := by exact_mod_cast hcov_card
  have hS1_r : (S1.card : ℝ) ≤ (K : ℝ) := by exact_mod_cast hS1_card
  linarith

/-- **Lemma 5.2:** `w₀ > y₀ + (5/8) N`. -/
theorem lemma_5_2 {A B : Set ℕ} (hA_inf : A.Infinite) (hB_inf : B.Infinite) {n₀ K N : ℕ}
    (hn0 : 1 ≤ n₀) (hstab : ∀ n ≥ n₀, repCount A B n = 1)
    (hL : LevelApprox A B n₀ K N) :
    (nextGt hA_inf N : ℝ) + (5 / 8 : ℝ) * (N : ℝ) < (nextGt hB_inf N : ℝ) := by
  classical
  set x₀ := maxLe A N
  set y₀ := nextGt hA_inf N
  set w₀ := nextGt hB_inf N
  have hy₀_spec := nextGt_spec hA_inf N
  have hw₀_spec := nextGt_spec hB_inf N
  have hx₀_mem := maxLe_mem (by rcases hL.hx₀_lo with ⟨a, haA, haN, _⟩; exact ⟨a, haA, haN⟩)
  have hx₀_hi : (x₀ : ℝ) ≤ (1 / 3 + 1 / 1000 : ℝ) * (N : ℝ) := hL.hx₀_hi x₀ hx₀_mem.1 hx₀_mem.2
  have hN_big : (10 ^ 7 : ℝ) * ((K : ℝ) + (errSum A B n₀ : ℝ) + (n₀ : ℝ) + 1) ≤ (N : ℝ) := by
    have hnat : 10 ^ 7 * (K + errSum A B n₀ + n₀ + 1) ≤ N := by
      have := hL.hN_large; nlinarith
    exact_mod_cast hnat
  have hN_ge_n0 : n₀ ≤ N := by
    have : (n₀ : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast this
  have hforbid : ∀ a ∈ A, N < a → ∀ b ∈ B, ¬ (a + n₀ ≤ b ∧ b + 2 * x₀ ≤ a + N) := by
    intro a haA haGt b hbB ⟨h1, h2⟩
    obtain ⟨a₀, ha₀A, ha₀_le, b₀, hb₀B, hb₀_le, hba⟩ :=
      diff_interval_in_B0_sub_A0 hstab hx₀_mem.1 hx₀_mem.2 (fun u hu huN => le_maxLe hu huN)
        (d := b - a) (by omega) (by omega)
    have hdiff : b + a₀ = b₀ + a := by omega
    have hne : a ≠ a₀ ∨ b ≠ b₀ := Or.inl (by omega)
    have hsmall := unique_large_diff hstab haA ha₀A hbB hb₀B hdiff hne
    omega
  have hw₀_gt_y0_n0 : y₀ + n₀ ≤ w₀ := lemma_5_2_step2 hA_inf hB_inf hn0 hstab hL hforbid
  have hw₀_gt_third : y₀ + (N - 2 * x₀) < w₀ := by
    by_contra hle
    exact hforbid y₀ hy₀_spec.2 hy₀_spec.1 w₀ hw₀_spec.2 ⟨hw₀_gt_y0_n0, by omega⟩
  -- Step 3 helper: (5.5) bounds on countNat A (y₀ + t) - countNat A x₀ - countNat A t
  have h55 : ∀ t ≤ N, y₀ + t < w₀ →
      -(errSum A B n₀ : ℤ) - (K : ℤ) ≤
        (countNat A (y₀ + t) : ℤ) - (countNat A x₀ : ℤ) - (countNat A t : ℤ) ∧
      (countNat A (y₀ + t) : ℤ) - (countNat A x₀ : ℤ) - (countNat A t : ℤ) ≤
        (errSum A B n₀ : ℤ) := by
    intro t htN htw
    have hident := conv_identity_55 hA_inf hB_inf hstab hN_ge_n0 htN htw
    dsimp only at hident
    set f₀ : ℕ → ℤ := fun n => if n ≤ x₀ ∧ n ∈ A then 1 else 0
    set f₁ : ℕ → ℤ := fun n => if y₀ + n ∈ A then 1 else 0
    set h : ℕ → ℤ := fun _ => 1
    set δ : ℕ → ℤ := fun n => (repCount A B n : ℤ) - 1
    set η₁ : ℕ → ℤ := fun n => (repTrunc A B N (y₀ + n) : ℤ)
    have hf1h : dconv f₁ h t = (countNat A (y₀ + t) : ℤ) - (countNat A x₀ : ℤ) := by
      unfold dconv h
      have hsum : ∑ i ∈ Finset.range (t + 1), f₁ i * 1 =
          (((Finset.range (y₀ + t + 1)).filter (fun a => y₀ ≤ a ∧ a ∈ A)).card : ℤ) := by
        have hterm : ∀ i ∈ Finset.range (t + 1), f₁ i * 1 = if y₀ + i ∈ A then (1 : ℤ) else 0 := by
          intro i _; simp [f₁]
        rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        congr 1
        apply Finset.card_bij (fun i _ => y₀ + i)
        · intro i hi; simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢; exact ⟨by omega, by omega, hi.2⟩
        · intro i₁ _ i₂ _ heq; omega
        · intro a ha; simp only [Finset.mem_filter, Finset.mem_range] at ha
          refine ⟨a - y₀, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, by omega⟩
          have hadd : y₀ + (a - y₀) = a := by omega
          rw [hadd]; exact ha.2.2
      rw [hsum]
      have hdisj : Disjoint
          ((Finset.range (y₀ + t + 1)).filter (fun a => y₀ ≤ a ∧ a ∈ A))
          ((Finset.range (x₀ + 1)).filter (· ∈ A)) := by
        rw [Finset.disjoint_left]; intro a h1 h2
        simp only [Finset.mem_filter, Finset.mem_range] at h1 h2; omega
      have hunion :
          ((Finset.range (y₀ + t + 1)).filter (fun a => y₀ ≤ a ∧ a ∈ A)) ∪
          ((Finset.range (x₀ + 1)).filter (· ∈ A)) =
          (Finset.range (y₀ + t + 1)).filter (· ∈ A) := by
        ext a; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro (⟨h1, _, h3⟩ | ⟨h1, h2⟩)
          · exact ⟨h1, h3⟩
          · exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          by_cases hge : y₀ ≤ a
          · left; exact ⟨h1, hge, h2⟩
          · right
            have haN : a ≤ N := by
              by_contra hgt; have := nextGt_le hA_inf (N := N) h2 (by omega); omega
            exact ⟨by have := le_maxLe h2 haN; omega, h2⟩
      have hcard := Finset.card_union_of_disjoint hdisj
      rw [hunion] at hcard
      unfold countNat
      have hcast : (((Finset.range (y₀ + t + 1)).filter (fun a => y₀ ≤ a ∧ a ∈ A)).card : ℤ) +
          (((Finset.range (x₀ + 1)).filter (· ∈ A)).card : ℤ) =
          (((Finset.range (y₀ + t + 1)).filter (· ∈ A)).card : ℤ) := by exact_mod_cast hcard.symm
      linarith
    have hf0h : dconv f₀ h t = (countNat A t : ℤ) := by
      unfold dconv h countNat
      have hterm : ∀ i ∈ Finset.range (t + 1), f₀ i * 1 = if i ∈ A then (1 : ℤ) else 0 := by
        intro i hi
        have hi_le : i ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        simp only [f₀]
        by_cases ha : i ∈ A
        · have : i ≤ x₀ := le_maxLe ha (by omega); simp [ha, this]
        · simp [ha]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hδ_bd : |dconv f₁ δ t| ≤ (errSum A B n₀ : ℤ) := by
      unfold dconv
      calc
        |∑ i ∈ Finset.range (t + 1), f₁ i * δ (t - i)|
            ≤ ∑ i ∈ Finset.range (t + 1), |f₁ i * δ (t - i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range (t + 1), |δ (t - i)| := by
              apply Finset.sum_le_sum; intro i _
              rw [abs_mul]; simp only [f₁]; split_ifs <;> simp
        _ = ∑ j ∈ Finset.range (t + 1), |δ j| := by
              apply Finset.sum_bij (fun i _ => t - i)
              · intro i hi; rw [Finset.mem_range] at hi ⊢; omega
              · intro i₁ h1 i₂ h2 heq; rw [Finset.mem_range] at h1 h2; omega
              · intro j hj; rw [Finset.mem_range] at hj; exact ⟨t - j, Finset.mem_range.mpr (by omega), by omega⟩
              · intro _ _; rfl
        _ ≤ (errSum A B n₀ : ℤ) := by
              unfold errSum δ; push_cast
              by_cases hle : t + 1 ≤ n₀
              · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hle) (fun _ _ _ => abs_nonneg _)
              · have hsp : t + 1 = n₀ + (t + 1 - n₀) := by omega
                rw [hsp, Finset.sum_range_add]
                have hz : ∑ m ∈ Finset.range (t + 1 - n₀), |((repCount A B (n₀ + m) : ℤ) - 1)| = 0 := by
                  apply Finset.sum_eq_zero; intro m _; simp [hstab (n₀ + m) (by omega)]
                rw [hz, add_zero]
    have hη_nn : 0 ≤ dconv f₀ η₁ t := by
      unfold dconv; apply Finset.sum_nonneg; intro i _
      have h1 : 0 ≤ f₀ i := by simp only [f₀]; split_ifs <;> norm_num
      exact mul_nonneg h1 (Nat.cast_nonneg _)
    have hη_le : dconv f₀ η₁ t ≤ (K : ℤ) := by
      unfold dconv
      calc
        ∑ i ∈ Finset.range (t + 1), f₀ i * η₁ (t - i)
            ≤ ∑ i ∈ Finset.range (t + 1), η₁ (t - i) := by
              apply Finset.sum_le_sum; intro i _
              have h2 : 0 ≤ η₁ (t - i) := Nat.cast_nonneg _
              simp only [f₀]; split_ifs <;> linarith
        _ = ∑ j ∈ Finset.range (t + 1), η₁ j := by
              apply Finset.sum_bij (fun i _ => t - i)
              · intro i hi; rw [Finset.mem_range] at hi ⊢; omega
              · intro i₁ h1 i₂ h2 heq; rw [Finset.mem_range] at h1 h2; omega
              · intro j hj; rw [Finset.mem_range] at hj; exact ⟨t - j, Finset.mem_range.mpr (by omega), by omega⟩
              · intro _ _; rfl
        _ ≤ (crossExcess A B N : ℤ) := by
              unfold η₁ crossExcess; push_cast
              have hsum_le : ∑ j ∈ Finset.range (t + 1), repTrunc A B N (y₀ + j) ≤
                  ∑ m ∈ Finset.range N, repTrunc A B N (N + 1 + m) := by
                set R0 := (Finset.range (t + 1)).filter (fun j => y₀ - (N + 1) + j < N)
                have hpos_le : ∑ j ∈ R0, repTrunc A B N (y₀ + j) =
                    ∑ j ∈ Finset.range (t + 1), repTrunc A B N (y₀ + j) := by
                  apply Finset.sum_subset (Finset.filter_subset _ _)
                  intro j hj hnot
                  simp only [Finset.mem_filter, hj, true_and] at hnot
                  exact repTrunc_eq_zero_of_gt A B (by omega)
                rw [← hpos_le]
                have himg : R0.image (fun j => y₀ - (N + 1) + j) ⊆ Finset.range N := by
                  intro m hm; rcases Finset.mem_image.mp hm with ⟨j, hj, rfl⟩
                  exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
                calc
                  ∑ j ∈ R0, repTrunc A B N (y₀ + j)
                      = ∑ m ∈ R0.image (fun j => y₀ - (N + 1) + j), repTrunc A B N (N + 1 + m) := by
                        rw [Finset.sum_image]
                        · apply Finset.sum_congr rfl; intro j _; congr 1; omega
                        · intro j₁ _ j₂ _ heq; dsimp only at heq; omega
                  _ ≤ ∑ m ∈ Finset.range N, repTrunc A B N (N + 1 + m) := Finset.sum_le_sum_of_subset himg
              exact_mod_cast hsum_le
        _ ≤ (K : ℤ) := by exact_mod_cast hL.hT_le
    rw [hf1h, hf0h] at hident
    have hδ_pair := abs_le.mp hδ_bd
    constructor <;> linarith
  -- Helper: extract an element of A in (y₀ + t_lo, y₀ + t_hi] from block mass ≥ 248/1000
  have hextract : ∀ t_lo t_hi : ℕ, t_lo ≤ t_hi → t_hi ≤ N → y₀ + t_hi < w₀ →
      (248 / 1000 : ℝ) * (countNat A N : ℝ) ≤ (countNat A t_hi : ℝ) - (countNat A t_lo : ℝ) →
      ∃ a ∈ A, y₀ + t_lo < a ∧ a ≤ y₀ + t_hi := by
    intro t_lo t_hi hle htN htw hblk
    have hb1 := h55 t_lo (by omega) (by omega)
    have hb2 := h55 t_hi htN htw
    have hA_big : (10 ^ 7 : ℝ) * ((K : ℝ) + (errSum A B n₀ : ℝ) + (n₀ : ℝ) + 1) ≤ (countNat A N : ℝ) := by
      have hnat : 10 ^ 7 * (K + errSum A B n₀ + n₀ + 1) ≤ countNat A N := by
        have := hL.hA_large; omega
      exact_mod_cast hnat
    have hb1_r : (countNat A (y₀ + t_lo) : ℝ) - (countNat A x₀ : ℝ) - (countNat A t_lo : ℝ) ≤ (errSum A B n₀ : ℝ) := by
      exact_mod_cast hb1.2
    have hb2_r : -(errSum A B n₀ : ℝ) - (K : ℝ) ≤ (countNat A (y₀ + t_hi) : ℝ) - (countNat A x₀ : ℝ) - (countNat A t_hi : ℝ) := by
      exact_mod_cast hb2.1
    have hdiff_pos : countNat A (y₀ + t_lo) < countNat A (y₀ + t_hi) := by
      have : (countNat A (y₀ + t_lo) : ℝ) < (countNat A (y₀ + t_hi) : ℝ) := by linarith
      exact_mod_cast this
    by_contra hno; push Not at hno
    have hle_cnt : countNat A (y₀ + t_hi) ≤ countNat A (y₀ + t_lo) := by
      unfold countNat; apply Finset.card_le_card
      intro a ha; simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
      refine ⟨?_, ha.2⟩
      by_contra hgt; have := hno a ha.2 (by omega); omega
    omega
  -- Substep 3a: w₀ > y₀ + (3/8) N
  have hw₀_38 : (y₀ : ℝ) + (3 / 8 : ℝ) * (N : ℝ) < (w₀ : ℝ) := by
    by_contra hle38; push Not at hle38
    set t₁ := ⌊(1 / 16 - 1 / 1000 : ℝ) * (N : ℝ)⌋₊
    set t₂ := ⌊(1 / 12 + 1 / 1000 : ℝ) * (N : ℝ)⌋₊
    have ht1_le : (t₁ : ℝ) ≤ (1 / 16 - 1 / 1000 : ℝ) * (N : ℝ) := Nat.floor_le (by linarith)
    have ht1_gt : (1 / 16 - 1 / 1000 : ℝ) * (N : ℝ) - 1 < (t₁ : ℝ) := by
      have h1 := Nat.lt_floor_add_one ((1 / 16 - 1 / 1000 : ℝ) * (N : ℝ))
      change (1 / 16 - 1 / 1000 : ℝ) * (N : ℝ) < (t₁ : ℝ) + 1 at h1; linarith
    have ht2_le : (t₂ : ℝ) ≤ (1 / 12 + 1 / 1000 : ℝ) * (N : ℝ) := Nat.floor_le (by linarith)
    have h2x : 2 * x₀ ≤ N := by
      have : 2 * (x₀ : ℝ) ≤ (N : ℝ) := by linarith
      exact_mod_cast this
    have hw_third_r : (y₀ : ℝ) + ((N : ℝ) - 2 * (x₀ : ℝ)) < (w₀ : ℝ) := by
      have : ((y₀ + (N - 2 * x₀) : ℕ) : ℝ) < (w₀ : ℝ) := by exact_mod_cast hw₀_gt_third
      rw [Nat.cast_add, Nat.cast_sub h2x, Nat.cast_mul] at this
      push_cast at this; linarith
    obtain ⟨a₁, ha₁A, ha₁_gt, ha₁_le⟩ := hextract t₁ t₂
      (by have : (t₁ : ℝ) ≤ (t₂ : ℝ) := by
            have h2 := Nat.lt_floor_add_one ((1 / 12 + 1 / 1000 : ℝ) * (N : ℝ))
            change (1 / 12 + 1 / 1000 : ℝ) * (N : ℝ) < (t₂ : ℝ) + 1 at h2; linarith
          exact_mod_cast this)
      (by have : (t₂ : ℝ) ≤ (N : ℝ) := by linarith
          exact_mod_cast this)
      (by have : ((y₀ + t₂ : ℕ) : ℝ) < (w₀ : ℝ) := by push_cast; linarith
          exact_mod_cast this)
      hL.hblock1_A
    have hbad1 : a₁ + n₀ ≤ w₀ := by
      have ha1_r : (a₁ : ℝ) ≤ (y₀ : ℝ) + (t₂ : ℝ) := by exact_mod_cast ha₁_le
      have : ((a₁ + n₀ : ℕ) : ℝ) ≤ (w₀ : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hbad2 : w₀ + 2 * x₀ ≤ a₁ + N := by
      have ha1_r : (y₀ : ℝ) + (t₁ : ℝ) < (a₁ : ℝ) := by exact_mod_cast ha₁_gt
      have : ((w₀ + 2 * x₀ : ℕ) : ℝ) ≤ ((a₁ + N : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    exact hforbid a₁ ha₁A (by omega) w₀ hw₀_spec.2 ⟨hbad1, hbad2⟩
  -- Substep 3b: w₀ > y₀ + (5/8) N
  by_contra hle58; push Not at hle58
  set t₃ := ⌊(5 / 16 - 1 / 1000 : ℝ) * (N : ℝ)⌋₊
  set t₄ := ⌊(1 / 3 + 1 / 1000 : ℝ) * (N : ℝ)⌋₊
  have ht3_le : (t₃ : ℝ) ≤ (5 / 16 - 1 / 1000 : ℝ) * (N : ℝ) := Nat.floor_le (by linarith)
  have ht3_gt : (5 / 16 - 1 / 1000 : ℝ) * (N : ℝ) - 1 < (t₃ : ℝ) := by
    have h1 := Nat.lt_floor_add_one ((5 / 16 - 1 / 1000 : ℝ) * (N : ℝ))
    change (5 / 16 - 1 / 1000 : ℝ) * (N : ℝ) < (t₃ : ℝ) + 1 at h1; linarith
  have ht4_le : (t₄ : ℝ) ≤ (1 / 3 + 1 / 1000 : ℝ) * (N : ℝ) := Nat.floor_le (by linarith)
  obtain ⟨a₂, ha₂A, ha₂_gt, ha₂_le⟩ := hextract t₃ t₄
    (by have : (t₃ : ℝ) ≤ (t₄ : ℝ) := by
          have h2 := Nat.lt_floor_add_one ((1 / 3 + 1 / 1000 : ℝ) * (N : ℝ))
          change (1 / 3 + 1 / 1000 : ℝ) * (N : ℝ) < (t₄ : ℝ) + 1 at h2; linarith
        exact_mod_cast this)
    (by have : (t₄ : ℝ) ≤ (N : ℝ) := by linarith
        exact_mod_cast this)
    (by have : ((y₀ + t₄ : ℕ) : ℝ) < (w₀ : ℝ) := by push_cast; linarith
        exact_mod_cast this)
    hL.hblock2_A
  have hbad1 : a₂ + n₀ ≤ w₀ := by
    have ha2_r : (a₂ : ℝ) ≤ (y₀ : ℝ) + (t₄ : ℝ) := by exact_mod_cast ha₂_le
    have : ((a₂ + n₀ : ℕ) : ℝ) ≤ (w₀ : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hbad2 : w₀ + 2 * x₀ ≤ a₂ + N := by
    have ha2_r : (y₀ : ℝ) + (t₃ : ℝ) < (a₂ : ℝ) := by exact_mod_cast ha₂_gt
    have : ((w₀ + 2 * x₀ : ℕ) : ℝ) ≤ ((a₂ + N : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  exact hforbid a₂ ha₂A (by omega) w₀ hw₀_spec.2 ⟨hbad1, hbad2⟩

/-! ### Proposition 5.3: Exact Forward Doubling Step and Quadratic Recurrence -/

/-- Shifted generating polynomial `P_{A₁'}(X) = ∑_{m ≤ T₁, y₀ + m ∈ A} X^m`. -/
def shiftedTruncPoly (A : Set ℕ) (y₀ T₁ : ℕ) : ℤ[X] :=
  letI := Classical.decPred (fun m => y₀ + m ∈ A)
  ∑ m ∈ (Finset.range (T₁ + 1)).filter (fun m => y₀ + m ∈ A), (X : ℤ[X]) ^ m

lemma shiftedTruncPoly_coeff (A : Set ℕ) (y₀ T₁ m : ℕ) :
    letI := Classical.decPred (fun m => y₀ + m ∈ A)
    (shiftedTruncPoly A y₀ T₁).coeff m = if m ≤ T₁ ∧ y₀ + m ∈ A then 1 else 0 := by
  classical
  unfold shiftedTruncPoly
  rw [finsetSum_coeff]
  simp only [coeff_X_pow]
  by_cases hcond : m ≤ T₁ ∧ y₀ + m ∈ A
  · rw [Finset.sum_eq_single m]
    · simp [hcond]
    · intro b _ hbm; simp [hbm.symm]
    · intro hnot
      have hmem : m ∈ (Finset.range (T₁ + 1)).filter (fun k => y₀ + k ∈ A) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hcond.2⟩
      exact absurd hmem hnot
  · rw [ite_eq_right_iff.mpr (fun hh => absurd hh hcond)]
    apply Finset.sum_eq_zero; intro b hb
    simp only [Finset.mem_filter, Finset.mem_range] at hb
    have hbm : m ≠ b := by intro heq; subst heq; exact hcond ⟨by omega, hb.2⟩
    simp [hbm]

/-- Intermediate output of Step 1 of Proposition 5.3 (exact zero-run + identities (5.6)). -/
private structure DoublingStep1Data (A B : Set ℕ) (hA_inf : A.Infinite) (n₀ N : ℕ) where
  T₁ : ℕ
  T₂ : ℕ
  Hη₁ : ℤ[X]
  U₁ : ℤ[X]
  hU₁_def : U₁ = 1 - (1 - X) * Hη₁
  hHη₁_coeff : ∀ m, Hη₁.coeff m = (repTrunc A B N (nextGt hA_inf N + m) : ℤ)
  hT1_lt_T2 : T₁ + n₀ < T₂
  hT1_upper : (T₁ : ℝ) ≤ (1 / 3 + 4 / 1000 : ℝ) * (N : ℝ) + 1
  hA_gap_zero : ∀ t, T₁ + 1 ≤ t → t ≤ T₂ → nextGt hA_inf N + t ∉ A
  hPA1_V : shiftedTruncPoly A (nextGt hA_inf N) T₁ * VPoly A B n₀ = truncPoly A N * U₁
  hWN_U1 : WPoly A B N = X ^ (nextGt hA_inf N - (N + 1)) * U₁
  hHη₁_eval_le : Hη₁.eval 1 ≤ (crossExcess A B N : ℤ)

private lemma forward_doubling_step1 {A B : Set ℕ} (hA_inf : A.Infinite) (hB_inf : B.Infinite)
    {n₀ K N : ℕ} (hn0 : 1 ≤ n₀) (hstab : ∀ n ≥ n₀, repCount A B n = 1)
    (hL : LevelApprox A B n₀ K N) :
    Nonempty (DoublingStep1Data A B hA_inf n₀ N) := by
  classical
  set x₀ := maxLe A N
  set z₀ := maxLe B N
  set y₀ := nextGt hA_inf N
  set w₀ := nextGt hB_inf N
  have hy₀_spec := nextGt_spec hA_inf N
  have hw₀_spec := nextGt_spec hB_inf N
  have hy₀_51 := lemma_5_1 hA_inf hn0 hstab hL
  have hw₀_52 := lemma_5_2 hA_inf hB_inf hn0 hstab hL
  have hx₀_mem := maxLe_mem (by rcases hL.hx₀_lo with ⟨a, haA, haN, _⟩; exact ⟨a, haA, haN⟩)
  have hz₀_mem := maxLe_mem (by rcases hL.hz₀_lo with ⟨b, hbB, hbN, _⟩; exact ⟨b, hbB, hbN⟩)
  have hx₀_hi : (x₀ : ℝ) ≤ (1 / 3 + 1 / 1000 : ℝ) * (N : ℝ) := hL.hx₀_hi x₀ hx₀_mem.1 hx₀_mem.2
  have hz₀_hi : (z₀ : ℝ) ≤ (2 / 3 + 1 / 1000 : ℝ) * (N : ℝ) := hL.hz₀_hi z₀ hz₀_mem.1 hz₀_mem.2
  set E := errSum A B n₀
  have hN_big : (10 ^ 7 : ℝ) * ((K : ℝ) + (E : ℝ) + (n₀ : ℝ) + 1) * ((E : ℝ) + (n₀ : ℝ) + 1) ≤ (N : ℝ) := by
    exact_mod_cast hL.hN_large
  have hE1_ge1 : (1 : ℝ) ≤ (E : ℝ) + (n₀ : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (E : ℝ) := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg _
    linarith
  have hN_ge_lin : (10 ^ 7 : ℝ) * ((K : ℝ) + (E : ℝ) + (n₀ : ℝ) + 1) ≤ (N : ℝ) := by nlinarith
  have hN_ge_n0 : n₀ ≤ N := by
    have : (n₀ : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast this
  have hwy : y₀ + 1 ≤ w₀ := by
    have hlt : (y₀ : ℝ) + 1 < (w₀ : ℝ) := by linarith
    exact Nat.le_of_lt (by exact_mod_cast hlt)
  set L₁ := min N (w₀ - 1 - y₀)
  have hL1_gt : (5 / 8 : ℝ) * (N : ℝ) - 1 < (L₁ : ℝ) := by
    have h1 : (5 / 8 : ℝ) * (N : ℝ) - 1 < ((w₀ - 1 - y₀ : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; linarith
    have h2 : (5 / 8 : ℝ) * (N : ℝ) - 1 < (N : ℝ) := by linarith
    simp only [L₁, Nat.cast_min, lt_min_iff]
    exact ⟨h2, h1⟩
  set T₀ := x₀ + ⌊(2 / 1000 : ℝ) * (N : ℝ)⌋₊ + 1
  set T₁ := T₀ + (E + 1) * (n₀ + 1)
  set T₂ := L₁ - (E + 1) * (n₀ + 1)
  have hfl2 : (⌊(2 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) ≤ (2 / 1000 : ℝ) * (N : ℝ) :=
    Nat.floor_le (by linarith)
  have hT0_le : (T₀ : ℝ) ≤ (1 / 3 + 3 / 1000 : ℝ) * (N : ℝ) + 1 := by
    simp only [T₀]; push_cast; linarith
  have hEn_small : (((E + 1) * (n₀ + 1) : ℕ) : ℝ) ≤ (N : ℝ) / 10 ^ 6 := by
    push_cast; nlinarith
  have hT1_upper : (T₁ : ℝ) ≤ (1 / 3 + 4 / 1000 : ℝ) * (N : ℝ) + 1 := by
    have h1 : (T₁ : ℝ) = (T₀ : ℝ) + (((E + 1) * (n₀ + 1) : ℕ) : ℝ) := by simp only [T₁]; push_cast; ring
    linarith
  have hEn_le_L1 : 2 * (E + 1) * (n₀ + 1) + T₀ + n₀ < L₁ := by
    have hEn_r : ((E : ℝ) + 1) * ((n₀ : ℝ) + 1) ≤ (N : ℝ) / 10 ^ 6 := by
      simpa using hEn_small
    have : ((2 * (E + 1) * (n₀ + 1) + T₀ + n₀ : ℕ) : ℝ) < (L₁ : ℝ) := by
      push_cast; nlinarith
    exact_mod_cast this
  have hT1_lt_T2 : T₁ + n₀ < T₂ := by
    have : 2 * (E + 1) * (n₀ + 1) = (E + 1) * (n₀ + 1) + (E + 1) * (n₀ + 1) := by ring
    omega
  -- Convolution setup
  set f₀ : ℕ → ℤ := fun n => if n ≤ x₀ ∧ n ∈ A then 1 else 0
  set f₁ : ℕ → ℤ := fun n => if y₀ + n ∈ A then 1 else 0
  set h : ℕ → ℤ := fun _ => 1
  set δ : ℕ → ℤ := fun n => (repCount A B n : ℤ) - 1
  set η₁ : ℕ → ℤ := fun n => (repTrunc A B N (y₀ + n) : ℤ)
  have hη₁_zero_large : ∀ n, ⌊(2 / 1000 : ℝ) * (N : ℝ)⌋₊ < n → η₁ n = 0 := by
    intro n hn
    unfold η₁
    suffices repTrunc A B N (y₀ + n) = 0 by simp [this]
    unfold repTrunc
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a ha; rintro ⟨haA, hale, hbN, hbB⟩
    have ha_x0 : a ≤ x₀ := le_maxLe haA (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))
    have hb_z0 : y₀ + n - a ≤ z₀ := le_maxLe hbB hbN
    have hsum : y₀ + n ≤ x₀ + z₀ := by omega
    have hcast : (y₀ : ℝ) + (n : ℝ) ≤ (x₀ : ℝ) + (z₀ : ℝ) := by exact_mod_cast hsum
    have hn_r : (⌊(2 / 1000 : ℝ) * (N : ℝ)⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hfl_gt := Nat.lt_floor_add_one ((2 / 1000 : ℝ) * (N : ℝ))
    have hy_r : (N : ℝ) + 1 ≤ (y₀ : ℝ) := by exact_mod_cast hy₀_spec.1
    linarith
  have hconv_id : ∀ t ≤ L₁, dconv f₁ h t - dconv f₀ h t = - dconv f₁ δ t - dconv f₀ η₁ t := by
    intro t ht
    have htN : t ≤ N := le_trans ht (min_le_left _ _)
    have htw : y₀ + t < w₀ := by
      have : t ≤ w₀ - 1 - y₀ := le_trans ht (min_le_right _ _); omega
    exact conv_identity_55 hA_inf hB_inf hstab hN_ge_n0 htN htw
  have hf0h_const : ∀ t ≥ x₀, dconv f₀ h t = (countNat A N : ℤ) := by
    intro t ht
    unfold dconv h countNat
    have hsplit : t + 1 = (x₀ + 1) + (t - x₀) := by omega
    rw [hsplit, Finset.sum_range_add]
    have hz : ∑ m ∈ Finset.range (t - x₀), f₀ (x₀ + 1 + m) * 1 = 0 := by
      apply Finset.sum_eq_zero; intro m _; simp [f₀]; omega
    rw [hz, add_zero]
    have hterm : ∀ i ∈ Finset.range (x₀ + 1), f₀ i * 1 = if i ∈ A then (1 : ℤ) else 0 := by
      intro i hi; have : i ≤ x₀ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi); simp [f₀, this]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard_eq : ((Finset.range (x₀ + 1)).filter (· ∈ A)).card =
        ((Finset.range (N + 1)).filter (· ∈ A)).card := by
      congr 1; ext a; simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨by have := le_maxLe (N := N) h2 (by omega); omega, h2⟩
    exact_mod_cast hcard_eq
  have hf0η_zero : ∀ t ≥ T₀, dconv f₀ η₁ t = 0 := by
    intro t ht; unfold dconv; apply Finset.sum_eq_zero; intro i _
    by_cases hix : i ≤ x₀
    · rw [hη₁_zero_large (t - i) (by omega), mul_zero]
    · simp [f₀, hix]
  set S : ℕ → ℤ := fun t => dconv f₁ h t
  have hS_eq_on : ∀ t, T₀ ≤ t → t ≤ L₁ → S t = (countNat A N : ℤ) - dconv f₁ δ t := by
    intro t ht1 ht2
    have hid := hconv_id t ht2
    rw [hf0h_const t (by omega), hf0η_zero t ht1] at hid; linarith
  have hδ_abs : ∀ t, |dconv f₁ δ t| ≤ (E : ℤ) := by
    intro t; unfold dconv
    calc
      |∑ i ∈ Finset.range (t + 1), f₁ i * δ (t - i)|
          ≤ ∑ i ∈ Finset.range (t + 1), |f₁ i * δ (t - i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (t + 1), |δ (t - i)| := by
            apply Finset.sum_le_sum; intro i _; rw [abs_mul]; simp only [f₁]; split_ifs <;> simp
      _ = ∑ j ∈ Finset.range (t + 1), |δ j| := by
            apply Finset.sum_bij (fun i _ => t - i)
            · intro i hi; rw [Finset.mem_range] at hi ⊢; omega
            · intro i₁ h1 i₂ h2 heq; rw [Finset.mem_range] at h1 h2; omega
            · intro j hj; rw [Finset.mem_range] at hj; exact ⟨t - j, Finset.mem_range.mpr (by omega), by omega⟩
            · intro _ _; rfl
      _ ≤ (E : ℤ) := by
            unfold E errSum δ; push_cast
            by_cases hle : t + 1 ≤ n₀
            · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hle) (fun _ _ _ => abs_nonneg _)
            · have hsp : t + 1 = n₀ + (t + 1 - n₀) := by omega
              rw [hsp, Finset.sum_range_add]
              have hz : ∑ m ∈ Finset.range (t + 1 - n₀), |((repCount A B (n₀ + m) : ℤ) - 1)| = 0 := by
                apply Finset.sum_eq_zero; intro m _; simp [hstab (n₀ + m) (by omega)]
              rw [hz, add_zero]
  have hpig := pigeonhole_zero_run (S := S) (f := f₁) (T₀ := T₀) (L₁ := L₁) (A₀c := countNat A N)
    (E := E) (n₀ := n₀)
    (fun t _ _ => by simp only [f₁]; split_ifs <;> simp)
    (fun t _ _ => by simp only [S, dconv, h, mul_one, Finset.sum_range_succ])
    (fun t ht1 ht2 => by
      rw [hS_eq_on t ht1 ht2]; have := abs_le.mp (hδ_abs t); constructor <;> linarith)
    (fun u hu1 hu2 hzeros => by
      rw [hS_eq_on u (by omega) hu2]
      have h0 : dconv f₁ δ u = 0 := by
        unfold dconv; apply Finset.sum_eq_zero; intro i hi
        have hi_le : i ≤ u := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        by_cases hlt : u - i < n₀
        · have : u - (u - i) = i := by omega
          rw [← this, hzeros (u - i) hlt, zero_mul]
        · simp [δ, hstab (u - i) (by omega)]
      linarith)
    hn0 (by omega)
  have hS_const : ∀ t, T₁ ≤ t → t ≤ T₂ → S t = (countNat A N : ℤ) := hpig.1
  have hf1_zero : ∀ t, T₁ + 1 ≤ t → t ≤ T₂ → f₁ t = 0 := hpig.2
  have hA_gap_zero : ∀ t, T₁ + 1 ≤ t → t ≤ T₂ → y₀ + t ∉ A := by
    intro t ht1 ht2 hmem
    have h0 := hf1_zero t ht1 ht2
    simp only [f₁, hmem, ↓reduceIte] at h0
    omega
  -- Polynomials PA1, Hη₁, U₁, Δ
  set PA1 := shiftedTruncPoly A y₀ T₁
  set Hη₁ : ℤ[X] := ∑ m ∈ Finset.range (⌊(2 / 1000 : ℝ) * (N : ℝ)⌋₊ + 1), C (η₁ m) * (X : ℤ[X]) ^ m
  set U₁ : ℤ[X] := 1 - (1 - X) * Hη₁
  set Δ : ℤ[X] := ∑ n ∈ Finset.range n₀, C (δ n) * (X : ℤ[X]) ^ n
  have hHη₁_coeff : ∀ m, Hη₁.coeff m = η₁ m := by
    intro m; unfold Hη₁; rw [finsetSum_coeff]; simp only [coeff_C_mul, coeff_X_pow]
    by_cases hm : m ≤ ⌊(2 / 1000 : ℝ) * (N : ℝ)⌋₊
    · rw [Finset.sum_eq_single m]
      · simp
      · intro b _ hbm; simp [hbm.symm]
      · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
    · rw [hη₁_zero_large m (by omega)]
      apply Finset.sum_eq_zero; intro b hb
      have hbm : m ≠ b := by intro heq; subst heq; exact hm (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))
      simp [hbm]
  have hΔ_coeff : ∀ n, Δ.coeff n = δ n := by
    intro n; unfold Δ; rw [finsetSum_coeff]; simp only [coeff_C_mul, coeff_X_pow]
    by_cases hn : n < n₀
    · rw [Finset.sum_eq_single n]
      · simp
      · intro b _ hbn; simp [hbn.symm]
      · intro hnot; exact absurd (Finset.mem_range.mpr hn) hnot
    · simp only [δ, hstab n (by omega), Nat.cast_one, sub_self]
      apply Finset.sum_eq_zero; intro b hb
      have hbn : n ≠ b := by intro heq; subst heq; exact hn (Finset.mem_range.mp hb)
      simp [hbn]
  have hPA0_coeff : ∀ m, (truncPoly A N).coeff m = f₀ m := by
    intro m; rw [truncPoly_coeff]; simp only [f₀]
    by_cases ha : m ∈ A
    · by_cases hleN : m ≤ N
      · have hle_x0 : m ≤ x₀ := le_maxLe ha hleN
        simp [ha, hleN, hle_x0]
      · have hnot_x0 : ¬ (m ≤ x₀) := by omega
        simp [ha, hleN, hnot_x0]
    · simp [ha]
  set f₁' : ℕ → ℤ := fun m => PA1.coeff m
  have hf1'_eq : ∀ t ≤ T₂, f₁' t = f₁ t := by
    intro t ht
    simp only [f₁', PA1, shiftedTruncPoly_coeff, f₁]
    by_cases ht1 : t ≤ T₁
    · simp [ht1]
    · have hnot := hA_gap_zero t (by omega) ht
      simp [ht1, hnot]
  have hall_t : ∀ t, dconv f₁' h t - dconv f₀ h t = - dconv f₁' δ t - dconv f₀ η₁ t := by
    intro t
    by_cases ht : t ≤ T₂
    · have h1 : dconv f₁' h t = dconv f₁ h t := by
        unfold dconv; apply Finset.sum_congr rfl; intro i hi
        rw [hf1'_eq i (by have := Finset.mem_range.mp hi; omega)]
      have h2 : dconv f₁' δ t = dconv f₁ δ t := by
        unfold dconv; apply Finset.sum_congr rfl; intro i hi
        rw [hf1'_eq i (by have := Finset.mem_range.mp hi; omega)]
      rw [h1, h2]; exact hconv_id t (by omega)
    · have hl1 : dconv f₁' h t = (countNat A N : ℤ) := by
        have hST1 : dconv f₁' h T₁ = (countNat A N : ℤ) := by
          have : dconv f₁' h T₁ = S T₁ := by
            unfold S dconv; apply Finset.sum_congr rfl; intro i hi
            rw [hf1'_eq i (by have := Finset.mem_range.mp hi; omega)]
          rw [this, hS_const T₁ le_rfl (by omega)]
        rw [← hST1]
        unfold dconv h
        have hsp : t + 1 = (T₁ + 1) + (t - T₁) := by omega
        rw [hsp, Finset.sum_range_add]
        have hz : ∑ m ∈ Finset.range (t - T₁), f₁' (T₁ + 1 + m) * 1 = 0 := by
          apply Finset.sum_eq_zero; intro m _; simp [f₁', PA1, shiftedTruncPoly_coeff]; omega
        rw [hz, add_zero]
      have hl2 : dconv f₀ h t = (countNat A N : ℤ) := hf0h_const t (by omega)
      have hr1 : dconv f₁' δ t = 0 := by
        unfold dconv; apply Finset.sum_eq_zero; intro i _
        by_cases hi1 : i ≤ T₁
        · simp [δ, hstab (t - i) (by omega)]
        · simp [f₁', PA1, shiftedTruncPoly_coeff, hi1]
      have hr2 : dconv f₀ η₁ t = 0 := hf0η_zero t (by omega)
      linarith
  have hPA1_V : PA1 * VPoly A B n₀ = truncPoly A N * U₁ := by
    have hVeq : VPoly A B n₀ = 1 + (1 - X) * Δ := rfl
    have hUeq : U₁ = 1 - (1 - X) * Hη₁ := rfl
    have hdiff : PA1 - truncPoly A N = (1 - X) * (-(PA1 * Δ) - truncPoly A N * Hη₁) := by
      ext t
      rw [coeff_sub, coeff_one_sub_X_mul]
      have hmul1 : ∀ k, (PA1 * Δ).coeff k = dconv f₁' δ k := by
        intro k
        rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => PA1.coeff x * Δ.coeff y)]
        unfold dconv; apply Finset.sum_congr rfl; intro i _; rw [hΔ_coeff]
      have hmul2 : ∀ k, (truncPoly A N * Hη₁).coeff k = dconv f₀ η₁ k := by
        intro k
        rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => (truncPoly A N).coeff x * Hη₁.coeff y)]
        unfold dconv; apply Finset.sum_congr rfl; intro i _; rw [hPA0_coeff, hHη₁_coeff]
      have hcoeff_rhs : ∀ k, (-(PA1 * Δ) - truncPoly A N * Hη₁).coeff k =
          dconv f₁' h k - dconv f₀ h k := by
        intro k; rw [coeff_sub, coeff_neg, hmul1 k, hmul2 k, hall_t k]
      cases t with
      | zero =>
        simp only [↓reduceIte, hcoeff_rhs 0, hPA0_coeff]
        simp only [dconv, h, zero_add, Finset.range_one, Finset.sum_singleton, mul_one, f₁']
      | succ m =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hcoeff_rhs (m + 1), hcoeff_rhs m, hPA0_coeff]
        simp only [dconv, h, mul_one, Finset.sum_range_succ, f₁']
        ring
    rw [hVeq, hUeq]; linear_combination hdiff
  set s := y₀ - (N + 1)
  have hWN_U1 : WPoly A B N = X ^ s * U₁ := by
    have hrep_gap : ∀ j < s, repTrunc A B N (N + 1 + j) = 1 := by
      intro j hj
      have h1 : repCount A B (N + 1 + j) = 1 := hstab (N + 1 + j) (by omega)
      have hge1 : 1 ≤ repTrunc A B N (N + 1 + j) := by
        have hpos : 0 < repCount A B (N + 1 + j) := by omega
        obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
        simp only [Finset.mem_filter, Finset.mem_range] at ha
        have haN : a ≤ N := by
          by_contra hgt; have := nextGt_le hA_inf (N := N) ha.2.1 (by omega); omega
        have hbN : N + 1 + j - a ≤ N := by
          by_contra hgt; have := nextGt_le hB_inf (N := N) ha.2.2 (by omega); omega
        apply Finset.card_pos.mpr
        exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ha.2.1, by omega, hbN, ha.2.2⟩⟩
      have hle1 := (repTrunc_le_repCount A B N (N + 1 + j)).trans (le_of_eq h1)
      omega
    have hU1_coeff : ∀ k, U₁.coeff k = if k = 0 then 1 - η₁ 0 else η₁ (k - 1) - η₁ k := by
      intro k; simp only [U₁, coeff_sub, coeff_one_sub_X_mul, hHη₁_coeff]
      cases k with
      | zero => simp
      | succ j => simp [Polynomial.coeff_one]
    ext m
    rw [WPoly_coeff, coeff_X_pow_mul']
    by_cases hms : s ≤ m
    · simp only [hms, ↓reduceIte]
      rw [hU1_coeff]
      by_cases hm0 : m = 0
      · subst hm0
        have hs0 : s = 0 := by omega
        have hy_eq : y₀ = N + 1 := by omega
        simp [η₁, hy_eq]
      · simp only [hm0, ↓reduceIte]
        by_cases hms0 : m - s = 0
        · simp only [hms0, ↓reduceIte]
          have h1 := hrep_gap (m - 1) (by omega)
          have hidx1 : N + m = N + 1 + (m - 1) := by omega
          have hidx2 : N + 1 + m = y₀ + 0 := by omega
          rw [hidx1, hidx2, h1]; simp [η₁]
        · simp only [hms0, ↓reduceIte]
          have hidx1 : N + m = y₀ + (m - s - 1) := by omega
          have hidx2 : N + 1 + m = y₀ + (m - s) := by omega
          rw [hidx1, hidx2]
    · simp only [hms, ↓reduceIte]
      by_cases hm0 : m = 0
      · subst hm0
        have h1 := hrep_gap 0 (by omega)
        simp [h1]
      · simp only [hm0, ↓reduceIte]
        have h1 := hrep_gap (m - 1) (by omega)
        have h2 := hrep_gap m (by omega)
        have hidx1 : N + m = N + 1 + (m - 1) := by omega
        rw [hidx1, h1, h2]; ring
  have hHη₁_eval_le : Hη₁.eval 1 ≤ (crossExcess A B N : ℤ) := by
    have h1 : Hη₁.eval 1 = ∑ m ∈ Finset.range (⌊(2 / 1000 : ℝ) * (N : ℝ)⌋₊ + 1), η₁ m := by
      simp [Hη₁, eval_finsetSum]
    rw [h1]
    have hsum_le : ∑ j ∈ Finset.range (⌊(2 / 1000 : ℝ) * (N : ℝ)⌋₊ + 1), repTrunc A B N (y₀ + j) ≤
        crossExcess A B N := by
      unfold crossExcess
      set R0 := (Finset.range (⌊(2 / 1000 : ℝ) * (N : ℝ)⌋₊ + 1)).filter (fun j => y₀ - (N + 1) + j < N)
      have hfilt : ∑ j ∈ R0, repTrunc A B N (y₀ + j) =
          ∑ j ∈ Finset.range (⌊(2 / 1000 : ℝ) * (N : ℝ)⌋₊ + 1), repTrunc A B N (y₀ + j) := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j hj hnot
        simp only [Finset.mem_filter, hj, true_and] at hnot
        exact repTrunc_eq_zero_of_gt A B (by omega)
      rw [← hfilt]
      have himg : R0.image (fun j => y₀ - (N + 1) + j) ⊆ Finset.range N := by
        intro m hm; rcases Finset.mem_image.mp hm with ⟨j, hj, rfl⟩
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
      calc
        ∑ j ∈ R0, repTrunc A B N (y₀ + j)
            = ∑ m ∈ R0.image (fun j => y₀ - (N + 1) + j), repTrunc A B N (N + 1 + m) := by
              rw [Finset.sum_image]
              · apply Finset.sum_congr rfl; intro j _; congr 1; omega
              · intro j₁ _ j₂ _ heq; dsimp only at heq; omega
        _ ≤ ∑ m ∈ Finset.range N, repTrunc A B N (N + 1 + m) := Finset.sum_le_sum_of_subset himg
    unfold η₁; exact_mod_cast hsum_le
  exact ⟨{
    T₁ := T₁
    T₂ := T₂
    Hη₁ := Hη₁
    U₁ := U₁
    hU₁_def := rfl
    hHη₁_coeff := hHη₁_coeff
    hT1_lt_T2 := hT1_lt_T2
    hT1_upper := hT1_upper
    hA_gap_zero := hA_gap_zero
    hPA1_V := hPA1_V
    hWN_U1 := hWN_U1
    hHη₁_eval_le := hHη₁_eval_le
  }⟩

/-- The output of a single exact forward doubling step (Proposition 5.3). -/
structure DoublingStepResult (A B : Set ℕ) (hA_inf : A.Infinite) (n₀ N : ℕ) where
  N₁' : ℕ
  T₁ : ℕ
  U₁ : ℤ[X]
  hN₁'_lo : 2 * N - 2 * n₀ ≤ N₁'
  hN₁'_hi : (N₁' : ℝ) ≤ (2 + 17 / 1000 : ℝ) * (N : ℝ)
  hN₁'_gt : N < N₁'
  hN₁'_formula : N₁' = 2 * nextGt hA_inf N + 2 * U₁.natTrailingDegree -
    mZero A B - 1 - max (minElem A) (minElem B)
  hU₁_eval : U₁.eval 1 = 1
  hU₁_strip0 : (stripPoly U₁).coeff 0 = 1
  hPA1_V : shiftedTruncPoly A (nextGt hA_inf N) T₁ * VPoly A B n₀ = truncPoly A N * U₁
  hWN_U1 : WPoly A B N = X ^ (nextGt hA_inf N - (N + 1)) * U₁
  hA_trunc : ∀ a, a ≤ N₁' → (a ∈ A ↔ (a ≤ N ∧ a ∈ A) ∨
      (nextGt hA_inf N ≤ a ∧ a ≤ nextGt hA_inf N + T₁ ∧ a ∈ A))
  hB_trunc : ∀ b, b ≤ N₁' → (b ∈ B ↔ b ≤ N ∧ b ∈ B)
  hpoly_exact : X ^ (N₁' + 1) * VPoly A B n₀ * WPoly A B N₁' =
      X ^ (2 * (N + 1)) * (WPoly A B N) ^ 2
  hW_ord : (WPoly A B N₁').natTrailingDegree = max (minElem A) (minElem B)
  hstrip_quad : stripPoly (VPoly A B n₀) * stripPoly (WPoly A B N₁') =
      (stripPoly (WPoly A B N)) ^ 2
  hT_bound : crossExcess A B N₁' ≤ 2 * crossExcess A B N + errSum A B n₀ + 2 * n₀

/-- **Proposition 5.3 (Exact Forward Doubling and Quadratic Polynomial Recurrence).** -/
theorem forward_doubling_step {A B : Set ℕ} (hA_inf : A.Infinite) (hB_inf : B.Infinite)
    {n₀ K N : ℕ} (hn0 : 1 ≤ n₀) (hstab : ∀ n ≥ n₀, repCount A B n = 1)
    (hL : LevelApprox A B n₀ K N) :
    Nonempty (DoublingStepResult A B hA_inf n₀ N) := by
  classical
  obtain ⟨d1⟩ := forward_doubling_step1 hA_inf hB_inf hn0 hstab hL
  set y₀ := nextGt hA_inf N
  set w₀ := nextGt hB_inf N
  have hy₀_spec := nextGt_spec hA_inf N
  have hy₀_51 := lemma_5_1 hA_inf hn0 hstab hL
  have hw₀_52 := lemma_5_2 hA_inf hB_inf hn0 hstab hL
  have hx₀_mem := maxLe_mem (by rcases hL.hx₀_lo with ⟨a, haA, haN, _⟩; exact ⟨a, haA, haN⟩)
  have hz₀_mem := maxLe_mem (by rcases hL.hz₀_lo with ⟨b, hbB, hbN, _⟩; exact ⟨b, hbB, hbN⟩)
  have hAne : A.Nonempty := ⟨maxLe A N, hx₀_mem.1⟩
  have hBne : B.Nonempty := ⟨maxLe B N, hz₀_mem.1⟩
  have hm0_le : mZero A B ≤ n₀ := mZero_le_n0 hstab
  have hamin_le : minElem A ≤ n₀ := by unfold mZero at hm0_le; omega
  have hbmin_le : minElem B ≤ n₀ := by unfold mZero at hm0_le; omega
  have hN_ge_lin : (10 ^ 7 : ℝ) * ((K : ℝ) + (errSum A B n₀ : ℝ) + (n₀ : ℝ) + 1) ≤ (N : ℝ) := by
    have hnat : 10 ^ 7 * (K + errSum A B n₀ + n₀ + 1) ≤ N := by
      have := hL.hN_large; nlinarith
    exact_mod_cast hnat
  have hN_ge_n0 : n₀ ≤ N := by
    have : (n₀ : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast this
  set PA1 := shiftedTruncPoly A y₀ d1.T₁
  set U₁ := d1.U₁
  set Hη₁ := d1.Hη₁
  have hHη₁_01 : ∀ m, Hη₁.coeff m = 0 ∨ Hη₁.coeff m = 1 := by
    intro m; simp only [Hη₁, d1.hHη₁_coeff]
    have hle1 : repTrunc A B N (nextGt hA_inf N + m) ≤ 1 :=
      (repTrunc_le_repCount A B N (nextGt hA_inf N + m)).trans (by rw [hstab _ (by omega)])
    omega
  have hU₁_props := one_sub_one_sub_X_mul_properties hHη₁_01
  rw [← d1.hU₁_def] at hU₁_props
  have hu1_le_K : U₁.natTrailingDegree ≤ K := by
    have h1 : (U₁.natTrailingDegree : ℤ) ≤ Hη₁.eval 1 := hU₁_props.2.2.2.2.2.2.2.2
    have h2 : Hη₁.eval 1 ≤ (K : ℤ) := le_trans d1.hHη₁_eval_le (by exact_mod_cast hL.hT_le)
    exact_mod_cast (le_trans h1 h2)
  -- Step 2: F := U₁ - (1 - X) * PA1 * truncPoly B N satisfies V * F = X^y₀ * U₁^2
  set F : ℤ[X] := U₁ - (1 - X) * (PA1 * truncPoly B N)
  have hXW : X ^ (N + 1) * WPoly A B N = X ^ y₀ * U₁ := by
    rw [d1.hWN_U1, ← mul_assoc, ← pow_add]; congr 2; omega
  have hVF : VPoly A B n₀ * F = X ^ y₀ * U₁ ^ 2 := by
    have htr := truncPoly_exact_identity hstab hN_ge_n0
    calc
      VPoly A B n₀ * F
          = VPoly A B n₀ * U₁ - (1 - X) * ((PA1 * VPoly A B n₀) * truncPoly B N) := by
            simp only [F]; ring
      _ = VPoly A B n₀ * U₁ - (1 - X) * ((truncPoly A N * U₁) * truncPoly B N) := by rw [d1.hPA1_V]
      _ = VPoly A B n₀ * U₁ - U₁ * ((1 - X) * (truncPoly A N * truncPoly B N)) := by ring
      _ = VPoly A B n₀ * U₁ - U₁ * (VPoly A B n₀ - X ^ (N + 1) * WPoly A B N) := by rw [htr]
      _ = U₁ * (X ^ (N + 1) * WPoly A B N) := by ring
      _ = U₁ * (X ^ y₀ * U₁) := by rw [hXW]
      _ = X ^ y₀ * U₁ ^ 2 := by ring
  set EF : ℤ[X] := Hη₁ + PA1 * truncPoly B N
  have hF_eq : F = 1 - (1 - X) * EF := by simp only [F, U₁, d1.hU₁_def, EF]; ring
  have hEF_coeff : ∀ n, EF.coeff n =
      (((Finset.range (y₀ + n + 1)).filter
        (fun a => ((a ≤ N ∨ (y₀ ≤ a ∧ a ≤ y₀ + d1.T₁)) ∧ a ∈ A) ∧ y₀ + n - a ≤ N ∧ y₀ + n - a ∈ B)).card : ℤ) := by
    intro n
    simp only [EF, coeff_add, Hη₁, d1.hHη₁_coeff]
    have hmul : (PA1 * truncPoly B N).coeff n =
        (((Finset.range (y₀ + n + 1)).filter
          (fun a => (y₀ ≤ a ∧ a ≤ y₀ + d1.T₁ ∧ a ∈ A) ∧ y₀ + n - a ≤ N ∧ y₀ + n - a ∈ B)).card : ℤ) := by
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => PA1.coeff x * (truncPoly B N).coeff y)]
      have hterm : ∀ i ∈ Finset.range (n + 1),
          PA1.coeff i * (truncPoly B N).coeff (n - i) =
            if i ≤ d1.T₁ ∧ y₀ + i ∈ A ∧ n - i ≤ N ∧ n - i ∈ B then (1 : ℤ) else 0 := by
        intro i _
        rw [shiftedTruncPoly_coeff, truncPoly_coeff]
        by_cases h1 : i ≤ d1.T₁ <;> by_cases h1' : y₀ + i ∈ A <;>
          by_cases h2 : n - i ≤ N <;> by_cases h2' : n - i ∈ B <;>
          simp [h1, h1', h2, h2']
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 1
      apply Finset.card_bij (fun i _ => y₀ + i)
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
        refine ⟨by omega, ⟨by omega, by omega, hi.2.2.1⟩, by omega, ?_⟩
        have hsub : y₀ + n - (y₀ + i) = n - i := by omega
        rw [hsub]; exact hi.2.2.2.2
      · intro i₁ _ i₂ _ heq; omega
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_range] at ha
        refine ⟨a - y₀, ?_, by omega⟩
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, by omega, ?_, by omega, ?_⟩
        · have hadd : y₀ + (a - y₀) = a := by omega
          rw [hadd]; exact ha.2.1.2.2
        · have hsub : n - (a - y₀) = y₀ + n - a := by omega
          rw [hsub]; exact ha.2.2.2
    have hrep : repTrunc A B N (nextGt hA_inf N + n) =
        ((Finset.range (y₀ + n + 1)).filter
          (fun a => (a ≤ N ∧ a ∈ A) ∧ y₀ + n - a ≤ N ∧ y₀ + n - a ∈ B)).card := by
      unfold repTrunc; congr 1; ext a
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨by omega, ⟨by omega, h2⟩, h4, h5⟩
      · rintro ⟨h1, ⟨h2, h3⟩, h4, h5⟩; exact ⟨by omega, h3, by omega, h4, h5⟩
    rw [hmul, hrep]
    have hdisj : Disjoint
        ((Finset.range (y₀ + n + 1)).filter (fun a => (a ≤ N ∧ a ∈ A) ∧ y₀ + n - a ≤ N ∧ y₀ + n - a ∈ B))
        ((Finset.range (y₀ + n + 1)).filter (fun a => (y₀ ≤ a ∧ a ≤ y₀ + d1.T₁ ∧ a ∈ A) ∧ y₀ + n - a ≤ N ∧ y₀ + n - a ∈ B)) := by
      rw [Finset.disjoint_left]; intro a h1 h2; simp only [Finset.mem_filter] at h1 h2; omega
    have hunion :
        ((Finset.range (y₀ + n + 1)).filter (fun a => (a ≤ N ∧ a ∈ A) ∧ y₀ + n - a ≤ N ∧ y₀ + n - a ∈ B)) ∪
        ((Finset.range (y₀ + n + 1)).filter (fun a => (y₀ ≤ a ∧ a ≤ y₀ + d1.T₁ ∧ a ∈ A) ∧ y₀ + n - a ≤ N ∧ y₀ + n - a ∈ B)) =
        (Finset.range (y₀ + n + 1)).filter
          (fun a => ((a ≤ N ∨ (y₀ ≤ a ∧ a ≤ y₀ + d1.T₁)) ∧ a ∈ A) ∧ y₀ + n - a ≤ N ∧ y₀ + n - a ∈ B) := by
      ext a; simp only [Finset.mem_union, Finset.mem_filter]; tauto
    have hc := Finset.card_union_of_disjoint hdisj
    rw [hunion] at hc; exact_mod_cast hc.symm
  have hEF_01 : ∀ n, EF.coeff n = 0 ∨ EF.coeff n = 1 := by
    intro n; rw [hEF_coeff n]
    have hle : ((Finset.range (y₀ + n + 1)).filter
        (fun a => ((a ≤ N ∨ (y₀ ≤ a ∧ a ≤ y₀ + d1.T₁)) ∧ a ∈ A) ∧ y₀ + n - a ≤ N ∧ y₀ + n - a ∈ B)).card ≤
        repCount A B (y₀ + n) := by
      unfold repCount; apply Finset.card_le_card
      intro a ha; simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
      exact ⟨ha.1, ha.2.1.2, ha.2.2.2⟩
    have hr1 := hstab (y₀ + n) (by omega)
    omega
  have hF_props := one_sub_one_sub_X_mul_properties hEF_01
  rw [← hF_eq] at hF_props
  have hV_props := VPoly_strip_properties hAne hBne hstab
  have hV_ne : VPoly A B n₀ ≠ 0 := by intro h0; have := VPoly_eval_one A B n₀; rw [h0] at this; simp at this
  have hU₁_ne : U₁ ≠ 0 := by intro h0; have := hU₁_props.1; change U₁.eval 1 = 1 at this; rw [h0] at this; simp at this
  have hF_ne : F ≠ 0 := by intro h0; have := hF_props.1; rw [h0] at this; simp at this
  have hF_ord : F.natTrailingDegree = y₀ + 2 * U₁.natTrailingDegree - mZero A B := by
    have hlhs := Polynomial.natTrailingDegree_mul hV_ne hF_ne
    have hrhs : (X ^ y₀ * U₁ ^ 2).natTrailingDegree = y₀ + 2 * U₁.natTrailingDegree := by
      rw [Polynomial.natTrailingDegree_mul (pow_ne_zero y₀ X_ne_zero) (pow_ne_zero 2 hU₁_ne),
          Polynomial.natTrailingDegree_X_pow, sq, Polynomial.natTrailingDegree_mul hU₁_ne hU₁_ne]
      omega
    rw [hVF, hrhs] at hlhs
    rw [hV_props.1] at hlhs
    omega
  set u₁ := U₁.natTrailingDegree
  set M₁ := F.natTrailingDegree
  set N₁ := y₀ + M₁ - 1
  set N₁' := 2 * y₀ + 2 * u₁ - mZero A B - 1 - max (minElem A) (minElem B)
  have hN₁'_lo : 2 * N - 2 * n₀ ≤ N₁' := by omega
  have hN₁'_hi : (N₁' : ℝ) ≤ (2 + 17 / 1000 : ℝ) * (N : ℝ) := by
    have hle : N₁' ≤ 2 * y₀ + 2 * u₁ := by omega
    have hcast : (N₁' : ℝ) ≤ 2 * (y₀ : ℝ) + 2 * (u₁ : ℝ) := by exact_mod_cast hle
    have hu1_r : (u₁ : ℝ) ≤ (K : ℝ) := by exact_mod_cast hu1_le_K
    linarith
  have hN₁'_gt : N < N₁' := by
    have h2 : (N : ℝ) < ((2 * N - 2 * n₀ : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; linarith
    have : N < 2 * N - 2 * n₀ := by exact_mod_cast h2
    omega
  have hN₁'_gt_yT1 : y₀ + d1.T₁ < N₁' := by
    have h2 : 2 * (N : ℝ) - 2 * (n₀ : ℝ) ≤ (N₁' : ℝ) := by
      have : ((2 * N - 2 * n₀ : ℕ) : ℝ) ≤ (N₁' : ℝ) := by exact_mod_cast hN₁'_lo
      rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
    have h1 := d1.hT1_upper
    have : ((y₀ + d1.T₁ : ℕ) : ℝ) < (N₁' : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hEF_one : ∀ n < M₁, ∃ a ∈ A, (a ≤ N ∨ (y₀ ≤ a ∧ a ≤ y₀ + d1.T₁)) ∧
      y₀ + n - a ≤ N ∧ y₀ + n - a ∈ B ∧ a ≤ y₀ + n := by
    intro n hn
    have h1 := hF_props.2.2.2.1 n hn
    rw [hEF_coeff n] at h1
    have hpos_z : (0 : ℤ) < (((Finset.range (y₀ + n + 1)).filter
        (fun a => ((a ≤ N ∨ (y₀ ≤ a ∧ a ≤ y₀ + d1.T₁)) ∧ a ∈ A) ∧ y₀ + n - a ≤ N ∧ y₀ + n - a ∈ B)).card : ℤ) := by
      omega
    have hpos : 0 < ((Finset.range (y₀ + n + 1)).filter
        (fun a => ((a ≤ N ∨ (y₀ ≤ a ∧ a ≤ y₀ + d1.T₁)) ∧ a ∈ A) ∧ y₀ + n - a ≤ N ∧ y₀ + n - a ∈ B)).card := by
      exact_mod_cast hpos_z
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    exact ⟨a, ha.2.1.2, ha.2.1.1, ha.2.2.1, ha.2.2.2, by omega⟩
  have hA_trunc : ∀ a, a ≤ N₁' → (a ∈ A ↔ (a ≤ N ∧ a ∈ A) ∨ (y₀ ≤ a ∧ a ≤ y₀ + d1.T₁ ∧ a ∈ A)) := by
    intro a ha_le
    constructor
    · intro haA
      by_cases h1 : a ≤ N
      · left; exact ⟨h1, haA⟩
      · right
        have ha_ge : y₀ ≤ a := nextGt_le hA_inf (N := N) haA (by omega)
        refine ⟨ha_ge, ?_, haA⟩
        by_contra hgt_T1; push Not at hgt_T1
        have ha_gt_T2 : y₀ + d1.T₂ < a := by
          by_contra hle_T2
          have hnot := d1.hA_gap_zero (a - y₀) (by omega) (by omega)
          have hadd : y₀ + (a - y₀) = a := by omega
          rw [hadd] at hnot; exact hnot haA
        set n := a + minElem B - y₀
        have hn_lt : n < M₁ := by omega
        obtain ⟨a', ha'A, ha'_rng, _, hb'B, ha'_le⟩ := hEF_one n hn_lt
        have huniq : a = a' := by
          have hr1 : repCount A B (y₀ + n) = 1 := hstab (y₀ + n) (by omega)
          unfold repCount at hr1
          have hmem1 : a ∈ (Finset.range (y₀ + n + 1)).filter (fun x => x ∈ A ∧ y₀ + n - x ∈ B) := by
            simp only [Finset.mem_filter, Finset.mem_range]
            refine ⟨by omega, haA, ?_⟩
            have hsub : y₀ + n - a = minElem B := by omega
            rw [hsub]; exact minElem_mem hBne
          have hmem2 : a' ∈ (Finset.range (y₀ + n + 1)).filter (fun x => x ∈ A ∧ y₀ + n - x ∈ B) := by
            simp only [Finset.mem_filter, Finset.mem_range]
            exact ⟨by omega, ha'A, hb'B⟩
          exact Finset.card_le_one.mp (le_of_eq hr1) a hmem1 a' hmem2
        have hT1_lt := d1.hT1_lt_T2
        omega
    · rintro (⟨_, haA⟩ | ⟨_, _, haA⟩) <;> exact haA
  have hB_trunc : ∀ b, b ≤ N₁' → (b ∈ B ↔ b ≤ N ∧ b ∈ B) := by
    intro b hb_le
    constructor
    · intro hbB
      refine ⟨?_, hbB⟩
      by_contra hgtN
      have hb_ge : w₀ ≤ b := nextGt_le hB_inf (N := N) hbB (by omega)
      have hy_lt_w : y₀ < w₀ := by
        have : (y₀ : ℝ) < (w₀ : ℝ) := by linarith
        exact_mod_cast this
      set n := minElem A + b - y₀
      have hn_lt : n < M₁ := by omega
      obtain ⟨a', ha'A, _, hb'_le, hb'B, ha'_le⟩ := hEF_one n hn_lt
      have huniq : minElem A = a' := by
        have hr1 : repCount A B (y₀ + n) = 1 := hstab (y₀ + n) (by omega)
        unfold repCount at hr1
        have hmem1 : minElem A ∈ (Finset.range (y₀ + n + 1)).filter (fun x => x ∈ A ∧ y₀ + n - x ∈ B) := by
          simp only [Finset.mem_filter, Finset.mem_range]
          refine ⟨by omega, minElem_mem hAne, ?_⟩
          have hsub : y₀ + n - minElem A = b := by omega
          rw [hsub]; exact hbB
        have hmem2 : a' ∈ (Finset.range (y₀ + n + 1)).filter (fun x => x ∈ A ∧ y₀ + n - x ∈ B) := by
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, ha'A, hb'B⟩
        exact Finset.card_le_one.mp (le_of_eq hr1) (minElem A) hmem1 a' hmem2
      omega
    · rintro ⟨_, hbB⟩; exact hbB
  -- Step 3: Exact truncPoly identities and quadratic recurrence
  have htruncA_N1' : truncPoly A N₁' = truncPoly A N + X ^ y₀ * PA1 := by
    ext n
    rw [truncPoly_coeff, coeff_add, truncPoly_coeff, coeff_X_pow_mul']
    by_cases h1 : n ≤ N₁' ∧ n ∈ A
    · simp only [h1]
      rcases (hA_trunc n h1.1).mp h1.2 with ⟨hN, _⟩ | ⟨hy, hT, _⟩
      · have hnot : ¬ (y₀ ≤ n) := by omega
        simp only [hN, and_self, hnot, ↓reduceIte, add_zero]
      · have hnotN : ¬ (n ≤ N) := by omega
        simp only [hnotN, false_and, hy, ↓reduceIte, zero_add]
        rw [shiftedTruncPoly_coeff]
        have hadd : y₀ + (n - y₀) = n := by omega
        have hT' : n - y₀ ≤ d1.T₁ := by omega
        simp only [hadd, hT', h1.2, and_self, ↓reduceIte]
    · simp only [h1, ↓reduceIte]
      have hnotA0 : ¬ (n ≤ N ∧ n ∈ A) := fun ⟨hN, hA⟩ => h1 ⟨by omega, hA⟩
      simp only [hnotA0, ↓reduceIte, zero_add]
      split_ifs with hy
      · rw [shiftedTruncPoly_coeff]
        have hadd : y₀ + (n - y₀) = n := by omega
        have hnot1 : ¬ (n - y₀ ≤ d1.T₁ ∧ n ∈ A) := fun ⟨hT, hA⟩ => h1 ⟨by omega, hA⟩
        simp only [hadd, hnot1, ↓reduceIte]
      · rfl
  have htruncB_N1' : truncPoly B N₁' = truncPoly B N := by
    ext n; rw [truncPoly_coeff, truncPoly_coeff]
    by_cases h1 : n ≤ N₁' ∧ n ∈ B
    · have h2 := (hB_trunc n h1.1).mp h1.2
      simp only [h1, h2]
    · have h2 : ¬ (n ≤ N ∧ n ∈ B) := fun ⟨hN, hB⟩ => h1 ⟨by omega, hB⟩
      simp only [h1, h2, ↓reduceIte]
  have hXN1_W : X ^ (N₁' + 1) * WPoly A B N₁' = X ^ y₀ * F := by
    have htr_N := truncPoly_exact_identity hstab hN_ge_n0
    have htr_N1' := truncPoly_exact_identity hstab (by omega : n₀ ≤ N₁')
    have hlhs : (1 - X) * (truncPoly A N₁' * truncPoly B N₁') = VPoly A B n₀ - X ^ y₀ * F := by
      rw [htruncA_N1', htruncB_N1']
      calc
        (1 - X) * ((truncPoly A N + X ^ y₀ * PA1) * truncPoly B N)
            = (1 - X) * (truncPoly A N * truncPoly B N) + X ^ y₀ * ((1 - X) * (PA1 * truncPoly B N)) := by ring
        _ = (VPoly A B n₀ - X ^ (N + 1) * WPoly A B N) + X ^ y₀ * (U₁ - F) := by
              rw [htr_N]; simp only [F]; ring
        _ = (VPoly A B n₀ - X ^ y₀ * U₁) + X ^ y₀ * (U₁ - F) := by rw [hXW]
        _ = VPoly A B n₀ - X ^ y₀ * F := by ring
    rw [htr_N1'] at hlhs
    linear_combination -hlhs
  have hpoly_exact : X ^ (N₁' + 1) * VPoly A B n₀ * WPoly A B N₁' =
      X ^ (2 * (N + 1)) * (WPoly A B N) ^ 2 := by
    calc
      X ^ (N₁' + 1) * VPoly A B n₀ * WPoly A B N₁'
          = VPoly A B n₀ * (X ^ (N₁' + 1) * WPoly A B N₁') := by ring
      _ = VPoly A B n₀ * (X ^ y₀ * F) := by rw [hXN1_W]
      _ = X ^ y₀ * (VPoly A B n₀ * F) := by ring
      _ = X ^ y₀ * (X ^ y₀ * U₁ ^ 2) := by rw [hVF]
      _ = (X ^ y₀ * U₁) ^ 2 := by ring
      _ = (X ^ (N + 1) * WPoly A B N) ^ 2 := by rw [hXW]
      _ = X ^ (2 * (N + 1)) * (WPoly A B N) ^ 2 := by rw [mul_pow, ← pow_mul]; ring
  have hWN1_ne : WPoly A B N₁' ≠ 0 := by
    intro h0; have := WPoly_eval_one A B N₁'; rw [h0] at this; simp at this
  have hW_ord : (WPoly A B N₁').natTrailingDegree = max (minElem A) (minElem B) := by
    have hl := Polynomial.natTrailingDegree_mul (pow_ne_zero (N₁' + 1) X_ne_zero) hWN1_ne
    have hr := Polynomial.natTrailingDegree_mul (pow_ne_zero y₀ X_ne_zero) hF_ne
    rw [hXN1_W] at hl
    rw [Polynomial.natTrailingDegree_X_pow] at hl hr
    rw [hr] at hl
    omega
  have hstrip_quad : stripPoly (VPoly A B n₀) * stripPoly (WPoly A B N₁') =
      (stripPoly (WPoly A B N)) ^ 2 := by
    have hWN_ord : (WPoly A B N).natTrailingDegree = (y₀ - (N + 1)) + u₁ := by
      rw [d1.hWN_U1, Polynomial.natTrailingDegree_mul (pow_ne_zero _ X_ne_zero) hU₁_ne,
          Polynomial.natTrailingDegree_X_pow]
    have hexp : N₁' + 1 + (VPoly A B n₀).natTrailingDegree + (WPoly A B N₁').natTrailingDegree =
        2 * (N + 1) + 2 * (WPoly A B N).natTrailingDegree := by
      rw [hV_props.1, hW_ord, hWN_ord]; omega
    have hmul :
        X ^ (N₁' + 1 + (VPoly A B n₀).natTrailingDegree + (WPoly A B N₁').natTrailingDegree) *
          (stripPoly (VPoly A B n₀) * stripPoly (WPoly A B N₁')) =
        X ^ (2 * (N + 1) + 2 * (WPoly A B N).natTrailingDegree) *
          (stripPoly (WPoly A B N)) ^ 2 := by
      calc
        X ^ (N₁' + 1 + (VPoly A B n₀).natTrailingDegree + (WPoly A B N₁').natTrailingDegree) *
            (stripPoly (VPoly A B n₀) * stripPoly (WPoly A B N₁'))
            = X ^ (N₁' + 1) * (X ^ (VPoly A B n₀).natTrailingDegree * stripPoly (VPoly A B n₀)) *
              (X ^ (WPoly A B N₁').natTrailingDegree * stripPoly (WPoly A B N₁')) := by
                simp only [pow_add]; ring
        _ = X ^ (N₁' + 1) * VPoly A B n₀ * WPoly A B N₁' := by
              rw [X_pow_mul_stripPoly, X_pow_mul_stripPoly]
        _ = X ^ (2 * (N + 1)) * (WPoly A B N) ^ 2 := hpoly_exact
        _ = X ^ (2 * (N + 1)) * (X ^ (WPoly A B N).natTrailingDegree * stripPoly (WPoly A B N)) ^ 2 := by
              rw [X_pow_mul_stripPoly]
        _ = X ^ (2 * (N + 1) + 2 * (WPoly A B N).natTrailingDegree) * (stripPoly (WPoly A B N)) ^ 2 := by
              rw [mul_pow, ← pow_mul, pow_add]; ring
    rw [hexp] at hmul
    exact mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) hmul
  have hT_bound : crossExcess A B N₁' ≤ 2 * crossExcess A B N + errSum A B n₀ + 2 * n₀ := by
    have hderiv := congrArg (fun P => (Polynomial.derivative P).eval 1) hpoly_exact
    simp only [derivative_mul, derivative_pow, derivative_X, mul_one, eval_add, eval_mul, eval_pow,
      eval_X, eval_C, one_pow, VPoly_eval_one, WPoly_eval_one, WPoly_deriv_eval_one,
      hV_props.2.2.2.2.2] at hderiv
    have hc_le : errSigned A B n₀ ≤ (errSum A B n₀ : ℤ) := (abs_le.mp (abs_errSigned_le_errSum A B n₀)).2
    have hdiff_N : (2 * (N + 1) : ℤ) - (N₁' + 1 : ℤ) ≤ 2 * (n₀ : ℤ) := by
      have h1 : 2 * N + 2 ≤ N₁' + 1 + 2 * n₀ := by omega
      have h2 : ((2 * N + 2 : ℕ) : ℤ) ≤ ((N₁' + 1 + 2 * n₀ : ℕ) : ℤ) := by exact_mod_cast h1
      push_cast at h2; linarith
    have hT_z : (crossExcess A B N₁' : ℤ) ≤ 2 * (crossExcess A B N : ℤ) + (errSum A B n₀ : ℤ) + 2 * (n₀ : ℤ) := by
      push_cast at hderiv; linarith
    exact_mod_cast hT_z
  exact ⟨{
    N₁' := N₁'
    T₁ := d1.T₁
    U₁ := U₁
    hN₁'_lo := hN₁'_lo
    hN₁'_hi := hN₁'_hi
    hN₁'_gt := hN₁'_gt
    hN₁'_formula := rfl
    hU₁_eval := hU₁_props.1
    hU₁_strip0 := hU₁_props.2.2.2.2.2.1
    hPA1_V := d1.hPA1_V
    hWN_U1 := d1.hWN_U1
    hA_trunc := hA_trunc
    hB_trunc := hB_trunc
    hpoly_exact := hpoly_exact
    hW_ord := hW_ord
    hstrip_quad := hstrip_quad
    hT_bound := hT_bound
  }⟩

end

end AlmostPerfect
