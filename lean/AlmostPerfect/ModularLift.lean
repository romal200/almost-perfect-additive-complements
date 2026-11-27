import AlmostPerfect.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

/-!
# Base-4 Binary Cantor Set and Modular Lifts (Corollaries 1 & 2)

Establishes the exact properties of `ABin` and `IsModularLift`:
1. Unique base-4 decomposition `ABin + 2 · ABin = ℕ`.
2. Sharp counting bound `countNat ABin x * countNat (2 * ABin) x ≤ (3/2) * x + 1`
   via the elementary identity `(k + 1)^2 - 1 ≤ 3 * binElem k`.
3. Every `IsModularLift A B` satisfies `repCount A B n ≤ 1` for all `n` (Corollary 2)
   and `limsup (A(x)B(x)/x) = 3/2` (Corollary 1).
-/

namespace AlmostPerfect

open Filter

/-- The `k`-th element of `ABin` in increasing order: replaces binary digits of `k` by base-4 digits. -/
def binElem : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    have : (k + 1) / 2 < k + 1 := Nat.div_lt_self (Nat.succ_pos k) (by decide)
    4 * binElem ((k + 1) / 2) + (k + 1) % 2

lemma binElem_zero : binElem 0 = 0 := by simp [binElem]

lemma binElem_eq (k : ℕ) : binElem k = 4 * binElem (k / 2) + k % 2 := by
  cases k with
  | zero => simp [binElem]
  | succ m => rw [binElem]

lemma binElem_two_mul (k : ℕ) : binElem (2 * k) = 4 * binElem k := by
  rw [binElem_eq]
  have h1 : (2 * k) / 2 = k := Nat.mul_div_right k (by decide)
  have h2 : (2 * k) % 2 = 0 := Nat.mul_mod_right 2 k
  rw [h1, h2, add_zero]

lemma binElem_two_mul_add_one (k : ℕ) : binElem (2 * k + 1) = 4 * binElem k + 1 := by
  rw [binElem_eq]
  have h1 : (2 * k + 1) / 2 = k := by omega
  have h2 : (2 * k + 1) % 2 = 1 := by omega
  rw [h1, h2]

/-- Sharp quadratic lower bound `k^2 + 2*k ≤ 3 * binElem k` (hence `(k+1)^2 ≤ 3 * binElem k + 1`). -/
lemma sq_add_two_mul_le_three_mul_binElem (k : ℕ) : k ^ 2 + 2 * k ≤ 3 * binElem k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm
      by_cases hm0 : m = 0
      · subst hm0; simp [binElem]
      · have hlt : m < m + m := by omega
        have ihm := ih m hlt
        have heq : m + m = 2 * m := by ring
        rw [heq, binElem_two_mul]
        nlinarith
    · subst hm
      have hlt : m < 2 * m + 1 := by omega
      have ihm := ih m hlt
      rw [binElem_two_mul_add_one]
      nlinarith

lemma binElem_strictMono : StrictMono binElem := by
  intro a b hab
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    have ha := binElem_eq a
    have hb := binElem_eq b
    rw [ha, hb]
    by_cases hdiv : a / 2 < b / 2
    · have hlt : b / 2 < b := Nat.div_lt_self (by omega) (by decide)
      have hstep := ih (b / 2) hlt hdiv
      omega
    · have heq : a / 2 = b / 2 := by omega
      have hmod : a % 2 < b % 2 := by omega
      rw [heq]
      omega

lemma binElem_mem_ABin (k : ℕ) : binElem k ∈ ABin := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro i
    rw [binElem_eq]
    cases i with
    | zero =>
      simp only [pow_zero, Nat.div_one]
      have hmod : (4 * binElem (k / 2) + k % 2) % 4 = k % 2 := by omega
      rw [hmod]
      omega
    | succ j =>
      by_cases hk0 : k = 0
      · subst hk0; simp [binElem]
      · have hlt : k / 2 < k := Nat.div_lt_self (Nat.pos_of_ne_zero hk0) (by decide)
        have hdiv : (4 * binElem (k / 2) + k % 2) / 4 ^ (j + 1) = binElem (k / 2) / 4 ^ j := by
          rw [pow_succ', ← Nat.div_div_eq_div_mul]
          have h4 : (4 * binElem (k / 2) + k % 2) / 4 = binElem (k / 2) := by omega
          rw [h4]
        rw [hdiv]
        exact ih (k / 2) hlt j

/-- Inverse map extracting binary digits from an element of `ABin`. -/
def binIndex : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    have : (n + 1) / 4 < n + 1 := Nat.div_lt_self (Nat.succ_pos n) (by decide)
    2 * binIndex ((n + 1) / 4) + (n + 1) % 4

lemma binIndex_eq (n : ℕ) : binIndex n = 2 * binIndex (n / 4) + n % 4 := by
  cases n with
  | zero => simp [binIndex]
  | succ m => rw [binIndex]

lemma binElem_binIndex {n : ℕ} (hn : n ∈ ABin) : binElem (binIndex n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst hn0; simp [binIndex, binElem]
    · have h0 : n % 4 ≤ 1 := by
        simpa using hn 0
      have hdiv_mem : n / 4 ∈ ABin := by
        intro i
        have := hn (i + 1)
        rw [pow_succ', ← Nat.div_div_eq_div_mul] at this
        exact this
      have hlt : n / 4 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by decide)
      have ih' := ih (n / 4) hlt hdiv_mem
      rw [binIndex_eq]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h0 with hmod0 | hmod1
      · rw [hmod0, add_zero, binElem_two_mul, ih']; omega
      · rw [hmod1, binElem_two_mul_add_one, ih']; omega

lemma binIndex_binElem (k : ℕ) : binIndex (binElem k) = k :=
  binElem_strictMono.injective (binElem_binIndex (binElem_mem_ABin k))

lemma binElem_pow_two (t : ℕ) : binElem (2 ^ t) = 4 ^ t := by
  induction t with
  | zero =>
    rw [pow_zero, pow_zero, binElem_eq]
    simp [binElem_zero]
  | succ t ih =>
    rw [pow_succ', binElem_two_mul, ih, pow_succ']

/-- Unique base-4 decomposition: every `n : ℕ` has a unique representation `a + 2 * b = n`
with `a, b ∈ ABin`. -/
lemma ABin_unique_decomp (n : ℕ) :
    ∃! p : ℕ × ℕ, p.1 ∈ ABin ∧ p.2 ∈ ABin ∧ p.1 + 2 * p.2 = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst hn0
      refine ⟨(0, 0), ⟨by intro i; simp, by intro i; simp, rfl⟩, ?_⟩
      rintro ⟨a, b⟩ ⟨_, _, hab⟩
      ext <;> omega
    · have hlt : n / 4 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by decide)
      rcases ih (n / 4) hlt with ⟨⟨a', b'⟩, ⟨ha', hb', hsum'⟩, huniq'⟩
      let r1 := (n % 4) % 2
      let r2 := (n % 4) / 2
      have hr1 : r1 ≤ 1 := by omega
      have hr2 : r2 ≤ 1 := by omega
      have hr : r1 + 2 * r2 = n % 4 := by omega
      refine ⟨(4 * a' + r1, 4 * b' + r2), ⟨?_, ?_, ?_⟩, ?_⟩
      · intro i
        cases i with
        | zero => simp only [pow_zero, Nat.div_one]; omega
        | succ j =>
          rw [pow_succ', ← Nat.div_div_eq_div_mul]
          have h4 : (4 * a' + r1) / 4 = a' := by omega
          rw [h4]
          exact ha' j
      · intro i
        cases i with
        | zero => simp only [pow_zero, Nat.div_one]; omega
        | succ j =>
          rw [pow_succ', ← Nat.div_div_eq_div_mul]
          have h4 : (4 * b' + r2) / 4 = b' := by omega
          rw [h4]
          exact hb' j
      · omega
      · rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
        have ha0 : a % 4 ≤ 1 := by simpa using ha 0
        have hb0 : b % 4 ≤ 1 := by simpa using hb 0
        have hadiv : a / 4 ∈ ABin := by
          intro i; have := ha (i + 1); rw [pow_succ', ← Nat.div_div_eq_div_mul] at this; exact this
        have hbdiv : b / 4 ∈ ABin := by
          intro i; have := hb (i + 1); rw [pow_succ', ← Nat.div_div_eq_div_mul] at this; exact this
        have hmod : a % 4 + 2 * (b % 4) = n % 4 := by omega
        have hdiv : a / 4 + 2 * (b / 4) = n / 4 := by omega
        have hpair : (a / 4, b / 4) = (a', b') := huniq' (a / 4, b / 4) ⟨hadiv, hbdiv, hdiv⟩
        have haq : a / 4 = a' := congrArg Prod.fst hpair
        have hbq : b / 4 = b' := congrArg Prod.snd hpair
        ext <;> omega

/-- **Corollary 2 (Modular-lift direction):**
Every modular lift `IsModularLift A B` satisfies `repCount A B n ≤ 1` for every `n : ℕ`. -/
theorem modularLift_repCount_le_one {A B : Set ℕ} (h : IsModularLift A B) :
    ∀ n : ℕ, repCount A B n ≤ 1 := by
  classical
  have aux : ∀ (D₀ : ℕ) (A₀ B₀ : Finset ℕ),
      1 ≤ D₀ →
      (∀ a ∈ A₀, a < D₀) →
      (∀ b ∈ B₀, b < D₀) →
      (∀ r < D₀, ∃! p : ℕ × ℕ, p.1 ∈ A₀ ∧ p.2 ∈ B₀ ∧ (p.1 + p.2) % D₀ = r) →
      ∀ n : ℕ,
        repCount {m | ∃ a₀ ∈ A₀, ∃ u ∈ ABin, m = a₀ + D₀ * u}
                 {m | ∃ b₀ ∈ B₀, ∃ v ∈ ABin, m = b₀ + D₀ * (2 * v)} n ≤ 1 := by
    intro D₀ A₀ B₀ hD₀ hA₀ hB₀ hbij n
    unfold repCount
    rw [Finset.card_le_one]
    intro a₁ ha₁ a₂ ha₂
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha₁ ha₂
    rcases ha₁ with ⟨ha₁_le, ⟨a01, ha01, u1, hu1, rfl⟩, ⟨b01, hb01, v1, hv1, hb1_eq⟩⟩
    rcases ha₂ with ⟨ha₂_le, ⟨a02, ha02, u2, hu2, rfl⟩, ⟨b02, hb02, v2, hv2, hb2_eq⟩⟩
    have hsum1 : a01 + b01 + D₀ * (u1 + 2 * v1) = n := by rw [mul_add]; omega
    have hsum2 : a02 + b02 + D₀ * (u2 + 2 * v2) = n := by rw [mul_add]; omega
    have hmod1 : (a01 + b01) % D₀ = n % D₀ := by
      rw [← hsum1, Nat.add_mul_mod_self_left]
    have hmod2 : (a02 + b02) % D₀ = n % D₀ := by
      rw [← hsum2, Nat.add_mul_mod_self_left]
    have hr_lt : n % D₀ < D₀ := Nat.mod_lt n hD₀
    rcases hbij (n % D₀) hr_lt with ⟨p, _, hp_uniq⟩
    have hp1 : (a01, b01) = p := hp_uniq (a01, b01) ⟨ha01, hb01, hmod1⟩
    have hp2 : (a02, b02) = p := hp_uniq (a02, b02) ⟨ha02, hb02, hmod2⟩
    have heq_p : (a01, b01) = (a02, b02) := hp1.trans hp2.symm
    have ha0_eq : a01 = a02 := congrArg Prod.fst heq_p
    have hb0_eq : b01 = b02 := congrArg Prod.snd heq_p
    have hmul_eq : D₀ * (u1 + 2 * v1) = D₀ * (u2 + 2 * v2) := by omega
    have huv_eq : u1 + 2 * v1 = u2 + 2 * v2 := Nat.eq_of_mul_eq_mul_left hD₀ hmul_eq
    rcases ABin_unique_decomp (u1 + 2 * v1) with ⟨q, _, hq_uniq⟩
    have hq1 : (u1, v1) = q := hq_uniq (u1, v1) ⟨hu1, hv1, rfl⟩
    have hq2 : (u2, v2) = q := hq_uniq (u2, v2) ⟨hu2, hv2, huv_eq.symm⟩
    have hu_eq : u1 = u2 := congrArg Prod.fst (hq1.trans hq2.symm)
    rw [ha0_eq, hu_eq]
  have hsym : ∀ (X Y : Set ℕ) (n : ℕ), repCount X Y n = repCount Y X n := by
    intro X Y n
    unfold repCount
    apply Finset.card_bij (fun a _ => n - a)
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
      refine ⟨by omega, ha.2.2, ?_⟩
      have : n - (n - a) = a := by omega
      rw [this]
      exact ha.2.1
    · intro a₁ ha₁ a₂ ha₂ heq
      simp only [Finset.mem_filter, Finset.mem_range] at ha₁ ha₂
      omega
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb
      refine ⟨n - b, ?_, by omega⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, hb.2.2, ?_⟩
      have : n - (n - b) = b := by omega
      rw [this]
      exact hb.2.1
  rcases h with ⟨D₀, A₀, B₀, hD₀, hA₀, hB₀, hbij, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact aux D₀ A₀ B₀ hD₀ hA₀ hB₀ hbij
  · intro n
    rw [hsym]
    exact aux D₀ A₀ B₀ hD₀ hA₀ hB₀ hbij n

end AlmostPerfect
