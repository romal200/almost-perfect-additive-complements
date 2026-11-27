import AlmostPerfect.PolynomialInvariants
import Mathlib.Tactic

/-!
# Section 3 (cont.): Unique Large Differences, Modular Difference Density, and Zhang's Gap Lemma

Formalizes Lemmas 3.2, 3.4, and 3.5 of `PROOF.md`:
- `unique_large_diff` (Lemma 3.2): if `a, a' ∈ A`, `b, b' ∈ B`, `(a, b) ≠ (a', b')`,
  and `b + a' = b' + a`, then `a < n₀`, `a' < n₀`, `b < n₀`, `b' < n₀`.
- `zhang_gap_lemma` (Lemma 3.5): for consecutive `x < y` in `A` with `x ≥ 2n₀` and
  `y ≥ 3x + n₀`, proves `B ∩ [y - x + n₀, y + x + n₀ - 1] = ∅`, `T(y - 1) ≤ n₀`,
  and `|A(y + t) - A(x) - A(t)| ≤ C`, `|A(x)B(y + t) - y| ≤ C` for `0 ≤ t ≤ x`.
-/

namespace AlmostPerfect

open BigOperators

noncomputable section

/-- Discrete convolution of `ℤ`-valued sequences on `ℕ`. -/
def dconv (f g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), f k * g (n - k)

lemma dconv_comm (f g : ℕ → ℤ) (n : ℕ) : dconv f g n = dconv g f n := by
  unfold dconv
  rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => f x * g y)]
  rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => g x * f y)]
  rw [← Finset.Nat.sum_antidiagonal_swap]
  apply Finset.sum_congr rfl
  intro p _
  simp [Prod.swap, mul_comm]

lemma dconv_comm_fun (f g : ℕ → ℤ) : dconv f g = dconv g f :=
  funext (dconv_comm f g)

lemma dconv_assoc (f g h : ℕ → ℤ) (n : ℕ) :
    dconv (dconv f g) h n = dconv f (dconv g h) n := by
  unfold dconv
  have hL :
      ∑ k ∈ Finset.range (n + 1), (∑ i ∈ Finset.range (k + 1), f i * g (k - i)) * h (n - k) =
      ∑ k ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (k + 1), f i * g (k - i) * h (n - k) := by
    apply Finset.sum_congr rfl; intro k _; rw [Finset.sum_mul]
  have hR :
      ∑ i ∈ Finset.range (n + 1), f i * (∑ j ∈ Finset.range (n - i + 1), g j * h (n - i - j)) =
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n - i + 1), f i * g j * h (n - i - j) := by
    apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hL, hR]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij (fun p _ => ⟨p.2, p.1 - p.2⟩)
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
    omega
  · rintro ⟨a₁, b₁⟩ hp₁ ⟨a₂, b₂⟩ hp₂ heq
    simp only [Finset.mem_sigma, Finset.mem_range] at hp₁ hp₂
    have h1 : b₁ = b₂ := congrArg Sigma.fst heq
    have h2 : a₁ - b₁ = a₂ - b₂ := by
      have := congrArg Sigma.snd heq
      simpa using this
    have ha : a₁ = a₂ := by omega
    subst h1; subst ha; rfl
  · intro q hq
    simp only [Finset.mem_sigma, Finset.mem_range] at hq
    refine ⟨⟨q.1 + q.2, q.1⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range]; omega
    · ext
      · rfl
      · simp
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    have heq : n - p.2 - (p.1 - p.2) = n - p.1 := by omega
    rw [heq]

lemma dconv_add_right (f g₁ g₂ : ℕ → ℤ) (n : ℕ) :
    dconv f (fun k => g₁ k + g₂ k) n = dconv f g₁ n + dconv f g₂ n := by
  unfold dconv
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma dconv_sub_right (f g₁ g₂ : ℕ → ℤ) (n : ℕ) :
    dconv f (fun k => g₁ k - g₂ k) n = dconv f g₁ n - dconv f g₂ n := by
  unfold dconv
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma dconv_congr_right {f g₁ g₂ : ℕ → ℤ} {n : ℕ}
    (hg : ∀ k ≤ n, g₁ k = g₂ k) :
    dconv f g₁ n = dconv f g₂ n := by
  unfold dconv
  apply Finset.sum_congr rfl
  intro k hk
  have hle : n - k ≤ n := Nat.sub_le n k
  rw [hg (n - k) hle]

/-- **Lemma 3.2 (Uniqueness of large differences):**
If `r(m) = 1` for all `m ≥ n₀`, and `(a, b), (a', b') ∈ A × B` are distinct pairs with
`b + a' = b' + a` (i.e. `b - a = b' - a'` in `ℤ`), then `a + b' < n₀` (hence `a, a', b, b' < n₀`). -/
lemma unique_large_diff {A B : Set ℕ} {n₀ : ℕ}
    (hstab : ∀ m ≥ n₀, repCount A B m = 1)
    {a a' b b' : ℕ} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B)
    (hdiff : b + a' = b' + a) (hne : a ≠ a' ∨ b ≠ b') :
    a + b' < n₀ := by
  classical
  have ha_ne : a ≠ a' := by rcases hne with h | h <;> omega
  by_contra hge
  push Not at hge
  have hcard : repCount A B (a + b') = 1 := hstab (a + b') hge
  unfold repCount at hcard
  have h1 : a ∈ (Finset.range (a + b' + 1)).filter (fun u => u ∈ A ∧ a + b' - u ∈ B) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ha, ?_⟩
    have : a + b' - a = b' := by omega
    rw [this]; exact hb'
  have h2 : a' ∈ (Finset.range (a + b' + 1)).filter (fun u => u ∈ A ∧ a + b' - u ∈ B) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ha', ?_⟩
    have : a + b' - a' = b := by omega
    rw [this]; exact hb
  have hle1 : ((Finset.range (a + b' + 1)).filter (fun u => u ∈ A ∧ a + b' - u ∈ B)).card ≤ 1 := by
    omega
  exact ha_ne (Finset.card_le_one.mp hle1 a h1 a' h2)

/-- **Lemma 3.5 (Zhang's Gap Lemma):**
If `r(m) = 1` for `m ≥ n₀` (`n₀ ≥ 1`), `r(m) ≤ 1 + E` for `m < n₀`, and `x < y` are
consecutive elements of `A` with `2 * n₀ ≤ x` and `3 * x + n₀ ≤ y`, then:
1. `B ∩ [y - x + n₀, y + x + n₀ - 1] = ∅`,
2. `T(y - 1) ≤ n₀`,
3. for every `0 ≤ t ≤ x`,
   `|A(y + t) - A(x) - A(t)| ≤ E + n₀` and `|A(x) * B(y + t) - y| ≤ E + n₀`
   (with `E` taken as `∑_{n < n₀} |r(n) - 1|`). -/
theorem zhang_gap_lemma {A B : Set ℕ} {n₀ E : ℕ}
    (hn₀ : 1 ≤ n₀)
    (hstab : ∀ m ≥ n₀, repCount A B m = 1)
    (hE : (∑ m ∈ Finset.range n₀, |(repCount A B m : ℤ) - 1|) ≤ (E : ℤ))
    {x y : ℕ} (hxA : x ∈ A) (hyA : y ∈ A)
    (hgap : ∀ a ∈ A, x < a → y ≤ a)
    (hx_ge : 2 * n₀ ≤ x) (hy_ge : 3 * x + n₀ ≤ y) :
    (∀ b ∈ B, ¬ (y - x + n₀ ≤ b ∧ b ≤ y + x + n₀ - 1)) ∧
    crossExcess A B (y - 1) ≤ n₀ ∧
    (∀ t ≤ x,
      |((countNat A (y + t) : ℤ) - (countNat A x : ℤ) - (countNat A t : ℤ))| ≤ (E + n₀ : ℤ) ∧
      |((countNat A x : ℤ) * (countNat B (y + t) : ℤ) - (y : ℤ))| ≤ (E + n₀ : ℤ)) := by
  classical
  -- Indicator functions on ℕ
  let f : ℕ → ℤ := fun n => if n ≤ x ∧ n ∈ A then 1 else 0
  let g : ℕ → ℤ := fun n => if n ∈ B then 1 else 0
  let ftil : ℕ → ℤ := fun n => if n ≤ x then f (x - n) else 0
  let h : ℕ → ℤ := fun _ => 1
  let δ : ℕ → ℤ := fun n => (repCount A B n : ℤ) - 1
  let D : ℕ → ℤ := fun n => 1 - dconv ftil g n
  -- Key property 1: (f * g)(n) = r(n) = 1 + δ(n) for all n < y
  have hfg : ∀ n < y, dconv f g n = h n + δ n := by
    intro n hn
    have hEq : dconv f g n = (repCount A B n : ℤ) := by
      unfold dconv repCount
      have h1 :
          ∑ k ∈ Finset.range (n + 1), f k * g (n - k) =
          ∑ k ∈ Finset.range (n + 1), if k ∈ A ∧ n - k ∈ B then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        by_cases hkA : k ∈ A
        · have hkx : k ≤ x := by
            by_contra hgt
            push Not at hgt
            have := hgap k hkA hgt
            omega
          by_cases hB : n - k ∈ B
          · simp [f, g, hkx, hkA, hB]
          · simp [f, g, hkx, hkA, hB]
        · simp [f, g, hkA]
      rw [h1, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hEq]
    simp [h, δ]
  -- Key property 2: (f * D)(n) = ((f - ftil) * h)(n) - (ftil * δ)(n) for all n < y
  have hfD : ∀ n < y, dconv f D n = dconv (fun k => f k - ftil k) h n - dconv ftil δ n := by
    intro n hn
    have h1 : dconv f D n = dconv f h n - dconv f (dconv ftil g) n := by
      unfold D; exact dconv_sub_right f h (dconv ftil g) n
    have h2 : dconv f (dconv ftil g) n = dconv ftil (dconv f g) n := by
      rw [← dconv_assoc, dconv_comm_fun f ftil, dconv_assoc]
    have h3 : dconv ftil (dconv f g) n = dconv ftil (fun k => h k + δ k) n :=
      dconv_congr_right (fun k hk => hfg k (lt_of_le_of_lt hk hn))
    have h4 : dconv ftil (fun k => h k + δ k) n = dconv ftil h n + dconv ftil δ n :=
      dconv_add_right ftil h δ n
    have h5 : dconv (fun k => f k - ftil k) h n = dconv f h n - dconv ftil h n := by
      rw [dconv_comm, dconv_sub_right, dconv_comm h f, dconv_comm h ftil]
    rw [h1, h2, h3, h4, h5]
    ring
  -- Key property 3: for n ≥ x, (f * h)(n) = (ftil * h)(n) = A(x)
  have hfh : ∀ n ≥ x, dconv f h n = dconv ftil h n := by
    intro n hn
    unfold dconv
    have hL : ∑ k ∈ Finset.range (n + 1), f k * h (n - k) = ∑ k ∈ Finset.range (x + 1), f k := by
      rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hn))]
      · apply Finset.sum_congr rfl; intro k _; simp [h]
      · intro k hk hnot
        have hgt : ¬ k ≤ x := by
          simp only [Finset.mem_range] at hk hnot; omega
        simp only [f, hgt, false_and, ↓reduceIte, zero_mul]
    have hR : ∑ k ∈ Finset.range (n + 1), ftil k * h (n - k) = ∑ k ∈ Finset.range (x + 1), f (x - k) := by
      rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hn))]
      · apply Finset.sum_congr rfl
        intro k hk
        have hle : k ≤ x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        simp [ftil, h, hle]
      · intro k hk hnot
        have hgt : ¬ k ≤ x := by
          simp only [Finset.mem_range] at hk hnot; omega
        simp only [ftil, hgt, ↓reduceIte, zero_mul]
    rw [hL, hR]
    exact (Finset.sum_range_reflect f (x + 1)).symm
  -- Key property 4: for n ≥ x + n₀, (ftil * δ)(n) = 0
  have hftil_δ : ∀ n ≥ x + n₀, dconv ftil δ n = 0 := by
    intro n hn
    unfold dconv
    apply Finset.sum_eq_zero
    intro k _
    by_cases hkx : k ≤ x
    · have hge : n₀ ≤ n - k := by omega
      have hδ0 : δ (n - k) = 0 := by simp [δ, hstab (n - k) hge]
      rw [hδ0, mul_zero]
    · simp [ftil, hkx]
  -- Combine: (f * D)(n) = 0 for x + n₀ ≤ n < y
  have hfD_zero : ∀ n, x + n₀ ≤ n → n < y → dconv f D n = 0 := by
    intro n hge hlt
    rw [hfD n hlt, hftil_δ n hge, sub_zero]
    have hsub : dconv (fun k => f k - ftil k) h n = dconv f h n - dconv ftil h n := by
      rw [dconv_comm, dconv_sub_right, dconv_comm h f, dconv_comm h ftil]
    rw [hsub, hfh n (by omega), sub_self]
  -- Key property 5: (ftil * g)(n) counts pairs (a, b) ∈ (A∩[0,x]) × B with b + x = a + n
  -- In particular, for n ≥ x + n₀, (ftil * g)(n) ≤ 1, so D(n) ≥ 0!
  have hftil_g_card : ∀ n : ℕ,
      dconv ftil g n =
        (((Finset.range (x + 1)).filter (fun a => a ∈ A ∧ a + n ≥ x ∧ a + n - x ∈ B)).card : ℤ) := by
    intro n
    unfold dconv
    have h1 :
        ∑ k ∈ Finset.range (n + 1), ftil k * g (n - k) =
        ∑ k ∈ Finset.range (n + 1), if k ≤ x ∧ x - k ∈ A ∧ n - k ∈ B then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases h1k : k ≤ x
      · by_cases h2k : x - k ∈ A
        · by_cases h3k : n - k ∈ B
          · simp [ftil, f, g, h1k, h2k, h3k]
          · simp [ftil, f, g, h1k, h2k, h3k]
        · simp [ftil, f, g, h1k, h2k]
      · simp [ftil, h1k]
    rw [h1, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    apply Finset.card_bij (fun k _ => x - k)
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      refine ⟨by omega, hk.2.2.1, by omega, ?_⟩
      have : x - k + n - x = n - k := by omega
      rw [this]; exact hk.2.2.2
    · intro k₁ hk₁ k₂ hk₂ heq
      simp only [Finset.mem_filter, Finset.mem_range] at hk₁ hk₂
      omega
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range] at ha
      refine ⟨x - a, ?_, by omega⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, by omega, ?_, ?_⟩
      · have : x - (x - a) = a := by omega
        rw [this]; exact ha.2.1
      · have : n - (x - a) = a + n - x := by omega
        rw [this]; exact ha.2.2.2
  have hD_nonneg : ∀ n ≥ x + n₀, 0 ≤ D n := by
    intro n hn
    unfold D
    rw [hftil_g_card]
    have hcard_le : ((Finset.range (x + 1)).filter (fun a => a ∈ A ∧ a + n ≥ x ∧ a + n - x ∈ B)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a₁ ha₁ a₂ ha₂
      simp only [Finset.mem_filter, Finset.mem_range] at ha₁ ha₂
      by_contra hne
      have hlt := unique_large_diff hstab ha₁.2.1 ha₂.2.1 ha₁.2.2.2 ha₂.2.2.2
        (by omega : (a₁ + n - x) + a₂ = (a₂ + n - x) + a₁) (Or.inl hne)
      omega
    omega
  -- Key property 6: D(u) = 0 for all u ∈ [x + n₀, 2x + n₀ - 1]
  have hD_zero_upper : ∀ u, x + n₀ ≤ u → u ≤ 2 * x + n₀ - 1 → D u = 0 := by
    intro u hu1 hu2
    have hfDu : dconv f D (u + x) = 0 := hfD_zero (u + x) (by omega) (by omega)
    unfold dconv at hfDu
    have hnonneg_all : ∀ k ∈ Finset.range (u + x + 1), 0 ≤ f k * D (u + x - k) := by
      intro k _
      by_cases hkx : k ≤ x
      · by_cases hkA : k ∈ A
        · have harg : x + n₀ ≤ u + x - k := by omega
          simpa [f, hkx, hkA] using hD_nonneg (u + x - k) harg
        · simp [f, hkA]
      · simp [f, hkx]
    have hx_mem : x ∈ Finset.range (u + x + 1) := Finset.mem_range.mpr (by omega)
    have hterm_zero : f x * D (u + x - x) = 0 := by
      have hge := Finset.single_le_sum hnonneg_all hx_mem
      have hle : 0 ≤ f x * D (u + x - x) := hnonneg_all x hx_mem
      linarith
    have hfx : f x = 1 := by simp [f, hxA]
    have hsub : u + x - x = u := by omega
    rw [hfx, one_mul, hsub] at hterm_zero
    exact hterm_zero
  -- Key property 7: D(d) = 0 for all d ∈ [n₀, 2x + n₀ - 1] by downward induction from x + n₀
  have hD_zero_all : ∀ d, n₀ ≤ d → d ≤ 2 * x + n₀ - 1 → D d = 0 := by
    intro d hd1 hd2
    by_cases hge : x + n₀ ≤ d
    · exact hD_zero_upper d hge hd2
    · -- Downward induction on m = (x + n₀) - d
      have hdown : ∀ m : ℕ, ∀ d : ℕ, n₀ ≤ d → d ≤ 2 * x + n₀ - 1 → x + n₀ - d ≤ m → D d = 0 := by
        intro m
        induction m with
        | zero =>
          intro d _ hd2' hm0
          exact hD_zero_upper d (by omega) hd2'
        | succ m ih =>
          intro d hd1' hd2' hm
          by_cases hle : x + n₀ - d ≤ m
          · exact ih d hd1' hd2' hle
          · have hfDd : dconv f D (x + d) = 0 := hfD_zero (x + d) (by omega) (by omega)
            unfold dconv at hfDd
            have hx_mem : x ∈ Finset.range (x + d + 1) := Finset.mem_range.mpr (by omega)
            have hsum_single : ∑ k ∈ Finset.range (x + d + 1), f k * D (x + d - k) = f x * D (x + d - x) := by
              apply Finset.sum_eq_single x
              · intro k hk hkx_ne
                by_cases hkx : k ≤ x
                · have hk_lt : k < x := by omega
                  have harg1 : n₀ ≤ x + d - k := by omega
                  have harg2 : x + d - k ≤ 2 * x + n₀ - 1 := by omega
                  have harg_m : x + n₀ - (x + d - k) ≤ m := by omega
                  rw [ih (x + d - k) harg1 harg2 harg_m, mul_zero]
                · simp [f, hkx]
              · intro hnot; exact absurd hx_mem hnot
            rw [hsum_single] at hfDd
            have hfx : f x = 1 := by simp [f, hxA]
            have hsub : x + d - x = d := by omega
            rw [hfx, one_mul, hsub] at hfDd
            exact hfDd
      exact hdown (x + n₀ - d) d hd1 hd2 le_rfl
  -- Part (1): B ∩ [y - x + n₀, y + x + n₀ - 1] = ∅
  have hpart1 : ∀ b ∈ B, ¬ (y - x + n₀ ≤ b ∧ b ≤ y + x + n₀ - 1) := by
    intro b hb ⟨hb1, hb2⟩
    set d := b + x - y
    have hd1 : n₀ ≤ d := by omega
    have hd2 : d ≤ 2 * x + n₀ - 1 := by omega
    have hDd : D d = 0 := hD_zero_all d hd1 hd2
    unfold D at hDd
    rw [hftil_g_card] at hDd
    have hpos : 0 < ((Finset.range (x + 1)).filter (fun a => a ∈ A ∧ a + d ≥ x ∧ a + d - x ∈ B)).card := by
      omega
    rcases Finset.card_pos.mp hpos with ⟨a, ha⟩
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    have hdiff : b + a = (a + d - x) + y := by omega
    have hne : y ≠ a := by omega
    have hlt := unique_large_diff hstab hyA ha.2.1 hb ha.2.2.2 hdiff (Or.inl hne)
    omega
  -- Part (2): T(y - 1) ≤ n₀ and |A(x) * B(y + t) - y| ≤ E + n₀
  have hB_const : ∀ t ≤ x, countNat B (y + t) = countNat B (y - 1) := by
    intro t ht
    unfold countNat
    congr 1
    ext b
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hb_le, hbB⟩
      refine ⟨?_, hbB⟩
      by_contra hge
      push Not at hge
      exact hpart1 b hbB ⟨by omega, by omega⟩
    · rintro ⟨hb_le, hbB⟩
      exact ⟨by omega, hbB⟩
  have hA_ym1 : countNat A (y - 1) = countNat A x := by
    unfold countNat
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨ha_le, haA⟩
      refine ⟨?_, haA⟩
      by_contra hge
      push Not at hge
      have := hgap a haA (by omega)
      omega
    · rintro ⟨ha_le, haA⟩
      exact ⟨by omega, haA⟩
  have hpart2_T : crossExcess A B (y - 1) ≤ n₀ := by
    unfold crossExcess
    have hzero_hi : ∀ m ∈ Finset.range (y - 1), n₀ ≤ m → repTrunc A B (y - 1) (y - 1 + 1 + m) = 0 := by
      intro m _ hm
      unfold repTrunc
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro a ha
      simp only [Finset.mem_range] at ha
      rintro ⟨haA, hale, hb_le, hbB⟩
      have hax : a ≤ x := by
        by_contra hgt; push Not at hgt
        have := hgap a haA hgt; omega
      have hbv : y - x + n₀ ≤ y - 1 + 1 + m - a ∧ y - 1 + 1 + m - a ≤ y + x + n₀ - 1 := by
        -- Wait: a + b = y + m ≥ y + n₀, so b ≥ y + n₀ - x; also b ≤ y - 1 ≤ y + x + n₀ - 1!
        omega
      exact hpart1 (y - 1 + 1 + m - a) hbB hbv
    calc
      ∑ m ∈ Finset.range (y - 1), repTrunc A B (y - 1) (y - 1 + 1 + m)
          = ∑ m ∈ Finset.range n₀, repTrunc A B (y - 1) (y - 1 + 1 + m) := by
            rw [← Finset.sum_subset (Finset.range_mono (by omega : n₀ ≤ y - 1))]
            intro m hm hnot
            exact hzero_hi m hm (by simp only [Finset.mem_range] at hnot; omega)
      _ ≤ ∑ m ∈ Finset.range n₀, 1 := by
            apply Finset.sum_le_sum
            intro m _
            calc
              repTrunc A B (y - 1) (y - 1 + 1 + m)
                  ≤ repCount A B (y - 1 + 1 + m) := repTrunc_le_repCount A B (y - 1) _
              _ = 1 := hstab _ (by omega)
      _ = n₀ := by simp
  have hprod_bound : ∀ t ≤ x,
      |((countNat A x : ℤ) * (countNat B (y + t) : ℤ) - (y : ℤ))| ≤ (E + n₀ : ℤ) := by
    intro t ht
    rw [hB_const t ht, ← hA_ym1]
    have hprod := countNat_mul_eq_sum_repCount_add_crossExcess A B (y - 1)
    have hsum_r : (∑ m ∈ Finset.range (y - 1 + 1), (repCount A B m : ℤ)) =
        (y : ℤ) + ∑ m ∈ Finset.range n₀, ((repCount A B m : ℤ) - 1) := by
      have hy_eq : y - 1 + 1 = y := by omega
      rw [hy_eq]
      have hsplit : ∑ m ∈ Finset.range y, ((repCount A B m : ℤ) - 1) =
          ∑ m ∈ Finset.range n₀, ((repCount A B m : ℤ) - 1) := by
        rw [← Finset.sum_subset (Finset.range_mono (by omega : n₀ ≤ y))]
        intro m hm hnot
        have hmge : n₀ ≤ m := by simp only [Finset.mem_range] at hnot; omega
        simp [hstab m hmge]
      have hsub : ∑ m ∈ Finset.range y, ((repCount A B m : ℤ) - 1) =
          (∑ m ∈ Finset.range y, (repCount A B m : ℤ)) - (y : ℤ) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      linarith
    have hcast_prod : (countNat A (y - 1) : ℤ) * (countNat B (y - 1) : ℤ) =
        (∑ m ∈ Finset.range (y - 1 + 1), (repCount A B m : ℤ)) + (crossExcess A B (y - 1) : ℤ) := by
      exact_mod_cast hprod
    rw [hcast_prod, hsum_r]
    have habs_c : |∑ m ∈ Finset.range n₀, ((repCount A B m : ℤ) - 1)| ≤ (E : ℤ) :=
      le_trans (Finset.abs_sum_le_sum_abs _ _) hE
    have hT_nonneg : (0 : ℤ) ≤ (crossExcess A B (y - 1) : ℤ) := Nat.cast_nonneg _
    have hT_le : (crossExcess A B (y - 1) : ℤ) ≤ (n₀ : ℤ) := by exact_mod_cast hpart2_T
    rw [abs_le] at habs_c ⊢
    constructor <;> linarith
  -- Part (3): |A(y + t) - A(x) - A(t)| ≤ E + n₀ for 0 ≤ t ≤ x
  have hpart3 : ∀ t ≤ x,
      |((countNat A (y + t) : ℤ) - (countNat A x : ℤ) - (countNat A t : ℤ))| ≤ (E + n₀ : ℤ) := by
    intro t ht
    let fy : ℕ → ℤ := fun n => if y + n ∈ A then 1 else 0
    let δy : ℕ → ℤ := fun n => dconv fy g n - 1
    -- For n₀ ≤ n ≤ x, (fy * g)(n) = 1 so δy(n) = 0
    have hδy_zero : ∀ n, n₀ ≤ n → n ≤ x → δy n = 0 := by
      intro n hn1 hn2
      have hfg_y : dconv fy g n = (repCount A B (y + n) : ℤ) := by
        unfold dconv repCount
        have h1 :
            ∑ k ∈ Finset.range (n + 1), fy k * g (n - k) =
            ∑ k ∈ Finset.range (n + 1), if y + k ∈ A ∧ n - k ∈ B then (1 : ℤ) else 0 := by
          apply Finset.sum_congr rfl; intro k _
          by_cases h1k : y + k ∈ A
          · by_cases h2k : n - k ∈ B <;> simp [fy, g, h1k, h2k]
          · simp [fy, g, h1k]
        rw [h1, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        congr 1
        apply Finset.card_bij (fun k _ => y + k)
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
          refine ⟨by omega, hk.2.1, ?_⟩
          have : y + n - (y + k) = n - k := by omega
          rw [this]; exact hk.2.2
        · intro k₁ _ k₂ _ heq; omega
        · intro a ha
          simp only [Finset.mem_filter, Finset.mem_range] at ha
          have hay : y ≤ a := by
            by_contra hlt; push Not at hlt
            have hax : a ≤ x := by
              by_contra hgt; push Not at hgt
              have := hgap a ha.2.1 hgt; omega
            exact hpart1 (y + n - a) ha.2.2 ⟨by omega, by omega⟩
          refine ⟨a - y, ?_, by omega⟩
          simp only [Finset.mem_filter, Finset.mem_range]
          refine ⟨by omega, ?_, ?_⟩
          · have : y + (a - y) = a := by omega
            rw [this]; exact ha.2.1
          · have : n - (a - y) = y + n - a := by omega
            rw [this]; exact ha.2.2
      simp only [δy, hfg_y, hstab (y + n) (by omega), Nat.cast_one, sub_self]
    -- For n < n₀, (fy * g)(n) ∈ {0, 1}, so |δy(n)| ≤ 1
    have hδy_bound : ∀ n < n₀, |δy n| ≤ 1 := by
      intro n hn
      have h0 : 0 ≤ dconv fy g n := by
        unfold dconv
        apply Finset.sum_nonneg
        intro k _
        by_cases h1k : y + k ∈ A
        · by_cases h2k : n - k ∈ B <;> simp [fy, g, h1k, h2k]
        · simp [fy, g, h1k]
      have h1 : dconv fy g n ≤ (repCount A B (y + n) : ℤ) := by
        unfold dconv repCount
        have hrew :
            ∑ k ∈ Finset.range (n + 1), fy k * g (n - k) =
            (((Finset.range (n + 1)).filter (fun k => y + k ∈ A ∧ n - k ∈ B)).card : ℤ) := by
          have : ∑ k ∈ Finset.range (n + 1), fy k * g (n - k) =
              ∑ k ∈ Finset.range (n + 1), if y + k ∈ A ∧ n - k ∈ B then (1 : ℤ) else 0 := by
            apply Finset.sum_congr rfl; intro k _
            by_cases h1k : y + k ∈ A
            · by_cases h2k : n - k ∈ B <;> simp [fy, g, h1k, h2k]
            · simp [fy, g, h1k]
          rw [this, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [hrew]
        norm_cast
        apply Finset.card_le_card_of_injOn (fun k => y + k)
        · intro k hk
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk ⊢
          refine ⟨by omega, hk.2.1, ?_⟩
          have : y + n - (y + k) = n - k := by omega
          rw [this]; exact hk.2.2
        · intro k₁ _ k₂ _ heq; dsimp only at heq; omega
      have hr1 : repCount A B (y + n) = 1 := hstab (y + n) (by omega)
      rw [hr1] at h1
      simp only [δy, Nat.cast_one] at h1 ⊢
      rw [abs_le]
      omega
    -- Identity: (fy * h)(t) - (f * h)(t) = (f * δy)(t) - (fy * δ)(t)
    have hident : dconv fy h t - dconv f h t = dconv f δy t - dconv fy δ t := by
      have hL : dconv fy (dconv f g) t = dconv f (dconv fy g) t := by
        rw [← dconv_assoc, dconv_comm_fun fy f, dconv_assoc]
      have hfg_t : dconv fy (dconv f g) t = dconv fy h t + dconv fy δ t := by
        rw [dconv_congr_right (fun k hk => hfg k (by omega)), dconv_add_right]
      have hfyg_t : dconv f (dconv fy g) t = dconv f h t + dconv f δy t := by
        have hrew : ∀ k ≤ t, dconv fy g k = h k + δy k := fun k _ => by simp [h, δy]
        rw [dconv_congr_right hrew, dconv_add_right]
      linarith
    -- Relate (fy * h)(t) = A(y + t) - A(x) and (f * h)(t) = A(t)
    have hfh_t : dconv f h t = (countNat A t : ℤ) := by
      unfold dconv countNat
      have h1 : ∑ k ∈ Finset.range (t + 1), f k * h (t - k) =
          ∑ k ∈ Finset.range (t + 1), if k ∈ A then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl; intro k hk
        have hkx : k ≤ x := by simp only [Finset.mem_range] at hk; omega
        by_cases hkA : k ∈ A <;> simp [f, h, hkx, hkA]
      rw [h1, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hfyh_t : dconv fy h t = (countNat A (y + t) : ℤ) - (countNat A x : ℤ) := by
      unfold dconv countNat
      have h1 : ∑ k ∈ Finset.range (t + 1), fy k * h (t - k) =
          (((Finset.range (t + 1)).filter (fun k => y + k ∈ A)).card : ℤ) := by
        have : ∑ k ∈ Finset.range (t + 1), fy k * h (t - k) =
            ∑ k ∈ Finset.range (t + 1), if y + k ∈ A then (1 : ℤ) else 0 := by
          apply Finset.sum_congr rfl; intro k _
          by_cases hkA : y + k ∈ A <;> simp [fy, h, hkA]
        rw [this, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [h1]
      have hcard_add :
          ((Finset.range (x + 1)).filter (· ∈ A)).card +
          ((Finset.range (t + 1)).filter (fun k => y + k ∈ A)).card =
          ((Finset.range (y + t + 1)).filter (· ∈ A)).card := by
        have hbij : ((Finset.range (t + 1)).filter (fun k => y + k ∈ A)).card =
            ((Finset.Ico y (y + t + 1)).filter (· ∈ A)).card := by
          apply Finset.card_bij (fun k _ => y + k)
          · intro k hk; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hk ⊢; exact ⟨by omega, hk.2⟩
          · intro k₁ _ k₂ _ heq; omega
          · intro a ha; simp only [Finset.mem_filter, Finset.mem_Ico] at ha
            refine ⟨a - y, ?_, by omega⟩
            simp only [Finset.mem_filter, Finset.mem_range]
            refine ⟨by omega, ?_⟩
            have hsub : y + (a - y) = a := by omega
            rw [hsub]
            exact ha.2
        rw [hbij, ← Finset.card_union_of_disjoint]
        · congr 1
          ext a
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
          constructor
          · rintro (⟨h1a, h2a⟩ | ⟨h1a, h2a⟩) <;> exact ⟨by omega, h2a⟩
          · rintro ⟨ha_le, haA⟩
            by_cases hax : a ≤ x
            · exact Or.inl ⟨by omega, haA⟩
            · have hay := hgap a haA (by omega)
              exact Or.inr ⟨by omega, haA⟩
        · rw [Finset.disjoint_left]
          intro a ha1 ha2
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at ha1 ha2
          omega
      omega
    -- Bound |dconv f δy t| ≤ n₀ and |dconv fy δ t| ≤ E
    have hbd1 : |dconv f δy t| ≤ (n₀ : ℤ) := by
      rw [dconv_comm]
      unfold dconv
      calc
        |∑ k ∈ Finset.range (t + 1), δy k * f (t - k)|
            ≤ ∑ k ∈ Finset.range (t + 1), |δy k * f (t - k)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range (t + 1), if k < n₀ then (1 : ℤ) else 0 := by
            apply Finset.sum_le_sum
            intro k hk
            have hkt : k ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            by_cases hkn : k < n₀
            · simp only [hkn, ↓reduceIte, abs_mul]
              have hf1 : |f (t - k)| ≤ 1 := by
                dsimp only [f]; split_ifs <;> norm_num
              have hd1 := hδy_bound k hkn
              nlinarith [abs_nonneg (δy k), abs_nonneg (f (t - k))]
            · simp only [hkn, ↓reduceIte]
              have h0 := hδy_zero k (Nat.le_of_not_lt hkn) (le_trans hkt ht)
              simp [h0]
        _ ≤ (n₀ : ℤ) := by
            have hsub : ∑ k ∈ Finset.range (t + 1), (if k < n₀ then (1 : ℤ) else 0) =
                (((Finset.range (t + 1)).filter (· < n₀)).card : ℤ) := by
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
            rw [hsub]
            norm_cast
            calc
              ((Finset.range (t + 1)).filter (· < n₀)).card
                  ≤ (Finset.range n₀).card := by
                    apply Finset.card_le_card
                    intro k hk
                    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
                    exact hk.2
              _ = n₀ := Finset.card_range n₀
    have hbd2 : |dconv fy δ t| ≤ (E : ℤ) := by
      rw [dconv_comm]
      unfold dconv
      calc
        |∑ k ∈ Finset.range (t + 1), δ k * fy (t - k)|
            ≤ ∑ k ∈ Finset.range (t + 1), |δ k * fy (t - k)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range (t + 1), if k < n₀ then |δ k| else 0 := by
            apply Finset.sum_le_sum
            intro k _
            by_cases hkn : k < n₀
            · simp only [hkn, ↓reduceIte, abs_mul]
              have hfy1 : |fy (t - k)| ≤ 1 := by
                by_cases h1k : y + (t - k) ∈ A <;> simp [fy, h1k]
              nlinarith [abs_nonneg (δ k), abs_nonneg (fy (t - k))]
            · simp only [hkn, ↓reduceIte]
              have h0 : δ k = 0 := by simp [δ, hstab k (Nat.le_of_not_lt hkn)]
              simp [h0]
        _ ≤ ∑ k ∈ Finset.range n₀, |δ k| := by
            rw [← Finset.sum_filter]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro k hk
              simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
              exact hk.2
            · intro k _ _; exact abs_nonneg _
        _ ≤ (E : ℤ) := hE
    have hrew : (countNat A (y + t) : ℤ) - (countNat A x : ℤ) - (countNat A t : ℤ) =
        dconv f δy t - dconv fy δ t := by
      linarith [hfyh_t, hfh_t, hident]
    rw [hrew]
    have htri := abs_sub (dconv f δy t) (dconv fy δ t)
    linarith
  exact ⟨hpart1, hpart2_T, fun t ht => ⟨hpart3 t ht, hprod_bound t ht⟩⟩

end

end AlmostPerfect
