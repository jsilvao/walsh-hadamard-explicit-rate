import FTPaper.Predictor
import FTPaper.Feedback

/-!
# The Hoeffding window (Theorem 1, step 2) and the constant of Theorem 1

Paper: Section 6. Shifts are bit vectors `γ : Fin m → Bool`, with Hamming weight `weight γ`.

* `sum_exp_weight`: `∑_γ exp(λ(|γ| − m/2)) = (2 cosh(λ/2))^m`.
* `card_tail_le`: `#{γ : t < ||γ| − m/2|} ≤ 2 · 2^m · exp(−2t²/m)` (Chernoff–Hoeffding).
* `window_fraction`: if `2t² ≥ m ln 80`, at most `2^m / 40` shifts fall outside the window.
* `mem_window_iff`, `window_width_le`: the integer window `[⌈m/2 − t⌉, ⌊m/2 + t⌋]` is exactly
  `{c : |c − m/2| ≤ t}`, and has width at most `2t`.
* `theorem1_bound`: with `t = ⌈√(m ln 80 / 2)⌉`, Theorem 1's cost is at most
  `(20/3 · √m + 40/9) ρ + 1` calls per row.
-/

open Finset Real

namespace FTPaper

variable {m : ℕ}

/-- A bit as a real number. -/
def bitR (b : Bool) : ℝ := if b then 1 else 0

lemma weight_eq_sum (γ : Fin m → Bool) : (weight γ : ℝ) = ∑ j, bitR (γ j) := by
  rw [weight, Finset.natCast_card_filter]
  simp [bitR]

lemma weight_not (γ : Fin m → Bool) :
    (weight (fun j => !γ j) : ℝ) = m - weight γ := by
  rw [weight_eq_sum, weight_eq_sum]
  have : ∀ j, bitR (!γ j) = 1 - bitR (γ j) := by
    intro j; cases γ j <;> simp [bitR]
  simp_rw [this]
  rw [Finset.sum_sub_distrib]
  simp

/-- Moment generating function of the centered weight. -/
theorem sum_exp_weight (l : ℝ) :
    ∑ γ : Fin m → Bool, exp (l * ((weight γ : ℝ) - m / 2)) = (2 * cosh (l / 2)) ^ m := by
  have h1 : ∀ γ : Fin m → Bool,
      exp (l * ((weight γ : ℝ) - m / 2)) = ∏ j, exp (l * (bitR (γ j) - 1 / 2)) := by
    intro γ
    rw [← Real.exp_sum]
    congr 1
    rw [weight_eq_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun (_ : Fin m) (b : Bool) => exp (l * (bitR b - 1 / 2)))]
  have hb1 : bitR true = 1 := by simp [bitR]
  have hb0 : bitR false = 0 := by simp [bitR]
  have h2 : ∀ _j : Fin m, ∑ b : Bool, exp (l * (bitR b - 1 / 2)) = 2 * cosh (l / 2) := by
    intro _j
    rw [Fintype.sum_bool, hb1, hb0, cosh_eq]
    have e1 : l * (1 - 1 / 2) = l / 2 := by ring
    have e2 : l * (0 - 1 / 2) = -(l / 2) := by ring
    rw [e1, e2]
    ring
  rw [Finset.prod_congr rfl fun j _ => h2 j, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- **Upper tail.** -/
theorem card_upper_tail (t : ℝ) (ht : 0 ≤ t) (hm : 0 < m) :
    ((univ.filter fun γ : Fin m → Bool => t < (weight γ : ℝ) - m / 2).card : ℝ)
      ≤ 2 ^ m * exp (-2 * t ^ 2 / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set l : ℝ := 4 * t / m with hl
  have hl0 : 0 ≤ l := by positivity
  have hmark : ((univ.filter fun γ : Fin m → Bool => t < (weight γ : ℝ) - m / 2).card : ℝ)
      ≤ ∑ γ : Fin m → Bool, exp (l * ((weight γ : ℝ) - m / 2 - t)) := by
    rw [Finset.natCast_card_filter]
    refine Finset.sum_le_sum fun γ _ => ?_
    split_ifs with h
    · exact one_le_exp (mul_nonneg hl0 (by linarith))
    · exact (exp_pos _).le
  have hfac : ∑ γ : Fin m → Bool, exp (l * ((weight γ : ℝ) - m / 2 - t))
      = exp (-(l * t)) * (2 * cosh (l / 2)) ^ m := by
    rw [← sum_exp_weight l, Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← exp_add]
    congr 1
    ring
  have hcosh : (2 * cosh (l / 2)) ^ m ≤ (2 * exp ((l / 2) ^ 2 / 2)) ^ m :=
    pow_le_pow_left₀ (by positivity) (by linarith [cosh_le_exp_half_sq (l / 2)]) m
  have hpow : (2 * exp ((l / 2) ^ 2 / 2)) ^ m = 2 ^ m * exp (m * ((l / 2) ^ 2 / 2)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
  have hexp : -(l * t) + m * ((l / 2) ^ 2 / 2) = -2 * t ^ 2 / m := by
    rw [hl]; field_simp; ring
  calc ((univ.filter fun γ : Fin m → Bool => t < (weight γ : ℝ) - m / 2).card : ℝ)
      ≤ exp (-(l * t)) * (2 * cosh (l / 2)) ^ m := hfac ▸ hmark
    _ ≤ exp (-(l * t)) * (2 ^ m * exp (m * ((l / 2) ^ 2 / 2))) := by
        rw [← hpow]; exact mul_le_mul_of_nonneg_left hcosh (exp_pos _).le
    _ = 2 ^ m * exp (-(l * t) + m * ((l / 2) ^ 2 / 2)) := by rw [exp_add]; ring
    _ = 2 ^ m * exp (-2 * t ^ 2 / m) := by rw [hexp]

/-- **Lower tail**, by complementing all bits. -/
theorem card_lower_tail (t : ℝ) (ht : 0 ≤ t) (hm : 0 < m) :
    ((univ.filter fun γ : Fin m → Bool => (weight γ : ℝ) - m / 2 < -t).card : ℝ)
      ≤ 2 ^ m * exp (-2 * t ^ 2 / m) := by
  have hbij : (univ.filter fun γ : Fin m → Bool => (weight γ : ℝ) - m / 2 < -t).card
      = (univ.filter fun γ : Fin m → Bool => t < (weight γ : ℝ) - m / 2).card := by
    refine Finset.card_bij (fun γ _ => fun j => !γ j) ?_ ?_ ?_
    · intro γ hγ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
      rw [weight_not]; linarith
    · intro γ₁ _ γ₂ _ h
      funext j; simpa using congrFun h j
    · intro γ hγ
      refine ⟨fun j => !γ j, ?_, by funext j; simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
      rw [weight_not]; linarith
  rw [hbij]
  exact card_upper_tail t ht hm

/-- **Two-sided tail.** -/
theorem card_tail_le (t : ℝ) (ht : 0 ≤ t) (hm : 0 < m) :
    ((univ.filter fun γ : Fin m → Bool => t < |(weight γ : ℝ) - m / 2|).card : ℝ)
      ≤ 2 * 2 ^ m * exp (-2 * t ^ 2 / m) := by
  have hsub : (univ.filter fun γ : Fin m → Bool => t < |(weight γ : ℝ) - m / 2|)
      ⊆ (univ.filter fun γ : Fin m → Bool => t < (weight γ : ℝ) - m / 2)
        ∪ (univ.filter fun γ : Fin m → Bool => (weight γ : ℝ) - m / 2 < -t) := by
    intro γ hγ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hγ ⊢
    rcases lt_abs.mp hγ with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  calc ((univ.filter fun γ : Fin m → Bool => t < |(weight γ : ℝ) - m / 2|).card : ℝ)
      ≤ ((univ.filter fun γ : Fin m → Bool => t < (weight γ : ℝ) - m / 2)
          ∪ (univ.filter fun γ : Fin m → Bool => (weight γ : ℝ) - m / 2 < -t)).card := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((univ.filter fun γ : Fin m → Bool => t < (weight γ : ℝ) - m / 2).card : ℝ)
          + (univ.filter fun γ : Fin m → Bool => (weight γ : ℝ) - m / 2 < -t).card := by
        exact_mod_cast Finset.card_union_le _ _
    _ ≤ 2 ^ m * exp (-2 * t ^ 2 / m) + 2 ^ m * exp (-2 * t ^ 2 / m) :=
        add_le_add (card_upper_tail t ht hm) (card_lower_tail t ht hm)
    _ = 2 * 2 ^ m * exp (-2 * t ^ 2 / m) := by ring

/-- **The window holds all but `1/40` of the shifts** when `2t² ≥ m ln 80`. -/
theorem window_fraction (t : ℝ) (ht : 0 ≤ t) (hm : 0 < m) (htm : m * Real.log 80 ≤ 2 * t ^ 2) :
    ((univ.filter fun γ : Fin m → Bool => t < |(weight γ : ℝ) - m / 2|).card : ℝ) ≤ 2 ^ m / 40 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hexp : exp (-2 * t ^ 2 / m) ≤ exp (-Real.log 80) := by
    apply exp_le_exp.mpr
    rw [div_le_iff₀ hm']
    nlinarith
  have h80 : exp (-Real.log 80) = 1 / 80 := by
    rw [exp_neg, exp_log (by norm_num)]; norm_num
  calc ((univ.filter fun γ : Fin m → Bool => t < |(weight γ : ℝ) - m / 2|).card : ℝ)
      ≤ 2 * 2 ^ m * exp (-2 * t ^ 2 / m) := card_tail_le t ht hm
    _ ≤ 2 * 2 ^ m * (1 / 80) := by rw [← h80]; gcongr
    _ = 2 ^ m / 40 := by ring

/-- The integer window `[⌈m/2 − t⌉, ⌊m/2 + t⌋]` is exactly `{c : |c − m/2| ≤ t}`. -/
theorem mem_window_iff (t : ℝ) (ht : 0 ≤ t) (c : ℕ) :
    (⌈(m : ℝ) / 2 - t⌉₊ ≤ c ∧ c ≤ ⌊(m : ℝ) / 2 + t⌋₊) ↔ |(c : ℝ) - m / 2| ≤ t := by
  rw [Nat.ceil_le, Nat.le_floor_iff (by positivity), abs_le]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- The window has width at most `2t`. -/
theorem window_width_le (t : ℝ) (ht : 0 ≤ t) :
    ((⌊(m : ℝ) / 2 + t⌋₊ : ℝ) - ⌈(m : ℝ) / 2 - t⌉₊) ≤ 2 * t := by
  have h1 : (⌊(m : ℝ) / 2 + t⌋₊ : ℝ) ≤ m / 2 + t := Nat.floor_le (by positivity)
  have h2 : (m : ℝ) / 2 - t ≤ ⌈(m : ℝ) / 2 - t⌉₊ := Nat.le_ceil _
  linarith

/-- `ln 80 ≤ 9/2`, from `e ≥ 2.718` and `e^{1/2} ≥ 3/2`. -/
theorem log_eighty_le : Real.log 80 ≤ 9 / 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have he : (2.718 : ℝ) ≤ exp 1 := le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)
  have hhalf : (3 / 2 : ℝ) ≤ exp (1 / 2) := by
    have := Real.add_one_le_exp (1 / 2 : ℝ); linarith
  have hsplit : exp (9 / 2 : ℝ) = exp 1 ^ 4 * exp (1 / 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [hsplit]
  have h4 : (2.718 : ℝ) ^ 4 ≤ exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) he 4
  nlinarith [exp_pos (1 / 2 : ℝ), pow_pos (exp_pos 1) 4]

/-- **Theorem 1, explicit constant.** With `t = ⌈√(m ln 80 / 2)⌉`, the window width `D ≤ 2t`,
two predictor applications at `ρ` calls per stage, exceptional fraction `1/40` (`G = 20`)
and feedback depth with `(1/10)^{g+1} A ≤ 1`, the calls per row are at most
`(20/3 · √m + 40/9) ρ + 1`. -/
theorem theorem1_bound (D ρ W A : ℝ) (hW : 0 < W) (hD0 : 0 ≤ D) (hρ : 0 ≤ ρ) (g : ℕ)
    (hD : D ≤ 2 * (⌈Real.sqrt (m * Real.log 80 / 2)⌉₊ : ℝ))
    (hA : (1 / 10 : ℝ) ^ (g + 1) * A ≤ 1) :
    feedbackCost (2 * D * ρ * W) W A 20 g / W ≤ (20 / 3 * Real.sqrt m + 40 / 9) * ρ + 1 := by
  have hbase := one_level_cost D ρ W A hW hD0 hρ g
  have hsq : Real.sqrt (m * Real.log 80 / 2) ≤ 3 / 2 * Real.sqrt m := by
    have hlog : Real.log 80 / 2 ≤ 9 / 4 := by linarith [log_eighty_le]
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    calc Real.sqrt (m * Real.log 80 / 2) = Real.sqrt (m * (Real.log 80 / 2)) := by ring_nf
      _ ≤ Real.sqrt (m * (9 / 4)) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 3 / 2 * Real.sqrt m := by
          rw [Real.sqrt_mul hm0, show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]; ring
  have hceil : (⌈Real.sqrt (m * Real.log 80 / 2)⌉₊ : ℝ) ≤ Real.sqrt (m * Real.log 80 / 2) + 1 :=
    (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le
  have hD' : D ≤ 3 * Real.sqrt m + 2 := by linarith
  calc feedbackCost (2 * D * ρ * W) W A 20 g / W
      ≤ 10 / 9 * (2 * D * ρ) + (1 / 10) ^ (g + 1) * A := hbase
    _ ≤ 10 / 9 * (2 * (3 * Real.sqrt m + 2) * ρ) + 1 := by
        have : 2 * D * ρ ≤ 2 * (3 * Real.sqrt m + 2) * ρ := by
          apply mul_le_mul_of_nonneg_right _ hρ; linarith
        linarith
    _ = (20 / 3 * Real.sqrt m + 40 / 9) * ρ + 1 := by ring

end FTPaper
