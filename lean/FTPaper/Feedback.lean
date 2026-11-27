import Mathlib

/-!
# Lemma C: cost of the feedback conversions, and the cost part of Theorem 1

Paper: Lemma 5.1 and Theorem 1.3.

A batch has `W` rows. One run of the procedure uses `w` calls outside conversions and two
rounds of `2s` conversions. `G = W / (2s)` batches of conversion rows fill one batch, so a
depth-`g` run feeds `2/G` batches per batch back into the depth-`(g−1)` procedure. Depth 0
converts directly at `A` calls per row: `4s · A = (2W/G) · A` calls per batch.

* `feedbackCost_eq`: closed form `w · ∑_{i ≤ g} (2/G)^i + (2/G)^{g+1} · W · A`.
* `feedbackCost_div_le`: per row, at most `(w/W)/(1 − 2/G) + (2/G)^{g+1} · A`.
* `one_level_cost`: with `w = 2·D·ρ·W` (two predictor applications of `D` pencil stages at
  `ρ` calls per row) and `G = 20` (`δ = 1/40`), at most `(10/9)·2Dρ + (1/10)^{g+1}·A`.
-/

namespace FTPaper

/-- Calls per batch of the depth-`g` feedback procedure. -/
noncomputable def feedbackCost (w W A G : ℝ) : ℕ → ℝ
  | 0 => w + 2 * W / G * A
  | g + 1 => w + 2 / G * feedbackCost w W A G g

theorem feedbackCost_eq (w W A G : ℝ) (hG : G ≠ 0) (g : ℕ) :
    feedbackCost w W A G g
      = w * ∑ i ∈ Finset.range (g + 1), (2 / G) ^ i + (2 / G) ^ (g + 1) * W * A := by
  induction g with
  | zero =>
    simp only [feedbackCost, zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, pow_one]
    field_simp
  | succ g ih =>
    rw [feedbackCost, ih, Finset.sum_range_succ' _ (g + 1)]
    have hs : ∑ i ∈ Finset.range (g + 1), (2 / G) ^ (i + 1)
        = 2 / G * ∑ i ∈ Finset.range (g + 1), (2 / G) ^ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hs]
    ring

/-- Partial geometric sums with ratio in `[0, 1)` are at most `1/(1 − r)`. -/
lemma geom_sum_le_inv {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ i ≤ 1 / (1 - r) := by
  have hpos : 0 < 1 - r := by linarith
  rw [geom_sum_eq (ne_of_lt h1), le_div_iff₀ hpos]
  have hpow : 0 ≤ r ^ n := pow_nonneg h0 n
  rw [div_mul_eq_mul_div, div_le_iff_of_neg (by linarith)]
  nlinarith

/-- **Lemma C, cost per row.** -/
theorem feedbackCost_div_le (w W A G : ℝ) (hW : 0 < W) (hG : 2 < G) (hw : 0 ≤ w) (g : ℕ) :
    feedbackCost w W A G g / W ≤ (w / W) / (1 - 2 / G) + (2 / G) ^ (g + 1) * A := by
  have hG0 : G ≠ 0 := by linarith
  have hr0 : 0 ≤ 2 / G := by positivity
  have hr1 : 2 / G < 1 := by rw [div_lt_one (by linarith)]; linarith
  rw [feedbackCost_eq w W A G hG0]
  have hsum := geom_sum_le_inv hr0 hr1 (g + 1)
  have hwW : 0 ≤ w / W := div_nonneg hw hW.le
  have hsplit : (w * ∑ i ∈ Finset.range (g + 1), (2 / G) ^ i + (2 / G) ^ (g + 1) * W * A) / W
      = w / W * ∑ i ∈ Finset.range (g + 1), (2 / G) ^ i + (2 / G) ^ (g + 1) * A := by
    field_simp
  rw [hsplit]
  have : w / W * ∑ i ∈ Finset.range (g + 1), (2 / G) ^ i ≤ w / W * (1 / (1 - 2 / G)) :=
    mul_le_mul_of_nonneg_left hsum hwW
  calc w / W * ∑ i ∈ Finset.range (g + 1), (2 / G) ^ i + (2 / G) ^ (g + 1) * A
      ≤ w / W * (1 / (1 - 2 / G)) + (2 / G) ^ (g + 1) * A := by linarith
    _ = (w / W) / (1 - 2 / G) + (2 / G) ^ (g + 1) * A := by rw [mul_one_div]

/-- **Theorem 1, cost part.** Two predictor applications of `D` pencil stages at `ρ` calls
per row, exceptional fraction `δ = 1/40` (`G = 20`), feedback depth `g`. -/
theorem one_level_cost (D ρ W A : ℝ) (hW : 0 < W) (hD : 0 ≤ D) (hρ : 0 ≤ ρ) (g : ℕ) :
    feedbackCost (2 * D * ρ * W) W A 20 g / W ≤ 10 / 9 * (2 * D * ρ) + (1 / 10) ^ (g + 1) * A := by
  have h := feedbackCost_div_le (2 * D * ρ * W) W A 20 hW (by norm_num) (by positivity) g
  have e1 : 2 * D * ρ * W / W / (1 - 2 / 20 : ℝ) = 10 / 9 * (2 * D * ρ) := by
    field_simp; ring
  have e2 : (2 / 20 : ℝ) = 1 / 10 := by norm_num
  rw [e1, e2] at h
  exact h

end FTPaper
