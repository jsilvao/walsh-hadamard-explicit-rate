import FTPaper.QFeedback
import FTPaper.Routing

/-!
# Theorem 1 with the routing parameters of Corollary R2

For an integer `x ≥ 2` with `2^x ≥ m + 1`, take `L = 2⌈√(x / log₂ x)⌉` and `q = 2^{⌈2x/L⌉}`.
OpenAI's routing system `system L (log₂ q)` then gives a correct plan with at most
`(20/3·√(m+1) + 40/9) · 2^{11√(x log₂ x) + 7} + 1` child calls per row.
-/

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open OAI.Computability.NearSquareRoot.KernelPass.Rect.Binary (System Label card_label system)
open scoped OAI.Computability.NearSquareRoot.CyclotomicCode

namespace FTPaper

lemma alphabetExp_pos {x : ℕ} (hx : 2 ≤ x) : 1 ≤ alphabetExp x := by
  have h := routing_alphabet hx
  rcases Nat.eq_zero_or_pos (alphabetExp x) with h0 | h0
  · rw [h0, zero_mul] at h; omega
  · exact h0

lemma routed_queries {x m : ℕ} (hx : 2 ≤ x) (hm : m + 1 ≤ 2 ^ x) :
    m + 1 ≤ (2 ^ alphabetExp x) ^ (2 * halfLabel x / 2) := by
  rw [Nat.mul_div_cancel_left _ (by norm_num), ← pow_mul]
  exact hm.trans (Nat.pow_le_pow_right (by norm_num) (routing_alphabet hx))

lemma rho_le_routed {x : ℕ} (hx : 2 ≤ x) :
    6 * (2 + ((2 * halfLabel x : ℕ) : ℝ) * 2 ^ alphabetExp x) * (1 + (alphabetExp x : ℝ)) ^ (2 * halfLabel x)
      ≤ (2 : ℝ) ^ (11 * Real.sqrt (x * Real.logb 2 x) + 7) := by
  have h := routing_exponent_le hx
  have hpos : 0 < rhoBound x := by unfold rhoBound; positivity
  have heq : 6 * (2 + ((2 * halfLabel x : ℕ) : ℝ) * 2 ^ alphabetExp x)
      * (1 + (alphabetExp x : ℝ)) ^ (2 * halfLabel x) = rhoBound x := by
    unfold rhoBound; push_cast; ring
  rw [heq]
  calc rhoBound x = (2 : ℝ) ^ (Real.logb 2 (rhoBound x)) := (Real.rpow_logb (by norm_num) (by norm_num) hpos).symm
    _ ≤ (2 : ℝ) ^ (11 * Real.sqrt (x * Real.logb 2 x) + 7) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h

/-- The call bound of the specific feedback plan with the routing of Corollary R2. -/
theorem fbPlan_calls_bound_routed (x m d : ℕ) (hx : 2 ≤ x) (hm : m + 1 ≤ 2 ^ x)
    (hd : 2 * (m + 2 + 2 * halfLabel x * 2 ^ alphabetExp x) ≤ 10 ^ d) :
    ((fbPlan (2 * halfLabel x) (alphabetExp x) m (uWin m) (vWin m)
        (system (2 * halfLabel x) (alphabetExp x)) d).calls : ℝ)
        / rows (2 * halfLabel x) (alphabetExp x) m (20 ^ d)
      ≤ (20 / 3 * Real.sqrt ((m + 1 : ℕ) : ℝ) + 40 / 9)
          * (2 : ℝ) ^ (11 * Real.sqrt (x * Real.logb 2 x) + 7) + 1 := by
  have hc := fbPlan_calls_bound_explicit (2 * halfLabel x) (alphabetExp x) m d
    (alphabetExp_pos hx) (routed_queries hx hm) hd
  refine hc.trans ?_
  have hρ := rho_le_routed hx
  have hpos : (0 : ℝ) ≤ 20 / 3 * Real.sqrt ((m + 1 : ℕ) : ℝ) + 40 / 9 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hρ hpos]

/-- **Theorem 1 with explicit routing.** For `m + 1` queries (odd) and `x ≥ 2` with
`2^x ≥ m + 1`, OpenAI's routing system with the parameters of Corollary R2 gives a correct plan
on `rows L b m (20^d)` rows with at most `(20/3·√(m+1) + 40/9)·2^{11√(x log₂ x)+7} + 1` child
calls per row, whenever `2 (m + 2 + L 2^b) ≤ 10^d`. -/
theorem theorem1_routed (x m d : ℕ) (hx : 2 ≤ x) (hodd : m + 1 ≡ 1 [MOD 2]) (hm : m + 1 ≤ 2 ^ x)
    (hd : 2 * (m + 2 + 2 * halfLabel x * 2 ^ alphabetExp x) ≤ 10 ^ d) :
    ∃ p : QPlan (Charged.Axes (m := m) (system (2 * halfLabel x) (alphabetExp x)).geometry)
        (rows (2 * halfLabel x) (alphabetExp x) m (20 ^ d))
        (rows (2 * halfLabel x) (alphabetExp x) m (20 ^ d)),
      QPlan.Correct p ∧
      (p.calls : ℝ) / rows (2 * halfLabel x) (alphabetExp x) m (20 ^ d)
        ≤ (20 / 3 * Real.sqrt ((m + 1 : ℕ) : ℝ) + 40 / 9)
            * (2 : ℝ) ^ (11 * Real.sqrt (x * Real.logb 2 x) + 7) + 1 := by
  exact ⟨_, correct_fbPlan _ _ m _ _ _ hodd d, fbPlan_calls_bound_routed x m d hx hm hd⟩

end FTPaper
