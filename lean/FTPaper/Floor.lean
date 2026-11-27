import FTPaper.QCircuit

/-!
# The per-level floor (paper: Theorem 1.5(1)), conditional on the lower bound

Suppose that over a field `F` of characteristic `0`, the Walsh–Hadamard transform `H^{⊗k}` needs
`c · 2^k · √k` binary linear gates for every `k ≥ 1`. This is OpenAI's lower bound (their Lean
theorem `fourierComplexity`, which we do not vendor), restricted to `G = (ℤ/2)^k`. Then every
correct rational plan on `W` rows over `A ≥ 1` axes makes at least `W · √(2A) / 2` child calls,
that is `σ/W ≥ √(A/2)`.

Otherwise the template would give `C(H^{⊗k}) = O(2^k (1+k)^θ)` with `θ < 1/2`
(`walsh_bound_of_plan`), which contradicts the lower bound. The factor `√2` comes from our
half-axis compilation.
-/

open OAI.LinearAlgebra.FiniteFourier

namespace FTPaper

/-- `k^{1/2 - θ}` exceeds any bound for large `k`. -/
lemma exists_large_sqrt {θ c D : ℝ} (hθ : 0 ≤ θ) (hθ2 : θ < 1 / 2) (hc : 0 < c) (hD : 0 < D) :
    ∃ k : ℕ, 1 ≤ k ∧ D * (1 + (k : ℝ)) ^ θ < c * Real.sqrt k := by
  set η := 1 / 2 - θ with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  set B := 2 * D / c + 1 with hB
  have hB0 : 0 < B := by positivity
  obtain ⟨k, hk⟩ := exists_nat_gt (B ^ (1 / η))
  refine ⟨k + 1, by omega, ?_⟩
  set K : ℝ := ((k + 1 : ℕ) : ℝ) with hK
  have hK1 : (1 : ℝ) ≤ K := by rw [hK]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hK0 : (0 : ℝ) < K := by linarith
  -- `K^η > B`
  have hKB : B < K ^ η := by
    have h1 : B ^ (1 / η) < K := by
      rw [hK]; push_cast; linarith
    have h2 := Real.rpow_lt_rpow (by positivity) h1 hη0
    rw [← Real.rpow_mul hB0.le, one_div, inv_mul_cancel₀ hη0.ne', Real.rpow_one] at h2
    exact h2
  -- `(1+K)^θ ≤ 2 K^θ`
  have hθ1 : θ ≤ 1 := by linarith
  have h1K : (1 + K) ^ θ ≤ 2 * K ^ θ := by
    have : 1 + K ≤ 2 * K := by linarith
    calc (1 + K) ^ θ ≤ (2 * K) ^ θ := Real.rpow_le_rpow (by linarith) this hθ
      _ = 2 ^ θ * K ^ θ := Real.mul_rpow (by norm_num) hK0.le
      _ ≤ 2 * K ^ θ := by
          have : (2 : ℝ) ^ θ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
          rw [Real.rpow_one] at this
          have hKθ : 0 ≤ K ^ θ := by positivity
          nlinarith
  -- `√K = K^θ K^η`
  have hsq : Real.sqrt K = K ^ θ * K ^ η := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hK0, hη]; ring_nf
  have hKθ : 0 < K ^ θ := by positivity
  have hstep : D * (1 + K) ^ θ < c * Real.sqrt K := by
    rw [hsq]
    have h2D : 2 * D < c * K ^ η := by
      have := mul_lt_mul_of_pos_left hKB hc
      rw [hB] at this
      field_simp at this ⊢
      nlinarith
    calc D * (1 + K) ^ θ ≤ D * (2 * K ^ θ) := mul_le_mul_of_nonneg_left h1K hD.le
      _ = K ^ θ * (2 * D) := by ring
      _ < K ^ θ * (c * K ^ η) := mul_lt_mul_of_pos_left h2D hKθ
      _ = c * (K ^ θ * K ^ η) := by ring
  exact hstep

/-- **Theorem 3(1) (per-level floor), conditional on the Walsh–Hadamard lower bound.** -/
theorem template_floor (F : Type) [Field F] [CharZero F]
    (hlow : ∃ c > (0 : ℝ), ∀ k : ℕ, 1 ≤ k →
      c * 2 ^ k * Real.sqrt k ≤ complexity (primeTransform 2 k (-1 : F)))
    {A W : ℕ} (p : QPlan A W W) (hp : QPlan.Correct p) (hA : 0 < A) (hW : 0 < W) :
    ((2 * A : ℕ) : ℝ) ^ ((1 : ℝ) / 2) ≤ ((2 * p.calls : ℕ) : ℝ) / W := by
  by_contra hcon
  push Not at hcon
  set z := ((2 * p.calls : ℕ) : ℝ) / W with hz
  set b := ((2 * A : ℕ) : ℝ) with hb
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hb1 : 1 < b := by
    rw [hb]; push_cast; linarith
  have hz0 : 0 ≤ z := by rw [hz]; positivity
  -- a smaller exponent `θ < 1/2` still saves
  obtain ⟨θ, hθ0, hθ2, hθz⟩ : ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 / 2 ∧ z < b ^ θ := by
    by_cases hz1 : z < 1
    · exact ⟨0, le_rfl, by norm_num, by rw [Real.rpow_zero]; exact hz1⟩
    · push Not at hz1
      set y := b ^ ((1 : ℝ) / 2) with hy
      set z' := (z + y) / 2 with hz'
      have hzz' : z < z' := by rw [hz']; linarith
      have hz'y : z' < y := by rw [hz']; linarith
      have hz'1 : 1 ≤ z' := by linarith
      refine ⟨Real.logb b z', Real.logb_nonneg hb1 hz'1, ?_, ?_⟩
      · have h1 : Real.logb b z' < Real.logb b y :=
          Real.logb_lt_logb hb1 (by linarith) hz'y
        have h2 : Real.logb b y = 1 / 2 := by
          rw [hy, Real.logb_rpow (by linarith) (by linarith)]
        linarith
      · rw [Real.rpow_logb (by linarith) (by linarith) (by linarith)]
        exact hzz'
  obtain ⟨D, hD, hbound⟩ := walsh_bound_of_plan p hp hA hW hθ0 hθz
  obtain ⟨c, hc, hlow'⟩ := hlow
  obtain ⟨k, hk1, hk⟩ := exists_large_sqrt hθ0 hθ2 hc hD
  have h1 := hlow' k hk1
  have h2 := hbound F k
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have : c * 2 ^ k * Real.sqrt k ≤ D * 2 ^ k * (1 + (k : ℝ)) ^ θ := h1.trans h2
  have : c * Real.sqrt k ≤ D * (1 + (k : ℝ)) ^ θ := by
    have e1 : c * 2 ^ k * Real.sqrt k = (c * Real.sqrt k) * 2 ^ k := by ring
    have e2 : D * 2 ^ k * (1 + (k : ℝ)) ^ θ = (D * (1 + (k : ℝ)) ^ θ) * 2 ^ k := by ring
    rw [e1, e2] at this
    exact le_of_mul_le_mul_right this h2k
  linarith

end FTPaper
