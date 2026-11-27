import Mathlib

/-!
# The routing parameters (paper: Corollary 7.2)

For an integer proxy `x ≥ 2` of `log₂ m`, the routing parameters are:
- `s = √(x / log₂ x)` and label length `L = 2⌈s⌉`;
- `q = 2^{lq}` with `lq = ⌈2x/L⌉`;
- auxiliary dimension `D = 2 + L·q`, the bound `dimension_le` of OpenAI's routing systems.

Lemma R1 (`RoutingOAI.lemmaR1_pencil`, against OpenAI's routing) bounds the cost of a pencil stage
by `ρ = 6·D·(1 + log₂ q)^L`. Here we prove the arithmetic about these parameters:

* `routing_alphabet`: `lq · (L/2) ≥ x`, hence `q^{L/2} ≥ 2^x ≥ m`;
* `routing_exponent_le`: `log₂ ρ ≤ 11·√(x·log₂ x) + 7`.
-/

open Real

namespace FTPaper

/-- `⌈√(x / log₂ x)⌉`, half the label length. -/
noncomputable def halfLabel (x : ℕ) : ℕ := ⌈Real.sqrt (x / Real.logb 2 x)⌉₊

/-- `lq = ⌈2x/L⌉` with `L = 2 · halfLabel x`. -/
noncomputable def alphabetExp (x : ℕ) : ℕ := ⌈(2 * x : ℝ) / (2 * halfLabel x)⌉₊

/-- The stage-cost expression `6·D·(1 + lq)^L` with `D = 2 + L·2^{lq}`, the dimension bound
`dimension_le` of OpenAI's routing systems for `ℓ = 2`. -/
noncomputable def rhoBound (x : ℕ) : ℝ :=
  6 * (2 + (2 * halfLabel x : ℝ) * 2 ^ alphabetExp x) * (1 + (alphabetExp x : ℝ)) ^ (2 * halfLabel x)

lemma logb_two_ge_one {x : ℕ} (hx : 2 ≤ x) : 1 ≤ Real.logb 2 x := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
  simpa using (show (2 : ℝ) ≤ x by exact_mod_cast hx)

lemma logb_two_le_self (x : ℕ) (hx : 1 ≤ x) : Real.logb 2 x ≤ x := by
  have h : (x : ℝ) ≤ 2 ^ x := by exact_mod_cast (Nat.lt_two_pow_self).le
  calc Real.logb 2 x ≤ Real.logb 2 ((2 : ℝ) ^ x) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) h
    _ = x := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

lemma halfLabel_pos {x : ℕ} (hx : 2 ≤ x) : 0 < halfLabel x := by
  have hl : 0 < Real.logb 2 x := lt_of_lt_of_le one_pos (logb_two_ge_one hx)
  have : 0 < Real.sqrt (x / Real.logb 2 x) :=
    Real.sqrt_pos.mpr (div_pos (by exact_mod_cast (show 0 < x by omega)) hl)
  exact Nat.ceil_pos.mpr this

/-- **The alphabet is large enough:** `lq · (L/2) ≥ x`, i.e. `q^{L/2} ≥ 2^x`. -/
theorem routing_alphabet {x : ℕ} (hx : 2 ≤ x) : x ≤ alphabetExp x * halfLabel x := by
  have ha : (0 : ℝ) < halfLabel x := by exact_mod_cast halfLabel_pos hx
  have h := Nat.le_ceil ((2 * x : ℝ) / (2 * halfLabel x))
  have : (x : ℝ) ≤ alphabetExp x * halfLabel x := by
    rw [alphabetExp]
    calc (x : ℝ) = (2 * x : ℝ) / (2 * halfLabel x) * halfLabel x := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right h ha.le
  exact_mod_cast this

/-- **Corollary R2 (Lean form).** `log₂ ρ ≤ 11 √(x log₂ x) + 7` for every integer `x ≥ 2`. -/
theorem routing_exponent_le {x : ℕ} (hx : 2 ≤ x) :
    Real.logb 2 (rhoBound x) ≤ 11 * Real.sqrt (x * Real.logb 2 x) + 7 := by
  -- notation
  set ℓ := Real.logb 2 x with hℓ
  set s := Real.sqrt (x / ℓ) with hs
  set y := Real.sqrt (x * ℓ) with hy
  set a := halfLabel x with ha
  set lq := alphabetExp x with hlq
  have hx2 : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hℓ1 : 1 ≤ ℓ := logb_two_ge_one hx
  have hℓ0 : 0 < ℓ := by linarith
  have hℓx : ℓ ≤ x := logb_two_le_self x (by omega)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  -- `y = s ℓ`, `s ≤ y`, `ℓ ≤ y`, `y ≤ x`
  have hys : y = s * ℓ := by
    have hxl : (x : ℝ) * ℓ = (x / ℓ) * ℓ ^ 2 := by field_simp
    rw [hy, hxl, Real.sqrt_mul (div_nonneg hx0.le hℓ0.le), Real.sqrt_sq hℓ0.le]
  have hsy : s ≤ y := by rw [hys]; nlinarith
  have hℓy : ℓ ≤ y := by
    rw [hy]; apply Real.le_sqrt_of_sq_le; nlinarith
  have hyx : y ≤ x := by
    rw [hy]; apply Real.sqrt_le_iff.mpr; constructor; linarith; nlinarith
  -- ceilings
  have ha_pos : (0 : ℝ) < a := by exact_mod_cast halfLabel_pos hx
  have has : s ≤ a := Nat.le_ceil _
  have has1 : (a : ℝ) ≤ s + 1 := (Nat.ceil_lt_add_one hs0).le
  have hlq1 : (lq : ℝ) ≤ y + 1 := by
    have hc := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (2 * x : ℝ) / (2 * a) by positivity)).le
    have hdiv : (2 * x : ℝ) / (2 * a) ≤ y := by
      rw [div_le_iff₀ (by positivity)]
      have hxs : (x : ℝ) = s * y := by
        rw [hys]
        have : s * (s * ℓ) = (Real.sqrt (x / ℓ)) ^ 2 * ℓ := by rw [hs]; ring
        rw [this, Real.sq_sqrt (div_nonneg hx0.le hℓ0.le)]; field_simp
      nlinarith
    calc (lq : ℝ) ≤ (2 * x : ℝ) / (2 * a) + 1 := hc
      _ ≤ y + 1 := by linarith
  -- split the logarithm
  have hD0 : (0 : ℝ) < 2 + (2 * a : ℝ) * 2 ^ lq := by positivity
  have hP0 : (0 : ℝ) < (1 + (lq : ℝ)) ^ (2 * a) := by positivity
  have hsplit : Real.logb 2 (rhoBound x)
      = Real.logb 2 6 + Real.logb 2 (2 + (2 * a : ℝ) * 2 ^ lq)
        + (2 * a : ℕ) * Real.logb 2 (1 + (lq : ℝ)) := by
    rw [rhoBound, ← ha, ← hlq, Real.logb_mul (by positivity) hP0.ne', Real.logb_mul (by norm_num)
      hD0.ne', Real.logb_pow]
  -- each piece
  have h6 : Real.logb 2 6 ≤ 3 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]; norm_num
  have hL : Real.logb 2 (2 * a : ℝ) ≤ 2 * a := by
    have := logb_two_le_self (2 * a) (by have := halfLabel_pos hx; omega)
    push_cast at this; exact this
  have hDlog : Real.logb 2 (2 + (2 * a : ℝ) * 2 ^ lq) ≤ 1 + 2 * a + lq := by
    have hle : 2 + (2 * a : ℝ) * 2 ^ lq ≤ 2 * ((2 * a : ℝ) * 2 ^ lq) := by
      have : (2 : ℝ) ≤ (2 * a : ℝ) * 2 ^ lq := by
        have h1 : (2 : ℝ) ≤ 2 * a := by linarith [show (1 : ℝ) ≤ a by exact_mod_cast halfLabel_pos hx]
        have h2 : (1 : ℝ) ≤ 2 ^ lq := one_le_pow₀ (by norm_num)
        nlinarith
      linarith
    calc Real.logb 2 (2 + (2 * a : ℝ) * 2 ^ lq)
        ≤ Real.logb 2 (2 * ((2 * a : ℝ) * 2 ^ lq)) :=
          Real.logb_le_logb_of_le (by norm_num) hD0 hle
      _ = 1 + Real.logb 2 (2 * a : ℝ) + lq := by
          rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_mul (by positivity)
            (by positivity), Real.logb_self_eq_one (by norm_num), Real.logb_pow,
            Real.logb_self_eq_one (by norm_num)]
          ring
      _ ≤ 1 + 2 * a + lq := by linarith
  have hPlog : Real.logb 2 (1 + (lq : ℝ)) ≤ 2 * ℓ := by
    have hle : 1 + (lq : ℝ) ≤ (x : ℝ) ^ 2 := by nlinarith
    calc Real.logb 2 (1 + (lq : ℝ)) ≤ Real.logb 2 ((x : ℝ) ^ 2) :=
          Real.logb_le_logb_of_le (by norm_num) (by positivity) hle
      _ = 2 * ℓ := by rw [Real.logb_pow]; push_cast; ring
  have hLℓ : ((2 * a : ℕ) : ℝ) * Real.logb 2 (1 + (lq : ℝ)) ≤ 8 * y := by
    have hL2 : ((2 * a : ℕ) : ℝ) ≤ 2 * s + 2 := by push_cast; linarith
    have hpos : 0 ≤ Real.logb 2 (1 + (lq : ℝ)) :=
      Real.logb_nonneg (by norm_num) (by linarith [show (0 : ℝ) ≤ lq from Nat.cast_nonneg _])
    calc ((2 * a : ℕ) : ℝ) * Real.logb 2 (1 + (lq : ℝ)) ≤ (2 * s + 2) * (2 * ℓ) :=
          mul_le_mul hL2 hPlog hpos (by linarith)
      _ = 4 * (s * ℓ) + 4 * ℓ := by ring
      _ ≤ 8 * y := by rw [← hys]; linarith
  rw [hsplit]
  have hsy' : (2 : ℝ) * a ≤ 2 * y + 2 := by linarith
  linarith

end FTPaper
