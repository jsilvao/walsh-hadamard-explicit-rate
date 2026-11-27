import FTPaper.ExplicitRate

/-!
# Where the explicit rate beats the trivial bound

The exponent of `walsh_explicit_rate` is `1/2 + 3 ε(x)`. It is below the trivial exponent `1`
for every `x ≥ 2^17`. Paper: the remark after Theorem 1.1.
-/

namespace FTPaper

/-- `ε(x) ≤ 0.1256` for every `x ≥ 2^17`. -/
theorem xε_le_of_large {x : ℕ} (hx : 2 ^ 17 ≤ x) : xε x ≤ 0.1256 := by
  have hX : (131072 : ℝ) ≤ x := by exact_mod_cast hx
  have hX0 : (0 : ℝ) < x := by linarith
  unfold xε
  set X : ℝ := (x : ℝ) with hXdef
  set L : ℝ := Real.logb 2 X with hLdef
  have hXne : X ≠ 0 := hX0.ne'
  -- `log X / X ≤ log 2^17 / 2^17`
  have he : Real.exp 1 ≤ (131072 : ℝ) := by
    have := Real.exp_one_lt_d9
    linarith
  have hanti : Real.log X / X ≤ Real.log 131072 / 131072 :=
    Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he) (Set.mem_Ici.mpr (he.trans hX)) hX
  have hlog : Real.log (131072 : ℝ) = 17 * Real.log 2 := by
    rw [show (131072 : ℝ) = 2 ^ 17 by norm_num, Real.log_pow]
    norm_num
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `L / X ≤ 17 / 2^17`
  have hLX : L / X ≤ 17 / 131072 := by
    have e1 : L / X = (Real.log X / X) / Real.log 2 := by
      rw [hLdef]
      simp only [Real.logb]
      field_simp
    rw [e1, div_le_iff₀ hlog2]
    calc Real.log X / X ≤ Real.log 131072 / 131072 := hanti
      _ = 17 / 131072 * Real.log 2 := by rw [hlog]; ring
  -- `√(L / X) ≤ 0.0114`
  have hs : Real.sqrt (L / X) ≤ 0.0114 := by
    calc Real.sqrt (L / X) ≤ Real.sqrt (0.0114 ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [hLX])
      _ = 0.0114 := Real.sqrt_sq (by norm_num)
  -- `√(X L) = X √(L / X)`
  have hsq : Real.sqrt (X * L) = X * Real.sqrt (L / X) := by
    have e2 : X * L = X ^ 2 * (L / X) := by
      field_simp
    rw [e2, Real.sqrt_mul (sq_nonneg X), Real.sqrt_sq hX0.le]
  rw [hsq, div_le_iff₀ (by linarith)]
  have h1 : X * Real.sqrt (L / X) ≤ X * 0.0114 := mul_le_mul_of_nonneg_left hs hX0.le
  nlinarith [h1]

/-- **The explicit rate beats the trivial exponent** for every `x ≥ 2^17`:
`1/2 + 3 ε(x) < 1`. -/
theorem rate_exponent_lt_one {x : ℕ} (hx : 2 ^ 17 ≤ x) : (1 : ℝ) / 2 + 3 * xε x < 1 := by
  have h := xε_le_of_large hx
  linarith

end FTPaper
