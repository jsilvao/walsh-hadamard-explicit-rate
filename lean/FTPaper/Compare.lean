import OAI.Computability.NearSquareRoot.KernelGeneratedRepair

/-!
# The stage count of OpenAI's one-level template

OpenAI's binary template runs `4 * clockPeriod m` pencil stages: four predictor applications,
each of `clockPeriod m` stages (their `KernelGeneratedRepair`: "the `4*b` stages use the same one
affine pencil"). `oai_template_cost` (`RoutingOAI.lean`) bounds its calls accordingly.

Here we bound that stage count from below:
`4 * clockPeriod m ≥ 8 ⌈√(2 m ⌈log₂ 2m⌉)⌉ ≥ 11.3 √(m log₂ 2m)`.
Our Theorem 1 uses at most `(20/3) √m + 40/9` stage costs per row. Paper: Proposition 1.4.
-/

open OAI.LinearAlgebra.FiniteFourier OAI.Computability.NearSquareRoot.PencilSearch

namespace FTPaper

/-- The window `[⌊μ - B⌋, ⌈μ + B⌉]` has width at least `2B`. -/
theorem two_radius_le_degree (m : ℕ) : 2 * repairWindowRadius 2 m ≤ repairWindowDegree 2 m := by
  unfold repairWindowDegree
  have h1 : repairWindowMean 2 m + (repairWindowRadius 2 m : ℝ) ≤ repairWindowUpper 2 m :=
    Int.le_ceil _
  have h2 : (repairWindowLower 2 m : ℝ) ≤ repairWindowMean 2 m - (repairWindowRadius 2 m : ℝ) :=
    Int.floor_le _
  have h3 : ((2 * repairWindowRadius 2 m : ℕ) : ℤ) ≤ repairWindowUpper 2 m - repairWindowLower 2 m := by
    have : ((2 * repairWindowRadius 2 m : ℕ) : ℝ)
        ≤ ((repairWindowUpper 2 m - repairWindowLower 2 m : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  omega

/-- **OpenAI's stage count**, exact form: `4 · clockPeriod m ≥ 8 ⌈√(2m ⌈log₂ 2m⌉)⌉`. -/
theorem oai_stages_ge (m : ℕ) :
    8 * ⌈Real.sqrt (2 * (m : ℝ) * repairWindowR m)⌉₊ ≤ 4 * clockPeriod m := by
  have h := two_radius_le_degree m
  have hc := (countPencilOrder_bounds (le_refl 2) m).1
  have hd : repairWindowDegree 2 m ≤ countPencilOrder 2 m := (le_max_right _ _).trans hc
  rw [clockPeriod_eq]
  unfold repairWindowRadius at h
  rw [show (2 : ℕ) - 1 = 1 from rfl, one_mul] at h
  omega

/-- **OpenAI's stage count**, real form: `4 · clockPeriod m ≥ 11.3 √(m log₂ 2m)` for `m ≥ 1`. -/
theorem oai_stages_ge_real {m : ℕ} (hm : 1 ≤ m) :
    (11.3 : ℝ) * Real.sqrt (m * Real.logb 2 (2 * m)) ≤ 4 * clockPeriod m := by
  have h := oai_stages_ge m
  have h' : (8 : ℝ) * ⌈Real.sqrt (2 * (m : ℝ) * repairWindowR m)⌉₊ ≤ 4 * clockPeriod m := by
    exact_mod_cast h
  have hm0 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  -- `log₂ 2m ≤ ⌈log₂ 2m⌉ = repairWindowR m`
  have hR : Real.logb 2 (2 * m) ≤ repairWindowR m := by
    have hp : 2 * m ≤ 2 ^ repairWindowR m := Nat.le_pow_clog (by norm_num) _
    have hp' : (2 * m : ℝ) ≤ (2 : ℝ) ^ repairWindowR m := by exact_mod_cast hp
    calc Real.logb 2 (2 * m) ≤ Real.logb 2 ((2 : ℝ) ^ repairWindowR m) :=
          Real.logb_le_logb_of_le (by norm_num) (by positivity) hp'
      _ = repairWindowR m := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  have hlog0 : 0 ≤ Real.logb 2 (2 * m) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  -- `√(2 m log₂ 2m) ≤ ⌈√(2 m R)⌉`
  have hs : Real.sqrt (2 * (m * Real.logb 2 (2 * m)))
      ≤ ⌈Real.sqrt (2 * (m : ℝ) * repairWindowR m)⌉₊ := by
    calc Real.sqrt (2 * (m * Real.logb 2 (2 * m)))
        ≤ Real.sqrt (2 * (m : ℝ) * repairWindowR m) := by
          apply Real.sqrt_le_sqrt
          have : (0 : ℝ) ≤ m := by linarith
          nlinarith
      _ ≤ _ := Nat.le_ceil _
  -- `11.3 ≤ 8 √2`
  have h2 : (11.3 : ℝ) ≤ 8 * Real.sqrt 2 := by
    have : (1.4125 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
    linarith
  have hsplit : Real.sqrt (2 * (m * Real.logb 2 (2 * m)))
      = Real.sqrt 2 * Real.sqrt (m * Real.logb 2 (2 * m)) :=
    Real.sqrt_mul (by norm_num) _
  have hx : 0 ≤ Real.sqrt (m * Real.logb 2 (2 * m)) := Real.sqrt_nonneg _
  calc (11.3 : ℝ) * Real.sqrt (m * Real.logb 2 (2 * m))
      ≤ 8 * Real.sqrt 2 * Real.sqrt (m * Real.logb 2 (2 * m)) :=
        mul_le_mul_of_nonneg_right h2 hx
    _ = 8 * Real.sqrt (2 * (m * Real.logb 2 (2 * m))) := by rw [hsplit]; ring
    _ ≤ 8 * ⌈Real.sqrt (2 * (m : ℝ) * repairWindowR m)⌉₊ := by linarith
    _ ≤ 4 * clockPeriod m := h'

end FTPaper
