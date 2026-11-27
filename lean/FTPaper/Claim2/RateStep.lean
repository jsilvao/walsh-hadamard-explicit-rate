import FTPaper.Claim2.Level

/-!
# One step of the growing recursion

* `step_le`: from one batch inequality `PrimeKernelBatch 2 A W σ C`, for `k = A f + h` with
  `W ≤ 2^h`, the normalized cost `t(k) = C(H^{⊗k})/2^k` satisfies
  `t(k) ≤ 2C/W + (2σ/W) t(f) + t(h)`.
* `xstep`: at routing parameter `x`, for every large enough `k`, with explicit bounds on every
  quantity: `t(k) ≤ 2^{14x+14} + 2(r + A) + 4B(x) t(f)` with `A(f+1) ≤ k+1`, where `A` is the
  number of half-axes, `r` the padding exponent, and `B(x)` Theorem 1's bound on calls per row.

The proof of `step_le` follows OpenAI's private `primeTransform_bound_padded`
(`LinearAlgebra/FiniteFourier/PrimeKernel.lean`, openai/math commit 3344da5, Apache License
2.0), keeping the local cost divided by `W`.
-/

set_option linter.unusedSectionVars false

open OAI.LinearAlgebra.FiniteFourier
open OAI.Computability.NearSquareRoot

namespace FTPaper.Claim2

/-- The normalized cost of the Walsh–Hadamard transform. -/
noncomputable def tcost (F : Type) [Field F] (k : ℕ) : ℝ :=
  (complexity (primeTransform 2 k (-1 : F)) : ℝ) / 2 ^ k

lemma tcost_nonneg (F : Type) [Field F] (k : ℕ) : 0 ≤ tcost F k := by
  unfold tcost; positivity

/-- The classical bound: `t(h) ≤ 2 (h + 1)`. -/
lemma tcost_classical (F : Type) [Field F] (h : ℕ) : tcost F h ≤ 2 * (h + 1) := by
  have hb := primeTransform_classical_bound 2 h (-1 : F) (by norm_num)
  have hb' : (complexity (primeTransform 2 h (-1 : F)) : ℝ) ≤ (h + 1) * 2 ^ (h + 1) := by
    exact_mod_cast hb
  unfold tcost
  rw [div_le_iff₀ (by positivity)]
  calc (complexity (primeTransform 2 h (-1 : F)) : ℝ) ≤ (h + 1) * 2 ^ (h + 1) := hb'
    _ = 2 * (h + 1) * 2 ^ h := by rw [pow_succ]; ring

/-- **One step of the recursion.** -/
theorem step_le (F : Type) [Field F] {A W σ C : ℕ} (hA : 0 < A) (hW : 0 < W)
    (hbatch : PrimeKernelBatch 2 A W σ C (-1 : F)) (f h : ℕ) (hf : 0 < f) (hWh : W ≤ 2 ^ h) :
    tcost F (A * f + h) ≤ 2 * C / W + 2 * σ / W * tcost F f + tcost F h := by
  have hsplit := primeTransform_complexity_split_batch 2 (A * f) h W (-1 : F) hW
  have hactive := (complexity_le_iff _ _).mpr (hbatch f hf)
  set S : ℕ → ℝ := fun k => complexity (primeTransform 2 k (-1 : F)) with hS
  have hceil : ((2 ^ h ⌈/⌉ W : ℕ) : ℝ) ≤ 2 * 2 ^ h / W := by
    have h1 := OAI.LinearAlgebra.FiniteFourier.ceil_div_real_leX (2 ^ h) W hW
    have hW' : (0 : ℝ) < W := by exact_mod_cast hW
    have h2 : (1 : ℝ) ≤ 2 ^ h / W := by
      rw [le_div_iff₀ hW', one_mul]; exact_mod_cast hWh
    push_cast at h1
    calc ((2 ^ h ⌈/⌉ W : ℕ) : ℝ) ≤ 2 ^ h / W + 1 := h1
      _ ≤ 2 * 2 ^ h / W := by rw [mul_div_assoc]; linarith
  have hraw : S (A * f + h) ≤ ((2 ^ h ⌈/⌉ W : ℕ) : ℝ) *
      ((C : ℝ) * 2 ^ (A * f) + σ * 2 ^ ((A - 1) * f) * S f) + 2 ^ (A * f) * S h := by
    simp only [hS]
    exact_mod_cast hsplit.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hactive) _)
  have hVol : (2 : ℝ) ^ ((A - 1) * f) = 2 ^ (A * f) / 2 ^ f := by
    rw [eq_div_iff (by positivity), ← pow_add]
    congr 1
    rw [← Nat.succ_mul, show (A - 1).succ = A by omega]
  have hbudget : S (A * f + h) ≤ 2 * 2 ^ h / W *
      ((C : ℝ) * 2 ^ (A * f) + σ * (2 ^ (A * f) / 2 ^ f) * S f) + 2 ^ (A * f) * S h := by
    rw [← hVol]
    refine hraw.trans (add_le_add_left (mul_le_mul_of_nonneg_right hceil ?_) _)
    have : 0 ≤ S f := Nat.cast_nonneg _
    positivity
  unfold tcost
  rw [div_le_iff₀ (by positivity)]
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hpow : (2 : ℝ) ^ (A * f + h) = 2 ^ (A * f) * 2 ^ h := pow_add _ _ _
  have key : 2 * 2 ^ h / W * ((C : ℝ) * 2 ^ (A * f) + σ * (2 ^ (A * f) / 2 ^ f) * S f)
        + 2 ^ (A * f) * S h
      = (2 * C / W + 2 * σ / W * (S f / 2 ^ f) + S h / 2 ^ h) * 2 ^ (A * f + h) := by
    rw [hpow]
    field_simp
  calc S (A * f + h) ≤ _ := hbudget
    _ = _ := key

end FTPaper.Claim2

namespace FTPaper.Claim2

/-! ## The step at routing parameter `x` -/

variable (F : Type) [Field F] [CharZero F]

lemma xbatch (x : ℕ) (hx : 4 ≤ x) :
    PrimeKernelBatch 2 (2 * xA x) (xW x) (2 * (xplan x).calls) (Circ.qsparse (xplan2 x hx)) (-1 : F) := by
  have := Circ.kernelBatch_of_correct_sparse (K := F) (xplan2 x hx) (xplan2_correct x hx)
  rwa [xplan2_calls] at this

/-- Theorem 1's bound on calls per row at parameter `x`. -/
noncomputable def Bx (x : ℕ) : ℝ :=
  (20 / 3 * Real.sqrt ((xm x + 1 : ℕ) : ℝ) + 40 / 9) *
    (2 : ℝ) ^ (11 * Real.sqrt (x * Real.logb 2 x) + 7) + 1

/-- **The step at routing parameter `x`.** -/
theorem xstep (x : ℕ) (hx : 4 ≤ x) (k : ℕ) (hk : xr x + 2 * xA x ≤ k) :
    ∃ f : ℕ, f < k ∧ 2 * xA x * (f + 1) ≤ k + 1 ∧
      tcost F k ≤ 2 ^ (14 * x + 14) + 2 * ((xr x + 2 * xA x : ℕ) : ℝ) + 4 * Bx x * tcost F f := by
  set A' := 2 * xA x with hA'
  set r := xr x with hr
  have hApos : 0 < A' := by have := xA_pos x; omega
  have hrA : A' ≤ r := by rw [hr, xr]; omega
  have hW := xW_pos x
  set f := (k - r) / A' with hf
  set h := r + (k - r) % A' with hh
  have hdec : A' * f + h = k := by
    have := Nat.mod_add_div (k - r) A'
    rw [hf, hh]; omega
  have hf1 : 0 < f := Nat.div_pos (by omega) hApos
  have hfk : f < k := by
    have : f ≤ k - r := Nat.div_le_self _ _
    have : 1 ≤ r := by rw [hr, xr]; omega
    omega
  have hmod : (k - r) % A' < A' := Nat.mod_lt _ hApos
  refine ⟨f, hfk, ?_, ?_⟩
  · rw [Nat.mul_add, Nat.mul_one]; omega
  · have hWh : xW x ≤ 2 ^ h :=
      (xW_lt_pow x).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hs := step_le F hApos hW (xbatch F x hx) f h hf1 hWh
    rw [hdec] at hs
    -- the local cost
    have hC := xplan2_cost x hx
    have hW' : (0 : ℝ) < xW x := by exact_mod_cast hW
    have hC' : 2 * (Circ.qsparse (xplan2 x hx) : ℝ) / xW x ≤ 2 ^ (14 * x + 14) := by
      rw [div_le_iff₀ hW']
      have : (9 * Circ.qsparse (xplan2 x hx) : ℝ) ≤ 10 * 2 ^ (14 * x + 12) * xW x := by
        exact_mod_cast hC
      have e : (2 : ℝ) ^ (14 * x + 14) = 4 * 2 ^ (14 * x + 12) := by
        rw [show 14 * x + 14 = (14 * x + 12) + 2 by ring, pow_add]; norm_num; ring
      rw [e]
      have : (0 : ℝ) ≤ 2 ^ (14 * x + 12) * xW x := by positivity
      nlinarith
    -- the leftover digits
    have hh' := tcost_classical F h
    have hh2 : 2 * ((h : ℝ) + 1) ≤ 2 * ((xr x + 2 * xA x : ℕ) : ℝ) := by
      have : h + 1 ≤ xr x + 2 * xA x := by omega
      have : ((h : ℝ) + 1) ≤ ((xr x + 2 * xA x : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    -- the calls
    have hcalls := xcalls x (by omega)
    have hσ : 2 * ((2 * (xplan x).calls : ℕ) : ℝ) / xW x ≤ 4 * Bx x := by
      have : 2 * ((2 * (xplan x).calls : ℕ) : ℝ) / xW x = 4 * (((xplan x).calls : ℝ) / xW x) := by
        push_cast; ring
      rw [this]
      unfold Bx
      linarith
    have htf := tcost_nonneg F f
    calc tcost F k ≤ 2 * (Circ.qsparse (xplan2 x hx) : ℝ) / xW x
          + 2 * ((2 * (xplan x).calls : ℕ) : ℝ) / xW x * tcost F f + tcost F h := hs
      _ ≤ 2 ^ (14 * x + 14) + 4 * Bx x * tcost F f + 2 * ((xr x + 2 * xA x : ℕ) : ℝ) := by
          gcongr
          linarith
      _ = _ := by ring

end FTPaper.Claim2
