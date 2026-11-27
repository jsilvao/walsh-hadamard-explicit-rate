import OAI.LinearAlgebra.FiniteFourier.PrimeKernel

/-!
# OpenAI's padded batch recursion, with its constant made public

Copied from OpenAI's `PrimeKernel.lean` (openai/math, commit 3344da5, Apache 2.0). There these
lemmas are private, and only the existence of a constant is exported. Here they are public, with
an `X` suffix, so that the constant `paddedKernelConstantX ℓ A W σ C r θ` is explicit:

`max (1 + ℓ^{r+A}) ((2C + ℓ^{r+A}) / (A^θ − (σ/W)(1 + W/ℓ^r)))`.

The proofs are OpenAI's, unchanged.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Filter
open scoped Topology

variable {K : Type*} [CommSemiring K]

/-- Solve the single-array recurrence after reserving enough inactive digits
that `A * (1 + f) ≤ 1 + k` in every recursive call. -/
theorem power_bound_of_recursionX {T : ℕ → ℝ} {A k₀ : ℕ} {b C θ small : ℝ}
    (hA : 0 < A) (hb : 0 ≤ b) (hθ : 0 ≤ θ) (hs : b < (A : ℝ) ^ θ)
    (hsmall : 0 ≤ small) (hbase : ∀ k < k₀, T k ≤ small)
    (hstep : ∀ k, k₀ ≤ k → ∃ f < k, A * (1 + f) ≤ 1 + k ∧ T k ≤ C + b * T f) :
    ∀ k : ℕ, T k ≤ max (1 + small) (C / ((A : ℝ) ^ θ - b)) * (1 + (k : ℝ)) ^ θ := by
  let D := max (1 + small) (C / ((A : ℝ) ^ θ - b))
  have hD : 0 < D := lt_of_lt_of_le (by linarith : 0 < 1 + small) (le_max_left _ _)
  have hC : C ≤ D * ((A : ℝ) ^ θ - b) := (div_le_iff₀ (sub_pos.mpr hs)).mp (le_max_right _ _)
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hone (u : ℕ) : 1 ≤ (1 + (u : ℝ)) ^ θ :=
      Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) u]) hθ
    by_cases hk : k < k₀
    · calc
        T k ≤ small := hbase k hk
        _ ≤ D := (by linarith : small ≤ 1 + small).trans (le_max_left _ _)
        _ ≤ D * (1 + (k : ℝ)) ^ θ := le_mul_of_one_le_right hD.le (hone k)
    · obtain ⟨f, hfk, hsize, hrec⟩ := hstep k (by omega)
      have hsize' : (A : ℝ) * (1 + (f : ℝ)) ≤ 1 + (k : ℝ) := by exact_mod_cast hsize
      have hpow := Real.rpow_le_rpow (by positivity) hsize' hθ
      rw [Real.mul_rpow (Nat.cast_nonneg _) (by positivity)] at hpow
      have hcost := le_mul_of_one_le_right (mul_nonneg hD.le (sub_nonneg.mpr hs.le)) (hone f)
      calc
        T k ≤ C + b * T f := hrec
        _ ≤ C + b * (D * (1 + (f : ℝ)) ^ θ) := by gcongr; exact ih f hfk
        _ ≤ D * ((A : ℝ) ^ θ * (1 + (f : ℝ)) ^ θ) := by linarith [hC.trans hcost]
        _ ≤ D * (1 + (k : ℝ)) ^ θ := mul_le_mul_of_nonneg_left hpow hD.le

/-- Real-valued upper bound on the integer number of batches, accounting
for the last, possibly padded, batch. -/
theorem ceil_div_real_leX (H W : ℕ) (hW : 0 < W) :
    ((H ⌈/⌉ W : ℕ) : ℝ) ≤ (H : ℝ) / W + 1 := by
  rw [Nat.ceilDiv_eq_add_pred_div, show H + W - 1 = H + (W - 1) by omega]
  have hn := Nat.div_mul_le_self (H + (W - 1)) W
  have h : (H + (W-1)) / W * W ≤ H + W := by omega
  have h' : (((H + (W-1)) / W : ℕ) : ℝ) * W ≤ (H : ℝ) + W := by exact_mod_cast h
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  calc
    _ ≤ ((H : ℝ) + W) / W := (le_div_iff₀ hW').mpr h'
    _ = (H : ℝ) / W + 1 := by field_simp


theorem normalized_splitX {x y z V U H W σ C : ℝ}
    (hV : 0 < V) (hU : 0 < U) (hH : 1 ≤ H) (hW : 1 ≤ W) (hC : 0 ≤ C)
    (h : x ≤ (H / W + 1) * (C * V + σ * (V / U) * y) + V * z) :
    x / (V * H) ≤ 2 * C + z / H + σ / W * (1 + W / H) * (y / U) := by
  have hp : 0 < H := by linarith
  have hw : 0 < W := by linarith
  have hinv : 1 / W + 1 / H ≤ 2 := by
    linarith [one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hW,
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hH]
  calc
    x / (V * H) ≤ ((H / W + 1) * (C * V + σ * (V / U) * y) + V * z) / (V * H) :=
      div_le_div_of_nonneg_right h (mul_pos hV hp).le
    _ = C * (1 / W + 1 / H) + z / H + σ / W * (1 + W / H) * (y / U) := by
      field_simp
      ring
    _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_left hinv hC]

noncomputable def paddedKernelConstantX (ℓ A W σ C r : ℕ) (θ : ℝ) : ℝ :=
  let small := (ℓ : ℝ) ^ (r + A)
  let b := (σ : ℝ) / W * (1 + (W : ℝ) / (ℓ : ℝ)^r)
  max (1 + small) ((2 * C + small) / ((A : ℝ)^θ - b))

theorem primeTransform_bound_paddedX {ℓ A W σ C r : ℕ} {ζ : K} {θ : ℝ}
    (hℓ : 1 < ℓ) (hA : 0 < A) (hW : 0 < W) (hθ : 0 ≤ θ) (hr : A ≤ r)
    (hsave : (σ : ℝ) / W * (1 + (W : ℝ) / (ℓ : ℝ)^r) < (A : ℝ)^θ)
    (hbatch : PrimeKernelBatch ℓ A W σ C ζ) :
    ∀ k : ℕ, (complexity (primeTransform ℓ k ζ) : ℝ) ≤
      paddedKernelConstantX ℓ A W σ C r θ * (ℓ : ℝ) ^ k * (1 + (k : ℝ)) ^ θ := by
  let V (k : ℕ) : ℝ := (ℓ : ℝ) ^ k
  let S (k : ℕ) : ℝ := complexity (primeTransform ℓ k ζ)
  let T (k : ℕ) : ℝ := S k / V k
  let b := (σ : ℝ) / W * (1 + (W : ℝ) / V r)
  have hW' : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hV (k : ℕ) : 1 ≤ V k := one_le_pow₀ (by exact_mod_cast hℓ.le)
  have hpV (k : ℕ) : 0 < V k := zero_lt_one.trans_le (hV k)
  have hS (k : ℕ) : 0 ≤ S k := Nat.cast_nonneg _
  have hT (k : ℕ) : 0 ≤ T k := div_nonneg (hS k) (hV k |>.trans' zero_le_one)
  let small := V (r + A)
  have hsmall (k : ℕ) (hk : k < r + A) : T k ≤ small := by
    have dense : complexity (primeTransform ℓ k ζ) ≤ ℓ^k * ℓ^k := by
      simpa using (complexity_le_iff _ _).mpr (realizableAtMost_card_mul_card (primeTransform ℓ k ζ))
    calc
      T k ≤ V k := (div_le_iff₀ (hpV k)).mpr (by dsimp [S, V]; exact_mod_cast dense)
      _ ≤ small := pow_le_pow_right₀ (by exact_mod_cast hℓ.le) hk.le
  have hb : 0 ≤ b := mul_nonneg (by positivity) (by linarith [div_nonneg (Nat.cast_nonneg W) (hpV r).le])
  have hstep (k : ℕ) (hk : r + A ≤ k) : ∃ f < k, A * (1 + f) ≤ 1 + k ∧
      T k ≤ (2 * C + small) + b * T f := by
    let f := (k - r) / A
    let h := r + (k - r) % A
    have dh : A * f + h = k := by
      have := Nat.mod_add_div (k - r) A
      dsimp [f, h]
      omega
    have hf : 0 < f := Nat.div_pos (by omega) hA
    have hrl : r ≤ h := Nat.le_add_right _ _
    have hrem : h < r + A := Nat.add_lt_add_left (Nat.mod_lt _ hA) _
    have haf : f ≤ A * f := Nat.le_mul_of_pos_left _ hA
    refine ⟨f, by omega, by rw [Nat.mul_add, Nat.mul_one]; omega, ?_⟩
    have hsplit := primeTransform_complexity_split_batch ℓ (A*f) h W ζ hW
    have hactive := (complexity_le_iff _ _).mpr (hbatch f hf)
    have raw := hsplit.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hactive) _)
    have hraw : S k ≤ ((ℓ ^ h ⌈/⌉ W : ℕ) : ℝ) *
        ((C : ℝ) * V (A*f) + σ * V ((A-1)*f) * S f) + V (A*f) * S h := by
      dsimp only [V, S]
      rw [← dh]
      exact_mod_cast raw
    have hVol : V ((A-1)*f) = V (A*f) / V f := by
      apply (eq_div_iff (hpV f).ne').mpr
      dsimp [V]
      rw [← pow_add]
      congr 1
      rw [← Nat.succ_mul, show (A - 1).succ = A by omega]
    have hH : V r ≤ V h := pow_le_pow_right₀ (by exact_mod_cast hℓ.le) hrl
    have hh := ceil_div_real_leX (ℓ ^ h) W hW
    push_cast at hh
    have hbudget : S k ≤ (V h / W + 1) *
        ((C : ℝ) * V (A*f) + σ * (V (A*f) / V f) * S f) + V (A*f) * S h := by
      rw [← hVol]
      exact hraw.trans (add_le_add_left (mul_le_mul_of_nonneg_right hh
        (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (hpV _).le)
          (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hpV _).le) (hS _)))) _)
    have hnorm := normalized_splitX (hpV _) (hpV f) (hV h) hW' (Nat.cast_nonneg C) hbudget
    have htotal : V (A*f) * V h = V k := by dsimp [V]; rw [← pow_add, dh]
    rw [htotal] at hnorm
    have hcoeff : (σ : ℝ) / W * (1 + (W : ℝ) / V h) ≤ b :=
      mul_le_mul_of_nonneg_left (add_le_add_right
        (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (hpV r) hH) _) (by positivity)
    exact hnorm.trans (add_le_add (add_le_add_right (hsmall h hrem) _)
      (mul_le_mul_of_nonneg_right hcoeff (hT f)))
  have hbound := power_bound_of_recursionX hA hb hθ hsave (hpV (r + A)).le hsmall hstep
  intro k
  have hh := (div_le_iff₀ (hpV k)).mp (hbound k)
  change S k ≤ max (1 + small) ((2 * C + small) / ((A : ℝ)^θ - b)) * V k * (1 + (k : ℝ))^θ
  linarith only [hh]

end FiniteFourier
end LinearAlgebra
end OAI
