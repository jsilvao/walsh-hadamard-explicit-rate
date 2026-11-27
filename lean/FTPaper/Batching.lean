import OAI.LinearAlgebra.FiniteFourier.PrimeBatch

/-!
# Exponentially large batches are free (paper: Theorem 1.5(2))

This is stated in OpenAI's circuit model: `complexity` counts binary linear gates
(vendored `OAI.LinearAlgebra.FiniteFourier`, see `OAI/NOTICE.md`). `primeTransform 2 k (-1)` is
the Walsh–Hadamard transform `H^{⊗k}`.

* `split_step`: one batch of `W ≤ 2^h` copies on `a` digits, plus `2^a` transforms on the other
  `h` digits.
* `batching_sufficient` (⇐): if for every `a`, some batch of `W ≤ 2^{γ a}` copies of `H^{⊗a}`
  costs `≤ C · W · 2^a · √a` gates, then `C(H^{⊗k}) ≤ M · 2^k · √k` for all `k ≥ 1`.
* `batching_necessary` (⇒): the converse, with `W = 1`.
-/

open OAI.LinearAlgebra.FiniteFourier

namespace FTPaper

variable {K : Type*} [CommRing K]

/-- Gates for `W` independent copies of the `a`-digit Walsh–Hadamard transform. -/
noncomputable abbrev batchCost (K : Type*) [CommRing K] (a W : ℕ) : ℕ :=
  complexity (Matrix.blockDiagonal (fun _ : Fin W => primeTransform 2 a (-1 : K)))

lemma ceilDiv_le_div_add_one (n W : ℕ) (hW : 0 < W) : ((n ⌈/⌉ W : ℕ) : ℝ) ≤ n / W + 1 := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  calc (((n + W - 1) / W : ℕ) : ℝ) ≤ ((n + W - 1 : ℕ) : ℝ) / W := Nat.cast_div_le
    _ ≤ ((n + W : ℕ) : ℝ) / W := by gcongr; exact_mod_cast Nat.sub_le _ _
    _ = n / W + 1 := by push_cast; field_simp

/-- One split: a batch of `W ≤ 2^h` copies on the first `a` digits, then `2^a` transforms on
the remaining `h` digits. -/
theorem split_step (C : ℝ) (hC : 0 ≤ C) (a h W : ℕ) (hW : 0 < W) (hWh : (W : ℝ) ≤ 2 ^ h)
    (hcost : (batchCost K a W : ℝ) ≤ C * W * 2 ^ a * Real.sqrt a) :
    (complexity (primeTransform 2 (a + h) (-1 : K)) : ℝ)
      ≤ 2 * C * 2 ^ (a + h) * Real.sqrt a + 2 ^ a * complexity (primeTransform 2 h (-1 : K)) := by
  have hs := primeTransform_complexity_split_batch (K := K) 2 a h W (-1) hW
  have hs' : (complexity (primeTransform 2 (a + h) (-1 : K)) : ℝ)
      ≤ ((2 ^ h ⌈/⌉ W : ℕ) : ℝ) * batchCost K a W
        + 2 ^ a * complexity (primeTransform 2 h (-1 : K)) := by
    unfold batchCost
    exact_mod_cast hs
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hcd : ((2 ^ h ⌈/⌉ W : ℕ) : ℝ) ≤ (2 : ℝ) ^ h / W + 1 := by
    have := ceilDiv_le_div_add_one (2 ^ h) W hW
    push_cast at this; exact this
  have hsq : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
  have hprod : ((2 ^ h ⌈/⌉ W : ℕ) : ℝ) * batchCost K a W ≤ 2 * C * 2 ^ (a + h) * Real.sqrt a := by
    calc ((2 ^ h ⌈/⌉ W : ℕ) : ℝ) * batchCost K a W
        ≤ ((2 : ℝ) ^ h / W + 1) * (C * W * 2 ^ a * Real.sqrt a) :=
          mul_le_mul hcd hcost (Nat.cast_nonneg _) (by positivity)
      _ = C * ((2 : ℝ) ^ h + W) * 2 ^ a * Real.sqrt a := by field_simp
      _ ≤ C * (2 * 2 ^ h) * 2 ^ a * Real.sqrt a := by
          gcongr; linarith
      _ = 2 * C * 2 ^ (a + h) * Real.sqrt a := by rw [pow_add]; ring
  linarith

/-- **Theorem 3(2), (⇐).** Exponentially large batches at cost `O(√a)` per entry give
`C(H^{⊗k}) = O(2^k √k)`. -/
theorem batching_sufficient (γ C : ℝ) (hγ : 0 < γ) (hC : 0 ≤ C)
    (hbatch : ∀ a : ℕ, 1 ≤ a → ∃ W : ℕ, 0 < W ∧ (W : ℝ) ≤ (2 : ℝ) ^ (γ * a) ∧
      (batchCost K a W : ℝ) ≤ C * W * 2 ^ a * Real.sqrt a) :
    ∃ M : ℝ, ∀ k : ℕ, 1 ≤ k →
      (complexity (primeTransform 2 k (-1 : K)) : ℝ) ≤ M * 2 ^ k * Real.sqrt k := by
  set θ : ℝ := γ / (1 + γ) with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one (by linarith)]; linarith
  set θ' : ℝ := (1 + θ) / 2 with hθ'
  have hθ'0 : 0 ≤ θ' := by rw [hθ']; linarith
  have hsθ' : Real.sqrt θ' < 1 := by
    rw [Real.sqrt_lt' one_pos]; rw [hθ']; linarith
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, 2 / (1 - θ) + 2 * (1 + γ) ≤ k₀ := exists_nat_ge _
  have h1θ : 0 < 1 - θ := by linarith
  have hk₀γ : 2 * (1 + γ) ≤ (k₀ : ℝ) := by
    have : 0 ≤ 2 / (1 - θ) := by positivity
    linarith
  set M₂ : ℝ := 2 * C / ((1 - Real.sqrt θ') * Real.sqrt (1 + γ)) with hM₂
  set M : ℝ := max (2 * ((k₀ : ℝ) + 1)) M₂ with hM
  have hMM₂ : M₂ ≤ M := le_max_right _ _
  have hMk₀ : 2 * ((k₀ : ℝ) + 1) ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := le_trans (by positivity) hMk₀
  suffices H : ∀ k : ℕ, 1 ≤ k →
      (complexity (primeTransform 2 k (-1 : K)) : ℝ) / 2 ^ k ≤ M * Real.sqrt k by
    refine ⟨M, fun k hk => ?_⟩
    have := H k hk
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hsqk : 1 ≤ Real.sqrt k := by rw [Real.le_sqrt (by norm_num) (by linarith)]; simpa using hk1
    by_cases hsmall : (k : ℝ) < k₀
    · -- base cases: the classical bound
      have hcl := primeTransform_classical_bound (K := K) 2 k (-1) (by norm_num)
      have hcl' : (complexity (primeTransform 2 k (-1 : K)) : ℝ) ≤ (k + 1) * 2 ^ (k + 1) := by
        exact_mod_cast hcl
      rw [div_le_iff₀ (by positivity)]
      calc (complexity (primeTransform 2 k (-1 : K)) : ℝ) ≤ (k + 1) * 2 ^ (k + 1) := hcl'
        _ = 2 * ((k : ℝ) + 1) * 2 ^ k := by rw [pow_succ]; ring
        _ ≤ 2 * ((k₀ : ℝ) + 1) * 2 ^ k := by gcongr
        _ ≤ M * 1 * 2 ^ k := by rw [mul_one]; gcongr
        _ ≤ M * Real.sqrt k * 2 ^ k := by gcongr
    · -- inductive step
      push Not at hsmall
      set a : ℕ := ⌊(k : ℝ) / (1 + γ)⌋₊ with ha
      have hγ1 : (0 : ℝ) < 1 + γ := by linarith
      have hkγ : 2 ≤ (k : ℝ) / (1 + γ) := by
        rw [le_div_iff₀ hγ1]; linarith
      have ha_le : (a : ℝ) ≤ (k : ℝ) / (1 + γ) := Nat.floor_le (by positivity)
      have ha_ge : (k : ℝ) / (1 + γ) - 1 ≤ a := by
        have := Nat.lt_floor_add_one ((k : ℝ) / (1 + γ)); linarith
      have ha1 : 1 ≤ a := by
        have : (1 : ℝ) ≤ a := by linarith
        exact_mod_cast this
      have hak : (1 + γ) * a ≤ k := by
        have := mul_le_mul_of_nonneg_left ha_le hγ1.le
        rwa [mul_div_cancel₀ _ hγ1.ne'] at this
      have hak_nat : a ≤ k := by
        have : (a : ℝ) ≤ k := by nlinarith
        exact_mod_cast this
      set h : ℕ := k - a with hh
      have hah : a + h = k := by omega
      have hhR : (h : ℝ) = k - a := by rw [hh, Nat.cast_sub hak_nat]
      have hγa : γ * a ≤ h := by rw [hhR]; linarith
      have hhk : h < k := by omega
      have hh1 : 1 ≤ h := by
        have : (0 : ℝ) < h := by
          have : 0 < γ * a := by
            have : (0 : ℝ) < a := by exact_mod_cast ha1
            positivity
          linarith
        exact_mod_cast this
      obtain ⟨W, hW0, hWγ, hcost⟩ := hbatch a ha1
      have hWh : (W : ℝ) ≤ 2 ^ h := by
        calc (W : ℝ) ≤ (2 : ℝ) ^ (γ * a) := hWγ
          _ ≤ (2 : ℝ) ^ (h : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hγa
          _ = 2 ^ h := Real.rpow_natCast 2 h
      have hsp := split_step (K := K) C hC a h W hW0 hWh hcost
      rw [hah] at hsp
      have ihh := ih h hhk hh1
      -- `t(k) ≤ 2C√a + t(h)`
      have hstep : (complexity (primeTransform 2 k (-1 : K)) : ℝ) / 2 ^ k
          ≤ 2 * C * Real.sqrt a + (complexity (primeTransform 2 h (-1 : K)) : ℝ) / 2 ^ h := by
        rw [div_le_iff₀ (by positivity)]
        have e : (2 : ℝ) ^ k = 2 ^ a * 2 ^ h := by rw [← pow_add, hah]
        calc (complexity (primeTransform 2 k (-1 : K)) : ℝ)
            ≤ 2 * C * 2 ^ k * Real.sqrt a + 2 ^ a * complexity (primeTransform 2 h (-1 : K)) := hsp
          _ = (2 * C * Real.sqrt a
                + (complexity (primeTransform 2 h (-1 : K)) : ℝ) / 2 ^ h) * 2 ^ k := by
              rw [e]; field_simp
      -- `√a ≤ √k / √(1+γ)` and `√h ≤ √θ' √k`
      have hsa : Real.sqrt a ≤ Real.sqrt k / Real.sqrt (1 + γ) := by
        rw [← Real.sqrt_div (by positivity)]; exact Real.sqrt_le_sqrt ha_le
      have hhθ : (h : ℝ) ≤ θ' * k := by
        have h1 : (h : ℝ) ≤ θ * k + 1 := by
          rw [hhR]
          have : (k : ℝ) - k / (1 + γ) = θ * k := by rw [hθ]; field_simp; ring
          linarith
        have h2 : 1 ≤ (θ' - θ) * k := by
          have : θ' - θ = (1 - θ) / 2 := by rw [hθ']; ring
          rw [this]
          have : 2 / (1 - θ) ≤ (k : ℝ) := by
            have : 0 ≤ 2 * (1 + γ) := by positivity
            linarith
          rw [div_le_iff₀ h1θ] at this
          linarith
        linarith
      have hsh : Real.sqrt h ≤ Real.sqrt θ' * Real.sqrt k := by
        rw [← Real.sqrt_mul hθ'0]; exact Real.sqrt_le_sqrt hhθ
      have hsγ : 0 < Real.sqrt (1 + γ) := Real.sqrt_pos.mpr hγ1
      -- combine
      have hfin : 2 * C * (Real.sqrt k / Real.sqrt (1 + γ)) + M * (Real.sqrt θ' * Real.sqrt k)
          ≤ M * Real.sqrt k := by
        have hkey : 2 * C / Real.sqrt (1 + γ) ≤ M * (1 - Real.sqrt θ') := by
          have : M₂ * (1 - Real.sqrt θ') = 2 * C / Real.sqrt (1 + γ) := by
            rw [hM₂]; field_simp [ne_of_gt (sub_pos.mpr hsθ')]
          rw [← this]
          exact mul_le_mul_of_nonneg_right hMM₂ (by linarith)
        have hsk0 : 0 ≤ Real.sqrt k := Real.sqrt_nonneg _
        calc 2 * C * (Real.sqrt k / Real.sqrt (1 + γ)) + M * (Real.sqrt θ' * Real.sqrt k)
            = (2 * C / Real.sqrt (1 + γ)) * Real.sqrt k + M * Real.sqrt θ' * Real.sqrt k := by ring
          _ ≤ (M * (1 - Real.sqrt θ')) * Real.sqrt k + M * Real.sqrt θ' * Real.sqrt k := by
              gcongr
          _ = M * Real.sqrt k := by ring
      calc (complexity (primeTransform 2 k (-1 : K)) : ℝ) / 2 ^ k
          ≤ 2 * C * Real.sqrt a + (complexity (primeTransform 2 h (-1 : K)) : ℝ) / 2 ^ h := hstep
        _ ≤ 2 * C * (Real.sqrt k / Real.sqrt (1 + γ)) + M * (Real.sqrt θ' * Real.sqrt k) := by
            gcongr
            calc (complexity (primeTransform 2 h (-1 : K)) : ℝ) / 2 ^ h ≤ M * Real.sqrt h := ihh
              _ ≤ M * (Real.sqrt θ' * Real.sqrt k) := by gcongr
        _ ≤ M * Real.sqrt k := hfin

/-- **Theorem 3(2), (⇒).** An `O(√k)` bound for single transforms gives batches with `W = 1`. -/
theorem batching_necessary (M : ℝ)
    (hM : ∀ k : ℕ, 1 ≤ k →
      (complexity (primeTransform 2 k (-1 : K)) : ℝ) ≤ M * 2 ^ k * Real.sqrt k) :
    ∀ a : ℕ, 1 ≤ a → ∃ W : ℕ, 0 < W ∧ (batchCost K a W : ℝ) ≤ M * W * 2 ^ a * Real.sqrt a := by
  intro a ha
  refine ⟨1, one_pos, ?_⟩
  have h1 : batchCost K a 1 ≤ complexity (primeTransform 2 a (-1 : K)) := by
    simpa using (complexity_le_iff _ _).mpr
      ((realizableAtMost_complexity (primeTransform 2 a (-1 : K))).blockDiagonal (Fin 1))
  have h1' : (batchCost K a 1 : ℝ) ≤ complexity (primeTransform 2 a (-1 : K)) := by
    exact_mod_cast h1
  simpa using h1'.trans (hM a ha)

end FTPaper
