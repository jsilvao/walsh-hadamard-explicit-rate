import FTPaper.QUpper
import FTPaper.LocalCostQ
import FTPaper.ExplicitRecursion

/-!
# An explicit rate for the Walsh–Hadamard transform

For a routing parameter `x`, take the Theorem 1 template with `m + 1 = 2^x − 1` queries
(`theorem1_routed`), its feedback plan, and OpenAI's padded batch recursion with its constant
made explicit (`ExplicitRecursion.lean`). Every quantity is bounded explicitly in terms of `x`:
calls per row, local cost, rows and axes.

Result (`walsh_explicit_rate`): for `x ≥ 12` and every `k` with `log₂(1+k) ≥ 2^{4x}`,

  `C(H^{⊗k}) ≤ 2^k (1+k)^{1/2 + 3ε(x)}`,  `ε(x) = (11√(x log₂ x) + 11)/(x + 1)`,

over every field of characteristic `0`, in OpenAI's model of binary linear circuits. With
`x ≈ (1/4) log₂ log₂ k` this is `C(H^{⊗k}) ≤ N (log N)^{1/2 + O(√(log⁽⁴⁾N / log⁽³⁾N))}`.
-/

open OAI.LinearAlgebra.FiniteFourier
open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open OAI.Computability.NearSquareRoot.KernelPass.Rect.Binary (System Label card_label system Free Paid)
open scoped OAI.Computability.NearSquareRoot.CyclotomicCode

namespace FTPaper

/-! ## From a plan to an explicit bound -/

/-- **A correct plan with a strict padded saving gives an explicit bound.** -/
theorem walsh_bound_explicit {A W : ℕ} (p : QPlan A W W) (hp : QPlan.Correct p) (hA : 0 < A)
    (hW : 0 < W) {θ : ℝ} (hθ : 0 ≤ θ) {r : ℕ} (hr : 2 * A ≤ r)
    (hsave : ((2 * p.calls : ℕ) : ℝ) / W * (1 + (W : ℝ) / (2 : ℝ) ^ r) < ((2 * A : ℕ) : ℝ) ^ θ)
    (F : Type) [Field F] [CharZero F] (k : ℕ) :
    (complexity (primeTransform 2 k (-1 : F)) : ℝ) ≤
      paddedKernelConstantX 2 (2 * A) W (2 * p.calls) (Circ.qfree p) r θ * 2 ^ k
        * (1 + (k : ℝ)) ^ θ := by
  have hsave' : ((2 * p.calls : ℕ) : ℝ) / W * (1 + (W : ℝ) / ((2 : ℕ) : ℝ) ^ r)
      < ((2 * A : ℕ) : ℝ) ^ θ := by
    simpa using hsave
  have h := primeTransform_bound_paddedX (ℓ := 2) (A := 2 * A) (W := W) (σ := 2 * p.calls)
    (C := Circ.qfree p) (ζ := (-1 : F)) (θ := θ) (by norm_num) (by omega) hW hθ hr hsave'
    (Circ.kernelBatch_of_correct (K := F) p hp) k
  simpa using h

/-- **The explicit constant is at most `2C + 2^{r+A} + 1`** once the saving leaves a margin of
one. -/
theorem paddedX_le {A W σ C r : ℕ} {θ : ℝ}
    (hmargin : 1 ≤ (A : ℝ) ^ θ - (σ : ℝ) / W * (1 + (W : ℝ) / (2 : ℝ) ^ r)) :
    paddedKernelConstantX 2 A W σ C r θ ≤ 2 * C + 2 ^ (r + A) + 1 := by
  unfold paddedKernelConstantX
  simp only [Nat.cast_ofNat]
  have hsmall : (0 : ℝ) ≤ 2 ^ (r + A) := by positivity
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  apply max_le
  · linarith
  · rw [div_le_iff₀ (by linarith)]
    nlinarith


/-! ## The template at routing parameter `x` -/

/-- Queries minus one: `m + 1 = 2^x − 1`. -/
def xm (x : ℕ) : ℕ := 2 ^ x - 2
/-- Label length. -/
noncomputable def xL (x : ℕ) : ℕ := 2 * halfLabel x
/-- Bits per letter. -/
noncomputable def xb (x : ℕ) : ℕ := alphabetExp x
/-- Feedback depth. -/
def xd (x : ℕ) : ℕ := x + 1
/-- OpenAI's routing system. -/
noncomputable def xS (x : ℕ) : System (xL x) (xb x) := system (xL x) (xb x)
/-- Rows of the template. -/
noncomputable abbrev xW (x : ℕ) : ℕ := rows (xL x) (xb x) (xm x) (20 ^ (xd x))
/-- Axes of the template. -/
noncomputable abbrev xA (x : ℕ) : ℕ := Charged.Axes (m := xm x) (xS x).geometry
/-- The plan. -/
noncomputable def xplan (x : ℕ) : QPlan (xA x) (xW x) (xW x) :=
  fbPlan (xL x) (xb x) (xm x) (uWin (xm x)) (vWin (xm x)) (xS x) (xd x)
/-- The padding exponent. -/
noncomputable def xr (x : ℕ) : ℕ := Nat.log 2 (xW x) + 1 + 2 * xA x
/-- The loss exponent. -/
noncomputable def xε (x : ℕ) : ℝ := (11 * Real.sqrt (x * Real.logb 2 x) + 11) / (x + 1)

lemma two_le_pow (x : ℕ) (hx : 2 ≤ x) : 4 ≤ 2 ^ x :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hx

lemma xm_succ (x : ℕ) (hx : 2 ≤ x) : xm x + 1 = 2 ^ x - 1 := by
  have := two_le_pow x hx; unfold xm; omega

lemma xm_odd (x : ℕ) (hx : 2 ≤ x) : xm x + 1 ≡ 1 [MOD 2] := by
  have h4 := two_le_pow x hx
  have hev : 2 ∣ 2 ^ x := dvd_pow_self 2 (by omega)
  obtain ⟨t, ht⟩ := hev
  rw [xm_succ x hx, ht]
  have : 2 * t - 1 = 2 * (t - 1) + 1 := by omega
  rw [this]
  simp [Nat.ModEq, Nat.add_mod]

lemma halfLabel_le (x : ℕ) (hx : 2 ≤ x) : halfLabel x ≤ x + 1 := by
  have hl : 1 ≤ Real.logb 2 x := logb_two_ge_one hx
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  have h1 : (x : ℝ) / Real.logb 2 x ≤ x := div_le_self hx0 hl
  have h2 : Real.sqrt ((x : ℝ) / Real.logb 2 x) ≤ x := by
    calc Real.sqrt ((x : ℝ) / Real.logb 2 x) ≤ Real.sqrt x := Real.sqrt_le_sqrt h1
      _ ≤ x := by
          rw [Real.sqrt_le_left hx0]
          have : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
          nlinarith
  have h3 := Nat.ceil_lt_add_one (Real.sqrt_nonneg ((x : ℝ) / Real.logb 2 x))
  have : (halfLabel x : ℝ) < x + 1 := by unfold halfLabel; linarith
  exact_mod_cast this.le

lemma alphabetExp_le (x : ℕ) (hx : 2 ≤ x) : alphabetExp x ≤ x + 1 := by
  have hpos : (1 : ℝ) ≤ halfLabel x := by exact_mod_cast halfLabel_pos hx
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  have h1 : (2 * x : ℝ) / (2 * halfLabel x) ≤ x := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h2 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (2 * x : ℝ) / (2 * halfLabel x) by positivity)
  have : (alphabetExp x : ℝ) < x + 1 := by unfold alphabetExp; linarith
  exact_mod_cast this.le

lemma xL_le (x : ℕ) (hx : 2 ≤ x) : xL x ≤ 2 * x + 2 := by
  have := halfLabel_le x hx; unfold xL; omega

lemma pow_lt_five_pow (x : ℕ) : 4 * x + 5 ≤ 5 ^ (x + 1) := by
  induction x with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have : 1 ≤ 5 ^ (n + 1) := Nat.one_le_pow _ _ (by norm_num)
    omega

lemma xd_ok (x : ℕ) (hx : 2 ≤ x) :
    2 * (xm x + 2 + 2 * halfLabel x * 2 ^ alphabetExp x) ≤ 10 ^ (xd x) := by
  have h4 := two_le_pow x hx
  have hL := halfLabel_le x hx
  have hb := alphabetExp_le x hx
  have h2b : 2 ^ alphabetExp x ≤ 2 ^ (x + 1) := Nat.pow_le_pow_right (by norm_num) hb
  have hm : xm x + 2 = 2 ^ x := by unfold xm; omega
  have hLb : 2 * halfLabel x * 2 ^ alphabetExp x ≤ (2 * x + 2) * 2 ^ (x + 1) :=
    Nat.mul_le_mul (by omega) h2b
  have h5 := pow_lt_five_pow x
  have h10 : 10 ^ (x + 1) = 2 ^ (x + 1) * 5 ^ (x + 1) := by rw [← mul_pow]; norm_num
  unfold xd
  rw [h10, hm]
  have : 2 * (2 ^ x + (2 * x + 2) * 2 ^ (x + 1)) = 2 ^ (x + 1) * (4 * x + 5) := by ring
  calc 2 * (2 ^ x + 2 * halfLabel x * 2 ^ alphabetExp x)
      ≤ 2 * (2 ^ x + (2 * x + 2) * 2 ^ (x + 1)) := by omega
    _ = 2 ^ (x + 1) * (4 * x + 5) := this
    _ ≤ 2 ^ (x + 1) * 5 ^ (x + 1) := Nat.mul_le_mul_left _ h5


/-! ## Sizes -/

lemma xb_le (x : ℕ) (hx : 2 ≤ x) : xb x ≤ x + 1 := alphabetExp_le x hx

lemma xbL_le (x : ℕ) (hx : 2 ≤ x) : xb x * xL x ≤ 2 * (x + 1) ^ 2 := by
  have h1 := xb_le x hx
  have h2 := xL_le x hx
  calc xb x * xL x ≤ (x + 1) * (2 * x + 2) := Nat.mul_le_mul h1 h2
    _ = 2 * (x + 1) ^ 2 := by ring

lemma xD_le (x : ℕ) : (xS x).D ≤ 2 + xL x * 2 ^ xb x := by
  have := (xS x).dimension_le
  simp only [Nat.reduceSub, pow_one] at this
  omega

/-- The axes: `A ≤ (8x + 12) 2^x`. -/
lemma xA_le (x : ℕ) (hx : 2 ≤ x) : xA x ≤ (8 * x + 12) * 2 ^ x := by
  have hAe : xA x = 2 * (xm x + (xS x).D) := axes_eq _ _ _ _
  have hD := xD_le x
  have hL := xL_le x hx
  have hb := xb_le x hx
  have h4 := two_le_pow x hx
  have h2b : 2 ^ xb x ≤ 2 * 2 ^ x := by
    calc 2 ^ xb x ≤ 2 ^ (x + 1) := Nat.pow_le_pow_right (by norm_num) hb
      _ = 2 * 2 ^ x := by ring
  have hLb : xL x * 2 ^ xb x ≤ (2 * x + 2) * (2 * 2 ^ x) := Nat.mul_le_mul hL h2b
  have hm : xm x + 2 = 2 ^ x := by unfold xm; omega
  rw [hAe]
  nlinarith

lemma xA_pos (x : ℕ) : 2 * (xm x + 1) ≤ xA x := by
  have hAe : xA x = 2 * (xm x + (xS x).D) := axes_eq _ _ _ _
  have := (xS x).dimension_pos
  omega

/-- Exponent bound for the rows. -/
def eW (x : ℕ) : ℕ := 2 * (x + 1) ^ 2 + 5 * (x + 1) + 2 ^ x

/-- The rows: `W ≤ 2^{eW}`. -/
lemma xW_le (x : ℕ) (hx : 2 ≤ x) : xW x ≤ 2 ^ eW x := by
  have hrows := rows_eq (xL x) (xb x) (xm x) (20 ^ (xd x))
  have hlab : Fintype.card (Label (xL x) (xb x)) = 2 ^ (xb x * xL x) := by
    rw [card_label, ← pow_mul]
  have hbL := xbL_le x hx
  have h20 : 20 ^ (xd x) ≤ 2 ^ (5 * (x + 1)) := by
    unfold xd
    calc 20 ^ (x + 1) ≤ 32 ^ (x + 1) := Nat.pow_le_pow_left (by norm_num) _
      _ = 2 ^ (5 * (x + 1)) := by rw [pow_mul]; norm_num
  have hm : 2 ^ (xm x + 1) ≤ 2 ^ (2 ^ x) := Nat.pow_le_pow_right (by norm_num) (by
    have := two_le_pow x hx; unfold xm; omega)
  calc xW x = Fintype.card (Label (xL x) (xb x)) * (20 ^ (xd x) * 2 ^ (xm x + 1)) := hrows
    _ ≤ 2 ^ (2 * (x + 1) ^ 2) * (2 ^ (5 * (x + 1)) * 2 ^ (2 ^ x)) := by
        rw [hlab]
        exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hbL) (Nat.mul_le_mul h20 hm)
    _ = 2 ^ eW x := by unfold eW; rw [← pow_add, ← pow_add, ← add_assoc]

lemma xW_pos (x : ℕ) : 0 < xW x := by
  show 0 < rows (xL x) (xb x) (xm x) (20 ^ (xd x))
  rw [rows_eq]
  have : 0 < Fintype.card (Label (xL x) (xb x)) := by rw [card_label]; positivity
  positivity

/-- Window width: `v − u ≤ 4·2^x`. -/
lemma xwidth_le (x : ℕ) (hx : 2 ≤ x) : vWin (xm x) - uWin (xm x) ≤ 4 * 2 ^ x := by
  have hw := window_width (xm x)
  have hm1 : ((xm x + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ x := by
    have := xm_succ x hx
    have h : xm x + 1 ≤ 2 ^ x := by omega
    exact_mod_cast h
  have hge : (1 : ℝ) ≤ ((xm x + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hsq : Real.sqrt ((xm x + 1 : ℕ) : ℝ) ≤ ((xm x + 1 : ℕ) : ℝ) := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have h2x : (2 : ℝ) ≤ (2 : ℝ) ^ x := by
    have := two_le_pow x hx
    have : (4 : ℝ) ≤ (2 : ℝ) ^ x := by exact_mod_cast this
    linarith
  have : ((vWin (xm x) - uWin (xm x) : ℕ) : ℝ) ≤ 4 * (2 : ℝ) ^ x := by linarith
  exact_mod_cast this

/-- Exponent bound for the feedback constant. -/
def eK (x : ℕ) : ℕ := 4 * (x + 1) ^ 2 + 2 * x + 10

lemma card_free_x (x : ℕ) (hx : 2 ≤ x) :
    Fintype.card (Free (xL x) (xb x)) ≤ 2 ^ (4 * (x + 1) ^ 2) := by
  have h := Circ.card_free_le (xL x) (xb x)
  have hb1 : xb x + 1 ≤ 2 ^ xb x := Nat.lt_two_pow_self
  have h2 : (xb x + 1) * 2 ^ xb x ≤ 2 ^ (2 * xb x) := by
    calc (xb x + 1) * 2 ^ xb x ≤ 2 ^ xb x * 2 ^ xb x := Nat.mul_le_mul_right _ hb1
      _ = 2 ^ (2 * xb x) := by rw [← pow_add]; ring_nf
  have hbL := xbL_le x hx
  calc Fintype.card (Free (xL x) (xb x)) ≤ ((xb x + 1) * 2 ^ xb x) ^ xL x := h
    _ ≤ (2 ^ (2 * xb x)) ^ xL x := Nat.pow_le_pow_left h2 _
    _ = 2 ^ (2 * (xb x * xL x)) := by rw [← pow_mul]; ring_nf
    _ ≤ 2 ^ (4 * (x + 1) ^ 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma card_paid_x (x : ℕ) (hx : 2 ≤ x) :
    Fintype.card (Paid (xL x) (xb x)) ≤ 2 ^ (4 * (x + 1) ^ 2) := by
  have h := Circ.card_paid_le (xL x) (xb x)
  have hbL := xbL_le x hx
  have hL := xL_le x hx
  have hhalf : (2 ^ xb x) ^ (xL x / 2) ≤ 2 ^ (xb x * xL x) := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (Nat.div_le_self _ _))
  calc Fintype.card (Paid (xL x) (xb x)) ≤ 2 ^ xL x * (2 ^ xb x) ^ (xL x / 2) := h
    _ ≤ 2 ^ xL x * 2 ^ (xb x * xL x) := Nat.mul_le_mul_left _ hhalf
    _ = 2 ^ (xL x + xb x * xL x) := by rw [← pow_add]
    _ ≤ 2 ^ (4 * (x + 1) ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- The feedback constant: `K ≤ 2^{eK}`. -/
lemma xK_le (x : ℕ) (hx : 2 ≤ x) :
    Circ.fbConst (xL x) (xb x) (xm x) (uWin (xm x)) (vWin (xm x)) ≤ 2 ^ eK x := by
  have hw := xwidth_le x hx
  have hF := card_free_x x hx
  have hP := card_paid_x x hx
  have hm : xm x + 2 = 2 ^ x := by have := two_le_pow x hx; unfold xm; omega
  set E := 4 * (x + 1) ^ 2 with hE
  have h1 : 1 ≤ 2 ^ E := Nat.one_le_two_pow
  have hpc : Circ.pencilCoef (xL x) (xb x) (xm x) ≤ 64 * 2 ^ E * 2 ^ x := by
    unfold Circ.pencilCoef
    rw [hm]
    have : Fintype.card (Free (xL x) (xb x)) + Fintype.card (Paid (xL x) (xb x)) + 1 ≤ 3 * 2 ^ E := by
      omega
    calc 20 * (Fintype.card (Free (xL x) (xb x)) + Fintype.card (Paid (xL x) (xb x)) + 1) * 2 ^ x
        ≤ 20 * (3 * 2 ^ E) * 2 ^ x := by gcongr
      _ ≤ 64 * 2 ^ E * 2 ^ x := by nlinarith [Nat.one_le_two_pow (n := x)]
  unfold Circ.fbConst eK
  set n := vWin (xm x) - uWin (xm x)
  have hx2 : 1 ≤ 2 ^ x := Nat.one_le_two_pow
  have key : 2 * n * Circ.pencilCoef (xL x) (xb x) (xm x) + 30 * n + 64
      ≤ 2 * (4 * 2 ^ x) * (64 * 2 ^ E * 2 ^ x) + 30 * (4 * 2 ^ x) + 64 := by gcongr
  have hpow : 2 ^ (E + 2 * x + 10) = 1024 * (2 ^ E * (2 ^ x * 2 ^ x)) := by
    rw [show E + 2 * x + 10 = E + (x + x) + 10 by ring, pow_add, pow_add, pow_add]; ring
  rw [hpow]
  have hEx : 1 ≤ 2 ^ E * (2 ^ x * 2 ^ x) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  nlinarith

/-- The local cost: `C ≤ 2^{eK + 2 + 3 eW}`. -/
lemma xC_le (x : ℕ) (hx : 2 ≤ x) : Circ.qfree (xplan x) ≤ 2 ^ (eK x + 2 + 3 * eW x) := by
  have h := Circ.qfree_fbPlan_le (xL x) (xb x) (xm x) (uWin (xm x)) (vWin (xm x)) (xS x)
    (outside_window (xm x)) (xd x)
  have hK := xK_le x hx
  have hW := xW_le x hx
  have h1 : 2 ≤ 2 ^ eK x := Nat.le_self_pow (by unfold eK; omega) 2
  calc Circ.qfree (xplan x) ≤ (2 * Circ.fbConst (xL x) (xb x) (xm x) (uWin (xm x)) (vWin (xm x)) + 3)
        * xW x ^ 3 := h
    _ ≤ (4 * 2 ^ eK x) * (2 ^ eW x) ^ 3 := by gcongr; omega
    _ = 2 ^ (eK x + 2 + 3 * eW x) := by
        rw [← pow_mul, pow_add, pow_add]; ring

lemma xr_le (x : ℕ) (hx : 2 ≤ x) : xr x ≤ eW x + 1 + 2 * xA x := by
  have hW := xW_le x hx
  have : Nat.log 2 (xW x) ≤ eW x := by
    calc Nat.log 2 (xW x) ≤ Nat.log 2 (2 ^ eW x) := Nat.log_mono_right hW
      _ = eW x := Nat.log_pow (by norm_num) _
  unfold xr; omega

lemma xW_lt_pow (x : ℕ) : xW x < 2 ^ xr x := by
  unfold xr
  calc xW x < 2 ^ (Nat.log 2 (xW x) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    _ ≤ 2 ^ (Nat.log 2 (xW x) + 1 + 2 * xA x) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The explicit constant is at most `2^{2^{3x}}`. -/
lemma xT_le (x : ℕ) (hx : 12 ≤ x) :
    2 * Circ.qfree (xplan x) + 2 ^ (xr x + 2 * xA x) + 1 ≤ 2 ^ (2 ^ (3 * x)) := by
  have hx2 : 2 ≤ x := by omega
  have hC := xC_le x hx2
  have hr := xr_le x hx2
  have hA := xA_le x hx2
  set E := eK x + 3 * eW x + 4 * xA x + 5 with hE
  have hx1 : x + 1 ≤ 2 ^ x := Nat.lt_two_pow_self
  have hxx : (x + 1) ^ 2 ≤ 2 ^ (2 * x) := by
    calc (x + 1) ^ 2 ≤ (2 ^ x) ^ 2 := Nat.pow_le_pow_left hx1 _
      _ = 2 ^ (2 * x) := by rw [← pow_mul]; ring_nf
  have h7 : 2 ^ 7 ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow3 : 2 ^ (3 * x) = 2 ^ x * 2 ^ (2 * x) := by rw [← pow_add]; ring_nf
  have h2x : 2 ^ (2 * x) = 2 ^ x * 2 ^ x := by rw [← pow_add]; ring_nf
  -- `E ≤ 2^{3x}`
  have hEle : E ≤ 2 ^ (3 * x) := by
    unfold eK eW at hE
    rw [hE, hpow3, h2x]
    have hA' : 4 * xA x ≤ 4 * ((8 * x + 12) * 2 ^ x) := Nat.mul_le_mul_left _ hA
    have hxx' : (x + 1) ^ 2 ≤ 2 ^ x * 2 ^ x := by rw [← h2x]; exact hxx
    nlinarith
  have hsum : 2 * 2 ^ (eK x + 2 + 3 * eW x) + 2 ^ (eW x + 1 + 2 * xA x + 2 * xA x) + 1 ≤ 2 ^ E := by
    have e1 : 2 * 2 ^ (eK x + 2 + 3 * eW x) ≤ 2 ^ (E - 1) := by
      rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have e2 : 2 ^ (eW x + 1 + 2 * xA x + 2 * xA x) ≤ 2 ^ (E - 2) :=
      Nat.pow_le_pow_right (by norm_num) (by unfold eK at hE; omega)
    have hE5 : 5 ≤ E := by omega
    have e3 : 2 ^ (E - 1) = 2 * 2 ^ (E - 2) := by
      rw [show E - 1 = (E - 2) + 1 by omega, pow_succ]; ring
    have e4 : 2 ^ E = 2 * 2 ^ (E - 1) := by
      rw [show E = (E - 1) + 1 by omega, pow_succ]; simp only [Nat.add_sub_cancel]; ring
    have e5 : 1 ≤ 2 ^ (E - 2) := Nat.one_le_two_pow
    omega
  calc 2 * Circ.qfree (xplan x) + 2 ^ (xr x + 2 * xA x) + 1
      ≤ 2 * 2 ^ (eK x + 2 + 3 * eW x) + 2 ^ (eW x + 1 + 2 * xA x + 2 * xA x) + 1 :=
        Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 2 hC)
          (Nat.pow_le_pow_right (by norm_num) (by omega))) 1
    _ ≤ 2 ^ E := hsum
    _ ≤ 2 ^ (2 ^ (3 * x)) := Nat.pow_le_pow_right (by norm_num) hEle


/-! ## Saving and margin -/

lemma xε_pos (x : ℕ) : 0 < xε x := by unfold xε; positivity

lemma xε_mul (x : ℕ) : 11 * Real.sqrt (x * Real.logb 2 x) + 11 = xε x * (x + 1) := by
  unfold xε; field_simp

/-- Calls per row of the template. -/
lemma xcalls (x : ℕ) (hx : 2 ≤ x) :
    ((xplan x).calls : ℝ) / xW x ≤ (20 / 3 * Real.sqrt ((xm x + 1 : ℕ) : ℝ) + 40 / 9)
      * (2 : ℝ) ^ (11 * Real.sqrt (x * Real.logb 2 x) + 7) + 1 := by
  have hm : xm x + 1 ≤ 2 ^ x := by have := xm_succ x hx; omega
  exact fbPlan_calls_bound_routed x (xm x) (xd x) hx hm (xd_ok x hx)

/-- `(2A)^ε ≥ 4`. -/
lemma xpowε (x : ℕ) (hx : 2 ≤ x) : (4 : ℝ) ≤ ((2 * xA x : ℕ) : ℝ) ^ xε x := by
  have hA := xA_pos x
  have hm1 := xm_succ x hx
  have h4 := two_le_pow x hx
  have hbase : (2 : ℝ) ^ ((x : ℝ) + 1) ≤ ((2 * xA x : ℕ) : ℝ) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_one]
    have : 2 ^ x * 2 ≤ 2 * xA x := by omega
    exact_mod_cast this
  have h1 : ((2 : ℝ) ^ ((x : ℝ) + 1)) ^ xε x ≤ ((2 * xA x : ℕ) : ℝ) ^ xε x :=
    Real.rpow_le_rpow (by positivity) hbase (xε_pos x).le
  have h2 : ((2 : ℝ) ^ ((x : ℝ) + 1)) ^ xε x = (2 : ℝ) ^ (11 * Real.sqrt (x * Real.logb 2 x) + 11) := by
    rw [← Real.rpow_mul (by norm_num), xε_mul]; ring_nf
  have h3 : (4 : ℝ) ≤ (2 : ℝ) ^ (11 * Real.sqrt (x * Real.logb 2 x) + 11) := by
    have : (2 : ℝ) ≤ 11 * Real.sqrt (x * Real.logb 2 x) + 11 := by
      have := Real.sqrt_nonneg ((x : ℝ) * Real.logb 2 x); linarith
    calc (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) this
  linarith

/-- **The padded saving and its margin.** With `θ = 1/2 + 2ε`:
`(2σ/W)(1 + W/2^r) + 1 ≤ (2A)^θ`, in particular the saving is strict. -/
lemma xsaving (x : ℕ) (hx : 2 ≤ x) :
    ((2 * (xplan x).calls : ℕ) : ℝ) / xW x * (1 + (xW x : ℝ) / (2 : ℝ) ^ xr x) + 1
      ≤ ((2 * xA x : ℕ) : ℝ) ^ ((1 : ℝ) / 2 + 2 * xε x) := by
  set B := (20 / 3 * Real.sqrt ((xm x + 1 : ℕ) : ℝ) + 40 / 9)
      * (2 : ℝ) ^ (11 * Real.sqrt (x * Real.logb 2 x) + 7) + 1 with hB
  have hc := xcalls x hx
  have hroute := saving_of_routing (A := xA x) (xε_pos x) hx (xm_succ x hx) (le_of_eq (xε_mul x))
    (xA_pos x)
  have hpow := xpowε x hx
  have hW : (0 : ℝ) < xW x := by exact_mod_cast xW_pos x
  have hWr : (xW x : ℝ) / (2 : ℝ) ^ xr x ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast (xW_lt_pow x).le
  have hB1 : 1 ≤ B := by
    have : 0 ≤ (20 / 3 * Real.sqrt ((xm x + 1 : ℕ) : ℝ) + 40 / 9)
        * (2 : ℝ) ^ (11 * Real.sqrt (x * Real.logb 2 x) + 7) := by positivity
    linarith
  have hsplit : ((2 * xA x : ℕ) : ℝ) ^ ((1 : ℝ) / 2 + 2 * xε x)
      = ((2 * xA x : ℕ) : ℝ) ^ ((1 : ℝ) / 2 + xε x) * ((2 * xA x : ℕ) : ℝ) ^ xε x := by
    rw [← Real.rpow_add (by have := xA_pos x; positivity)]; ring_nf
  have h8 : 8 * B ≤ ((2 * xA x : ℕ) : ℝ) ^ ((1 : ℝ) / 2 + 2 * xε x) := by
    rw [hsplit]
    have hpos : (0 : ℝ) ≤ ((2 * xA x : ℕ) : ℝ) ^ ((1 : ℝ) / 2 + xε x) := by positivity
    nlinarith
  have hcalls2 : ((2 * (xplan x).calls : ℕ) : ℝ) / xW x = 2 * (((xplan x).calls : ℝ) / xW x) := by
    push_cast; ring
  have hc0 : (0 : ℝ) ≤ ((xplan x).calls : ℝ) / xW x := by positivity
  rw [hcalls2]
  nlinarith

/-! ## The explicit rate -/

/-- **Explicit rate for the Walsh–Hadamard transform.** For every routing parameter `x ≥ 12`
and every `k` with `2^{2^{4x}} ≤ 1 + k`, over every field of characteristic `0`,

  `C(H^{⊗k}) ≤ 2^k (1+k)^{1/2 + 3ε(x)}`,   `ε(x) = (11√(x log₂ x) + 11)/(x + 1)`,

in OpenAI's model of binary linear circuits. Choosing `x = ⌊(1/4) log₂ log₂(1+k)⌋` gives
`C(H^{⊗k}) ≤ 2^k k^{1/2 + O(√(log log log k / log log k))}`. -/
theorem walsh_explicit_rate (x : ℕ) (hx : 12 ≤ x) (k : ℕ) (hk : (2 : ℝ) ^ (2 ^ (4 * x)) ≤ 1 + k)
    (F : Type) [Field F] [CharZero F] :
    (complexity (primeTransform 2 k (-1 : F)) : ℝ) ≤ 2 ^ k * (1 + (k : ℝ)) ^ ((1 : ℝ) / 2 + 3 * xε x) := by
  have hx2 : 2 ≤ x := by omega
  have hsave := xsaving x hx2
  have hW := xW_pos x
  have hA : 0 < xA x := by have := xA_pos x; omega
  have hθ : (0 : ℝ) ≤ 1 / 2 + 2 * xε x := by have := xε_pos x; positivity
  have hr : 2 * xA x ≤ xr x := by unfold xr; omega
  have hcorrect : QPlan.Correct (xplan x) :=
    correct_fbPlan (xL x) (xb x) (xm x) _ _ (xS x) (xm_odd x hx2) (xd x)
  have hb := walsh_bound_explicit (xplan x) hcorrect hA hW hθ hr (by linarith) F k
  have hD := paddedX_le (A := 2 * xA x) (W := xW x) (σ := 2 * (xplan x).calls)
    (C := Circ.qfree (xplan x)) (r := xr x) (θ := (1 : ℝ) / 2 + 2 * xε x) (by linarith)
  have hT := xT_le x hx
  have hT' : (2 * (Circ.qfree (xplan x) : ℝ) + 2 ^ (xr x + 2 * xA x) + 1) ≤ (2 : ℝ) ^ (2 ^ (3 * x)) := by
    exact_mod_cast hT
  -- `2^{2^{3x}} ≤ (1+k)^ε`
  have hk0 : (0 : ℝ) < 1 + k := by positivity
  have hε := xε_pos x
  have hε2 : (2 : ℝ) ^ (3 * x) ≤ (2 : ℝ) ^ (4 * x) * xε x := by
    have h11 : (x : ℝ) + 1 ≤ 11 * 2 ^ x := by
      have : x + 1 ≤ 2 ^ x := Nat.lt_two_pow_self
      have : (x : ℝ) + 1 ≤ 2 ^ x := by exact_mod_cast this
      have : (0 : ℝ) ≤ 2 ^ x := by positivity
      linarith
    have hεge : 11 / ((x : ℝ) + 1) ≤ xε x := by
      unfold xε
      apply div_le_div_of_nonneg_right _ (by positivity)
      have := Real.sqrt_nonneg ((x : ℝ) * Real.logb 2 x)
      linarith
    have hpow : (2 : ℝ) ^ (4 * x) = 2 ^ (3 * x) * 2 ^ x := by rw [← pow_add]; ring_nf
    have h1 : (2 : ℝ) ^ (3 * x) ≤ (2 : ℝ) ^ (3 * x) * 2 ^ x * (11 / ((x : ℝ) + 1)) := by
      have hx1 : (0 : ℝ) < (x : ℝ) + 1 := by positivity
      rw [mul_div_assoc', le_div_iff₀ hx1]
      have : (0 : ℝ) ≤ 2 ^ (3 * x) := by positivity
      nlinarith
    rw [hpow]
    calc (2 : ℝ) ^ (3 * x) ≤ (2 : ℝ) ^ (3 * x) * 2 ^ x * (11 / ((x : ℝ) + 1)) := h1
      _ ≤ (2 : ℝ) ^ (3 * x) * 2 ^ x * xε x := by gcongr
  have hkε : (2 : ℝ) ^ (2 ^ (3 * x)) ≤ (1 + (k : ℝ)) ^ xε x := by
    have e1 : (2 : ℝ) ^ (2 ^ (3 * x)) = (2 : ℝ) ^ (((2 : ℝ) ^ (3 * x)) : ℝ) := by
      rw [← Real.rpow_natCast]; push_cast; ring_nf
    have e2 : ((2 : ℝ) ^ (2 ^ (4 * x))) ^ xε x = (2 : ℝ) ^ ((2 : ℝ) ^ (4 * x) * xε x) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; push_cast; ring_nf
    calc (2 : ℝ) ^ (2 ^ (3 * x)) = (2 : ℝ) ^ (((2 : ℝ) ^ (3 * x)) : ℝ) := e1
      _ ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (4 * x) * xε x) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hε2
      _ = ((2 : ℝ) ^ (2 ^ (4 * x))) ^ xε x := e2.symm
      _ ≤ (1 + (k : ℝ)) ^ xε x := Real.rpow_le_rpow (by positivity) hk hε.le
  have hsplit : (1 + (k : ℝ)) ^ ((1 : ℝ) / 2 + 3 * xε x)
      = (1 + (k : ℝ)) ^ xε x * (1 + (k : ℝ)) ^ ((1 : ℝ) / 2 + 2 * xε x) := by
    rw [← Real.rpow_add hk0]; ring_nf
  have hpk : (0 : ℝ) ≤ (1 + (k : ℝ)) ^ ((1 : ℝ) / 2 + 2 * xε x) := by positivity
  have h2k : (0 : ℝ) ≤ 2 ^ k := by positivity
  calc (complexity (primeTransform 2 k (-1 : F)) : ℝ)
      ≤ paddedKernelConstantX 2 (2 * xA x) (xW x) (2 * (xplan x).calls) (Circ.qfree (xplan x)) (xr x)
          ((1 : ℝ) / 2 + 2 * xε x) * 2 ^ k * (1 + (k : ℝ)) ^ ((1 : ℝ) / 2 + 2 * xε x) := hb
    _ ≤ (1 + (k : ℝ)) ^ xε x * 2 ^ k * (1 + (k : ℝ)) ^ ((1 : ℝ) / 2 + 2 * xε x) := by
        gcongr
        calc paddedKernelConstantX 2 (2 * xA x) (xW x) (2 * (xplan x).calls) (Circ.qfree (xplan x))
              (xr x) ((1 : ℝ) / 2 + 2 * xε x)
            ≤ 2 * (Circ.qfree (xplan x) : ℝ) + 2 ^ (xr x + 2 * xA x) + 1 := hD
          _ ≤ (2 : ℝ) ^ (2 ^ (3 * x)) := hT'
          _ ≤ (1 + (k : ℝ)) ^ xε x := hkε
    _ = 2 ^ k * (1 + (k : ℝ)) ^ ((1 : ℝ) / 2 + 3 * xε x) := by rw [hsplit]; ring


/-- The routing parameter chosen from `k`: `x(k) = ⌊log₂ log₂(1+k) / 4⌋`. -/
def xOf (k : ℕ) : ℕ := Nat.log 2 (Nat.log 2 (1 + k)) / 4

lemma xOf_spec (k : ℕ) (hk : 1 ≤ Nat.log 2 (1 + k)) : (2 : ℝ) ^ (2 ^ (4 * xOf k)) ≤ 1 + k := by
  have h1 : 2 ^ (4 * xOf k) ≤ Nat.log 2 (1 + k) := by
    calc 2 ^ (4 * xOf k) ≤ 2 ^ Nat.log 2 (Nat.log 2 (1 + k)) :=
          Nat.pow_le_pow_right (by norm_num) (by unfold xOf; omega)
      _ ≤ Nat.log 2 (1 + k) := Nat.pow_log_le_self 2 (by omega)
  have h2 : 2 ^ Nat.log 2 (1 + k) ≤ 1 + k := Nat.pow_log_le_self 2 (by omega)
  have h3 : 2 ^ (2 ^ (4 * xOf k)) ≤ 1 + k :=
    (Nat.pow_le_pow_right (by norm_num) h1).trans h2
  exact_mod_cast h3

/-- **Explicit rate, with the parameter chosen from `k`.** If `log₂ log₂(1+k) ≥ 48`, then over
every field of characteristic `0`,
`C(H^{⊗k}) ≤ 2^k (1+k)^{1/2 + 3ε(x(k))}` with `x(k) = ⌊log₂ log₂(1+k)/4⌋`. -/
theorem walsh_explicit_rate_k (k : ℕ) (hk : 48 ≤ Nat.log 2 (Nat.log 2 (1 + k)))
    (F : Type) [Field F] [CharZero F] :
    (complexity (primeTransform 2 k (-1 : F)) : ℝ)
      ≤ 2 ^ k * (1 + (k : ℝ)) ^ ((1 : ℝ) / 2 + 3 * xε (xOf k)) :=
  have hk1 : 1 ≤ Nat.log 2 (1 + k) := by
    by_contra h
    have h0 : Nat.log 2 (1 + k) = 0 := by omega
    rw [h0] at hk
    simp at hk
  walsh_explicit_rate (xOf k) (by unfold xOf; omega) k (xOf_spec k hk1) F


/-! ## The asymptotic form -/

/-- `ε(x) ≤ 22 √(log₂ x / x)` for `x ≥ 2`. -/
lemma xε_le (x : ℕ) (hx : 2 ≤ x) : xε x ≤ 22 * Real.sqrt (Real.logb 2 x / x) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hl : 1 ≤ Real.logb 2 x := logb_two_ge_one hx
  have hxl : (1 : ℝ) ≤ x * Real.logb 2 x := by
    have : (2 : ℝ) ≤ x := by exact_mod_cast hx
    nlinarith
  have hs1 : 1 ≤ Real.sqrt (x * Real.logb 2 x) := by
    rw [Real.one_le_sqrt]; exact hxl
  have hnum : 11 * Real.sqrt (x * Real.logb 2 x) + 11 ≤ 22 * Real.sqrt (x * Real.logb 2 x) := by
    linarith
  have hsplit : Real.sqrt (x * Real.logb 2 x) = x * Real.sqrt (Real.logb 2 x / x) := by
    have : (x : ℝ) * Real.logb 2 x = x ^ 2 * (Real.logb 2 x / x) := by field_simp
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hx0.le]
  unfold xε
  rw [div_le_iff₀ (by positivity)]
  have hq : 0 ≤ Real.sqrt (Real.logb 2 x / x) := Real.sqrt_nonneg _
  calc 11 * Real.sqrt (x * Real.logb 2 x) + 11 ≤ 22 * Real.sqrt (x * Real.logb 2 x) := hnum
    _ = 22 * Real.sqrt (Real.logb 2 x / x) * x := by rw [hsplit]; ring
    _ ≤ 22 * Real.sqrt (Real.logb 2 x / x) * (x + 1) := by nlinarith

/-- **The explicit rate in asymptotic form.** Put `ℓ = ⌊log₂ ⌊log₂(1+k)⌋⌋`. If `ℓ ≥ 48`, then over
every field of characteristic `0`,

  `C(H^{⊗k}) ≤ 2^k (1+k)^{1/2 + 200 √(log₂ ℓ / ℓ)}`.

With `N = 2^k` this is `N (log N)^{1/2 + O(√(log⁽⁴⁾N / log⁽³⁾N))}`. -/
theorem walsh_rate_asymptotic (k : ℕ) (hk : 48 ≤ Nat.log 2 (Nat.log 2 (1 + k)))
    (F : Type) [Field F] [CharZero F] :
    (complexity (primeTransform 2 k (-1 : F)) : ℝ)
      ≤ 2 ^ k * (1 + (k : ℝ)) ^ ((1 : ℝ) / 2 + 200 * Real.sqrt
          (Real.logb 2 (Nat.log 2 (Nat.log 2 (1 + k)) : ℝ) / (Nat.log 2 (Nat.log 2 (1 + k)) : ℝ))) := by
  set ℓ := Nat.log 2 (Nat.log 2 (1 + k)) with hℓ
  have h := walsh_explicit_rate_k k hk F
  refine h.trans ?_
  have hk1 : (1 : ℝ) ≤ 1 + k := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg _; linarith
  have h2k : (0 : ℝ) ≤ 2 ^ k := by positivity
  apply mul_le_mul_of_nonneg_left _ h2k
  apply Real.rpow_le_rpow_of_exponent_le hk1
  -- `3 ε(x) ≤ 200 √(log₂ ℓ / ℓ)` with `x = ⌊ℓ/4⌋`
  have hx : xOf k = ℓ / 4 := rfl
  have hx12 : 12 ≤ xOf k := by rw [hx]; omega
  have hε := xε_le (xOf k) (by omega)
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast (show 0 < ℓ by omega)
  have hx0 : (0 : ℝ) < xOf k := by exact_mod_cast (show 0 < xOf k by omega)
  have hxℓ : (ℓ : ℝ) ≤ 8 * (xOf k : ℝ) := by
    have : ℓ ≤ 8 * xOf k := by rw [hx]; omega
    exact_mod_cast this
  have hxle : (xOf k : ℝ) ≤ ℓ := by
    have : xOf k ≤ ℓ := by rw [hx]; omega
    exact_mod_cast this
  have hlog : Real.logb 2 (xOf k) ≤ Real.logb 2 ℓ :=
    Real.logb_le_logb_of_le (by norm_num) hx0 hxle
  have hlog0 : 0 ≤ Real.logb 2 (xOf k) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ xOf k by omega))
  have hfrac : Real.logb 2 (xOf k) / xOf k ≤ 8 * (Real.logb 2 ℓ / ℓ) := by
    rw [div_le_iff₀ hx0]
    have : 8 * (Real.logb 2 ℓ / ℓ) * (xOf k : ℝ) = Real.logb 2 ℓ * (8 * xOf k / ℓ) := by
      field_simp
    rw [this]
    have h8 : (1 : ℝ) ≤ 8 * xOf k / ℓ := by rw [le_div_iff₀ hℓ0]; linarith
    nlinarith
  have hsq : Real.sqrt (Real.logb 2 (xOf k) / xOf k) ≤ 3 * Real.sqrt (Real.logb 2 ℓ / ℓ) := by
    calc Real.sqrt (Real.logb 2 (xOf k) / xOf k) ≤ Real.sqrt (8 * (Real.logb 2 ℓ / ℓ)) :=
          Real.sqrt_le_sqrt hfrac
      _ = Real.sqrt 8 * Real.sqrt (Real.logb 2 ℓ / ℓ) := Real.sqrt_mul (by norm_num) _
      _ ≤ 3 * Real.sqrt (Real.logb 2 ℓ / ℓ) := by
          have : Real.sqrt 8 ≤ 3 := by
            rw [Real.sqrt_le_left (by norm_num)]; norm_num
          have h0 := Real.sqrt_nonneg (Real.logb 2 ℓ / ℓ)
          nlinarith
  have h0 := Real.sqrt_nonneg (Real.logb 2 ℓ / ℓ)
  linarith

end FTPaper
