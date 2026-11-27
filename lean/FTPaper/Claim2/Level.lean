import FTPaper.Claim2.Cost
import FTPaper.ExplicitRate

/-!
# One level of the growing recursion (paper: Theorem 1.6)

At routing parameter `x` (with `m + 1 = 2^x − 1` queries), the structured template
`xplan2 x` is correct, makes exactly the calls of Theorem 5's template `xplan x`, and spends at
most `(10/9) · 2^{14x+12}` gates per row and address outside calls (`xplan2_cost`). The local
cost is now polynomial in `m`, where Theorem 5's dense count was exponential.
-/

set_option linter.unusedSectionVars false

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open OAI.Computability.NearSquareRoot.KernelPass.Plan (frequency convertBank calls_convertBank)
open OAI.Computability.NearSquareRoot.KernelPass.Rect
open OAI.Computability.NearSquareRoot.KernelPass.Rect.Binary
open scoped OAI.Computability.NearSquareRoot.CyclotomicCode
open OAI.Computability.NearSquareRoot.BinaryQuery
open Matrix Finset Polynomial
open FTPaper.Circ FTPaper.QPlan FTPaper.LemmaS

namespace FTPaper.Claim2

/-! ## The same calls as Theorem 1 -/

lemma calls_restrictOr_congr {A W : ℕ} (W' : ℕ) (p p' : QPlan A W W) (h : p.calls = p'.calls) :
    (QPlan.restrictOr W' p).calls = (QPlan.restrictOr W' p').calls := by
  unfold QPlan.restrictOr
  split
  · simp [QPlan.calls_restrict, h]
  · rfl

theorem calls_fbPlanS_eq (L b m u v : ℕ) (S : System L b) (hv : u + v = m + 1) (q : ℚ[X])
    (j : ℕ) : (fbPlanS L b m u v S hv q j).calls = (fbPlan L b m u v S j).calls := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have h1 : (fbPlanS L b m u v S hv q (j + 1)).calls
        = 2 * (v - u) * (ourStageS L b m (20 ^ (j + 1)) S).calls
          + 2 * (QPlan.restrictOr (checks L b m (20 ^ (j + 1)) u v + checks L b m (20 ^ (j + 1)) u v)
              (fbPlanS L b m u v S hv q j)).calls := by
      rw [fbPlanS, fbPlan2, QPlan.calls_wrap _ _ _ (QPlan.calls_outerFront _ _)
        (QPlan.calls_outerBack _ _), calls_batch2]
    have h2 : (fbPlan L b m u v S (j + 1)).calls
        = 2 * (v - u) * (ourPencil L b m (20 ^ (j + 1)) S).calls
          + 2 * (QPlan.restrictOr (checks L b m (20 ^ (j + 1)) u v + checks L b m (20 ^ (j + 1)) u v)
              (fbPlan L b m u v S j)).calls := by
      rw [fbPlan, QPlan.calls_wrap _ _ _ (QPlan.calls_outerFront _ _) (QPlan.calls_outerBack _ _),
        calls_batchVia]
    rw [h1, h2, calls_ourStageS, calls_restrictOr_congr _ _ _ ih]

/-! ## The window is symmetric -/

lemma tHalf_eq (m : ℕ) : ∃ T : ℕ, tHalf m = T ∧
    (T : ℝ) < Real.sqrt (((m + 1 : ℕ) : ℝ) * Real.log 80 / 2) + 1 ∧ 1 ≤ T := by
  refine ⟨⌈Real.sqrt (((m + 1 : ℕ) : ℝ) * Real.log 80 / 2)⌉₊, rfl,
    Nat.ceil_lt_add_one (Real.sqrt_nonneg _), ?_⟩
  apply Nat.one_le_iff_ne_zero.mpr
  intro h0
  rw [Nat.ceil_eq_zero] at h0
  have : 0 < Real.sqrt (((m + 1 : ℕ) : ℝ) * Real.log 80 / 2) := by
    apply Real.sqrt_pos.mpr
    have := Real.log_pos (show (1 : ℝ) < 80 by norm_num)
    positivity
  linarith

/-- **The Hoeffding window is symmetric**: `u + v = m + 1` and `u ≤ v`, once `m + 1 ≥ 15`
is odd. -/
lemma window_symm (j : ℕ) (hj : 7 ≤ j) :
    uWin (2 * j) + vWin (2 * j) = 2 * j + 1 ∧ uWin (2 * j) ≤ vWin (2 * j) := by
  obtain ⟨T, hT, hTlt, hT1⟩ := tHalf_eq (2 * j)
  have hsq : Real.sqrt (((2 * j + 1 : ℕ) : ℝ) * Real.log 80 / 2) ≤ (j : ℝ) - 1 := by
    have hlog : Real.log 80 ≤ 9 / 2 := log_eighty_le
    have hj' : (7 : ℝ) ≤ j := by exact_mod_cast hj
    rw [Real.sqrt_le_left (by linarith)]
    have : ((2 * j + 1 : ℕ) : ℝ) = 2 * j + 1 := by push_cast; ring
    rw [this]
    have h0 : (0 : ℝ) ≤ 2 * j + 1 := by positivity
    nlinarith
  have hTj : T ≤ j := by
    have : (T : ℝ) < j := by
      have := hTlt
      push_cast at this hsq ⊢
      linarith
    exact_mod_cast this.le
  have hcast : ((2 * j + 1 : ℕ) : ℝ) / 2 = (j : ℝ) + 1 / 2 := by push_cast; ring
  have hu : uWin (2 * j) = j - T + 1 := by
    unfold uWin
    rw [hT, hcast]
    rw [Nat.ceil_eq_iff (by omega)]
    constructor
    · rw [show j - T + 1 - 1 = j - T by omega, Nat.cast_sub hTj]
      linarith
    · push_cast [Nat.cast_sub hTj]
      linarith
  have hv : vWin (2 * j) = j + T := by
    unfold vWin
    rw [hT, hcast]
    rw [Nat.floor_eq_iff (by positivity)]
    push_cast
    constructor <;> linarith
  rw [hu, hv]
  omega

lemma xm_eq (x : ℕ) (hx : 2 ≤ x) : xm x = 2 * (2 ^ (x - 1) - 1) := by
  unfold xm
  have : 2 ^ x = 2 * 2 ^ (x - 1) := by rw [← pow_succ']; congr 1; omega
  have h1 : 1 ≤ 2 ^ (x - 1) := Nat.one_le_two_pow
  omega

lemma xwin (x : ℕ) (hx : 4 ≤ x) :
    uWin (xm x) + vWin (xm x) = xm x + 1 ∧ uWin (xm x) ≤ vWin (xm x) := by
  have h8 : 8 ≤ 2 ^ (x - 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (x - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [xm_eq x (by omega)]
  exact window_symm _ (by omega)

/-! ## The decoder at parameter `x` -/

lemma xm_odd' (x : ℕ) (hx : 2 ≤ x) : Odd (xm x + 1) := by
  rw [xm_eq x hx]
  exact ⟨2 ^ (x - 1) - 1, rfl⟩

lemma exists_xq (x : ℕ) (hx : 4 ≤ x) : ∃ q : ℚ[X], q.natDegree + 1 ≤ (xm x + 1 + 1) ^ 2 ∧
    (∀ f : Fn (xm x + 1), aeval (checkOp (uWin (xm x))) q (checkOp (uWin (xm x)) f)
      = restrictE (uWin (xm x)) f) ∧
    (∀ f : Fn (xm x + 1), checkOp (uWin (xm x)) (aeval (checkOp (uWin (xm x))) q f)
      = restrictE (uWin (xm x)) f) := by
  have hw := xwin x hx
  exact decoder_poly (xm_odd' x (by omega)) (by omega)

/-- The decoder polynomial at parameter `x`. -/
noncomputable def xq (x : ℕ) (hx : 4 ≤ x) : ℚ[X] := Classical.choose (exists_xq x hx)

/-- **The structured template at parameter `x`.** -/
noncomputable def xplan2 (x : ℕ) (hx : 4 ≤ x) : QPlan (xA x) (xW x) (xW x) :=
  fbPlanS (xL x) (xb x) (xm x) (uWin (xm x)) (vWin (xm x)) (xS x) (xwin x hx).1 (xq x hx) (xd x)

theorem xplan2_correct (x : ℕ) (hx : 4 ≤ x) : QPlan.Correct (xplan2 x hx) := by
  have hq := Classical.choose_spec (exists_xq x hx)
  exact correct_fbPlan2 _ _ _ _ _ _ _ (xm_odd x (by omega)) hq.2.1 hq.2.2 _
    (fun R h x' j y => frequency_ourStageS _ _ _ R _ x' j y) _

theorem xplan2_calls (x : ℕ) (hx : 4 ≤ x) : (xplan2 x hx).calls = (xplan x).calls :=
  calls_fbPlanS_eq _ _ _ _ _ _ _ _ _

/-! ## Parameter bounds, polynomial in `2^x` -/

lemma alphabet_half_le (x : ℕ) (hx : 2 ≤ x) : alphabetExp x * halfLabel x ≤ x + halfLabel x := by
  have ha : (0 : ℝ) < halfLabel x := by exact_mod_cast halfLabel_pos hx
  have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (2 * x : ℝ) / (2 * halfLabel x) by positivity)
  have : (alphabetExp x : ℝ) * halfLabel x < x + halfLabel x := by
    unfold alphabetExp
    calc (⌈(2 * x : ℝ) / (2 * halfLabel x)⌉₊ : ℝ) * halfLabel x
        < ((2 * x : ℝ) / (2 * halfLabel x) + 1) * halfLabel x :=
          mul_lt_mul_of_pos_right h ha
      _ = x + halfLabel x := by field_simp
  exact_mod_cast this.le

lemma xbL_sharp (x : ℕ) (hx : 2 ≤ x) : xb x * xL x ≤ 4 * x + 2 := by
  have h1 := alphabet_half_le x hx
  have h2 := halfLabel_le x hx
  unfold xb xL
  nlinarith

lemma card_label_x (x : ℕ) (hx : 2 ≤ x) :
    Fintype.card (Label (xL x) (xb x)) ≤ 2 ^ (4 * x + 2) := by
  rw [card_label, ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by have := xbL_sharp x hx; nlinarith)

lemma card_free_sharp (x : ℕ) (hx : 2 ≤ x) :
    Fintype.card (Free (xL x) (xb x)) ≤ 2 ^ (8 * x + 4) := by
  have h := Circ.card_free_le (xL x) (xb x)
  have hb1 : xb x + 1 ≤ 2 ^ xb x := Nat.lt_two_pow_self
  have h2 : (xb x + 1) * 2 ^ xb x ≤ 2 ^ (2 * xb x) := by
    calc (xb x + 1) * 2 ^ xb x ≤ 2 ^ xb x * 2 ^ xb x := Nat.mul_le_mul_right _ hb1
      _ = 2 ^ (2 * xb x) := by rw [← pow_add]; ring_nf
  have hbL := xbL_sharp x hx
  calc Fintype.card (Free (xL x) (xb x)) ≤ ((xb x + 1) * 2 ^ xb x) ^ xL x := h
    _ ≤ (2 ^ (2 * xb x)) ^ xL x := Nat.pow_le_pow_left h2 _
    _ = 2 ^ (2 * (xb x * xL x)) := by rw [← pow_mul]; ring_nf
    _ ≤ 2 ^ (8 * x + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma card_paid_sharp (x : ℕ) (hx : 2 ≤ x) :
    Fintype.card (Paid (xL x) (xb x)) ≤ 2 ^ (6 * x + 4) := by
  have h := Circ.card_paid_le (xL x) (xb x)
  have hbL := xbL_sharp x hx
  have hL := xL_le x hx
  have hhalf : (2 ^ xb x) ^ (xL x / 2) ≤ 2 ^ (xb x * xL x) := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (Nat.div_le_self _ _))
  calc Fintype.card (Paid (xL x) (xb x)) ≤ 2 ^ xL x * (2 ^ xb x) ^ (xL x / 2) := h
    _ ≤ 2 ^ xL x * 2 ^ (xb x * xL x) := Nat.mul_le_mul_left _ hhalf
    _ = 2 ^ (xL x + xb x * xL x) := by rw [← pow_add]
    _ ≤ 2 ^ (6 * x + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma xm2 (x : ℕ) (hx : 2 ≤ x) : xm x + 2 = 2 ^ x := by
  have := two_le_pow x hx; unfold xm; omega

lemma pencilPerRow_x (x : ℕ) (hx : 2 ≤ x) :
    pencilPerRow (xL x) (xb x) (xm x) ≤ 2 ^ (13 * x + 8) := by
  have hF := card_free_sharp x hx
  have hP := card_paid_sharp x hx
  have hL := card_label_x x hx
  have hm := xm2 x hx
  unfold pencilPerRow
  rw [hm]
  have e1 : (2 : ℕ) ^ (13 * x + 8) = 2 ^ (8 * x + 4) * 2 ^ (4 * x + 2) * 2 ^ x * 4 := by
    rw [← pow_add, ← pow_add]; ring_nf
  have hx1 : 1 ≤ 2 ^ x := Nat.one_le_two_pow
  have hp1 : 1 ≤ 2 ^ (8 * x + 4) := Nat.one_le_two_pow
  have hp2 : 1 ≤ 2 ^ (4 * x + 2) := Nat.one_le_two_pow
  have h6 : 2 ^ (6 * x + 4) * (2 * (xm x + 1) + 1) ≤ 2 ^ (8 * x + 4) * 2 ^ (4 * x + 2) * 2 ^ x := by
    have : 2 * (xm x + 1) + 1 ≤ 2 * 2 ^ x := by omega
    calc 2 ^ (6 * x + 4) * (2 * (xm x + 1) + 1) ≤ 2 ^ (6 * x + 4) * (2 * 2 ^ x) :=
          Nat.mul_le_mul_left _ this
      _ = 2 ^ (6 * x + 5) * 2 ^ x := by rw [pow_succ]; ring
      _ ≤ 2 ^ (8 * x + 4) * 2 ^ (4 * x + 2) * 2 ^ x := by
          apply Nat.mul_le_mul_right
          rw [← pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmul : Fintype.card (Free (xL x) (xb x)) * (Fintype.card (Label (xL x) (xb x)) * 2 ^ x + 1)
      ≤ 2 ^ (8 * x + 4) * (2 ^ (4 * x + 2) * 2 ^ x + 1) :=
    Nat.mul_le_mul hF (by have := Nat.mul_le_mul_right (2 ^ x) hL; omega)
  have hmul2 : Fintype.card (Paid (xL x) (xb x)) * (2 * (xm x + 1) + 1)
      ≤ 2 ^ (8 * x + 4) * 2 ^ (4 * x + 2) * 2 ^ x :=
    (Nat.mul_le_mul_right _ hP).trans h6
  have key : ∀ X Y Z a c : ℕ, 2 ≤ X → 1 ≤ Y → 1 ≤ Z → a ≤ X * (Y * Z + 1) → c ≤ X * Y * Z →
      a + c + 2 ≤ X * Y * Z * 4 := by
    intro X Y Z a c hX hY hZ ha hc
    have hYZ : 1 ≤ Y * Z := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hXYZ : X ≤ X * Y * Z := by
      calc X = X * 1 := (mul_one X).symm
        _ ≤ X * (Y * Z) := Nat.mul_le_mul_left _ hYZ
        _ = X * Y * Z := by ring
    nlinarith
  have hp1' : 2 ≤ 2 ^ (8 * x + 4) :=
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (8 * x + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [e1]
  exact key _ _ _ _ _ hp1' hp2 hx1 hmul hmul2

lemma xq_deg (x : ℕ) (hx : 4 ≤ x) : (xq x hx).natDegree + 1 ≤ 2 ^ (2 * x) := by
  have h := (Classical.choose_spec (exists_xq x hx)).1
  have hm := xm2 x (by omega)
  have : (xm x + 1 + 1) ^ 2 = 2 ^ (2 * x) := by rw [hm, ← pow_mul, mul_comm]
  change (xq x hx).natDegree + 1 ≤ (xm x + 1 + 1) ^ 2 at h
  omega

lemma repairPerRow_x (x : ℕ) (hx : 4 ≤ x) :
    repairPerRow (xL x) (xb x) (xm x) (uWin (xm x)) (vWin (xm x)) (xq x hx).natDegree
      ≤ 2 ^ (14 * x + 12) := by
  have hP := pencilPerRow_x x (by omega)
  have hw := xwidth_le x (by omega)
  have hd := xq_deg x hx
  have hm := xm2 x (by omega)
  unfold repairPerRow
  set n := vWin (xm x) - uWin (xm x)
  set P := pencilPerRow (xL x) (xb x) (xm x)
  set d := (xq x hx).natDegree
  have hx1 : 1 ≤ 2 ^ x := Nat.one_le_two_pow
  have hP1 : P + 1 ≤ 2 * 2 ^ (13 * x + 8) := by have := @Nat.one_le_two_pow (13 * x + 8); omega
  have e1 : (2 : ℕ) ^ (14 * x + 12) = 2 ^ x * 2 ^ (13 * x + 8) * 16 := by
    rw [← pow_add]; ring_nf
  have e2 : (2 : ℕ) ^ (2 * x) = 2 ^ x * 2 ^ x := by rw [← pow_add]; ring_nf
  have h13 : 2 ^ x ≤ 2 ^ (13 * x + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have t1 : 2 * n * (P + 1) ≤ 2 * (4 * 2 ^ x) * (2 * 2 ^ (13 * x + 8)) := by gcongr
  have t2 : 2 * d * (xm x + 1 + 1) ≤ 2 * (2 ^ x * 2 ^ x) * 2 ^ x := by
    rw [show xm x + 1 + 1 = 2 ^ x by omega]
    have : d ≤ 2 ^ x * 2 ^ x := by rw [← e2]; omega
    gcongr
  have t3 : 2 ^ x * 2 ^ x ≤ 2 ^ (13 * x + 8) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [e1]
  nlinarith

/-- **Sparse local cost of the structured template**: at most `(10/9) 2^{14x+12}` gates per row
and address. -/
theorem xplan2_cost (x : ℕ) (hx : 4 ≤ x) :
    9 * qsparse (xplan2 x hx) ≤ 10 * 2 ^ (14 * x + 12) * xW x := by
  have h := qsparse_fbPlanS_le (xL x) (xb x) (xm x) (uWin (xm x)) (vWin (xm x)) (xS x)
    (xwin x hx).1 (xq x hx) (xd x)
  have hr := repairPerRow_x x hx
  calc 9 * qsparse (xplan2 x hx)
      ≤ 10 * repairPerRow (xL x) (xb x) (xm x) (uWin (xm x)) (vWin (xm x)) (xq x hx).natDegree
          * xW x := h
    _ ≤ 10 * 2 ^ (14 * x + 12) * xW x := by gcongr

end FTPaper.Claim2
