import FTPaper.QHoeffding

/-!
# Feedback conversions inside the plan language (Lemma C at the plan level)

The spectral table converts the `2s` syndrome rows into frequency coordinates and back. Each
conversion is the normalized transform on those rows, so any correct plan can do it
(`spectralVia`). Here the template does it itself, on `1/20` as many copies, recursively to
depth `d`; the bottom level uses OpenAI's direct conversion bank (`fbPlan`).

* `theorem1_feedback`: for every depth `d` there is a correct plan on `rows L b m (20^d)` rows
  with at most `(20/3·√(m+1) + 40/9) · 6D(1+b)^L + A/10^d` child calls per row.
* `theorem1`: when `A ≤ 10^d`, the bound is `(20/3·√(m+1) + 40/9) ρ + 1` with `ρ = 6D(1+b)^L`.
  This is the draft's Theorem 1, with `m + 1` queries.

Every call count here is read off the plan itself.
-/

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open OAI.Computability.NearSquareRoot.KernelPass.Plan (frequency walshMatrix convertBank
  applyAt_convertBank frequency_frequency calls_convertBank outer_kernel)
open OAI.Computability.NearSquareRoot.KernelPass.Rect.Binary (System Label card_label system)
open scoped OAI.Computability.NearSquareRoot.CyclotomicCode
open OAI.Computability.NearSquareRoot.BinaryQuery
open Matrix Finset

namespace FTPaper

namespace QPlan

variable {A : ℕ}

/-- **A correct plan computes the normalized transform on every row.** -/
theorem rowAction_of_correct {n : ℕ} (p : QPlan A n n) (hp : Correct p) (h : ℕ)
    (x : Bank A h n) : p.applyAt h x = frequency x := by
  have hconv : KernelPass.Correct (convertBank A n) :=
    KernelPass.Plan.correct_of_row_action (convertBank A n)
      (fun h x i => by rw [applyAt_convertBank]; rfl)
  have : p.applyAt h x = (convertBank A n).applyAt h x := by
    show Function.curry ((p.eval h).mulVec (Function.uncurry x)) =
      Function.curry (((convertBank A n).eval h).mulVec (Function.uncurry x))
    rw [hp h, hconv h]
  rw [this, applyAt_convertBank]

theorem correct_convertBank (n : ℕ) : Correct (QPlan.embed (A := A) (convertBank A n)) := by
  apply correct_of_row_action
  intro h x i
  rw [applyAt_embed, applyAt_convertBank]
  rfl

/-- Pad a bank with zero rows. -/
def padRows {W' W : ℕ} (hle : W' ≤ W) : QPlan A W' W :=
  .mix fun b a => if b = Fin.castLE hle a then 1 else 0

/-- Run a plan on the first `W'` of its `W` rows. -/
def restrict {W' W : ℕ} (hle : W' ≤ W) (p : QPlan A W W) : QPlan A W' W' :=
  (route (Fin.castLE hle)).seq (p.seq (padRows hle))

@[simp] theorem calls_restrict {W' W : ℕ} (hle : W' ≤ W) (p : QPlan A W W) :
    (restrict hle p).calls = p.calls := by
  simp [restrict, padRows, calls]

theorem correct_restrict {W' W : ℕ} (hle : W' ≤ W) (p : QPlan A W W) (hp : Correct p) :
    Correct (restrict hle p) := by
  apply correct_of_row_action
  intro h x i
  rw [restrict, applyAt_seq, applyAt_seq, applyAt_route, rowAction_of_correct p hp]
  simp only [Function.comp_apply, frequency]
  congr 1
  funext y
  simp only [padRows, applyAt_mix]
  rw [Finset.sum_eq_single i]
  · simp
  · intro a _ ha
    have hne : Fin.castLE hle i ≠ Fin.castLE hle a := by
      intro he
      apply ha
      ext
      have := congrArg Fin.val he
      simpa using this.symm
    simp [hne]
  · simp

/-- Restriction when the plan has enough rows; direct conversion otherwise. -/
def restrictOr {W : ℕ} (W' : ℕ) (p : QPlan A W W) : QPlan A W' W' :=
  if hle : W' ≤ W then restrict hle p else QPlan.embed (convertBank A W')

theorem correct_restrictOr {W : ℕ} (W' : ℕ) (p : QPlan A W W) (hp : Correct p) :
    Correct (restrictOr W' p) := by
  unfold restrictOr
  split
  · exact correct_restrict _ p hp
  · exact correct_convertBank W'

theorem calls_restrictOr {W W' : ℕ} (hle : W' ≤ W) (p : QPlan A W W) :
    (restrictOr W' p).calls = p.calls := by
  simp [restrictOr, hle]

/-- Address-dependent mixing in frequency coordinates, with a given conversion plan. -/
def spectralVia {n q : ℕ} (conv : QPlan A n n) (test : Column A → Fin q → ZMod 2)
    (c : (Fin q → ZMod 2) → Fin n → Fin n → ℚ) : QPlan A n n :=
  conv.seq ((matrixTable test c).seq conv)

theorem frequency_spectralVia {n q h : ℕ} (conv : QPlan A n n) (hconv : Correct conv)
    (test : Column A → Fin q → ZMod 2) (c : (Fin q → ZMod 2) → Fin n → Fin n → ℚ)
    (x : Bank A h n) (b : Fin n) (y : Addr A h) :
    frequency ((spectralVia conv test c).applyAt h x) b y =
      ∑ a, c (∑ t, test (y t)) b a * frequency x a y := by
  rw [spectralVia, applyAt_seq, applyAt_seq, rowAction_of_correct conv hconv,
    rowAction_of_correct conv hconv, frequency_frequency, applyAt_matrixTable]

@[simp] theorem calls_spectralVia {n q : ℕ} (conv : QPlan A n n)
    (test : Column A → Fin q → ZMod 2) (c : (Fin q → ZMod 2) → Fin n → Fin n → ℚ) :
    (spectralVia conv test c).calls = 2 * conv.calls := by
  simp [spectralVia]
  ring

theorem calls_batchWith {N s : ℕ} (stage : QPlan A N N) (c : ℕ → Fin N → ℚ) (n : ℕ)
    (H : Matrix (Fin s) (Fin N) ℚ) (tbl : QPlan A (s + s) (s + s)) :
    (twoPass (horner stage c n) (QPlan.mix fun r i => H r i) (QPlan.mix fun i r => H r i) tbl).calls
      = 2 * n * stage.calls + tbl.calls := by
  rw [calls_twoPass, calls_horner]
  simp only [calls_mix]
  ring

/-! ## OpenAI's outer passes, fixed once -/

/-- The front outer pass: OpenAI's sign pass for the chirp (`outer_passes`). -/
noncomputable def outerFront (m u : ℕ) : Plan (Arity m u) 1 1 := signPass (phaseBit (m := m) (u := u))

/-- The back outer pass: OpenAI's swap of the two halves, then the same sign pass. The swap is
the explicit XOR word of `reindex_linearF`. -/
noncomputable def outerBack (m u : ℕ) : Plan (Arity m u) 1 1 :=
  (reindex_linearF (swapHalves m u)).choose.seq (signPass (phaseBit (m := m) (u := u)))

theorem calls_outerFront (m u : ℕ) : (outerFront m u).calls = 0 := rfl

theorem calls_outerBack (m u : ℕ) : (outerBack m u).calls = 0 := by
  change (reindex_linearF (swapHalves m u)).choose.calls + 0 = 0
  rw [(reindex_linearF (swapHalves m u)).choose_spec.1]

theorem free_outerFront (m u : ℕ) : Circ.planFree (outerFront m u) = 0 := rfl

theorem free_outerBack (m u : ℕ) : Circ.planFree (outerBack m u) = 0 := by
  change Circ.planFree (reindex_linearF (swapHalves m u)).choose + 0 = 0
  rw [(reindex_linearF (swapHalves m u)).choose_spec.2.1]

theorem implements_outerFront (m u : ℕ) : Implements (outerFront m u) (chirp m u) :=
  implements_sign _

theorem implements_outerBack (m u : ℕ) :
    Implements (outerBack m u) (pushAddress (swapHalves m u) * chirp m u) :=
  (reindex_linearF (swapHalves m u)).choose_spec.2.2.seq (implements_sign _)

/-- **Product of signs in frequency gives a correct plan after the fixed outer passes.** -/
theorem correct_wrapOuter {m u n : ℕ} (hm : m ≡ 1 [MOD 2]) (p : QPlan (Arity m u) n n)
    (hp : ∀ h (x : Bank (Arity m u) h n) (i : Fin n) (y : Addr (Arity m u) h),
      frequency (p.applyAt h x) i y =
        (∏ j : Fin m, (-1 : ℚ) ^ ((∑ c, test m u (y c)) j).val) * frequency x i y) :
    Correct (wrap (outerFront m u) (outerBack m u) p) := by
  have hf := implements_outerFront m u
  have hb := implements_outerBack m u
  refine QPlan.correct_wrap (outerFront m u) (outerBack m u) p
    (fun h => walshMatrix (Arity m u) h *
      diagonal (fun y => ∏ j : Fin m, (-1 : ℚ) ^ ((∑ c, test m u (y c)) j).val) *
      walshMatrix (Arity m u) h) ?_ ?_
  · intro h x i
    exact applyAt_of_frequency p (fun _ y => ∏ j : Fin m, (-1 : ℚ) ^ ((∑ c, test m u (y c)) j).val)
      (fun x b y => hp h x b y) x i
  · intro h
    exact outer_kernel hm (outerFront m u) (outerBack m u) hf hb _ (product_kernel m u h)

end QPlan

/-! ## The batch with a conversion plan -/

/-- The repaired batch, with a conversion plan on the `2·checks` syndrome rows. -/
noncomputable def batchVia (L b m R u v : ℕ) (S : System L b)
    (conv : QPlan (Charged.Axes (m := m) S.geometry) (checks L b m R u v + checks L b m R u v)
      (checks L b m R u v + checks L b m R u v)) :
    QPlan (Charged.Axes (m := m) S.geometry) (rows L b m R) (rows L b m R) :=
  QPlan.twoPass (QPlan.horner (ourStage L b m R S) (fun t i => (winPoly u v (shiftAt i)).coeff t) (v - u))
    (QPlan.mix fun r i => checkMatrix L b m R u v r i) (QPlan.mix fun i r => checkMatrix L b m R u v r i)
    (QPlan.spectralVia conv (test (m + 1) (S.D - 1))
      fun κ => QPlan.tabMatrix (table L b m R u v κ) (sgnZ κ))

theorem frequency_batchVia (L b m R u v : ℕ) (S : System L b)
    (conv : QPlan (Charged.Axes (m := m) S.geometry) (checks L b m R u v + checks L b m R u v)
      (checks L b m R u v + checks L b m R u v)) (hconv : QPlan.Correct conv) {h : ℕ}
    (x : Bank (Charged.Axes (m := m) S.geometry) h (rows L b m R)) (i : Fin (rows L b m R))
    (y : Addr (Charged.Axes (m := m) S.geometry) h) :
    frequency ((batchVia L b m R u v S conv).applyAt h x) i y
      = sgnZ (∑ t, test (m + 1) (S.D - 1) (y t)) * frequency x i y :=
  QPlan.frequency_batchWith (ourStage L b m R S) (test (m + 1) (S.D - 1))
    (fun i κ => (mismatch κ (shiftAt i) : ℚ)) (fun x j y => frequency_ourStage L b m R S x j y)
    (fun t i => (winPoly u v (shiftAt i)).coeff t) (v - u) sgnZ (checkMatrix L b m R u v)
    (table L b m R u v) (fun κ => Classical.choose_spec (exists_tables L b m R u v κ)) _
    (fun w r y => QPlan.frequency_spectralVia conv hconv _ _ w r y) x i y

theorem calls_batchVia (L b m R u v : ℕ) (S : System L b)
    (conv : QPlan (Charged.Axes (m := m) S.geometry) (checks L b m R u v + checks L b m R u v)
      (checks L b m R u v + checks L b m R u v)) :
    (batchVia L b m R u v S conv).calls
      = 2 * (v - u) * (ourPencil L b m R S).calls + 2 * conv.calls := by
  have h1 := QPlan.calls_batchWith (A := Charged.Axes (m := m) S.geometry) (ourStage L b m R S)
    (fun t i => (winPoly u v (shiftAt i)).coeff t) (v - u) (checkMatrix L b m R u v)
    (QPlan.spectralVia conv (test (m + 1) (S.D - 1))
      fun κ => QPlan.tabMatrix (table L b m R u v κ) (sgnZ κ))
  have h2 : (QPlan.spectralVia conv (test (m + 1) (S.D - 1))
      fun κ => QPlan.tabMatrix (table L b m R u v κ) (sgnZ κ)).calls = 2 * conv.calls :=
    QPlan.calls_spectralVia _ _ _
  have h3 : (ourStage L b m R S).calls = (ourPencil L b m R S).calls := by
    simp only [ourStage, QPlan.calls_embed,
      OAI.Computability.NearSquareRoot.KernelPass.Rect.calls_renumber]
  rw [h2, h3] at h1
  exact h1

/-! ## The feedback family -/

/-- The feedback family. Level `j` works on `20^j` copies, and its conversions are done by
level `j − 1`. Level `0` is OpenAI's direct conversion bank. -/
noncomputable def fbPlan (L b m u v : ℕ) (S : System L b) :
    (j : ℕ) → QPlan (Charged.Axes (m := m) S.geometry) (rows L b m (20 ^ j)) (rows L b m (20 ^ j))
  | 0 => QPlan.embed (convertBank _ _)
  | j + 1 => QPlan.wrap (QPlan.outerFront (m + 1) (S.geometry.D - 1))
      (QPlan.outerBack (m + 1) (S.geometry.D - 1))
      (batchVia L b m (20 ^ (j + 1)) u v S (QPlan.restrictOr _ (fbPlan L b m u v S j)))

/-- **Every level of the feedback family is correct**, for any window. -/
theorem correct_fbPlan (L b m u v : ℕ) (S : System L b) (hodd : m + 1 ≡ 1 [MOD 2]) (j : ℕ) :
    QPlan.Correct (fbPlan L b m u v S j) := by
  induction j with
  | zero => exact QPlan.correct_convertBank _
  | succ j ih =>
    rw [fbPlan]
    apply QPlan.correct_wrapOuter (m := m + 1) (u := S.geometry.D - 1) hodd
    intro h x i y
    exact frequency_batchVia L b m _ u v S _ (QPlan.correct_restrictOr _ _ ih) x i y

/-- Rows per batch: `|labels| · R · 2^(m+1)`. -/
lemma rows_eq (L b m R : ℕ) : rows L b m R = Fintype.card (Label L b) * (R * 2 ^ (m + 1)) := by
  simp [rows, Row, Fintype.card_prod, Fintype.card_fin, ZMod.card]

lemma rows_twenty (L b m j : ℕ) : rows L b m (20 ^ (j + 1)) = 20 * rows L b m (20 ^ j) := by
  rw [rows_eq, rows_eq]; ring

lemma rows_pow (L b m j : ℕ) : rows L b m (20 ^ j) = 20 ^ j * rows L b m 1 := by
  rw [rows_eq, rows_eq]; ring

/-- **The syndrome rows of level `j + 1` fit into level `j`** when at most `1/40` of the
shifts falls outside the window. -/
lemma syndrome_fits (L b m j u v : ℕ)
    (hE : 40 * (outside u v (0 : Fin (m + 1) → ZMod 2)).card ≤ 2 ^ (m + 1)) :
    checks L b m (20 ^ (j + 1)) u v + checks L b m (20 ^ (j + 1)) u v ≤ rows L b m (20 ^ j) := by
  rw [rows_eq]
  simp only [checks]
  have : Fintype.card (Label L b) * 20 ^ (j + 1) * (outside u v (0 : Fin (m + 1) → ZMod 2)).card
      + Fintype.card (Label L b) * 20 ^ (j + 1) * (outside u v (0 : Fin (m + 1) → ZMod 2)).card
      = Fintype.card (Label L b) * (20 ^ j * (40 * (outside u v (0 : Fin (m + 1) → ZMod 2)).card)) := by
    ring
  rw [this]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hE)

/-- The stage costs at most `6 D (1+b)^L` calls per row (Lemma R1). -/
lemma ourPencil_calls_le (L b m R : ℕ) (S : System L b) (hb : 1 ≤ b) (hq : m + 1 ≤ (2 ^ b) ^ (L / 2)) :
    (ourPencil L b m R S).calls ≤ 6 * S.D * (1 + b) ^ L * rows L b m R := by
  have hR1 := lemmaR1_pencilF S m (stageB₀ m) (stageB m (fun k : Fin R × (Fin (m + 1) → ZMod 2) => k.2))
    hb hq
  have hrows : (2 ^ b) ^ L * Fintype.card (Fin R × (Fin (m + 1) → ZMod 2)) = rows L b m R := by
    simp only [rows, Row, Fintype.card_prod, card_label]
  rw [hrows] at hR1
  exact hR1

/-- **Exact recursion of the feedback family's calls.** -/
theorem calls_fbPlan_succ (L b m u v : ℕ) (S : System L b) (j : ℕ)
    (hle : checks L b m (20 ^ (j + 1)) u v + checks L b m (20 ^ (j + 1)) u v ≤ rows L b m (20 ^ j)) :
    (fbPlan L b m u v S (j + 1)).calls
      = 2 * (v - u) * (ourPencil L b m (20 ^ (j + 1)) S).calls + 2 * (fbPlan L b m u v S j).calls := by
  rw [fbPlan, QPlan.calls_wrap _ _ _ (QPlan.calls_outerFront _ _) (QPlan.calls_outerBack _ _),
    calls_batchVia, QPlan.calls_restrictOr hle]

/-- **Cost of the feedback family (Lemma C at the plan level).** With `K = 6 D (1+b)^L` and
`n = v − u`, level `j` makes at most `(20/9)·n·K` calls per row, plus `2^j·A` calls per copy of
the bottom batch. -/
theorem calls_fbPlan_le (L b m u v : ℕ) (S : System L b) (hb : 1 ≤ b)
    (hq : m + 1 ≤ (2 ^ b) ^ (L / 2))
    (hE : 40 * (outside u v (0 : Fin (m + 1) → ZMod 2)).card ≤ 2 ^ (m + 1)) (j : ℕ) :
    9 * (fbPlan L b m u v S j).calls
      ≤ 20 * (v - u) * (6 * S.D * (1 + b) ^ L) * rows L b m (20 ^ j)
        + 9 * 2 ^ j * Charged.Axes (m := m) S.geometry * rows L b m 1 := by
  induction j with
  | zero =>
    have h0 : (fbPlan L b m u v S 0).calls = rows L b m (20 ^ 0) * Charged.Axes (m := m) S.geometry := by
      rw [fbPlan, QPlan.calls_embed, calls_convertBank]
    rw [h0, pow_zero, pow_zero]
    nlinarith [Nat.zero_le (20 * (v - u) * (6 * S.D * (1 + b) ^ L) * rows L b m 1)]
  | succ j ih =>
    rw [calls_fbPlan_succ L b m u v S j (syndrome_fits L b m j u v hE)]
    have hst := ourPencil_calls_le L b m (20 ^ (j + 1)) S hb hq
    have hrw := rows_twenty L b m j
    set K := 6 * S.D * (1 + b) ^ L
    set n := v - u
    set Ax := Charged.Axes (m := m) S.geometry
    have hst' : 2 * n * (ourPencil L b m (20 ^ (j + 1)) S).calls ≤ 2 * n * (K * rows L b m (20 ^ (j + 1))) :=
      Nat.mul_le_mul_left _ hst
    calc 9 * (2 * n * (ourPencil L b m (20 ^ (j + 1)) S).calls + 2 * (fbPlan L b m u v S j).calls)
        = 9 * (2 * n * (ourPencil L b m (20 ^ (j + 1)) S).calls) + 2 * (9 * (fbPlan L b m u v S j).calls) := by
          ring
      _ ≤ 9 * (2 * n * (K * rows L b m (20 ^ (j + 1))))
          + 2 * (20 * n * K * rows L b m (20 ^ j) + 9 * 2 ^ j * Ax * rows L b m 1) := by
          gcongr
      _ = 20 * n * K * rows L b m (20 ^ (j + 1)) + 9 * 2 ^ (j + 1) * Ax * rows L b m 1 := by
          rw [hrw]; ring

/-! ## Theorem 1 -/

/-- Half-width of the Hoeffding window. -/
noncomputable def tHalf (m : ℕ) : ℝ := (⌈Real.sqrt (((m + 1 : ℕ) : ℝ) * Real.log 80 / 2)⌉₊ : ℝ)

/-- Lower end of the window. -/
noncomputable def uWin (m : ℕ) : ℕ := ⌈((m + 1 : ℕ) : ℝ) / 2 - tHalf m⌉₊

/-- Upper end of the window. -/
noncomputable def vWin (m : ℕ) : ℕ := ⌊((m + 1 : ℕ) : ℝ) / 2 + tHalf m⌋₊

lemma tHalf_nonneg (m : ℕ) : 0 ≤ tHalf m := Nat.cast_nonneg _

lemma tHalf_hoeffding (m : ℕ) : ((m + 1 : ℕ) : ℝ) * Real.log 80 ≤ 2 * tHalf m ^ 2 := by
  have h1 : Real.sqrt (((m + 1 : ℕ) : ℝ) * Real.log 80 / 2) ≤ tHalf m := Nat.le_ceil _
  have h2 : (Real.sqrt (((m + 1 : ℕ) : ℝ) * Real.log 80 / 2)) ^ 2
      = ((m + 1 : ℕ) : ℝ) * Real.log 80 / 2 :=
    Real.sq_sqrt (by have := Real.log_nonneg (show (1 : ℝ) ≤ 80 by norm_num); positivity)
  have h0 : 0 ≤ Real.sqrt (((m + 1 : ℕ) : ℝ) * Real.log 80 / 2) := Real.sqrt_nonneg _
  nlinarith

/-- At most `1/40` of the shifts lie outside the window. -/
lemma outside_window (m : ℕ) :
    40 * (outside (uWin m) (vWin m) (0 : Fin (m + 1) → ZMod 2)).card ≤ 2 ^ (m + 1) := by
  have h := outside_card_le (M := m + 1) (Nat.succ_pos m) (tHalf m) (tHalf_nonneg m)
    (tHalf_hoeffding m)
  have h' : ((40 * (outside (uWin m) (vWin m) (0 : Fin (m + 1) → ZMod 2)).card : ℕ) : ℝ)
      ≤ ((2 ^ (m + 1) : ℕ) : ℝ) := by
    push_cast
    unfold uWin vWin
    linarith
  exact_mod_cast h'

/-- The window has width at most `3√(m+1) + 2`. -/
lemma window_width (m : ℕ) : ((vWin m - uWin m : ℕ) : ℝ) ≤ 3 * Real.sqrt ((m + 1 : ℕ) : ℝ) + 2 := by
  have ht0 := tHalf_nonneg m
  have hw := window_width_le (m := m + 1) (tHalf m) ht0
  have hsub : ((vWin m - uWin m : ℕ) : ℝ) ≤ 2 * tHalf m := by
    rcases le_total (uWin m) (vWin m) with h | h
    · rw [Nat.cast_sub h]; unfold uWin vWin; exact hw
    · rw [Nat.sub_eq_zero_of_le h]; simp only [Nat.cast_zero]; linarith
  have hsq0 : 0 ≤ Real.sqrt (((m + 1 : ℕ) : ℝ) * Real.log 80 / 2) := Real.sqrt_nonneg _
  have hsqrt : Real.sqrt (((m + 1 : ℕ) : ℝ) * Real.log 80 / 2) ≤ 3 / 2 * Real.sqrt ((m + 1 : ℕ) : ℝ) := by
    have hlog : Real.log 80 / 2 ≤ 9 / 4 := by linarith [log_eighty_le]
    have hm0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    calc Real.sqrt (((m + 1 : ℕ) : ℝ) * Real.log 80 / 2)
        = Real.sqrt (((m + 1 : ℕ) : ℝ) * (Real.log 80 / 2)) := by ring_nf
      _ ≤ Real.sqrt (((m + 1 : ℕ) : ℝ) * (9 / 4)) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 3 / 2 * Real.sqrt ((m + 1 : ℕ) : ℝ) := by
          rw [Real.sqrt_mul hm0, show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]; ring
  have htle : tHalf m ≤ Real.sqrt (((m + 1 : ℕ) : ℝ) * Real.log 80 / 2) + 1 :=
    (Nat.ceil_lt_add_one hsq0).le
  linarith

/-- The call bound of the specific feedback plan with the Hoeffding window. -/
theorem fbPlan_calls_bound (L b m d : ℕ) (S : System L b) (hb : 1 ≤ b)
    (hq : m + 1 ≤ (2 ^ b) ^ (L / 2)) :
    ((fbPlan L b m (uWin m) (vWin m) S d).calls : ℝ) / rows L b m (20 ^ d)
      ≤ (20 / 3 * Real.sqrt ((m + 1 : ℕ) : ℝ) + 40 / 9) * (6 * S.D * (1 + b) ^ L)
        + (Charged.Axes (m := m) S.geometry : ℝ) / 10 ^ d := by
  have hc := calls_fbPlan_le L b m (uWin m) (vWin m) S hb hq (outside_window m) d
  have hc' : (9 * (fbPlan L b m (uWin m) (vWin m) S d).calls : ℝ)
      ≤ 20 * ((vWin m - uWin m : ℕ) : ℝ) * (6 * S.D * (1 + b) ^ L) * rows L b m (20 ^ d)
        + 9 * 2 ^ d * (Charged.Axes (m := m) S.geometry : ℝ) * rows L b m 1 := by
    exact_mod_cast hc
  have hG : (0 : ℝ) < rows L b m 1 := by
    have : 0 < rows L b m 1 := by
      rw [rows_eq]
      have : 0 < Fintype.card (Label L b) := by rw [card_label]; positivity
      positivity
    exact_mod_cast this
  have hpow : (rows L b m (20 ^ d) : ℝ) = 20 ^ d * rows L b m 1 := by
    rw [rows_pow]; push_cast; ring
  have hrows0 : (0 : ℝ) < rows L b m (20 ^ d) := by rw [hpow]; positivity
  have hw := window_width m
  have hK : (0 : ℝ) ≤ 6 * S.D * (1 + b) ^ L := by positivity
  have hA : (0 : ℝ) ≤ (Charged.Axes (m := m) S.geometry : ℝ) := Nat.cast_nonneg _
  rw [div_le_iff₀ hrows0]
  have h10 : (10 : ℝ) ^ d * 2 ^ d = 20 ^ d := by rw [← mul_pow]; norm_num
  have h10pos : (0 : ℝ) < 10 ^ d := by positivity
  have hbase : 9 * 2 ^ d * (Charged.Axes (m := m) S.geometry : ℝ) * rows L b m 1
      = 9 * ((Charged.Axes (m := m) S.geometry : ℝ) / 10 ^ d) * rows L b m (20 ^ d) := by
    rw [hpow, ← h10]
    field_simp
  have hmain : 20 * ((vWin m - uWin m : ℕ) : ℝ) * (6 * S.D * (1 + b) ^ L) * rows L b m (20 ^ d)
      ≤ 20 * (3 * Real.sqrt ((m + 1 : ℕ) : ℝ) + 2) * (6 * S.D * (1 + b) ^ L) * rows L b m (20 ^ d) := by
    gcongr
  nlinarith [hc', hbase, hmain]

/-- **Theorem 1 with feedback conversions, end to end in OpenAI's routing.** Take an odd number
`m + 1` of queries and a routing system with `m + 1 ≤ q^{L/2}`. For every depth `d` there is a
plan on `rows L b m (20^d)` rows that computes the normalized Walsh–Hadamard transform on every
row (`QPlan.Correct`), with at most `(20/3·√(m+1) + 40/9) · 6D(1+b)^L + A/10^d` child calls per
row. -/
theorem theorem1_feedback (L b m d : ℕ) (S : System L b) (hodd : m + 1 ≡ 1 [MOD 2]) (hb : 1 ≤ b)
    (hq : m + 1 ≤ (2 ^ b) ^ (L / 2)) :
    ∃ p : QPlan (Charged.Axes (m := m) S.geometry) (rows L b m (20 ^ d)) (rows L b m (20 ^ d)),
      QPlan.Correct p ∧
      (p.calls : ℝ) / rows L b m (20 ^ d)
        ≤ (20 / 3 * Real.sqrt ((m + 1 : ℕ) : ℝ) + 40 / 9) * (6 * S.D * (1 + b) ^ L)
          + (Charged.Axes (m := m) S.geometry : ℝ) / 10 ^ d := by
  exact ⟨fbPlan L b m (uWin m) (vWin m) S d, correct_fbPlan L b m _ _ S hodd d,
    fbPlan_calls_bound L b m d S hb hq⟩

/-- The call bound of the specific feedback plan, when `A ≤ 10^d`. -/
theorem fbPlan_calls_bound_one (L b m d : ℕ) (S : System L b) (hb : 1 ≤ b)
    (hq : m + 1 ≤ (2 ^ b) ^ (L / 2)) (hd : Charged.Axes (m := m) S.geometry ≤ 10 ^ d) :
    ((fbPlan L b m (uWin m) (vWin m) S d).calls : ℝ) / rows L b m (20 ^ d)
      ≤ (20 / 3 * Real.sqrt ((m + 1 : ℕ) : ℝ) + 40 / 9) * (6 * S.D * (1 + b) ^ L) + 1 := by
  refine (fbPlan_calls_bound L b m d S hb hq).trans ?_
  have h10 : (0 : ℝ) < 10 ^ d := by positivity
  have hd' : (Charged.Axes (m := m) S.geometry : ℝ) ≤ 10 ^ d := by exact_mod_cast hd
  have : (Charged.Axes (m := m) S.geometry : ℝ) / 10 ^ d ≤ 1 := by
    rw [div_le_one h10]; exact hd'
  linarith

/-- **Theorem 1** (the draft's statement, with `m + 1` queries): when the depth satisfies
`A ≤ 10^d`, the plan makes at most `(20/3·√(m+1) + 40/9) ρ + 1` calls per row, where
`ρ = 6 D (1+b)^L` bounds one pencil stage (Lemma R1). -/
theorem theorem1 (L b m d : ℕ) (S : System L b) (hodd : m + 1 ≡ 1 [MOD 2]) (hb : 1 ≤ b)
    (hq : m + 1 ≤ (2 ^ b) ^ (L / 2)) (hd : Charged.Axes (m := m) S.geometry ≤ 10 ^ d) :
    ∃ p : QPlan (Charged.Axes (m := m) S.geometry) (rows L b m (20 ^ d)) (rows L b m (20 ^ d)),
      QPlan.Correct p ∧
      (p.calls : ℝ) / rows L b m (20 ^ d)
        ≤ (20 / 3 * Real.sqrt ((m + 1 : ℕ) : ℝ) + 40 / 9) * (6 * S.D * (1 + b) ^ L) + 1 := by
  exact ⟨fbPlan L b m (uWin m) (vWin m) S d, correct_fbPlan L b m _ _ S hodd d,
    fbPlan_calls_bound_one L b m d S hb hq hd⟩


/-- The axis count of the template: `A = 2 (m + D)`. -/
lemma axes_eq (L b m : ℕ) (S : System L b) : Charged.Axes (m := m) S.geometry = 2 * (m + S.D) := by
  have hD : 0 < S.D := S.dimension_pos
  show (m + 1 + (S.D - 1)) + (m + 1 + (S.D - 1)) = 2 * (m + S.D)
  omega

/-- The call bound of the specific feedback plan for OpenAI's `system L b`. (Theorem 1, explicit.) For every `L`, every `b ≥ 1`, every even `m` with
`m + 1 ≤ 2^{b⌊L/2⌋}`, and every `d` with `2 (m + 2 + L 2^b) ≤ 10^d`, OpenAI's routing system
`system L b` yields a plan that computes the normalized Walsh–Hadamard transform on every row of
a batch of `rows L b m (20^d)` rows, with at most
`(20/3·√(m+1) + 40/9) · 6 (2 + L 2^b)(1+b)^L + 1` child calls per row. -/
theorem fbPlan_calls_bound_explicit (L b m d : ℕ) (hb : 1 ≤ b)
    (hq : m + 1 ≤ (2 ^ b) ^ (L / 2)) (hd : 2 * (m + 2 + L * 2 ^ b) ≤ 10 ^ d) :
    ((fbPlan L b m (uWin m) (vWin m) (system L b) d).calls : ℝ) / rows L b m (20 ^ d)
        ≤ (20 / 3 * Real.sqrt ((m + 1 : ℕ) : ℝ) + 40 / 9) * (6 * (2 + L * 2 ^ b) * (1 + b) ^ L) + 1 := by
  set S := system L b
  have hD : S.D ≤ 2 + L * 2 ^ b := by
    have := S.dimension_le
    simp only [Nat.reduceSub, pow_one] at this
    omega
  have hA : Charged.Axes (m := m) S.geometry ≤ 10 ^ d := by
    rw [axes_eq]; omega
  have hc := fbPlan_calls_bound_one L b m d S hb hq hA
  refine hc.trans ?_
  have hD' : (S.D : ℝ) ≤ 2 + L * 2 ^ b := by exact_mod_cast hD
  have hpos : (0 : ℝ) ≤ 20 / 3 * Real.sqrt ((m + 1 : ℕ) : ℝ) + 40 / 9 := by positivity
  have hb' : (0 : ℝ) ≤ (1 + (b : ℝ)) ^ L := by positivity
  have : 6 * (S.D : ℝ) * (1 + b) ^ L ≤ 6 * (2 + L * 2 ^ b) * (1 + b) ^ L := by gcongr
  nlinarith [mul_le_mul_of_nonneg_left this hpos]

/-- **Theorem 1, explicit.** For every `L`, every `b ≥ 1`, every even `m` with
`m + 1 ≤ 2^{b⌊L/2⌋}`, and every `d` with `2 (m + 2 + L 2^b) ≤ 10^d`, OpenAI's routing system
`system L b` yields a plan that computes the normalized Walsh–Hadamard transform on every row of
a batch of `rows L b m (20^d)` rows, with at most
`(20/3·√(m+1) + 40/9) · 6 (2 + L 2^b)(1+b)^L + 1` child calls per row. -/
theorem theorem1_explicit (L b m d : ℕ) (hodd : m + 1 ≡ 1 [MOD 2]) (hb : 1 ≤ b)
    (hq : m + 1 ≤ (2 ^ b) ^ (L / 2)) (hd : 2 * (m + 2 + L * 2 ^ b) ≤ 10 ^ d) :
    ∃ p : QPlan (Charged.Axes (m := m) (system L b).geometry) (rows L b m (20 ^ d))
        (rows L b m (20 ^ d)),
      QPlan.Correct p ∧
      (p.calls : ℝ) / rows L b m (20 ^ d)
        ≤ (20 / 3 * Real.sqrt ((m + 1 : ℕ) : ℝ) + 40 / 9) * (6 * (2 + L * 2 ^ b) * (1 + b) ^ L) + 1 :=
  ⟨fbPlan L b m (uWin m) (vWin m) (system L b) d, correct_fbPlan L b m _ _ _ hodd d,
    fbPlan_calls_bound_explicit L b m d hb hq hd⟩

end FTPaper
