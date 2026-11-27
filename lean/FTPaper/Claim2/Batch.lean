import FTPaper.Claim2.Table
import FTPaper.QFeedback

/-!
# The Theorem 1 template with structured checks (paper: Section 9)

The template of `FTPaper/QMain.lean` and `FTPaper/QFeedback.lean`, with the dense Vandermonde
checks and dense tables replaced by Lemma S:
* character checks on the tails, by one fast Walsh–Hadamard transform per (label, copy) block;
* the structured table `D_κ q(M) Λ_κ q(M) D_κ` with a fixed polynomial `q` (`decoder_poly`).

`fbPlan2` is the feedback family with these checks. It is correct (`correct_fbPlan2`) and makes
exactly as many calls as `fbPlan` (`calls_fbPlan2_le`), for any stage family with the frequency
action of the routed pencil.
-/

set_option linter.unusedSectionVars false

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open OAI.Computability.NearSquareRoot.KernelPass.Plan (frequency walshMatrix convertBank
  applyAt_convertBank frequency_frequency calls_convertBank)
open OAI.Computability.NearSquareRoot.KernelPass.Rect.Binary (System Label card_label)
open scoped OAI.Computability.NearSquareRoot.CyclotomicCode
open OAI.Computability.NearSquareRoot.BinaryQuery
open Matrix Finset Polynomial
open FTPaper.LemmaS FTPaper.QPlan

namespace FTPaper.Claim2

/-! ## Shifts as subsets -/

lemma zmod2_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by
  revert t; decide

/-- Shifts as subsets. -/
def supEquiv (M : ℕ) : (Fin M → ZMod 2) ≃ Finset (Fin M) where
  toFun := supK
  invFun S j := if j ∈ S then 1 else 0
  left_inv κ := by
    funext j
    rcases zmod2_cases (κ j) with h | h <;> simp [supK, h]
  right_inv S := by
    ext j
    by_cases h : j ∈ S <;> simp [supK, h]

lemma mismatch_eq {M : ℕ} (κ β : Fin M → ZMod 2) :
    mismatch κ β = (symmDiff (supK β) (supK κ)).card := by
  unfold mismatch
  congr 1
  ext j
  simp only [mem_filter, mem_univ, true_and, mem_symmDiff, supK]
  rcases zmod2_cases (κ j) with h | h <;> rcases zmod2_cases (β j) with h' | h' <;> simp [h, h']

/-! ## The block structure of the template -/

/-- Blocks: a label and a copy index. -/
abbrev Blk (L b R : ℕ) := Label L b × Fin R

/-- Rows as (block, subset). -/
noncomputable def rowE (L b m R : ℕ) : Fin (rows L b m R) ≃ Blk L b R × Finset (Fin (m + 1)) :=
  (rowEquiv L b m R).symm.trans
    ((Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodCongr (Equiv.refl _) (supEquiv (m + 1))))

lemma rowE_snd (L b m R : ℕ) (i : Fin (rows L b m R)) : (rowE L b m R i).2 = supK (shiftAt i) :=
  rfl

lemma card_tail (u v m : ℕ) (hv : u + v = m + 1) :
    Fintype.card (Tail (m + 1) u) = (outside u v (0 : Fin (m + 1) → ZMod 2)).card := by
  rw [Fintype.card_subtype]
  have h0 : ∀ γ : Fin (m + 1) → ZMod 2, mismatch 0 γ = (supK γ).card := by
    intro γ
    rw [mismatch_eq]
    have : supK (0 : Fin (m + 1) → ZMod 2) = ∅ := by ext j; simp [supK]
    rw [this, ← bot_eq_empty, symmDiff_bot]
  symm
  refine Finset.card_bij (fun γ _ => supK γ) ?_ ?_ ?_
  · intro γ hγ
    simp only [outside, mem_filter, mem_univ, true_and, h0] at hγ ⊢
    omega
  · intro γ₁ _ γ₂ _ h
    exact (supEquiv (m + 1)).injective h
  · intro S hS
    refine ⟨(supEquiv (m + 1)).symm S, ?_, (supEquiv (m + 1)).apply_symm_apply S⟩
    simp only [outside, mem_filter, mem_univ, true_and, h0] at hS ⊢
    have : supK ((supEquiv (m + 1)).symm S) = S := (supEquiv (m + 1)).apply_symm_apply S
    rw [this]
    omega

lemma card_checks (L b m R u v : ℕ) (hv : u + v = m + 1) :
    checks L b m R u v = Fintype.card (Blk L b R × Tail (m + 1) u) := by
  rw [Fintype.card_prod, Fintype.card_prod, card_tail u v m hv, Fintype.card_fin]

/-- Check rows as (block, tail subset). -/
noncomputable def checkC (L b m R u v : ℕ) (hv : u + v = m + 1) :
    Fin (checks L b m R u v) ≃ Blk L b R × Tail (m + 1) u :=
  (finCongr (card_checks L b m R u v hv)).trans (Fintype.equivFin _).symm

/-- The block structure of the template. -/
noncomputable def tmpl (L b m R u v : ℕ) (hv : u + v = m + 1) :
    Blocks (Blk L b R) (m + 1) u (rows L b m R) (checks L b m R u v) :=
  ⟨rowE L b m R, checkC L b m R u v hv⟩

/-- **The predictor errs only on translates of the tails.** -/
lemma wrong_tail (L b m R u v : ℕ) (hv : u + v = m + 1) (i : Fin (rows L b m R))
    (κ : Fin (m + 1) → ZMod 2) (h : predMult L b m R u v i κ ≠ sgnZ κ) :
    (symmDiff ((tmpl L b m R u v hv).e i).2 (supK κ)).card < u ∨
      m + 1 - u < (symmDiff ((tmpl L b m R u v hv).e i).2 (supK κ)).card := by
  have hout : ¬ (u ≤ mismatch κ (shiftAt i) ∧ mismatch κ (shiftAt i) ≤ v) := by
    rintro ⟨h1, h2⟩
    exact h (by rw [predMult_eq, winPoly_window u v κ _ h1 h2])
  rw [mismatch_eq] at hout
  have hrow : ((tmpl L b m R u v hv).e i).2 = supK (shiftAt i) := rfl
  rw [hrow]
  omega

/-! ## Calls of the structured plans -/

namespace Blocks

variable {B : Type} [Fintype B] [DecidableEq B] {M u N s : ℕ} (bk : Blocks B M u N s) {A : ℕ}

@[simp] lemma calls_whtPlan (js : List (Fin M)) : (bk.whtPlan (A := A) js).calls = 0 := by
  induction js with
  | nil => rfl
  | cons j js ih => simp [whtPlan, ih]

@[simp] lemma calls_gather : (bk.gather (A := A)).calls = 0 := by
  simp [gather, restrictPlan]

@[simp] lemma calls_scatter : (bk.scatter (A := A)).calls = 0 := by
  simp [scatter, extendPlan]

@[simp] lemma calls_mPlan : (bk.mPlan (A := A)).calls = 0 := by
  simp [mPlan, restrictPlan, extendPlan]

@[simp] lemma calls_tablePlan (test : Column A → Fin M → ZMod 2) (q : ℚ[X])
    (Λ : B → (Fin M → ZMod 2) → Fn M) (z : (Fin M → ZMod 2) → ℚ) :
    (bk.tablePlan test q Λ z).calls = 0 := by
  simp [tablePlan, tPlan, twistPlan, scalePlan, qPlan, diffPlan, calls_horner, QPlan.calls]

/-- The table with conversions acts in frequency coordinates by `tabMatrix`. -/
lemma frequency_tbl (test : Column A → Fin M → ZMod 2) (q : ℚ[X])
    (Λ : B → (Fin M → ZMod 2) → Fn M) (z : (Fin M → ZMod 2) → ℚ)
    (conv : QPlan A (s + s) (s + s)) (hconv : QPlan.Correct conv) {h : ℕ}
    (w : Bank A h (s + s)) (r : Fin (s + s)) (y : Addr A h) :
    frequency ((conv.seq ((bk.tablePlan test q Λ z).seq conv)).applyAt h w) r y
      = ∑ a, tabMatrix (bk.blockAct fun k =>
          decodeL u q (supK (∑ t, test (y t))) (Λ k (∑ t, test (y t)))) (z (∑ t, test (y t))) r a
          * frequency w a y := by
  rw [applyAt_seq, applyAt_seq, QPlan.rowAction_of_correct conv hconv,
    QPlan.rowAction_of_correct conv hconv, frequency_frequency]
  rw [show (bk.tablePlan test q Λ z).applyAt h (frequency w) r y
    = colAt ((bk.tablePlan test q Λ z).applyAt h (frequency w)) y r from rfl, colAt_tablePlan]
  have := congrFun (tabMatrix_apply (bk.blockAct fun k =>
      decodeL u q (supK (∑ t, test (y t))) (Λ k (∑ t, test (y t)))) (z (∑ t, test (y t)))
    (leftPart (colAt (frequency w) y)) (rightPart (colAt (frequency w) y))) r
  rw [append_parts] at this
  exact this.symm

end Blocks

/-! ## The batch with structured checks -/

/-- The division weights of the template at signature `κ`. -/
noncomputable def divTmpl (L b m R u v : ℕ) (hv : u + v = m + 1) (k : Blk L b R)
    (κ : Fin (m + 1) → ZMod 2) : Fn (m + 1) :=
  divW (supK κ) (fun S => predMult L b m R u v ((tmpl L b m R u v hv).e.symm (k, S)) κ - sgnZ κ)

/-- **The repaired batch with structured checks.** -/
noncomputable def batch2 (L b m : ℕ) (S : System L b) (R u v : ℕ) (hv : u + v = m + 1) (q : ℚ[X])
    (stage : QPlan (Charged.Axes (m := m) S.geometry) (rows L b m R) (rows L b m R))
    (conv : QPlan (Charged.Axes (m := m) S.geometry) (checks L b m R u v + checks L b m R u v)
      (checks L b m R u v + checks L b m R u v)) :
    QPlan (Charged.Axes (m := m) S.geometry) (rows L b m R) (rows L b m R) :=
  QPlan.twoPass (QPlan.horner stage (fun t i => (winPoly u v (shiftAt i)).coeff t) (v - u))
    (tmpl L b m R u v hv).gather (tmpl L b m R u v hv).scatter
    (conv.seq (((tmpl L b m R u v hv).tablePlan (test (m + 1) (S.geometry.D - 1)) q
      (divTmpl L b m R u v hv) sgnZ).seq conv))

/-- **The batch with structured checks multiplies every frequency by the product of signs.** -/
theorem frequency_batch2 (L b m : ℕ) (S : System L b) (R u v : ℕ) (hv : u + v = m + 1)
    {q : ℚ[X]}
    (hq1 : ∀ f : Fn (m + 1), aeval (checkOp u) q (checkOp u f) = restrictE u f)
    (hq2 : ∀ f : Fn (m + 1), checkOp u (aeval (checkOp u) q f) = restrictE u f)
    (stage : QPlan (Charged.Axes (m := m) S.geometry) (rows L b m R) (rows L b m R))
    (hstage : ∀ {h : ℕ} (x : Bank (Charged.Axes (m := m) S.geometry) h (rows L b m R)) j y,
      frequency (stage.applyAt h x) j y
        = (mismatch (∑ t, test (m + 1) (S.geometry.D - 1) (y t)) (shiftAt j) : ℚ) * frequency x j y)
    (conv : QPlan (Charged.Axes (m := m) S.geometry) (checks L b m R u v + checks L b m R u v)
      (checks L b m R u v + checks L b m R u v)) (hconv : QPlan.Correct conv) {h : ℕ}
    (x : Bank (Charged.Axes (m := m) S.geometry) h (rows L b m R)) (i : Fin (rows L b m R))
    (y : Addr (Charged.Axes (m := m) S.geometry) h) :
    frequency ((batch2 L b m S R u v hv q stage conv).applyAt h x) i y
      = sgnZ (∑ t, test (m + 1) (S.geometry.D - 1) (y t)) * frequency x i y := by
  have happ : (batch2 L b m S R u v hv q stage conv).applyAt h x
      = (QPlan.twoPass (QPlan.horner stage (fun t i => (winPoly u v (shiftAt i)).coeff t) (v - u))
          (QPlan.mix fun r i => (tmpl L b m R u v hv).charMatrix r i)
          (QPlan.mix fun i r => (tmpl L b m R u v hv).charMatrix r i)
          (conv.seq (((tmpl L b m R u v hv).tablePlan (test (m + 1) (S.geometry.D - 1)) q
            (divTmpl L b m R u v hv) sgnZ).seq conv))).applyAt h x := by
    rw [batch2, applyAt_twoPass, applyAt_twoPass]
    simp only [(tmpl L b m R u v hv).gather_applyAt, (tmpl L b m R u v hv).scatter_applyAt]
  rw [happ]
  refine QPlan.frequency_batchWith stage (test (m + 1) (S.geometry.D - 1))
    (fun i κ => (mismatch κ (shiftAt i) : ℚ)) (fun x j y => hstage x j y)
    (fun t i => (winPoly u v (shiftAt i)).coeff t) (v - u) sgnZ (tmpl L b m R u v hv).charMatrix
    (fun κ => (tmpl L b m R u v hv).blockAct fun k =>
      decodeL u q (supK κ) (divTmpl L b m R u v hv k κ))
    (fun κ => ?_) _
    (fun w r y => (tmpl L b m R u v hv).frequency_tbl _ q _ sgnZ conv hconv w r y) x i y
  exact (tmpl L b m R u v hv).isTable_struct hq1 hq2 (fun i => predMult L b m R u v i κ)
    (sgnZ κ) (supK κ) (fun i hi => wrong_tail L b m R u v hv i κ hi)

theorem calls_batch2 (L b m : ℕ) (S : System L b) (R u v : ℕ) (hv : u + v = m + 1) (q : ℚ[X])
    (stage : QPlan (Charged.Axes (m := m) S.geometry) (rows L b m R) (rows L b m R))
    (conv : QPlan (Charged.Axes (m := m) S.geometry) (checks L b m R u v + checks L b m R u v)
      (checks L b m R u v + checks L b m R u v)) :
    (batch2 L b m S R u v hv q stage conv).calls = 2 * (v - u) * stage.calls + 2 * conv.calls := by
  rw [batch2, calls_twoPass, calls_horner]
  simp only [Blocks.calls_gather, Blocks.calls_scatter]
  rw [QPlan.calls_seq, QPlan.calls_seq, Blocks.calls_tablePlan]
  ring


/-! ## The feedback family with structured checks -/

/-- **The feedback family with structured checks**, for a family of stages `stg`. Level `j`
works on `20^j` copies, and its conversions are done by level `j − 1`. -/
noncomputable def fbPlan2 (L b m u v : ℕ) (S : System L b) (hv : u + v = m + 1) (q : ℚ[X])
    (stg : (R : ℕ) → QPlan (Charged.Axes (m := m) S.geometry) (rows L b m R) (rows L b m R)) :
    (j : ℕ) → QPlan (Charged.Axes (m := m) S.geometry) (rows L b m (20 ^ j)) (rows L b m (20 ^ j))
  | 0 => QPlan.embed (convertBank _ _)
  | j + 1 => QPlan.wrap (QPlan.outerFront (m + 1) (S.geometry.D - 1))
      (QPlan.outerBack (m + 1) (S.geometry.D - 1))
      (batch2 L b m S (20 ^ (j + 1)) u v hv q (stg (20 ^ (j + 1)))
        (QPlan.restrictOr _ (fbPlan2 L b m u v S hv q stg j)))

/-- **Every level of the structured feedback family is correct.** -/
theorem correct_fbPlan2 (L b m u v : ℕ) (S : System L b) (hv : u + v = m + 1)
    (hodd : m + 1 ≡ 1 [MOD 2]) {q : ℚ[X]}
    (hq1 : ∀ f : Fn (m + 1), aeval (checkOp u) q (checkOp u f) = restrictE u f)
    (hq2 : ∀ f : Fn (m + 1), checkOp u (aeval (checkOp u) q f) = restrictE u f)
    (stg : (R : ℕ) → QPlan (Charged.Axes (m := m) S.geometry) (rows L b m R) (rows L b m R))
    (hstg : ∀ R {h : ℕ} (x : Bank (Charged.Axes (m := m) S.geometry) h (rows L b m R)) j y,
      frequency ((stg R).applyAt h x) j y
        = (mismatch (∑ t, test (m + 1) (S.geometry.D - 1) (y t)) (shiftAt j) : ℚ) * frequency x j y)
    (j : ℕ) : QPlan.Correct (fbPlan2 L b m u v S hv q stg j) := by
  induction j with
  | zero => exact QPlan.correct_convertBank _
  | succ j ih =>
    rw [fbPlan2]
    apply QPlan.correct_wrapOuter (m := m + 1) (u := S.geometry.D - 1) hodd
    intro h x i y
    exact frequency_batch2 L b m S _ u v hv hq1 hq2 _ (fun x j y => hstg _ x j y) _
      (QPlan.correct_restrictOr _ _ ih) x i y

theorem calls_fbPlan2_succ (L b m u v : ℕ) (S : System L b) (hv : u + v = m + 1) (q : ℚ[X])
    (stg : (R : ℕ) → QPlan (Charged.Axes (m := m) S.geometry) (rows L b m R) (rows L b m R))
    (j : ℕ)
    (hle : checks L b m (20 ^ (j + 1)) u v + checks L b m (20 ^ (j + 1)) u v ≤ rows L b m (20 ^ j)) :
    (fbPlan2 L b m u v S hv q stg (j + 1)).calls
      = 2 * (v - u) * (stg (20 ^ (j + 1))).calls + 2 * (fbPlan2 L b m u v S hv q stg j).calls := by
  rw [fbPlan2, QPlan.calls_wrap _ _ _ (QPlan.calls_outerFront _ _) (QPlan.calls_outerBack _ _),
    calls_batch2, QPlan.calls_restrictOr hle]

/-- **Calls of the structured feedback family**: the same bound as `calls_fbPlan_le`. -/
theorem calls_fbPlan2_le (L b m u v : ℕ) (S : System L b) (hv : u + v = m + 1) (q : ℚ[X])
    (stg : (R : ℕ) → QPlan (Charged.Axes (m := m) S.geometry) (rows L b m R) (rows L b m R))
    (K : ℕ) (hK : ∀ R, (stg R).calls ≤ K * rows L b m R)
    (hE : 40 * (outside u v (0 : Fin (m + 1) → ZMod 2)).card ≤ 2 ^ (m + 1)) (j : ℕ) :
    9 * (fbPlan2 L b m u v S hv q stg j).calls
      ≤ 20 * (v - u) * K * rows L b m (20 ^ j)
        + 9 * 2 ^ j * Charged.Axes (m := m) S.geometry * rows L b m 1 := by
  induction j with
  | zero =>
    have h0 : (fbPlan2 L b m u v S hv q stg 0).calls
        = rows L b m (20 ^ 0) * Charged.Axes (m := m) S.geometry := by
      rw [fbPlan2, QPlan.calls_embed, calls_convertBank]
    rw [h0, pow_zero, pow_zero]
    nlinarith [Nat.zero_le (20 * (v - u) * K * rows L b m 1)]
  | succ j ih =>
    rw [calls_fbPlan2_succ L b m u v S hv q stg j (syndrome_fits L b m j u v hE)]
    have hst := hK (20 ^ (j + 1))
    have hrw := rows_twenty L b m j
    have hst' : 2 * (v - u) * (stg (20 ^ (j + 1))).calls
        ≤ 2 * (v - u) * (K * rows L b m (20 ^ (j + 1))) := Nat.mul_le_mul_left _ hst
    calc 9 * (2 * (v - u) * (stg (20 ^ (j + 1))).calls
            + 2 * (fbPlan2 L b m u v S hv q stg j).calls)
        = 9 * (2 * (v - u) * (stg (20 ^ (j + 1))).calls)
            + 2 * (9 * (fbPlan2 L b m u v S hv q stg j).calls) := by ring
      _ ≤ 9 * (2 * (v - u) * (K * rows L b m (20 ^ (j + 1))))
          + 2 * (20 * (v - u) * K * rows L b m (20 ^ j)
            + 9 * 2 ^ j * Charged.Axes (m := m) S.geometry * rows L b m 1) := by
          gcongr
      _ = 20 * (v - u) * K * rows L b m (20 ^ (j + 1))
          + 9 * 2 ^ (j + 1) * Charged.Axes (m := m) S.geometry * rows L b m 1 := by
          rw [hrw]; ring

/-- The routed pencil stage has the frequency action required of a stage family. -/
theorem frequency_ourStage' (L b m R : ℕ) (S : System L b) {h : ℕ}
    (x : Bank (Charged.Axes (m := m) S.geometry) h (rows L b m R)) (j : Fin (rows L b m R))
    (y : Addr (Charged.Axes (m := m) S.geometry) h) :
    frequency ((ourStage L b m R S).applyAt h x) j y
      = (mismatch (∑ t, test (m + 1) (S.geometry.D - 1) (y t)) (shiftAt j) : ℚ) * frequency x j y :=
  frequency_ourStage L b m R S x j y


end FTPaper.Claim2
