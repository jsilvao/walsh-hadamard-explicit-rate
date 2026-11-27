import FTPaper.Claim2.Stage
import FTPaper.LocalCostQ

/-!
# Sparse local cost of the structured feedback family

* the structured checks cost `M` gates per row and the table `2 deg(q) (M + 1) + 1` per row;
* `qsparse_batch2_le`: one repaired batch;
* `qsparse_fbPlan2_le`: the whole feedback family costs at most `(10/9) K'` gates per row and
  address, with `K' = 2 n (P + 1) + 4M + 2 d (M + 1) + 3`, where `n = v - u`, `P` is the pencil
  cost per row, `M = m + 1` and `d = deg q`.
-/

set_option linter.unusedSectionVars false

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open OAI.Computability.NearSquareRoot.KernelPass.Plan (frequency convertBank)
open OAI.Computability.NearSquareRoot.KernelPass.Rect
open OAI.Computability.NearSquareRoot.KernelPass.Rect.Binary
open scoped OAI.Computability.NearSquareRoot.CyclotomicCode
open OAI.Computability.NearSquareRoot.BinaryQuery
open Matrix Finset Polynomial
open FTPaper.Circ FTPaper.QPlan FTPaper.LemmaS

namespace FTPaper.Claim2

/-! ## OpenAI's plan combinators -/

lemma planSparse_collect {A i : ℕ} : ∀ (n : ℕ) (p : Fin n → Plan A i 1),
    planSparse (Plan.collect n p) = ∑ j, planSparse (p j)
  | 0, p => by simp [Plan.collect, planSparse, rowCost]
  | n + 1, p => by
    rw [Plan.collect, planSparse_fork, planSparse_collect n, Fin.sum_univ_castSucc]

lemma planSparse_perRow {A n : ℕ} (p : Fin n → Plan A 1 1) :
    planSparse (Plan.perRow p) = ∑ j, planSparse (p j) := by
  rw [Plan.perRow, planSparse_collect]
  simp

lemma planSparse_convertBank (A n : ℕ) : planSparse (convertBank A n) = 0 := by
  rw [convertBank, planSparse_perRow]
  simp [planSparse_eq_zero (planFree_fullConversion _)]

lemma qsparse_wrap {A n : ℕ} (front back : Plan A 1 1) (p : QPlan A n n)
    (hf : planFree front = 0) (hb : planFree back = 0) :
    qsparse (QPlan.wrap front back p) = qsparse p := by
  simp [QPlan.wrap, planSparse_perRow, planSparse_eq_zero hf, planSparse_eq_zero hb]

lemma qsparse_restrictOr {A W : ℕ} (W' : ℕ) (p : QPlan A W W) :
    qsparse (QPlan.restrictOr W' p) ≤ qsparse p := by
  unfold QPlan.restrictOr
  split
  · rename_i hle
    have hpad : rowCost (fun (b : Fin W) (a : Fin W') => if b = Fin.castLE hle a then (1 : ℚ) else 0)
        = 0 := by
      have := QPlan.rowCost_le_of (k := 0) (c := fun (b : Fin W) (a : Fin W') =>
          if b = Fin.castLE hle a then (1 : ℚ) else 0) (fun b => by
        calc (univ.filter fun a : Fin W' => (if b = Fin.castLE hle a then (1 : ℚ) else 0) ≠ 0).card
            ≤ 1 := by
              rw [Finset.card_le_one]
              intro a ha a' ha'
              simp only [mem_filter, mem_univ, true_and, ne_eq, ite_eq_right_iff, one_ne_zero,
                imp_false, not_not] at ha ha'
              exact Fin.castLE_injective hle (ha.symm.trans ha')
          _ = 0 + 1 := rfl)
      omega
    simp [QPlan.restrict, QPlan.padRows, qsparse_mix, hpad]
  · simp [planSparse_convertBank]

lemma qsparse_twoPass_le {A W s : ℕ} (p : QPlan A W W) (gather : QPlan A W s)
    (scatter : QPlan A s W) (table : QPlan A (s + s) (s + s)) :
    qsparse (QPlan.twoPass p gather scatter table)
      ≤ 2 * qsparse p + 2 * qsparse gather + 2 * qsparse scatter + qsparse table + 2 * W := by
  have h1 := qsparse_combine_le (A := A) (fun _ : Fin W => (-1 : ℚ)) (fun _ => 1)
  have h2 := qsparse_combine_le (A := A) (fun _ : Fin W => (1 : ℚ)) (fun _ => 1)
  simp only [QPlan.twoPass, qsparse_seq, qsparse_fork, qsparse_parallel, qsparse_route]
  omega

/-! ## The structured plans -/

namespace Blocks

variable {B : Type} [Fintype B] [DecidableEq B] {M u N s : ℕ} (bk : Blocks B M u N s) {A : ℕ}

lemma qsparse_layer (j : Fin M) : qsparse (QPlan.mix (A := A) (bk.layerCoef j)) ≤ N := by
  rw [qsparse_mix]
  have := QPlan.rowCost_le_of (k := 1) (c := bk.layerCoef j) (fun b => by
    calc (univ.filter fun a => bk.layerCoef j b a ≠ 0).card
        ≤ ({bk.e.symm ((bk.e b).1, (bk.e b).2), bk.e.symm ((bk.e b).1, symmDiff (bk.e b).2 {j})} :
            Finset (Fin N)).card := card_le_card fun a ha => by
          simp only [mem_filter, mem_univ, true_and] at ha
          simp only [mem_insert, mem_singleton]
          unfold layerCoef at ha
          by_cases h1 : (bk.e a).1 = (bk.e b).1
          · by_cases h2 : (bk.e a).2 = (bk.e b).2
            · left
              rw [← h1, ← h2, Prod.mk.eta, Equiv.symm_apply_apply]
            · by_cases h3 : (bk.e a).2 = symmDiff (bk.e b).2 {j}
              · right
                rw [← h1, ← h3, Prod.mk.eta, Equiv.symm_apply_apply]
              · simp [h1, h2, h3] at ha
          · simp [h1] at ha
      _ ≤ 1 + 1 := card_le_two)
  simpa using this

lemma qsparse_whtPlan (js : List (Fin M)) : qsparse (bk.whtPlan (A := A) js) ≤ js.length * N := by
  induction js with
  | nil => simp [whtPlan]
  | cons j js ih =>
    have := bk.qsparse_layer (A := A) j
    simp only [whtPlan, qsparse_seq, List.length_cons]
    rw [Nat.succ_mul]
    omega

lemma qsparse_extendPlan : qsparse (bk.extendPlan (A := A)) = 0 := by
  rw [extendPlan, qsparse_mix]
  have := QPlan.rowCost_le_of (k := 0) (c := bk.extCoef) (fun b => by
    calc (univ.filter fun r => bk.extCoef b r ≠ 0).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro r hr r' hr'
          simp only [mem_filter, mem_univ, true_and, extCoef, ne_eq, ite_eq_right_iff,
            one_ne_zero, imp_false, not_not] at hr hr'
          apply bk.c.injective
          exact Prod.ext (hr.1.trans hr'.1.symm) (Subtype.ext (hr.2.trans hr'.2.symm))
      _ = 0 + 1 := rfl)
  omega

lemma qsparse_gather : qsparse (bk.gather (A := A)) ≤ M * N := by
  have := bk.qsparse_whtPlan (A := A) (List.finRange M)
  simp only [gather, restrictPlan, qsparse_seq, qsparse_route, zero_add, List.length_finRange]
    at this ⊢
  exact this

lemma qsparse_scatter : qsparse (bk.scatter (A := A)) ≤ M * N := by
  have := bk.qsparse_whtPlan (A := A) (List.finRange M)
  simp only [scatter, qsparse_seq, bk.qsparse_extendPlan, add_zero, List.length_finRange] at this ⊢
  exact this

lemma qsparse_mPlan : qsparse (bk.mPlan (A := A)) ≤ M * N := by
  have := bk.qsparse_whtPlan (A := A) (List.finRange M)
  simp only [mPlan, restrictPlan, qsparse_seq, qsparse_route, bk.qsparse_extendPlan, zero_add,
    add_zero, List.length_finRange] at this ⊢
  exact this

lemma qsparse_qPlan (q : ℚ[X]) : qsparse (bk.qPlan (A := A) q) ≤ q.natDegree * (M * N + s) := by
  have h1 := qsparse_horner_le (bk.mPlan (A := A)) (fun t _ => q.coeff t) q.natDegree
  have h2 := bk.qsparse_mPlan (A := A)
  calc qsparse (bk.qPlan (A := A) q) ≤ q.natDegree * (qsparse (bk.mPlan (A := A)) + s) := h1
    _ ≤ q.natDegree * (M * N + s) := Nat.mul_le_mul_left _ (by omega)

lemma qsparse_tablePlan (test : Column A → Fin M → ZMod 2) (q : ℚ[X])
    (Λ : B → (Fin M → ZMod 2) → Fn M) (z : (Fin M → ZMod 2) → ℚ) :
    qsparse (bk.tablePlan test q Λ z) ≤ 2 * (q.natDegree * (M * N + s)) + s := by
  have h1 := bk.qsparse_qPlan (A := A) q
  have h2 := qsparse_combine_le (A := A) (fun _ : Fin s => (1 : ℚ)) (fun _ => -1)
  simp only [tablePlan, tPlan, twistPlan, scalePlan, diffPlan, qsparse_seq, qsparse_fork,
    qsparse_route, qsparse_scaleRows]
  omega

end Blocks

/-! ## One repaired batch and the feedback family -/

lemma batch_arith {N s n M d c st pH pG pS pT : ℕ} (hs : s ≤ N) (h2 : pH ≤ n * (st + N))
    (h3 : pG ≤ M * N) (h4 : pS ≤ M * N) (h5 : pT ≤ 2 * (d * (M * N + s)) + s) :
    2 * pH + 2 * pG + 2 * pS + (c + (pT + c)) + 2 * N
      ≤ 2 * c + 2 * n * st + N * (2 * n + 4 * M + 2 * d * (M + 1) + 3) := by
  have hds : d * s ≤ d * N := Nat.mul_le_mul_left _ hs
  nlinarith

theorem qsparse_batch2_le (L b m : ℕ) (S : System L b) (R u v : ℕ) (hv : u + v = m + 1)
    (q : ℚ[X]) (stage : QPlan (Charged.Axes (m := m) S.geometry) (rows L b m R) (rows L b m R))
    (conv : QPlan (Charged.Axes (m := m) S.geometry) (checks L b m R u v + checks L b m R u v)
      (checks L b m R u v + checks L b m R u v)) :
    qsparse (batch2 L b m S R u v hv q stage conv)
      ≤ 2 * qsparse conv + 2 * (v - u) * qsparse stage
        + rows L b m R * (2 * (v - u) + 4 * (m + 1) + 2 * q.natDegree * (m + 1 + 1) + 3) := by
  have hs := Circ.checks_le_rows L b m R u v
  have h1 := qsparse_twoPass_le
    (QPlan.horner stage (fun t i => (winPoly u v (shiftAt i)).coeff t) (v - u))
    (tmpl L b m R u v hv).gather (tmpl L b m R u v hv).scatter
    (conv.seq (((tmpl L b m R u v hv).tablePlan (test (m + 1) (S.geometry.D - 1)) q
      (divTmpl L b m R u v hv) sgnZ).seq conv))
  have h2 := qsparse_horner_le stage (fun t i => (winPoly u v (shiftAt i)).coeff t) (v - u)
  have h3 := (tmpl L b m R u v hv).qsparse_gather (A := Charged.Axes (m := m) S.geometry)
  have h4 := (tmpl L b m R u v hv).qsparse_scatter (A := Charged.Axes (m := m) S.geometry)
  have h5 := (tmpl L b m R u v hv).qsparse_tablePlan (test (m + 1) (S.geometry.D - 1)) q
    (divTmpl L b m R u v hv) sgnZ
  have hseq : qsparse (conv.seq (((tmpl L b m R u v hv).tablePlan (test (m + 1) (S.geometry.D - 1)) q
      (divTmpl L b m R u v hv) sgnZ).seq conv))
      = qsparse conv + (qsparse ((tmpl L b m R u v hv).tablePlan (test (m + 1) (S.geometry.D - 1)) q
          (divTmpl L b m R u v hv) sgnZ) + qsparse conv) := rfl
  rw [hseq] at h1
  exact h1.trans (batch_arith hs h2 h3 h4 h5)

/-- The structured feedback family with the row-diagonal stage. -/
noncomputable def fbPlanS (L b m u v : ℕ) (S : System L b) (hv : u + v = m + 1) (q : ℚ[X]) :=
  fbPlan2 L b m u v S hv q (fun R => ourStageS L b m R S)

/-- The repair cost per row and address, outside the pencil. -/
def repairPerRow (L b m u v d : ℕ) : ℕ :=
  2 * (v - u) * (pencilPerRow L b m + 1) + 4 * (m + 1) + 2 * d * (m + 1 + 1) + 3

/-- **Sparse local cost of the structured feedback family**: at most `(10/9) K'` gates per row
and address, `K' = repairPerRow`. -/
theorem qsparse_fbPlanS_le (L b m u v : ℕ) (S : System L b) (hv : u + v = m + 1) (q : ℚ[X])
    (j : ℕ) :
    9 * qsparse (fbPlanS L b m u v S hv q j)
      ≤ 10 * repairPerRow L b m u v q.natDegree * rows L b m (20 ^ j) := by
  induction j with
  | zero => simp [fbPlanS, fbPlan2, planSparse_convertBank]
  | succ j ih =>
    have hb := qsparse_batch2_le L b m S (20 ^ (j + 1)) u v hv q (ourStageS L b m (20 ^ (j + 1)) S)
      (QPlan.restrictOr _ (fbPlan2 L b m u v S hv q (fun R => ourStageS L b m R S) j))
    have hr := qsparse_restrictOr (checks L b m (20 ^ (j + 1)) u v + checks L b m (20 ^ (j + 1)) u v)
      (fbPlan2 L b m u v S hv q (fun R => ourStageS L b m R S) j)
    have hst := qsparse_ourStageS L b m (20 ^ (j + 1)) S
    have hrw := rows_twenty L b m j
    have hwrap : qsparse (fbPlanS L b m u v S hv q (j + 1))
        = qsparse (batch2 L b m S (20 ^ (j + 1)) u v hv q (ourStageS L b m (20 ^ (j + 1)) S)
            (QPlan.restrictOr _ (fbPlan2 L b m u v S hv q (fun R => ourStageS L b m R S) j))) := by
      rw [fbPlanS, fbPlan2]
      exact qsparse_wrap _ _ _ (QPlan.free_outerFront _ _) (QPlan.free_outerBack _ _)
    rw [hwrap]
    have ih' : 9 * qsparse (fbPlan2 L b m u v S hv q (fun R => ourStageS L b m R S) j)
        ≤ 10 * repairPerRow L b m u v q.natDegree * rows L b m (20 ^ j) := ih
    set N := rows L b m (20 ^ (j + 1))
    set N0 := rows L b m (20 ^ j)
    set P := pencilPerRow L b m
    set d := q.natDegree
    have hst' : 2 * (v - u) * qsparse (ourStageS L b m (20 ^ (j + 1)) S) ≤ 2 * (v - u) * (N * P) :=
      Nat.mul_le_mul_left _ hst
    have hK : repairPerRow L b m u v d * N
        = 2 * (v - u) * (N * P) + N * (2 * (v - u) + 4 * (m + 1) + 2 * d * (m + 1 + 1) + 3) := by
      unfold repairPerRow; ring
    have h20 : 2 * (10 * repairPerRow L b m u v d * N0) = repairPerRow L b m u v d * N := by
      rw [hrw]; ring
    nlinarith

end FTPaper.Claim2
