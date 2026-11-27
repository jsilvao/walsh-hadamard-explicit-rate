import FTPaper.QCircuit
import FTPaper.LocalCostOAI

/-!
# Gates outside calls of our template

Exact or explicit counts of `qfree` (dense count, per address) for the rational-plan
combinators of the template (`route`, `fork`, `combine`, the Horner predictor, the two-pass
repair, the spectral table, restriction, outer passes), and a recursive bound for the feedback
family `fbPlan`.
-/

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open OAI.Computability.NearSquareRoot.KernelPass.Plan (convertBank perRow)
open OAI.Computability.NearSquareRoot.KernelPass.Rect (renumber)
open OAI.Computability.NearSquareRoot.KernelPass.Rect.Binary
open OAI.Computability.NearSquareRoot.BinaryQuery (test)
open scoped OAI.Computability.NearSquareRoot.CyclotomicCode
open Finset

namespace FTPaper

namespace Circ

open QPlan

variable {A : ℕ}

@[simp] theorem qfree_seq {i j o : ℕ} (p : QPlan A j o) (q : QPlan A i j) :
    qfree (p.seq q) = qfree p + qfree q := rfl

@[simp] theorem qfree_parallel {i j o u : ℕ} (p : QPlan A i o) (q : QPlan A j u) :
    qfree (p.parallel q) = qfree p + qfree q := rfl

@[simp] theorem qfree_embed {i o : ℕ} (p : Plan A i o) : qfree (QPlan.embed p) = planFree p := rfl

@[simp] theorem qfree_mix {i o : ℕ} (c : Fin o → Fin i → ℚ) : qfree (QPlan.mix (A := A) c) = o * i :=
  rfl

@[simp] theorem qfree_scaleRows {n q : ℕ} (test : Column A → Fin q → ZMod 2)
    (t : Fin n → (Fin q → ZMod 2) → ℚ) : qfree (QPlan.scaleRows (A := A) q test t) = 0 := rfl

@[simp] theorem qfree_route {i o : ℕ} (r : Fin o → Fin i) : qfree (QPlan.route (A := A) r) = o * i :=
  rfl

@[simp] theorem qfree_fork {i o u : ℕ} (p : QPlan A i o) (q : QPlan A i u) :
    qfree (p.fork q) = qfree p + qfree q + (i + i) * i := by
  simp only [QPlan.fork, qfree_seq, qfree_parallel, qfree_route]

@[simp] theorem qfree_combine {W : ℕ} (u v : Fin W → ℚ) :
    qfree (combine (A := A) u v) = W * (W + W) := rfl

theorem qfree_hornerPair {N : ℕ} (stage : QPlan A N N) :
    ∀ (c : ℕ → Fin N → ℚ) (n : ℕ),
      qfree (hornerPair stage c n) = n * (qfree stage + 13 * N * N) + 4 * N * N
  | c, 0 => by
    simp only [hornerPair, qfree_fork, diagMix, qfree_mix, qfree_route]
    ring
  | c, n + 1 => by
    rw [hornerPair, qfree_seq, qfree_hornerPair stage _ n]
    simp only [hornerStep, qfree_seq, qfree_fork, qfree_combine, qfree_route, qfree_parallel]
    ring

theorem qfree_horner {N : ℕ} (stage : QPlan A N N) (c : ℕ → Fin N → ℚ) (n : ℕ) :
    qfree (horner stage c n) = n * (qfree stage + 13 * N * N) + 6 * N * N := by
  rw [horner, qfree_seq, qfree_route, qfree_hornerPair]
  ring

theorem qfree_twoPass {W s : ℕ} (p : QPlan A W W) (gather : QPlan A W s) (scatter : QPlan A s W)
    (table : QPlan A (s + s) (s + s)) :
    qfree (twoPass p gather scatter table)
      = 2 * qfree p + 2 * qfree gather + 2 * qfree scatter + qfree table + 18 * W * W := by
  simp only [twoPass, qfree_seq, qfree_fork, qfree_combine, qfree_route, qfree_parallel]
  ring

theorem qfree_matrixTable {i o q : ℕ} (test : Column A → Fin q → ZMod 2)
    (c : (Fin q → ZMod 2) → Fin o → Fin i → ℚ) :
    qfree (matrixTable test c) = o * (o * i) + (o * i) * i := by
  simp only [matrixTable, qfree_seq, qfree_mix, qfree_scaleRows, qfree_route]
  ring

theorem qfree_spectralVia {n q : ℕ} (conv : QPlan A n n) (test : Column A → Fin q → ZMod 2)
    (c : (Fin q → ZMod 2) → Fin n → Fin n → ℚ) :
    qfree (spectralVia conv test c) = 2 * qfree conv + 2 * (n * n * n) := by
  rw [spectralVia, qfree_seq, qfree_seq, qfree_matrixTable]
  ring

theorem qfree_restrict {W' W : ℕ} (hle : W' ≤ W) (p : QPlan A W W) :
    qfree (QPlan.restrict hle p) = qfree p + 2 * (W' * W) := by
  simp only [QPlan.restrict, padRows, qfree_seq, qfree_route, qfree_mix]
  ring

theorem qfree_restrictOr {W W' : ℕ} (hle : W' ≤ W) (p : QPlan A W W) :
    qfree (QPlan.restrictOr W' p) = qfree p + 2 * (W' * W) := by
  simp only [QPlan.restrictOr, hle, dite_true, qfree_restrict]

theorem qfree_wrap {n : ℕ} (front back : Plan A 1 1) (p : QPlan A n n)
    (hf : planFree front = 0) (hb : planFree back = 0) :
    qfree (wrap front back p) ≤ qfree p + 2 * (n * n + 2 * n * n * n) := by
  have h1 := planFree_perRow_free (A := A) (n := n) (fun _ => back) (fun _ => hb)
  have h2 := planFree_perRow_free (A := A) (n := n) (fun _ => front) (fun _ => hf)
  simp only [wrap, qfree_seq, qfree_embed]
  omega

theorem qfree_renumber {I : Type} [Fintype I] {n : ℕ} (e : I ≃ Fin n) (p : Rect.On A I I) :
    planFree (renumber e p) ≤ planFree p + 2 * (n * Fintype.card I) := by
  have h1 := planFree_route (A := A) ((Fintype.equivFin I) ∘ e.symm)
  have h2 := planFree_route (A := A) (e ∘ (Fintype.equivFin I).symm)
  simp only [renumber, planFree_seq]
  nlinarith


/-! ## The template -/

/-- The pencil coefficient `20 (|free| + |charged| + 1)(m + 2)`. -/
def pencilCoef (L b m : ℕ) : ℕ := 20 * (Fintype.card (Free L b) + Fintype.card (Paid L b) + 1) * (m + 2)

theorem qfree_ourStage (L b m R : ℕ) (S : System L b) :
    qfree (ourStage L b m R S) ≤ pencilCoef L b m * rows L b m R ^ 3 + 2 * rows L b m R ^ 2 := by
  have h1 := qfree_renumber (A := Charged.Axes (m := m) S.geometry) (rowEquiv L b m R)
    (ourPencil L b m R S)
  have h2 := planFree_geometricPencilF S m (stageB₀ m)
    (stageB m (fun k : Fin R × (Fin (m + 1) → ZMod 2) => k.2))
  simp only [ourStage, qfree_embed]
  unfold pencilCoef
  change planFree (renumber (rowEquiv L b m R) (ourPencil L b m R S)) ≤ _
  have : planFree (ourPencil L b m R S) ≤ 20 * (Fintype.card (Free L b) + Fintype.card (Paid L b) + 1)
      * (m + 2) * rows L b m R ^ 3 := h2
  have h1' : planFree (renumber (rowEquiv L b m R) (ourPencil L b m R S))
      ≤ planFree (ourPencil L b m R S) + 2 * (rows L b m R * rows L b m R) := h1
  nlinarith

theorem qfree_batchVia (L b m R u v : ℕ) (S : System L b)
    (conv : QPlan (Charged.Axes (m := m) S.geometry) (checks L b m R u v + checks L b m R u v)
      (checks L b m R u v + checks L b m R u v)) :
    qfree (batchVia L b m R u v S conv)
      = 2 * ((v - u) * (qfree (ourStage L b m R S) + 13 * rows L b m R * rows L b m R)
          + 6 * rows L b m R * rows L b m R)
        + 2 * (checks L b m R u v * rows L b m R) + 2 * (rows L b m R * checks L b m R u v)
        + (2 * qfree conv + 2 * ((checks L b m R u v + checks L b m R u v) *
            (checks L b m R u v + checks L b m R u v) * (checks L b m R u v + checks L b m R u v)))
        + 18 * rows L b m R * rows L b m R := by
  have h := qfree_twoPass (A := Charged.Axes (m := m) S.geometry)
    (QPlan.horner (ourStage L b m R S) (fun t i => (winPoly u v (shiftAt i)).coeff t) (v - u))
    (QPlan.mix fun r i => checkMatrix L b m R u v r i) (QPlan.mix fun i r => checkMatrix L b m R u v r i)
    (QPlan.spectralVia conv (test (m + 1) (S.D - 1))
      fun κ => QPlan.tabMatrix (table L b m R u v κ) (sgnZ κ))
  have h2 : qfree (QPlan.spectralVia conv (test (m + 1) (S.D - 1))
      fun κ => QPlan.tabMatrix (table L b m R u v κ) (sgnZ κ))
      = 2 * qfree conv + 2 * ((checks L b m R u v + checks L b m R u v) *
        (checks L b m R u v + checks L b m R u v) * (checks L b m R u v + checks L b m R u v)) :=
    qfree_spectralVia _ _ _
  rw [qfree_horner, qfree_mix, qfree_mix, h2] at h
  exact h

/-- Checks are at most the rows. -/
lemma checks_le_rows (L b m R u v : ℕ) : checks L b m R u v ≤ rows L b m R := by
  rw [rows_eq]
  simp only [checks]
  have hE : (outside u v (0 : Fin (m + 1) → ZMod 2)).card ≤ 2 ^ (m + 1) := by
    calc (outside u v (0 : Fin (m + 1) → ZMod 2)).card ≤ (Finset.univ : Finset (Fin (m + 1) → ZMod 2)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = 2 ^ (m + 1) := by simp
  calc Fintype.card (Label L b) * R * (outside u v (0 : Fin (m + 1) → ZMod 2)).card
      ≤ Fintype.card (Label L b) * R * 2 ^ (m + 1) := Nat.mul_le_mul_left _ hE
    _ = _ := by ring

/-- The constant of the feedback family. -/
def fbConst (L b m u v : ℕ) : ℕ := 2 * (v - u) * pencilCoef L b m + 30 * (v - u) + 64

/-- The arithmetic of one feedback level. -/
lemma fb_arith {xw xb xst xc xp N Nj s n Pc : ℕ}
    (hw : xw ≤ xb + 2 * (N * N + 2 * N * N * N))
    (hb : xb = 2 * (n * (xst + 13 * N * N) + 6 * N * N) + 2 * (s * N) + 2 * (N * s)
      + (2 * xc + 2 * ((s + s) * (s + s) * (s + s))) + 18 * N * N)
    (hc : xc = xp + 2 * ((s + s) * Nj))
    (hst : xst ≤ Pc * N ^ 3 + 2 * N ^ 2)
    (hp : xp ≤ (2 * (2 * n * Pc + 30 * n + 64) + 3) * Nj ^ 3)
    (hfit : s + s ≤ Nj) (hN : N = 20 * Nj) :
    xw ≤ (2 * (2 * n * Pc + 30 * n + 64) + 3) * N ^ 3 := by
  subst hN
  have hNj2 : Nj ^ 2 ≤ Nj ^ 3 := by
    rcases Nat.eq_zero_or_pos Nj with h0 | hpos
    · subst h0; simp
    · exact Nat.pow_le_pow_right hpos (by norm_num)
  have hs : s ≤ Nj := by omega
  have hsNj : s * Nj ≤ Nj ^ 3 := by nlinarith
  have hs3 : (s + s) * (s + s) * (s + s) ≤ Nj ^ 3 := by
    calc (s + s) * (s + s) * (s + s) ≤ Nj * Nj * Nj := by gcongr
      _ = Nj ^ 3 := by ring
  have hssNj : (s + s) * Nj ≤ Nj ^ 3 := by nlinarith
  have hst' : n * (xst + 13 * (20 * Nj) * (20 * Nj)) ≤ n * (8000 * Pc * Nj ^ 3 + 6000 * Nj ^ 3) := by
    apply Nat.mul_le_mul_left
    have : (20 * Nj) ^ 3 = 8000 * Nj ^ 3 := by ring
    have : (20 * Nj) ^ 2 = 400 * Nj ^ 2 := by ring
    nlinarith
  have hrest : 2 * (6 * (20 * Nj) * (20 * Nj)) + 2 * (s * (20 * Nj)) + 2 * ((20 * Nj) * s)
      + 2 * ((s + s) * (s + s) * (s + s)) + 18 * (20 * Nj) * (20 * Nj)
      + 2 * ((20 * Nj) * (20 * Nj) + 2 * (20 * Nj) * (20 * Nj) * (20 * Nj)) + 4 * ((s + s) * Nj)
      ≤ 50000 * Nj ^ 3 := by nlinarith
  have hpow : (20 * Nj) ^ 3 = 8000 * Nj ^ 3 := by ring
  rw [hpow]
  have hn1 : n * (8000 * Pc * Nj ^ 3 + 6000 * Nj ^ 3) = 8000 * (n * Pc * Nj ^ 3) + 6000 * (n * Nj ^ 3) := by
    ring
  have hp' : xp ≤ 4 * (n * Pc * Nj ^ 3) + 60 * (n * Nj ^ 3) + 131 * Nj ^ 3 := by
    have : (2 * (2 * n * Pc + 30 * n + 64) + 3) * Nj ^ 3
        = 4 * (n * Pc * Nj ^ 3) + 60 * (n * Nj ^ 3) + 131 * Nj ^ 3 := by ring
    omega
  have hgoal : (2 * (2 * n * Pc + 30 * n + 64) + 3) * (8000 * Nj ^ 3)
      = 32000 * (n * Pc * Nj ^ 3) + 480000 * (n * Nj ^ 3) + 1048000 * Nj ^ 3 := by ring
  rw [hgoal]
  omega

/-- **Gates outside calls of the feedback family**: at most `(2K + 3) N_d³`, where
`K = 2 (v − u) · pencilCoef + 30 (v − u) + 64` and `N_d = rows L b m (20^d)`. -/
theorem qfree_fbPlan_le (L b m u v : ℕ) (S : System L b)
    (hE : 40 * (outside u v (0 : Fin (m + 1) → ZMod 2)).card ≤ 2 ^ (m + 1)) (d : ℕ) :
    qfree (fbPlan L b m u v S d) ≤ (2 * fbConst L b m u v + 3) * rows L b m (20 ^ d) ^ 3 := by
  induction d with
  | zero =>
    have h := planFree_convertBank (Charged.Axes (m := m) S.geometry) (rows L b m (20 ^ 0))
    simp only [fbPlan, qfree_embed]
    have hN : rows L b m (20 ^ 0) ^ 2 ≤ rows L b m (20 ^ 0) ^ 3 := by
      rcases Nat.eq_zero_or_pos (rows L b m (20 ^ 0)) with h0 | hpos
      · rw [h0]; simp
      · exact Nat.pow_le_pow_right hpos (by norm_num)
    have : rows L b m (20 ^ 0) * rows L b m (20 ^ 0) = rows L b m (20 ^ 0) ^ 2 := by ring
    have h3 : 2 * rows L b m (20 ^ 0) * rows L b m (20 ^ 0) * rows L b m (20 ^ 0)
        = 2 * rows L b m (20 ^ 0) ^ 3 := by ring
    nlinarith
  | succ j ih =>
    have hfit := syndrome_fits L b m j u v hE
    have hw := qfree_wrap (A := Charged.Axes (m := m) S.geometry)
      (QPlan.outerFront (m + 1) (S.geometry.D - 1)) (QPlan.outerBack (m + 1) (S.geometry.D - 1))
      (batchVia L b m (20 ^ (j + 1)) u v S (QPlan.restrictOr _ (fbPlan L b m u v S j)))
      (QPlan.free_outerFront _ _) (QPlan.free_outerBack _ _)
    have hbv := qfree_batchVia L b m (20 ^ (j + 1)) u v S
      (QPlan.restrictOr _ (fbPlan L b m u v S j))
    have hro := qfree_restrictOr (A := Charged.Axes (m := m) S.geometry) hfit (fbPlan L b m u v S j)
    have hst := qfree_ourStage L b m (20 ^ (j + 1)) S
    rw [fbPlan]
    exact fb_arith hw hbv hro hst ih hfit (rows_twenty L b m j)

end Circ

end FTPaper
