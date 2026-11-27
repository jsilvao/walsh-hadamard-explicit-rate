import FTPaper.QStage
import FTPaper.Predictor
import FTPaper.RoutingOAI

/-!
# Theorem 1 template, end to end (direct conversions)

One level of the binary template with our changes:
* the stage is OpenAI's routed pencil with our coefficients (`QStage`);
* the predictor is Horner evaluation of the window polynomial (`QHorner`, Lemma A);
* the repair uses two passes, Vandermonde checks, and a per-frequency table (`QTemplate`, Lemma B);
* OpenAI's outer passes are wrapped around the result (`QWrap`).

The plan computes the normalized Walsh–Hadamard transform on every row (`QPlan.Correct`).
Its child calls are `2·(v−u)·(pencil calls) + 4·s·A`. Here `s = |labels|·R·E`, and `E` counts the
shifts outside the window.
-/

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open OAI.Computability.NearSquareRoot.KernelPass.Plan (frequency walshMatrix)
open OAI.Computability.NearSquareRoot.KernelPass.Rect (renumber)
open OAI.Computability.NearSquareRoot.KernelPass.Rect.Binary (geometricPencil System Label card_label)
open scoped OAI.Computability.NearSquareRoot.CyclotomicCode
open OAI.Computability.NearSquareRoot.BinaryQuery
open Matrix Finset Polynomial

namespace FTPaper

/-! ## Signs of ZMod-2 signatures -/

/-- `∏_j (−1)^{γ_j}`. -/
def sgnZ {M : ℕ} (γ : Fin M → ZMod 2) : ℚ := ∏ j, (-1 : ℚ) ^ (γ j).val

lemma sign_mismatch {M : ℕ} (κ γ : Fin M → ZMod 2) :
    (-1 : ℚ) ^ mismatch κ γ * sgnZ γ = sgnZ κ := by
  have h1 : (-1 : ℚ) ^ mismatch κ γ = ∏ j, (if κ j ≠ γ j then (-1 : ℚ) else 1) := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, mismatch]
  rw [h1, sgnZ, sgnZ, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hz : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hz (κ j) with h | h <;> rcases hz (γ j) with h' | h' <;> simp [h, h', ZMod.val_one]

/-! ## The window predictor, one polynomial per shift -/

lemma exists_winPoly (u v : ℕ) {M : ℕ} (γ : Fin M → ZMod 2) :
    ∃ π : ℚ[X], π.natDegree ≤ v - u ∧
      ∀ c, u ≤ c → c ≤ v → π.eval (c : ℚ) = (-1 : ℚ) ^ c * sgnZ γ :=
  exists_window_poly u v (fun c => (-1 : ℚ) ^ c * sgnZ γ)

/-- The interpolation polynomial for shift `γ`. -/
noncomputable def winPoly (u v : ℕ) {M : ℕ} (γ : Fin M → ZMod 2) : ℚ[X] :=
  Classical.choose (exists_winPoly u v γ)

lemma winPoly_degree (u v : ℕ) {M : ℕ} (γ : Fin M → ZMod 2) : (winPoly u v γ).natDegree ≤ v - u :=
  (Classical.choose_spec (exists_winPoly u v γ)).1

/-- On the window the predictor gives the target sign. -/
lemma winPoly_window (u v : ℕ) {M : ℕ} (κ γ : Fin M → ZMod 2)
    (hu : u ≤ mismatch κ γ) (hv : mismatch κ γ ≤ v) :
    (winPoly u v γ).eval (mismatch κ γ : ℚ) = sgnZ κ := by
  have h := (Classical.choose_spec (exists_winPoly u v γ)).2 _ hu hv
  rw [show winPoly u v γ = Classical.choose (exists_winPoly u v γ) from rfl, h, sign_mismatch]

/-- Horner's finite sum equals evaluation, since the degree is at most `v − u`. -/
lemma horner_sum_eval (u v : ℕ) {M : ℕ} (γ : Fin M → ZMod 2) (c : ℚ) :
    ∑ t ∈ Finset.range (v - u + 1), (winPoly u v γ).coeff t * c ^ t = (winPoly u v γ).eval c := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (winPoly_degree u v γ))]

/-! ## Counting exceptional shifts -/

/-- Shifts whose distance to `κ` lies outside the window. -/
def outside (u v : ℕ) {M : ℕ} (κ : Fin M → ZMod 2) : Finset (Fin M → ZMod 2) :=
  univ.filter fun γ => ¬ (u ≤ mismatch κ γ ∧ mismatch κ γ ≤ v)

lemma card_outside (u v : ℕ) {M : ℕ} (κ : Fin M → ZMod 2) :
    (outside u v κ).card = (outside u v (0 : Fin M → ZMod 2)).card := by
  refine Finset.card_bij (fun γ _ => κ - γ) ?_ ?_ ?_
  · intro γ hγ
    simp only [outside, Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
    have : mismatch 0 (κ - γ) = mismatch κ γ := by
      unfold mismatch; congr 1; ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, Pi.zero_apply]
      rw [ne_comm, ne_eq, sub_eq_zero]
    rwa [this]
  · intro γ₁ _ γ₂ _ h
    have := congrArg (fun f => κ - f) h
    simpa using this
  · intro δ hδ
    refine ⟨κ - δ, ?_, by simp⟩
    simp only [outside, Finset.mem_filter, Finset.mem_univ, true_and] at hδ ⊢
    have : mismatch κ (κ - δ) = mismatch 0 δ := by
      unfold mismatch; congr 1; ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, Pi.zero_apply]
      constructor
      · intro h hd; exact h (by rw [← hd, sub_zero])
      · intro h he
        rw [eq_comm, sub_eq_self] at he
        exact h he.symm
    rwa [this]

end FTPaper
