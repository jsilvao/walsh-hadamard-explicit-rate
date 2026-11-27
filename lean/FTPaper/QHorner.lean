import FTPaper.QPlan

/-!
# The Horner predictor as a plan (paper: Lemma 3.1(3))

Take a stage plan that acts on row `i` by a matrix `C i`. The predictor
`π_i(C_i) X_i = Σ_t c_t(i) C_i^t X_i` is computed by a plan with exactly `n` copies of the
stage, plus zero-call row combinations with rational coefficients. One extra stored row
(`X`) is kept alongside the working row.
-/

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

namespace FTPaper

namespace QPlan

variable {A N h : ℕ}

/-- Row-wise scaling `c ⊙ x`. -/
def diagMix (c : Fin N → ℚ) : QPlan A N N := .mix fun b a => if a = b then c b else 0

theorem applyAt_diagMix (c : Fin N → ℚ) (x : Bank A h N) :
    (diagMix c).applyAt h x = fun b z => c b * x b z := by
  rw [diagMix, applyAt_mix]
  funext b z
  rw [Finset.sum_eq_single b]
  · simp
  · intro a _ ha; simp [ha]
  · simp

/-- One Horner step on the pair `(V, X)`: `(V, X) ↦ (stage V + c ⊙ X, X)`. -/
def hornerStep (stage : QPlan A N N) (c : Fin N → ℚ) : QPlan A (N + N) (N + N) :=
  ((combine (fun _ => 1) c).fork (route (Fin.natAdd N))).seq (stage.parallel (route id))

theorem applyAt_hornerStep (stage : QPlan A N N) (c : Fin N → ℚ) (V X : Bank A h N) :
    (hornerStep stage c).applyAt h (Fin.append V X) =
      Fin.append (fun b z => stage.applyAt h V b z + c b * X b z) X := by
  rw [hornerStep, applyAt_seq, applyAt_parallel, applyAt_route, applyAt_fork, applyAt_combine,
    applyAt_route]
  congr 1
  · funext b z; simp
  · funext b; simp only [Function.comp_apply, Fin.append_right, id_eq]

@[simp] theorem calls_hornerStep (stage : QPlan A N N) (c : Fin N → ℚ) :
    (hornerStep stage c).calls = stage.calls := by
  simp [hornerStep]

/-- `(P_n X, X)` where `P_n = Σ_{t ≤ n} c_t C^t`, by Horner's rule. -/
def hornerPair (stage : QPlan A N N) : (ℕ → Fin N → ℚ) → ℕ → QPlan A N (N + N)
  | c, 0 => (diagMix (c 0)).fork (route id)
  | c, n + 1 => (hornerStep stage (c 0)).seq (hornerPair stage (fun t => c (t + 1)) n)

/-- The Horner predictor `X ↦ Σ_{t ≤ n} c_t ⊙ C^t X`. -/
def horner (stage : QPlan A N N) (c : ℕ → Fin N → ℚ) (n : ℕ) : QPlan A N N :=
  (route (Fin.castAdd N)).seq (hornerPair stage c n)

theorem calls_hornerPair (stage : QPlan A N N) (c : ℕ → Fin N → ℚ) (n : ℕ) :
    (hornerPair stage c n).calls = n * stage.calls := by
  induction n generalizing c with
  | zero => simp [hornerPair, diagMix, fork, route, calls]
  | succ n ih => simp [hornerPair, ih, Nat.succ_mul, Nat.add_comm]

/-- **The predictor uses exactly `n` stages.** -/
theorem calls_horner (stage : QPlan A N N) (c : ℕ → Fin N → ℚ) (n : ℕ) :
    (horner stage c n).calls = n * stage.calls := by
  simp [horner, calls_hornerPair]

/-- **Horner semantics.** If the stage acts on row `i` by `C i`, the predictor acts on row `i`
by `Σ_{t ≤ n} c_t(i) C_i^t`. -/
theorem applyAt_horner (stage : QPlan A N N) (C : Fin N → Matrix (Addr A h) (Addr A h) ℚ)
    (hC : ∀ (x : Bank A h N) (i : Fin N), stage.applyAt h x i = C i *ᵥ x i)
    (c : ℕ → Fin N → ℚ) (n : ℕ) (X : Bank A h N) (i : Fin N) :
    (horner stage c n).applyAt h X i =
      (∑ t ∈ Finset.range (n + 1), c t i • (C i) ^ t) *ᵥ X i := by
  have key : ∀ (c : ℕ → Fin N → ℚ) (n : ℕ),
      (hornerPair stage c n).applyAt h X =
        Fin.append (fun b => (∑ t ∈ Finset.range (n + 1), c t b • (C b) ^ t) *ᵥ X b) X := by
    intro c n
    induction n generalizing c with
    | zero =>
      rw [hornerPair, applyAt_fork, applyAt_diagMix, applyAt_route]
      congr 1
      funext b z
      simp [Matrix.smul_mulVec, Matrix.one_mulVec]
    | succ n ih =>
      rw [hornerPair, applyAt_seq, ih, applyAt_hornerStep]
      congr 1
      funext b z
      rw [hC]
      have hmat : (∑ t ∈ Finset.range (n + 1 + 1), c t b • C b ^ t)
          = C b * (∑ t ∈ Finset.range (n + 1), c (t + 1) b • C b ^ t) + c 0 b • 1 := by
        rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero]
        congr 1
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Matrix.mul_smul, ← pow_succ']
      rw [hmat, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      simp [Pi.add_apply, Pi.smul_apply]
  rw [horner, applyAt_seq, key, applyAt_route]
  simp

end QPlan

end FTPaper
