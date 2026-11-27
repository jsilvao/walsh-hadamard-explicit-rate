import FTPaper.QTemplate

/-!
# Correctness through OpenAI's outer passes

A rational plan whose rows are multiplied in frequency by the product of query signs becomes
`Correct` after OpenAI's two zero-call outer passes. `Correct` means it computes the normalized
Walsh–Hadamard transform on every row.
-/

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open OAI.Computability.NearSquareRoot.KernelPass.Plan (frequency walshMatrix walshMatrix_mul_self
  convertBank applyAt_convertBank applyAt_one_perRow perRow outer_kernel)
open OAI.Computability.NearSquareRoot.BinaryQuery
open Matrix Finset

namespace FTPaper

namespace QPlan

variable {A h n : ℕ}

theorem eval_eq_of_applyAt {i o : ℕ} (p : QPlan A i o) (M : RowMatrix A h i o)
    (hp : ∀ x, p.applyAt h x = Function.curry (M.mulVec (Function.uncurry x))) : p.eval h = M := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  simpa only [applyAt, Function.uncurry_curry] using congrArg Function.uncurry (hp (Function.curry v))

/-- **Row action of the normalized transform gives correctness**, using OpenAI's verified
conversion bank as the reference. -/
theorem correct_of_row_action (p : QPlan A n n)
    (hp : ∀ h (x : Bank A h n) (i : Fin n), p.applyAt h x i = walshMatrix A h *ᵥ x i) :
    Correct p := by
  have hconv : KernelPass.Correct (convertBank A n) :=
    KernelPass.Plan.correct_of_row_action (convertBank A n)
      (fun h x i => by rw [applyAt_convertBank]; rfl)
  intro h
  rw [← hconv h]
  apply eval_eq_of_applyAt
  intro x
  have : p.applyAt h x = (convertBank A n).applyAt h x := by
    rw [applyAt_convertBank]; funext i; exact hp h x i
  rw [this]
  rfl

/-- Outer passes around a rational plan. -/
def wrap (front back : Plan A 1 1) (p : QPlan A n n) : QPlan A n n :=
  ((QPlan.embed (perRow fun _ => back)).seq p).seq (QPlan.embed (perRow fun _ => front))

@[simp] theorem calls_wrap (front back : Plan A 1 1) (p : QPlan A n n)
    (hf : front.calls = 0) (hb : back.calls = 0) : (wrap front back p).calls = p.calls := by
  simp [wrap, hf, hb]

theorem correct_wrap (front back : Plan A 1 1) (p : QPlan A n n)
    (U : (h : ℕ) → Matrix (Addr A h) (Addr A h) ℚ)
    (hp : ∀ h (x : Bank A h n) (i : Fin n), p.applyAt h x i = U h *ᵥ x i)
    (hu : ∀ h, oneRow (back.eval h) * U h * oneRow (front.eval h) = walshMatrix A h) :
    Correct (wrap front back p) := by
  apply QPlan.correct_of_row_action
  intro h x i
  rw [wrap, applyAt_seq, applyAt_seq, applyAt_embed, applyAt_embed, applyAt_one_perRow, hp,
    applyAt_one_perRow, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hu]

/-- **Product of signs in frequency gives a correct plan after the outer passes.** -/
theorem correct_of_product {m u : ℕ} (hm : m ≡ 1 [MOD 2]) (p : QPlan (Arity m u) n n)
    (hp : ∀ h (x : Bank (Arity m u) h n) (i : Fin n) (y : Addr (Arity m u) h),
      frequency (p.applyAt h x) i y =
        (∏ j : Fin m, (-1 : ℚ) ^ ((∑ c, test m u (y c)) j).val) * frequency x i y) :
    ∃ front back : Plan (Arity m u) 1 1, front.calls = 0 ∧ back.calls = 0 ∧
      Correct (wrap front back p) := by
  obtain ⟨front, back, hf0, hb0, hf, hb⟩ := outer_passes m u
  refine ⟨front, back, hf0, hb0, ?_⟩
  refine QPlan.correct_wrap front back p
    (fun h => walshMatrix (Arity m u) h *
      diagonal (fun y => ∏ j : Fin m, (-1 : ℚ) ^ ((∑ c, test m u (y c)) j).val) *
      walshMatrix (Arity m u) h) ?_ ?_
  · intro h x i
    exact applyAt_of_frequency p (fun _ y => ∏ j : Fin m, (-1 : ℚ) ^ ((∑ c, test m u (y c)) j).val)
      (fun x b y => hp h x b y) x i
  · intro h
    exact outer_kernel hm front back hf hb _ (product_kernel m u h)

end QPlan

end FTPaper
