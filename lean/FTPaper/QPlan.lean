import OAI.Computability.NearSquareRoot.KernelBinaryTemplate

/-!
# Plans with rational coefficients

OpenAI's template language `KernelPass.Plan` only has dyadic coefficients. Our Horner
predictor needs rational ones (paper: Section 7.1). `QPlan` is the same language with:
* rational coefficients in `mix`;
* row-wise, address-dependent rational scalings `scaleRows`, which generalize their `scale`;
* `embed`, which runs any of OpenAI's plans unchanged, with the same matrix and the same
  number of child calls.

A child call is still the only charged operation.
-/

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

namespace FTPaper

/-- Plans over `A` axes with `i` input and `o` output rows and rational coefficients. -/
inductive QPlan (A : ℕ) : ℕ → ℕ → Type
  | mix {i o} (coeff : Fin o → Fin i → ℚ) : QPlan A i o
  | scaleRows {n} (q : ℕ) (test : Column A → Fin q → ZMod 2)
      (table : Fin n → (Fin q → ZMod 2) → ℚ) : QPlan A n n
  | embed {i o} (p : Plan A i o) : QPlan A i o
  | seq {i j o} (p : QPlan A j o) (q : QPlan A i j) : QPlan A i o
  | parallel {i j o u} (p : QPlan A i o) (q : QPlan A j u) : QPlan A (i + j) (o + u)

namespace QPlan

variable {A : ℕ}

/-- Child calls: the only charged operation. -/
def calls {i o : ℕ} : QPlan A i o → ℕ
  | .mix _ | .scaleRows _ _ _ => 0
  | .embed p => p.calls
  | .seq p q => calls p + calls q
  | .parallel p q => calls p + calls q

/-- The matrix of a plan at child width `h` (same conventions as `Plan.eval`). -/
def eval {i o : ℕ} (h : ℕ) : QPlan A i o → RowMatrix A h i o
  | .mix coeff => fun ⟨b, y⟩ ⟨a, x⟩ => if x = y then coeff b a else 0
  | .scaleRows _ test t => fun ⟨b, y⟩ ⟨a, x⟩ =>
      if b = a ∧ x = y then t b (∑ c, test (x c)) else 0
  | .embed p => p.eval h
  | .seq p q => p.eval h * q.eval h
  | .parallel p q => directSum (p.eval h) (q.eval h)

/-- Action on a bank of rows. -/
def applyAt {i o : ℕ} (p : QPlan A i o) (h : ℕ) (x : Bank A h i) : Bank A h o :=
  Function.curry ((p.eval h).mulVec (Function.uncurry x))

/-- A plan is correct if it computes the normalized transform on every row. -/
def Correct {W : ℕ} (p : QPlan A W W) : Prop := ∀ h, p.eval h = target A W h

variable {i j o u h : ℕ}

@[simp] theorem calls_seq (p : QPlan A j o) (q : QPlan A i j) :
    (p.seq q).calls = p.calls + q.calls := rfl
@[simp] theorem calls_parallel (p : QPlan A i o) (q : QPlan A j u) :
    (p.parallel q).calls = p.calls + q.calls := rfl
@[simp] theorem calls_embed (p : Plan A i o) : (QPlan.embed p).calls = p.calls := rfl
@[simp] theorem calls_mix (c : Fin o → Fin i → ℚ) : (QPlan.mix (A := A) c).calls = 0 := rfl

theorem applyAt_seq (p : QPlan A j o) (q : QPlan A i j) (x : Bank A h i) :
    (p.seq q).applyAt h x = p.applyAt h (q.applyAt h x) := by
  simp [applyAt, eval, Matrix.mulVec_mulVec]

theorem applyAt_embed (p : Plan A i o) (x : Bank A h i) :
    (QPlan.embed p).applyAt h x = p.applyAt h x := rfl

theorem applyAt_mix (c : Fin o → Fin i → ℚ) (x : Bank A h i) :
    (QPlan.mix c).applyAt h x = fun b y => ∑ a, c b a * x a y := by
  funext b y
  simp [applyAt, eval, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul]

theorem applyAt_scaleRows {n q : ℕ} (test : Column A → Fin q → ZMod 2)
    (t : Fin n → (Fin q → ZMod 2) → ℚ) (x : Bank A h n) :
    (QPlan.scaleRows q test t).applyAt h x = fun b y => t b (∑ c, test (y c)) * x b y := by
  funext b y
  simp only [applyAt, eval, Function.curry_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Function.uncurry]
  rw [Finset.sum_eq_single b]
  · rw [Finset.sum_eq_single y]
    · simp
    · intro x _ hx; simp [hx]
    · simp
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro x _
    simp [Ne.symm ha]
  · simp

theorem applyAt_parallel (p : QPlan A i o) (q : QPlan A j u) (x : Bank A h i) (y : Bank A h j) :
    (p.parallel q).applyAt h (Fin.append x y) = Fin.append (p.applyAt h x) (q.applyAt h y) := by
  funext b z
  refine Fin.addCases (fun l => ?_) (fun r => ?_) b <;>
    simp only [applyAt, eval, directSum, Function.curry_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Function.uncurry, Fin.append_left, Fin.append_right,
      Fin.addCases_left, Fin.addCases_right] <;>
    rw [Fin.sum_univ_add] <;> simp

/-! ## Routing, forking, combining -/

/-- Copy or forget rows. -/
def route (r : Fin o → Fin i) : QPlan A i o := .mix fun b a => if a = r b then 1 else 0

theorem applyAt_route (r : Fin o → Fin i) (x : Bank A h i) :
    (route (A := A) r).applyAt h x = x ∘ r := by
  rw [route, applyAt_mix]
  funext b y
  rw [Finset.sum_eq_single (r b)]
  · simp
  · intro a _ ha; simp [ha]
  · simp

@[simp] theorem calls_route (r : Fin o → Fin i) : (route (A := A) r).calls = 0 := rfl

/-- Run both plans on copies of the same input. -/
def fork (p : QPlan A i o) (q : QPlan A i u) : QPlan A i (o + u) :=
  (p.parallel q).seq (route (Fin.append id id))

theorem applyAt_fork (p : QPlan A i o) (q : QPlan A i u) (x : Bank A h i) :
    (p.fork q).applyAt h x = Fin.append (p.applyAt h x) (q.applyAt h x) := by
  rw [fork, applyAt_seq, applyAt_route]
  have hx : x ∘ Fin.append (id : Fin i → Fin i) id = Fin.append x x := by
    funext a
    refine Fin.addCases (fun k => ?_) (fun k => ?_) a <;>
      simp only [Function.comp_apply, Fin.append_left, Fin.append_right, id_eq]
  rw [hx, applyAt_parallel]

@[simp] theorem calls_fork (p : QPlan A i o) (q : QPlan A i u) :
    (p.fork q).calls = p.calls + q.calls := by simp [fork]

/-- Row-wise linear combination of two banks of the same size: `u ⊙ x + v ⊙ y`. -/
def combine {W : ℕ} (u v : Fin W → ℚ) : QPlan A (W + W) W :=
  .mix fun b => Fin.append (fun a => if a = b then u b else 0) (fun a => if a = b then v b else 0)

theorem applyAt_combine {W : ℕ} (u v : Fin W → ℚ) (x y : Bank A h W) :
    (combine u v).applyAt h (Fin.append x y) = fun b z => u b * x b z + v b * y b z := by
  rw [combine, applyAt_mix]
  funext b z
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  have step (k : ℚ) (r : Bank A h W) :
      ∑ a, (if a = b then k else 0) * r a z = k * r b z := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro a _ ha; simp [ha]
    · simp
  rw [step, step]

@[simp] theorem calls_combine {W : ℕ} (u v : Fin W → ℚ) : (combine (A := A) u v).calls = 0 := rfl

/-- Left and right halves of a bank. -/
def leftPart {X : Type*} {m n : ℕ} (x : Fin (m + n) → X) : Fin m → X := x ∘ Fin.castAdd n
def rightPart {X : Type*} {m n : ℕ} (x : Fin (m + n) → X) : Fin n → X := x ∘ Fin.natAdd m

@[simp] theorem leftPart_append {X : Type*} {m n : ℕ} (x : Fin m → X) (y : Fin n → X) :
    leftPart (Fin.append x y) = x := by funext k; exact Fin.append_left ..
@[simp] theorem rightPart_append {X : Type*} {m n : ℕ} (x : Fin m → X) (y : Fin n → X) :
    rightPart (Fin.append x y) = y := by funext k; exact Fin.append_right ..

theorem append_parts {X : Type*} {m n : ℕ} (x : Fin (m + n) → X) :
    Fin.append (leftPart x) (rightPart x) = x := by
  funext k
  refine Fin.addCases (fun l => ?_) (fun r => ?_) k <;>
    simp only [Fin.append_left, Fin.append_right, leftPart, rightPart, Function.comp_apply]

theorem applyAt_parallel_parts (p : QPlan A i o) (q : QPlan A j u) (x : Bank A h (i + j)) :
    (p.parallel q).applyAt h x =
      Fin.append (p.applyAt h (leftPart x)) (q.applyAt h (rightPart x)) := by
  rw [← applyAt_parallel, append_parts]

end QPlan

end FTPaper
