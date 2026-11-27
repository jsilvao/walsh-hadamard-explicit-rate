import FTPaper.QTwoPass

/-!
# Frequency-level semantics of rational plans

`frequency x b = W x_b`, where `W` is the normalized Walsh involution. That is OpenAI's
`Plan.frequency`.

* `frequency_mix`: row mixing commutes with conversion.
* `frequency_horner`: if the stage multiplies frequency `y` of row `i` by `μ i y`, the predictor
  multiplies it by `Σ_t c_t(i) μ(i,y)^t`.
* `matrixTable`, `spectralTable`: address-dependent rational row mixing, and its conjugate by
  conversions. `frequency_spectralTable` says the table acts at frequency `y` by the matrix
  `c (k y)`. Here `k y = Σ_t test (y t)` is the query signature.
-/

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open OAI.Computability.NearSquareRoot.KernelPass.Plan (frequency walshMatrix walshMatrix_mul_self
  convertBank applyAt_convertBank frequency_frequency calls_convertBank)
open Matrix Finset

namespace FTPaper

namespace QPlan

variable {A h N : ℕ}

theorem frequency_mix {i o : ℕ} (M : Fin o → Fin i → ℚ) (x : Bank A h i) (b : Fin o)
    (y : Addr A h) :
    frequency ((QPlan.mix M).applyAt h x) b y = ∑ a, M b a * frequency x a y := by
  simp only [frequency, applyAt_mix]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x' _ => ?_
  ring

/-- A plan diagonal in frequency, with multiplier `μ`, acts in ordinary coordinates by
`W diag(μ_i) W`. -/
theorem applyAt_of_frequency {i : ℕ} (p : QPlan A i i) (μ : Fin i → Addr A h → ℚ)
    (hμ : ∀ x b y, frequency (p.applyAt h x) b y = μ b y * frequency x b y)
    (x : Bank A h i) (b : Fin i) :
    p.applyAt h x b = (walshMatrix A h * diagonal (μ b) * walshMatrix A h) *ᵥ x b := by
  have hw : walshMatrix A h *ᵥ (p.applyAt h x b) = diagonal (μ b) *ᵥ (walshMatrix A h *ᵥ x b) := by
    funext y
    rw [Matrix.mulVec_diagonal]
    exact hμ x b y
  calc p.applyAt h x b = walshMatrix A h *ᵥ (walshMatrix A h *ᵥ p.applyAt h x b) := by
        rw [Matrix.mulVec_mulVec, walshMatrix_mul_self, Matrix.one_mulVec]
    _ = _ := by rw [hw, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- **Predictor in frequency.** -/
theorem frequency_horner (stage : QPlan A N N) (μ : Fin N → Addr A h → ℚ)
    (hμ : ∀ x b y, frequency (stage.applyAt h x) b y = μ b y * frequency x b y)
    (c : ℕ → Fin N → ℚ) (n : ℕ) (X : Bank A h N) (b : Fin N) (y : Addr A h) :
    frequency ((horner stage c n).applyAt h X) b y =
      (∑ t ∈ Finset.range (n + 1), c t b * μ b y ^ t) * frequency X b y := by
  let C : Fin N → Matrix (Addr A h) (Addr A h) ℚ :=
    fun i => walshMatrix A h * diagonal (μ i) * walshMatrix A h
  have hC : ∀ (x : Bank A h N) (i : Fin N), stage.applyAt h x i = C i *ᵥ x i :=
    fun x i => applyAt_of_frequency stage μ hμ x i
  have hpow : ∀ (i : Fin N) (t : ℕ), C i ^ t = walshMatrix A h * diagonal (μ i ^ t) * walshMatrix A h := by
    intro i t
    induction t with
    | zero =>
      simp [walshMatrix_mul_self]
    | succ t ih =>
      rw [pow_succ, ih]
      simp only [C]
      have : walshMatrix A h * diagonal (μ i ^ t) * walshMatrix A h *
          (walshMatrix A h * diagonal (μ i) * walshMatrix A h)
          = walshMatrix A h * (diagonal (μ i ^ t) * (walshMatrix A h * walshMatrix A h) *
            diagonal (μ i)) * walshMatrix A h := by simp only [Matrix.mul_assoc]
      rw [this, walshMatrix_mul_self, Matrix.mul_one, diagonal_mul_diagonal, pow_succ]
      rfl
  have hh := applyAt_horner stage C hC c n X b
  simp only [frequency]
  rw [hh, Matrix.mulVec_mulVec]
  have hsum : walshMatrix A h * (∑ t ∈ Finset.range (n + 1), c t b • C b ^ t)
      = diagonal (fun y => ∑ t ∈ Finset.range (n + 1), c t b * μ b y ^ t) * walshMatrix A h := by
    rw [Finset.mul_sum]
    have : ∀ t ∈ Finset.range (n + 1), walshMatrix A h * (c t b • C b ^ t)
        = diagonal (fun y => c t b * μ b y ^ t) * walshMatrix A h := by
      intro t _
      rw [hpow, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, walshMatrix_mul_self,
        Matrix.one_mul, ← Matrix.smul_mul]
      congr 1
      ext u v
      simp [diagonal_apply, Pi.pow_apply]
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul]
    congr 1
    ext u v
    simp [diagonal_apply, Matrix.sum_apply]
  rw [hsum, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]

/-- Address-dependent rational row mixing: at address `y`, the bank is multiplied by `c (k y)`,
where `k y = Σ_t test (y t)`. -/
def matrixTable {i o q : ℕ} (test : Column A → Fin q → ZMod 2)
    (c : (Fin q → ZMod 2) → Fin o → Fin i → ℚ) : QPlan A i o :=
  (QPlan.mix fun b r => if (finProdFinEquiv.symm r).1 = b then 1 else 0).seq
    ((QPlan.scaleRows q test fun r k => c k (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2).seq
      (route fun r => (finProdFinEquiv.symm r).2))

theorem applyAt_matrixTable {i o q : ℕ} (test : Column A → Fin q → ZMod 2)
    (c : (Fin q → ZMod 2) → Fin o → Fin i → ℚ) (x : Bank A h i) :
    (matrixTable test c).applyAt h x = fun b y => ∑ a, c (∑ t, test (y t)) b a * x a y := by
  rw [matrixTable, applyAt_seq, applyAt_seq, applyAt_route, applyAt_scaleRows, applyAt_mix]
  funext b y
  rw [← (finProdFinEquiv (m := o) (n := i)).sum_comp]
  simp only [Equiv.symm_apply_apply, Function.comp_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' _ hb'
    apply Finset.sum_eq_zero
    intro a _
    simp [hb']
  · simp

@[simp] theorem calls_matrixTable {i o q : ℕ} (test : Column A → Fin q → ZMod 2)
    (c : (Fin q → ZMod 2) → Fin o → Fin i → ℚ) : (matrixTable test c).calls = 0 := by
  simp [matrixTable, calls]

/-- Address-dependent mixing in frequency coordinates: convert, mix, convert back. -/
def spectralTable {i o q : ℕ} (test : Column A → Fin q → ZMod 2)
    (c : (Fin q → ZMod 2) → Fin o → Fin i → ℚ) : QPlan A i o :=
  (QPlan.embed (convertBank A o)).seq ((matrixTable test c).seq (QPlan.embed (convertBank A i)))

theorem frequency_spectralTable {i o q : ℕ} (test : Column A → Fin q → ZMod 2)
    (c : (Fin q → ZMod 2) → Fin o → Fin i → ℚ) (x : Bank A h i) (b : Fin o) (y : Addr A h) :
    frequency ((spectralTable test c).applyAt h x) b y =
      ∑ a, c (∑ t, test (y t)) b a * frequency x a y := by
  rw [spectralTable, applyAt_seq, applyAt_seq, applyAt_embed, applyAt_embed, applyAt_convertBank,
    applyAt_convertBank, frequency_frequency, applyAt_matrixTable]

/-- **Direct conversions cost `A` calls per row**, in and out. -/
@[simp] theorem calls_spectralTable {i o q : ℕ} (test : Column A → Fin q → ZMod 2)
    (c : (Fin q → ZMod 2) → Fin o → Fin i → ℚ) :
    (spectralTable test c).calls = o * A + i * A := by
  simp [spectralTable]

end QPlan

end FTPaper
