import FTPaper.QFreq
import FTPaper.Repair

/-!
# The repaired batch, end to end in frequency coordinates

Take any stage plan that is diagonal in frequency, with a multiplier depending only on the query
signature `k y = Σ_t test (y t)`. The batch is

  `twoPass (horner stage c n) (mix H) (mix Hᵀ) (spectralTable test tab)`

with tables satisfying the per-frequency table property (`IsTable`, from `Repair.lean`). It
multiplies every frequency of every row by the target multiplier `z (k y)`. This is
Lemma A(3) + Lemma B at the plan level, with direct conversions.
-/

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open OAI.Computability.NearSquareRoot.KernelPass.Plan (frequency walshMatrix)
open Matrix Finset

namespace FTPaper

namespace QPlan

variable {A h N s q : ℕ}

/-- The `2s × 2s` spectral table: `(U, U') ↦ (T (U − z U'), z · T (U − z U'))`. -/
noncomputable def tabMatrix (T : (Fin s → ℚ) →ₗ[ℚ] (Fin s → ℚ)) (z : ℚ) :
    Fin (s + s) → Fin (s + s) → ℚ :=
  let M := LinearMap.toMatrix' T
  Fin.append (fun r => Fin.append (fun r' => M r r') (fun r' => -z * M r r'))
    (fun r => Fin.append (fun r' => z * M r r') (fun r' => -z * z * M r r'))

theorem tabMatrix_apply (T : (Fin s → ℚ) →ₗ[ℚ] (Fin s → ℚ)) (z : ℚ) (U U' : Fin s → ℚ) :
    (fun r => ∑ r'', tabMatrix T z r r'' * Fin.append U U' r'')
      = Fin.append (T (U - z • U')) (z • T (U - z • U')) := by
  have hT : ∀ v : Fin s → ℚ, T v = LinearMap.toMatrix' T *ᵥ v := by
    intro v; rw [LinearMap.toMatrix'_mulVec]
  funext r
  refine Fin.addCases (fun l => ?_) (fun l => ?_) r
  · simp only [tabMatrix, Fin.append_left, Fin.sum_univ_add, Fin.append_right]
    rw [hT, Matrix.mulVec, dotProduct]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun r' _ => ?_
    ring
  · simp only [tabMatrix, Fin.append_left, Fin.sum_univ_add, Fin.append_right, Pi.smul_apply,
      smul_eq_mul]
    rw [hT, Matrix.mulVec, dotProduct]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib,
      Finset.mul_sum]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun r' _ => ?_; ring
    · refine Finset.sum_congr rfl fun r' _ => ?_; ring

theorem frequency_combo (a b c : Bank A h N) (i : Fin N) (y : Addr A h) :
    frequency (fun j ω => a j ω - b j ω + c j ω) i y
      = frequency a i y - frequency b i y + frequency c i y := by
  simp only [frequency, Matrix.mulVec, dotProduct, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

theorem frequency_append {m n : ℕ} (u : Bank A h m) (v : Bank A h n) :
    frequency (Fin.append u v) = Fin.append (frequency u) (frequency v) := by
  funext r
  refine Fin.addCases (fun l => ?_) (fun l => ?_) r <;> simp [frequency]

theorem frequency_leftPart {m n : ℕ} (x : Bank A h (m + n)) :
    frequency (leftPart x) = leftPart (frequency x) := rfl

theorem frequency_rightPart {m n : ℕ} (x : Bank A h (m + n)) :
    frequency (rightPart x) = rightPart (frequency x) := rfl

/-- **The repaired batch is the target product, row by row and frequency by frequency**, for any
table plan `tbl` that acts in frequency coordinates by the matrices `tabMatrix (T κ) (z κ)`. -/
theorem frequency_batchWith (stage : QPlan A N N) (test : Column A → Fin q → ZMod 2)
    (mult : Fin N → (Fin q → ZMod 2) → ℚ)
    (hstage : ∀ x b y, frequency (stage.applyAt h x) b y = mult b (∑ t, test (y t)) * frequency x b y)
    (c : ℕ → Fin N → ℚ) (n : ℕ) (z : (Fin q → ZMod 2) → ℚ) (H : Matrix (Fin s) (Fin N) ℚ)
    (T : (Fin q → ZMod 2) → (Fin s → ℚ) →ₗ[ℚ] (Fin s → ℚ))
    (hT : ∀ κ, IsTable H (fun i => ∑ t ∈ Finset.range (n + 1), c t i * mult i κ ^ t) (z κ) (T κ))
    (tbl : QPlan A (s + s) (s + s))
    (htbl : ∀ (w : Bank A h (s + s)) (r : Fin (s + s)) (y : Addr A h),
      frequency (tbl.applyAt h w) r y =
        ∑ a, tabMatrix (T (∑ t, test (y t))) (z (∑ t, test (y t))) r a * frequency w a y)
    (x : Bank A h N) (i : Fin N) (y : Addr A h) :
    frequency ((twoPass (horner stage c n) (QPlan.mix fun r i => H r i) (QPlan.mix fun i r => H r i)
        tbl).applyAt h x) i y
      = z (∑ t, test (y t)) * frequency x i y := by
  set κ := ∑ t, test (y t) with hκ
  set p : Fin N → ℚ := fun i => ∑ t ∈ Finset.range (n + 1), c t i * mult i κ ^ t with hp
  set P := horner stage c n with hP
  have hpred : ∀ (w : Bank A h N) (j : Fin N),
      frequency (P.applyAt h w) j y = p j * frequency w j y := by
    intro w j
    rw [hP, frequency_horner stage (fun b y => mult b (∑ t, test (y t))) hstage c n w j y]
  set Xh : Fin N → ℚ := fun j => frequency x j y with hXh
  -- the two check vectors at `y`
  set px := P.applyAt h x with hpx
  have hgp : (fun r => frequency ((QPlan.mix fun r i => H r i).applyAt h px) r y) = H *ᵥ (p * Xh) := by
    funext r
    rw [frequency_mix]
    simp only [Matrix.mulVec, dotProduct, Pi.mul_apply, hpx, hpred, hXh]
  have hgx : (fun r => frequency ((QPlan.mix fun r i => H r i).applyAt h x) r y) = H *ᵥ Xh := by
    funext r
    rw [frequency_mix]
    simp [Matrix.mulVec, dotProduct, hXh]
  -- the table output at `y`
  set out := tbl.applyAt h
    (Fin.append ((QPlan.mix fun r i => H r i).applyAt h px) ((QPlan.mix fun r i => H r i).applyAt h x))
    with hout
  set a : Fin s → ℚ := T κ (H *ᵥ (p * Xh) - z κ • (H *ᵥ Xh)) with ha
  have hfo : (fun r => frequency out r y) = Fin.append a (z κ • a) := by
    have h1 : (fun r => frequency out r y) =
        fun r => ∑ r'', tabMatrix (T κ) (z κ) r r'' *
          Fin.append (H *ᵥ (p * Xh)) (H *ᵥ Xh) r'' := by
      funext r
      rw [hout, htbl, frequency_append]
      refine Finset.sum_congr rfl fun r'' _ => ?_
      congr 1
      refine Fin.addCases (fun l => ?_) (fun l => ?_) r''
      · simp only [Fin.append_left]; exact congrFun hgp l
      · simp only [Fin.append_right]; exact congrFun hgx l
    rw [h1, tabMatrix_apply]
  have hleft : ∀ r, frequency (leftPart out) r y = a r := by
    intro r
    have hr := congrFun hfo (Fin.castAdd s r)
    simp only [Fin.append_left] at hr
    exact hr
  have hright : ∀ r, frequency (rightPart out) r y = z κ * a r := by
    intro r
    have hr := congrFun hfo (Fin.natAdd s r)
    simp only [Fin.append_right, Pi.smul_apply, smul_eq_mul] at hr
    exact hr
  -- lifted rows
  have hz : ∀ j, frequency ((QPlan.mix fun i r => H r i).applyAt h (leftPart out)) j y = (Hᵀ *ᵥ a) j := by
    intro j
    rw [frequency_mix]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hleft r]
  have hfz : ∀ j, frequency ((QPlan.mix fun i r => H r i).applyAt h (rightPart out)) j y
      = z κ * (Hᵀ *ᵥ a) j := by
    intro j
    rw [frequency_mix]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hright r]
    ring
  -- assemble with the per-frequency repair identity
  rw [applyAt_twoPass]
  dsimp only
  rw [frequency_combo, ← hpx, hpred, hpred, hz, hfz]
  have key := congrFun (output_eq (hT κ) Xh) i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at key
  rw [← ha] at key
  exact key

/-- **The repaired batch with direct conversions is the target product.** -/
theorem frequency_batch (stage : QPlan A N N) (test : Column A → Fin q → ZMod 2)
    (mult : Fin N → (Fin q → ZMod 2) → ℚ)
    (hstage : ∀ x b y, frequency (stage.applyAt h x) b y = mult b (∑ t, test (y t)) * frequency x b y)
    (c : ℕ → Fin N → ℚ) (n : ℕ) (z : (Fin q → ZMod 2) → ℚ) (H : Matrix (Fin s) (Fin N) ℚ)
    (T : (Fin q → ZMod 2) → (Fin s → ℚ) →ₗ[ℚ] (Fin s → ℚ))
    (hT : ∀ κ, IsTable H (fun i => ∑ t ∈ Finset.range (n + 1), c t i * mult i κ ^ t) (z κ) (T κ))
    (x : Bank A h N) (i : Fin N) (y : Addr A h) :
    frequency ((twoPass (horner stage c n) (QPlan.mix fun r i => H r i) (QPlan.mix fun i r => H r i)
        (spectralTable test fun κ => tabMatrix (T κ) (z κ))).applyAt h x) i y
      = z (∑ t, test (y t)) * frequency x i y :=
  frequency_batchWith stage test mult hstage c n z H T hT _
    (fun w r y => frequency_spectralTable test _ w r y) x i y

/-- **Calls of the repaired batch with direct conversions.** -/
theorem calls_batch (stage : QPlan A N N) (test : Column A → Fin q → ZMod 2)
    (c : ℕ → Fin N → ℚ) (n : ℕ) (H : Matrix (Fin s) (Fin N) ℚ)
    (tab : (Fin q → ZMod 2) → Fin (s + s) → Fin (s + s) → ℚ) :
    (twoPass (horner stage c n) (QPlan.mix fun r i => H r i) (QPlan.mix fun i r => H r i)
        (spectralTable test tab)).calls = 2 * n * stage.calls + 2 * (s + s) * A := by
  rw [calls_twoPass, calls_horner, calls_spectralTable]
  simp only [calls_mix]
  ring

end QPlan

end FTPaper
