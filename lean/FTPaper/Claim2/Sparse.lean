import FTPaper.QCircuit

/-!
# Sparse local costs (paper: Lemma 10.1)

The circuit compilation of `FTPaper/QCircuit.lean` charges a mix densely, `o·i` gates per
address. Here a mix is charged by its nonzero pattern: a row with `t` nonzero coefficients costs
`t - 1` gates (`rowCost`). A row with one nonzero is a scaling, which folds into a readout, and
a zero row is a zero readout.

* `realizable_sparse`: every matrix is realizable with `∑_o (|supp row o| - 1)` gates. The
  row-by-row construction is OpenAI's (`Circuit.lean`, private there), started from a free
  readout instead of a gate.
* `planSparse`, `qsparse`: the sparse local cost of OpenAI's plans and of rational plans.
* `program_qplan_sparse`, `program_batch_sparse`, `kernelBatch_of_correct_sparse`: the circuit
  compilation with sparse local cost.

Source: `HasRowS`, `hasRowS_step`, `addInputS`, `addRowS`, `addRowsS` and `realizable_sparse`
adapt the private `HasRow`, `hasRow_step`, `addInput`, `addRow`, `addRows` and the public
`realizableAtMost_card_mul_card` of OpenAI's `LinearAlgebra/FiniteFourier/Circuit.lean`
(openai/math, commit 3344da5, Apache License 2.0). Change: a row supported on `s` costs
`|s| - 1` gates, starting from a free readout.
-/

open OAI.LinearAlgebra.FiniteFourier
open OAI.Computability.NearSquareRoot
open Matrix Finset

namespace FTPaper

namespace Circ

open KernelPass

/-! ## Sparse realizability -/

section Realize

variable {K I O : Type*} [Semiring K]

/-- A row available from the registers of a program by a free readout. -/
def HasRowS {r : ℕ} (p : Program K I r) (f : (I → K) → K) : Prop :=
  ∃ z : Readout K (I ⊕ Fin r), ∀ x, z.eval (Sum.elim x (p.value x)) = f x

lemma hasRowS_step {r : ℕ} {p : Program K I r} {f : (I → K) → K}
    (hf : HasRowS p f) (g : BinaryGate K (I ⊕ Fin r)) : HasRowS (p.step g) f := by
  obtain ⟨z, hz⟩ := hf
  cases z with
  | zero => exact ⟨.zero, hz⟩
  | scaled c w =>
    cases w with
    | inl i => exact ⟨.scaled c (.inl i), hz⟩
    | inr j => exact ⟨.scaled c (.inr j.succ), hz⟩

/-- Add one weighted input to an available row with a single gate. -/
lemma addInputS {r : ℕ} {p : Program K I r} {f : (I → K) → K}
    (hf : HasRowS p f) (i : I) (a : K) :
    ∃ g : BinaryGate K (I ⊕ Fin r), HasRowS (p.step g) (fun x => a * x i + f x) := by
  obtain ⟨z, hz⟩ := hf
  cases z with
  | zero =>
    refine ⟨⟨.inl i, .inl i, a, 0⟩, .scaled 1 (.inr 0), fun x => ?_⟩
    change _ = a * x i + f x
    rw [← hz x]
    simp [Readout.eval, Program.value, BinaryGate.eval]
  | scaled c w =>
    refine ⟨⟨.inl i, w, a, c⟩, .scaled 1 (.inr 0), fun x => ?_⟩
    change _ = a * x i + f x
    rw [← hz x]
    simp [Readout.eval, Program.value, BinaryGate.eval]

/-- A row supported on `s` costs `|s| - 1` gates. -/
lemma addRowS [DecidableEq I] {r : ℕ} (p : Program K I r) (s : Finset I) (f : I → K) :
    ∃ n ≤ r + (s.card - 1), ∃ q : Program K I n,
      (∀ u, HasRowS p u → HasRowS q u) ∧ HasRowS q (fun x => ∑ i ∈ s, f i * x i) := by
  induction s using Finset.induction with
  | empty => exact ⟨r, by simp, p, fun _ h => h, .zero, by simp [Readout.eval]⟩
  | @insert i s hi ih =>
    by_cases hs : s = ∅
    · subst hs
      refine ⟨r, by simp, p, fun _ h => h, .scaled (f i) (.inl i), fun x => ?_⟩
      simp [Readout.eval]
    · obtain ⟨n, hn, q, hpq, hrow⟩ := ih
      obtain ⟨g, hg⟩ := addInputS hrow i (f i)
      have hpos : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
      refine ⟨n + 1, ?_, q.step g, fun u h => hasRowS_step (hpq u h) _, ?_⟩
      · rw [Finset.card_insert_of_notMem hi]
        omega
      · simpa only [Finset.sum_insert hi] using hg

/-- The support of a row. -/
def rowSupp [Fintype I] [DecidableEq K] (M : Matrix O I K) (o : O) : Finset I :=
  univ.filter fun i => M o i ≠ 0

lemma addRowsS [Fintype I] [DecidableEq I] [DecidableEq K] (t : Finset O) (M : Matrix O I K) :
    ∃ n ≤ ∑ o ∈ t, ((rowSupp M o).card - 1), ∃ q : Program K I n,
      ∀ o ∈ t, HasRowS q (fun x => ∑ i, M o i * x i) := by
  classical
  induction t using Finset.induction with
  | empty => exact ⟨0, by simp, .nil, by simp⟩
  | @insert o t ho ih =>
    obtain ⟨r, hr, p, hrows⟩ := ih
    obtain ⟨n, hn, q, hpq, hrow⟩ := addRowS p (rowSupp M o) (M o)
    refine ⟨n, ?_, q, fun j hj => ?_⟩
    · rw [Finset.sum_insert ho]
      omega
    · rcases Finset.mem_insert.mp hj with rfl | hj
      · have : (fun x : I → K => ∑ i ∈ rowSupp M j, M j i * x i) = fun x => ∑ i, M j i * x i := by
          funext x
          rw [rowSupp, Finset.sum_filter]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases h : M j i = 0
          · simp [h]
          · simp [h]
        rw [← this]
        exact hrow
      · exact hpq _ (hrows j hj)

/-- **Sparse realizability.** A matrix is realizable with `∑_o (|supp row o| - 1)` gates. -/
theorem realizable_sparse [Fintype I] [Fintype O] [DecidableEq K] (M : Matrix O I K) :
    RealizableAtMost M (∑ o, ((rowSupp M o).card - 1)) := by
  classical
  obtain ⟨n, hn, q, hrows⟩ := addRowsS Finset.univ M
  choose z hz using fun o => hrows o (Finset.mem_univ o)
  refine ⟨n, hn, ⟨q, z⟩, ?_⟩
  ext o i
  change (z o).eval (Sum.elim _ _) = _
  rw [hz]
  simp [Pi.single_apply, mul_ite]

end Realize

/-! ## Sparse costs of plans -/

/-- The sparse cost of a coefficient array: `t - 1` gates for a row with `t` nonzeros. -/
def rowCost {i o : ℕ} (c : Fin o → Fin i → ℚ) : ℕ :=
  ∑ b, ((univ.filter fun a => c b a ≠ 0).card - 1)

/-- Sparse gates outside calls, per address, of one of OpenAI's plans. -/
def planSparse {A : ℕ} : {i o : ℕ} → Plan A i o → ℕ
  | _, _, .mix c => rowCost fun b a => value (c b a)
  | _, _, .xor _ => 0
  | _, _, .scale _ _ _ => 0
  | _, _, .child _ => 0
  | _, _, .seq p q => planSparse p + planSparse q
  | _, _, .parallel p q => planSparse p + planSparse q

/-- Sparse gates outside calls, per address, of a rational plan. -/
def qsparse {A : ℕ} : {i o : ℕ} → QPlan A i o → ℕ
  | _, _, .mix c => rowCost c
  | _, _, .scaleRows _ _ _ => 0
  | _, _, .embed p => planSparse p
  | _, _, .seq p q => qsparse p + qsparse q
  | _, _, .parallel p q => qsparse p + qsparse q

variable {K : Type} [Field K] [CharZero K]

lemma rowSupp_cast_card {i o : ℕ} [DecidableEq K] (c : Fin o → Fin i → ℚ) (b : Fin o) :
    (rowSupp (Matrix.of fun b a => ((c b a : ℚ) : K)) b).card
      = (univ.filter fun a => c b a ≠ 0).card := by
  congr 1
  ext a
  simp [rowSupp]

/-- A sparse row mixing at every address. -/
theorem program_mixing_sparse {A h i o : ℕ} (c : Fin o → Fin i → ℚ) :
    PrimeTemplateProgram 2 h (2 ^ ((2 * A - 1) * h)) (-1 : K)
      (Matrix.blockDiagonal fun _ : Addr A h => Matrix.of fun b a => ((c b a : ℚ) : K))
      (rowCost c * 2 ^ (2 * A * h)) 0 := by
  classical
  refine .localCircuit (realizable_mono ((realizable_sparse
    (Matrix.of fun b a => ((c b a : ℚ) : K))).blockDiagonal (Addr A h)) ?_)
  rw [card_addr, mul_comm, rowCost]
  simp only [rowSupp_cast_card]
  rfl

/-- **Every OpenAI plan compiles with sparse local cost.** -/
theorem program_plan_sparse {A : ℕ} (h : ℕ) : ∀ {i o : ℕ} (p : Plan A i o),
    PrimeTemplateProgram 2 h (2 ^ ((2 * A - 1) * h)) (-1 : K)
      ((p.eval h).map (Rat.castHom K)) (planSparse p * 2 ^ (2 * A * h)) (2 * p.calls)
  | _, _, @Plan.mix _ i o c => by
    classical
    have hM : ((Plan.mix (A := A) c).eval h).map (Rat.castHom K)
        = Matrix.blockDiagonal fun _ : Addr A h => Matrix.of fun b a => ((value (c b a) : ℚ) : K) := by
      ext ⟨b, y⟩ ⟨a, x⟩
      change (((if x = y then value (c b a) else 0 : ℚ)) : K) =
        Matrix.blockDiagonal (fun _ : Addr A h => Matrix.of fun b a => ((value (c b a) : ℚ) : K))
          (b, y) (a, x)
      rw [Matrix.blockDiagonal_apply]
      by_cases hxy : x = y
      · subst hxy; simp
      · simp [hxy, Ne.symm hxy]
    rw [hM]
    exact program_cast (program_mixing_sparse (fun b a => value (c b a))) (by simp [planSparse])
      (by simp [Plan.calls])
  | _, _, .xor g => by
    exact program_cast (program_plan h (Plan.xor g)) (by simp [planFree, planSparse]) rfl
  | _, _, .scale q test t => by
    exact program_cast (program_plan h (Plan.scale q test t)) (by simp [planFree, planSparse]) rfl
  | _, _, .child a => by
    exact program_cast (program_plan h (Plan.child a)) (by simp [planFree, planSparse]) rfl
  | _, _, .seq p q => by
    have hp := program_plan_sparse h p
    have hq := program_plan_sparse h q
    rw [Plan.eval, Matrix.map_mul]
    exact program_cast (hp.serial hq) (by simp [planSparse]; ring) (by simp [Plan.calls]; ring)
  | _, _, .parallel p q => by
    have hp := program_plan_sparse h p
    have hq := program_plan_sparse h q
    rw [Plan.eval, map_directSum]
    exact program_cast (program_directSum hp hq) (by simp [planSparse]; ring)
      (by simp [Plan.calls]; ring)

/-- **Every rational plan compiles with sparse local cost.** -/
theorem program_qplan_sparse {A : ℕ} (h : ℕ) : ∀ {i o : ℕ} (p : QPlan A i o),
    PrimeTemplateProgram 2 h (2 ^ ((2 * A - 1) * h)) (-1 : K)
      ((p.eval h).map (Rat.castHom K)) (qsparse p * 2 ^ (2 * A * h)) (2 * p.calls)
  | _, _, @QPlan.mix _ i o c => by
    classical
    have hM : ((QPlan.mix (A := A) c).eval h).map (Rat.castHom K)
        = Matrix.blockDiagonal fun _ : Addr A h => Matrix.of fun b a => ((c b a : ℚ) : K) := by
      ext ⟨b, y⟩ ⟨a, x⟩
      change (((if x = y then c b a else 0 : ℚ)) : K) =
        Matrix.blockDiagonal (fun _ : Addr A h => Matrix.of fun b a => ((c b a : ℚ) : K)) (b, y) (a, x)
      rw [Matrix.blockDiagonal_apply]
      by_cases hxy : x = y
      · subst hxy; simp
      · simp [hxy, Ne.symm hxy]
    rw [hM]
    exact program_cast (program_mixing_sparse c) (by simp [qsparse]) (by simp [QPlan.calls])
  | _, _, .scaleRows q test t => by
    exact program_cast (program_qplan h (QPlan.scaleRows q test t)) (by simp [qfree, qsparse]) rfl
  | _, _, .embed p => by
    exact program_cast (program_plan_sparse h p) (by simp [qsparse]) (by simp [QPlan.calls])
  | _, _, .seq p q => by
    have hp := program_qplan_sparse h p
    have hq := program_qplan_sparse h q
    rw [QPlan.eval, Matrix.map_mul]
    exact program_cast (hp.serial hq) (by simp [qsparse]; ring) (by simp [QPlan.calls]; ring)
  | _, _, .parallel p q => by
    have hp := program_qplan_sparse h p
    have hq := program_qplan_sparse h q
    rw [QPlan.eval, map_directSum]
    exact program_cast (program_directSum hp hq) (by simp [qsparse]; ring)
      (by simp [QPlan.calls]; ring)

/-- **A correct rational plan is a program for `W` copies of `H^{⊗2Ah}`, with sparse local
cost.** -/
theorem program_batch_sparse {A W : ℕ} (p : QPlan A W W) (hp : QPlan.Correct p) (h : ℕ) :
    PrimeTemplateProgram 2 h (2 ^ ((2 * A - 1) * h)) (-1 : K)
      (Matrix.blockDiagonal fun _ : Fin W => primeTransform 2 (2 * A * h) (-1 : K))
      (qsparse p * 2 ^ (2 * A * h)) (2 * p.calls) := by
  have h1 := program_qplan_sparse (K := K) h p
  rw [hp h, target_eq] at h1
  have h2 := (h1.diagonal (fun _ => (2 : K) ^ (A * h)) (fun _ => 1)).reindex
    (batchIndex A W h) (batchIndex A W h)
  convert h2 using 1
  ext u v
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Matrix.smul_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply]
  simp only [Equiv.symm_symm, Equiv.apply_symm_apply, smul_eq_mul, one_mul]
  rw [← mul_assoc, ← mul_pow]
  norm_num

/-- **OpenAI's batch inequality from a correct rational plan, with sparse local cost.** -/
theorem kernelBatch_of_correct_sparse {A W : ℕ} (p : QPlan A W W) (hp : QPlan.Correct p) :
    PrimeKernelBatch 2 (2 * A) W (2 * p.calls) (qsparse p) (-1 : K) := by
  apply primeKernelBatch_of_template
  intro f _
  exact ⟨qsparse p * 2 ^ (2 * A * f), le_rfl, 2 * p.calls, le_rfl, program_batch_sparse p hp f⟩

end Circ

end FTPaper
