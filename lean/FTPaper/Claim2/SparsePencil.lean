import FTPaper.Claim2.Sparse
import FTPaper.LocalCostOAI

/-!
# The rectangle pencil with row-diagonal entries (paper: Lemma 10.2)

OpenAI's pencil (`KernelPassRectPencil.lean`) assembles each rectangle with `entries`, an array
of single-row plans over ALL pairs of bank rows: `R²` entries per rectangle, where `R` is the
number of rows (exponential in the number of queries). Our stage coefficients are diagonal in
the rows of a label, so only pairs `((w, l), (v, l))` with the same row `l` carry nonzero
entries. Here the rectangles are rebuilt over those pairs only:
* `dentries`: entries over `L × L × W` instead of `(L × W)²`;
* `freeS`, `chargedS`, `pencilS`: OpenAI's free rectangle, charged rectangle and pencil, with
  row-diagonal entries.

`block_pencilS`: for diagonal coefficients the new pencil has OpenAI's block matrices, hence
the same matrix (`eval_eq_of_block`; for the template's stage, `eval_ourPencilS` in
`Stage.lean`); `calls_pencilS`: it makes the same calls.

Source: adapted from OpenAI's `KernelPassRectBank.lean` (`entries`, `block_entries`),
`KernelPassRectFree.lean` (`free`, `block_free`), `KernelPassRectCharged.lean` (`charged`,
`block_charged`, and the private `fanout`, `collect`) and `KernelPassRectPencil.lean` (`pencil`)
in openai/math, commit 3344da5, Apache License 2.0. Changes: the entries are restricted to
row-diagonal pairs, and the block lemmas are proved for diagonal stage coefficients.
-/

set_option linter.unusedSectionVars false

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open OAI.Computability.NearSquareRoot.KernelPass.Rect
open Matrix Finset

namespace FTPaper.Claim2

variable {A : ℕ} {L W J F C : Type} [Fintype L] [Fintype W] [Fintype J] [Fintype F] [Fintype C]
  [DecidableEq L] [DecidableEq W]

/-! ## Row-diagonal entries -/

/-- Entries over the pairs `((w, l), (v, l))` only, indexed by `(w, v, l)`. -/
noncomputable def dentries (p : L × W → L × W → Plan A 1 1) : On A (L × W) (L × W) :=
  (mixing (A := A) (fun (b : L × W) (k : L × L × W) =>
      if k.1 = b.1 ∧ k.2.2 = b.2 then ((1 : ℤ), 0) else (0, 0))).seq
    ((diagonal (fun k : L × L × W => p (k.1, k.2.2) (k.2.1, k.2.2))).seq
      (mixing (fun (k : L × L × W) (a : L × W) =>
        if k.2.1 = a.1 ∧ k.2.2 = a.2 then ((1 : ℤ), 0) else (0, 0))))

lemma value_pick (c : Prop) [Decidable c] :
    value (if c then ((1 : ℤ), 0) else (0, 0)) = if c then 1 else 0 := by
  split <;> simp [value]

theorem block_dentries (p : L × W → L × W → Plan A 1 1) (h : ℕ) (b a : L × W) :
    block (I := L × W) (O := L × W) (dentries p) h b a
      = if b.2 = a.2 then oneRow ((p b a).eval h) else 0 := by
  classical
  obtain ⟨w, k⟩ := b
  obtain ⟨v, l⟩ := a
  unfold dentries
  rw [block_seq (J := L × L × W), block_seq (J := L × L × W), block_mixing, block_diagonal,
    block_mixing, Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, Matrix.of_apply, value_pick, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_eq_single (w, v, k)]
  · by_cases hkl : k = l
    · subst hkl
      simp
    · simp [hkl]
  · rintro ⟨w', v', l'⟩ _ hne
    by_cases h1 : w' = w ∧ l' = k
    · by_cases h2 : v' = v ∧ l' = l
      · exfalso; apply hne; rw [h1.1, h2.1, h1.2]
      · simp [h2]
    · simp [h1]
  · intro h; exact absurd (mem_univ _) h

/-- With entries that vanish off the row diagonal, `dentries` has the blocks of `entries`. -/
theorem block_dentries_eq (p : L × W → L × W → Plan A 1 1) (h : ℕ)
    (hp : ∀ b a : L × W, b.2 ≠ a.2 → oneRow ((p b a).eval h) = 0) :
    block (I := L × W) (O := L × W) (dentries p) h = block (I := L × W) (O := L × W) (entries p) h := by
  funext b a
  rw [block_dentries, block_entries, Matrix.of_apply]
  split_ifs with hba
  · rfl
  · exact (hp b a hba).symm

theorem calls_dentries (p : L × W → L × W → Plan A 1 1) :
    (dentries p).calls = ∑ k : L × L × W, (p (k.1, k.2.2) (k.2.1, k.2.2)).calls := by
  simp [dentries, Plan.calls, mixing, calls_diagonal]

/-! ## Free rectangles -/

/-- OpenAI's free rectangle with row-diagonal entries. -/
noncomputable def freeS (src dst : Finset L) (weight : Coefficient) (B : J → W → W → Coefficient)
    (S T : L → Single A) (M : J → L → L → Single A) : On A (L × W) (L × W) :=
  (side dst T).seq ((dentries (fun (b a : L × W) =>
    times weight (total fun j => times (B j b.2 a.2) (M j b.1 a.1)))).seq (side src S))

theorem block_freeS (src dst : Finset L) (weight : Coefficient) (B : J → W → W → Coefficient)
    (S T : L → Single A) (M : J → L → L → Single A)
    (hB : ∀ j k l, k ≠ l → value (B j k l) = 0) (h : ℕ) :
    block (I := L × W) (O := L × W) (freeS src dst weight B S T M) h
      = block (I := L × W) (O := L × W) (free src dst weight B S T M) h := by
  unfold freeS free
  rw [block_seq (J := L × W), block_seq (J := L × W), block_seq (J := L × W),
    block_seq (J := L × W), block_dentries_eq]
  intro b a hba
  rw [matrix_times, oneRow_total]
  simp only [matrix_times, hB _ _ _ hba, zero_smul, Finset.sum_const_zero, smul_zero]

theorem calls_freeS (src dst : Finset L) (weight : Coefficient) (B : J → W → W → Coefficient)
    (S T : L → Single A) (M : J → L → L → Single A) (hm : ∀ j w v, (M j w v).calls = 0) :
    (freeS src dst weight B S T M).calls = (free src dst weight B S T M).calls := by
  simp [freeS, free, Plan.calls, calls_dentries, calls_entries, calls_total, hm]

/-! ## Charged rectangles -/

/-- Broadcast each internal row to its targets. -/
noncomputable def fanoutS (T : Finset L) (weight : Coefficient) (dstOut : L → Plan A 1 1) :
    On A W (L × W) :=
  (diagonal (fun b : L × W => if b.1 ∈ T then times weight (dstOut b.1) else emptyPlan)).seq
    (mixing (fun (b : L × W) (l : W) => if b.2 = l then ((1 : ℤ), 0) else (0, 0)))

/-- Collect the sources into the internal rows, with diagonal coefficients. -/
noncomputable def collectS (S : Finset L) (B : W → W → Coefficient) (srcIn : L → Plan A 1 1) :
    On A (L × W) W :=
  (mixing (fun (k : W) (a : L × W) => if a.2 = k then ((1 : ℤ), 0) else (0, 0))).seq
    (diagonal (fun a : L × W => if a.1 ∈ S then times (B a.2 a.2) (srcIn a.1) else emptyPlan))

/-- OpenAI's charged rectangle with row-diagonal fan-out and fan-in. -/
noncomputable def chargedS (S T : Finset L) (weight : Coefficient) (B : W → W → Coefficient)
    (srcIn dstOut : L → Plan A 1 1) (common : Plan A 1 1) : On A (L × W) (L × W) :=
  (fanoutS T weight dstOut).seq ((diagonal (fun _ : W => common)).seq (collectS S B srcIn))

theorem block_fanoutS (T : Finset L) (weight : Coefficient) (dstOut : L → Plan A 1 1) (h : ℕ)
    (b : L × W) (l : W) :
    block (I := W) (O := L × W) (fanoutS T weight dstOut) h b l
      = if b.2 = l then oneRow ((if b.1 ∈ T then times weight (dstOut b.1) else emptyPlan).eval h)
        else 0 := by
  classical
  unfold fanoutS
  rw [block_seq (J := L × W), block_diagonal, block_mixing]
  simp only [Matrix.diagonal_mul, Matrix.of_apply, value_pick, ite_smul, one_smul, zero_smul,
    mul_ite, mul_one, mul_zero]

theorem block_collectS (S : Finset L) (B : W → W → Coefficient) (srcIn : L → Plan A 1 1) (h : ℕ)
    (k : W) (a : L × W) :
    block (I := L × W) (O := W) (collectS S B srcIn) h k a
      = if a.2 = k then oneRow ((if a.1 ∈ S then times (B a.2 a.2) (srcIn a.1) else emptyPlan).eval h)
        else 0 := by
  classical
  unfold collectS
  rw [block_seq (J := L × W), block_diagonal, block_mixing]
  simp only [Matrix.mul_diagonal, Matrix.of_apply, value_pick, ite_smul, one_smul, zero_smul,
    ite_mul, one_mul, zero_mul]

theorem block_chargedS (S T : Finset L) (weight : Coefficient) (B : W → W → Coefficient)
    (srcIn dstOut : L → Plan A 1 1) (common : Plan A 1 1)
    (hB : ∀ k l, k ≠ l → value (B k l) = 0) (h : ℕ) (w v : L) (k l : W) :
    block (I := L × W) (O := L × W) (chargedS S T weight B srcIn dstOut common) h (w, k) (v, l)
      = block (I := L × W) (O := L × W) (charged S T weight B srcIn dstOut common) h (w, k) (v, l) := by
  classical
  rw [block_charged]
  unfold chargedS
  rw [block_seq (J := W), block_seq (J := W), block_diagonal, Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, block_fanoutS, block_collectS]
  rw [Finset.sum_eq_single k]
  · by_cases hkl : l = k
    · subst hkl
      by_cases hv : v ∈ S <;> by_cases hw : w ∈ T <;>
        simp [hv, hw, matrix_times, Matrix.mul_assoc, smul_comm (value weight) (value (B l l))]
    · have hB' := hB k l (Ne.symm hkl)
      simp [hkl, hB']
  · intro k' _ hk'
    simp [Ne.symm hk']
  · intro h; exact absurd (mem_univ _) h

theorem calls_chargedS (S T : Finset L) (weight : Coefficient) (B : W → W → Coefficient)
    (srcIn dstOut : L → Plan A 1 1) (common : Plan A 1 1)
    (hsrc : ∀ v, (srcIn v).calls = 0) (hdst : ∀ w, (dstOut w).calls = 0) :
    (chargedS S T weight B srcIn dstOut common).calls = Fintype.card W * common.calls := by
  simp [chargedS, fanoutS, collectS, Plan.calls, mixing, calls_diagonal, apply_ite, hsrc, hdst]

/-! ## The pencil -/

/-- OpenAI's pencil with row-diagonal rectangles. -/
noncomputable def pencilS (Frees : F → FreeData A L J) (Charged : C → ChargedData A L J)
    (B₀ : W → W → Coefficient) (B : J → W → W → Coefficient) : On A (L × W) (L × W) :=
  addPlan (constantPart B₀) (addPlan
    (total fun r => freeS (Frees r).sources (Frees r).destinations (Frees r).weight B
      (Frees r).source (Frees r).target (Frees r).middle)
    (total fun r => total fun j => chargedS (Charged r).sources (Charged r).destinations
      (Charged r).weight (B j) ((Charged r).input j) ((Charged r).output j) ((Charged r).common j)))

theorem block_pencilS (Frees : F → FreeData A L J) (Charged : C → ChargedData A L J)
    (B₀ : W → W → Coefficient) (B : J → W → W → Coefficient)
    (hB : ∀ j k l, k ≠ l → value (B j k l) = 0) (h : ℕ) :
    block (I := L × W) (O := L × W) (pencilS Frees Charged B₀ B) h
      = block (I := L × W) (O := L × W) (pencil Frees Charged B₀ B) h := by
  unfold pencilS pencil
  rw [block_addPlan, block_addPlan, block_addPlan, block_addPlan, block_total, block_total,
    block_total, block_total]
  congr 2
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [FreeData.plan, block_freeS _ _ _ _ _ _ _ hB]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [ChargedData.plan, block_total, block_total]
    refine Finset.sum_congr rfl fun j _ => ?_
    funext b a
    exact block_chargedS _ _ _ _ _ _ _ (hB j) h b.1 a.1 b.2 a.2

theorem calls_pencilS (Frees : F → FreeData A L J) (Charged : C → ChargedData A L J)
    (B₀ : W → W → Coefficient) (B : J → W → W → Coefficient) :
    (pencilS Frees Charged B₀ B).calls = (pencil Frees Charged B₀ B).calls := by
  unfold pencilS pencil
  rw [calls_addPlan, calls_addPlan, calls_addPlan, calls_addPlan, calls_total, calls_total,
    calls_total, calls_total]
  congr 2
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [FreeData.plan, calls_freeS _ _ _ _ _ _ _ (Frees r).middle_free]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [ChargedData.plan, calls_total, calls_total]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [calls_chargedS _ _ _ _ _ _ _ ((Charged r).input_free j) ((Charged r).output_free j),
      calls_charged _ _ _ _ _ _ _ ((Charged r).input_free j) ((Charged r).output_free j)]

/-- Equal blocks give equal matrices. -/
theorem eval_eq_of_block {I O : Type} [Fintype I] [Fintype O] (p q : On A I O) (h : ℕ)
    (hb : block (I := I) (O := O) p h = block (I := I) (O := O) q h) : p.eval h = q.eval h := by
  ext ⟨b, y⟩ ⟨a, x⟩
  have := congrFun (congrFun (congrFun (congrFun hb ((Fintype.equivFin O).symm b))
    ((Fintype.equivFin I).symm a)) y) x
  simpa [block] using this

end FTPaper.Claim2
