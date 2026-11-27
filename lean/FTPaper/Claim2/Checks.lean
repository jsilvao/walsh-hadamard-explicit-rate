import FTPaper.Claim2.Local
import FTPaper.LemmaS.BlockTable
import FTPaper.Repair

/-!
# Structured checks and the structured table, as plans (Lemma S at the plan level)

Rows of a bank are pairs (block, subset of `Fin M`); check rows are pairs (block, tail subset).
* `gather` and `scatter` compute the character checks `H r i = [same block] (-1)^{|γ ∩ S|}`
  and their transpose with one fast Walsh–Hadamard transform: `M` butterfly layers of two
  terms per row (`gather_applyAt`, `scatter_applyAt`).
* `mPlan` applies the check operator `M = P_E H P_E` blockwise to check vectors.
* `isTable_struct`: the blockwise structured decoder is a table for the character checks
  (`IsTable`, `FTPaper/Repair.lean`), whenever the predictor errs only on translates of the
  tails.
-/

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset Polynomial
open FTPaper.LemmaS

set_option linter.unusedSectionVars false

namespace FTPaper.Claim2

/-- Tails as a type. -/
abbrev Tail (M u : ℕ) := {S : Finset (Fin M) // S.card < u ∨ M - u < S.card}

/-- A block structure: rows are (block, subset) and checks are (block, tail subset). -/
structure Blocks (B : Type) (M u N s : ℕ) where
  e : Fin N ≃ B × Finset (Fin M)
  c : Fin s ≃ B × Tail M u

variable {B : Type} [Fintype B] [DecidableEq B] {M u N s : ℕ}

namespace Blocks

variable (bk : Blocks B M u N s)

/-! ## Block views of row and check vectors -/

/-- Block `k` of a row vector, as a function on subsets. -/
def blockFn (x : Fin N → ℚ) (k : B) : Fn M := fun S => x (bk.e.symm (k, S))

/-- Block `k` of a check vector, extended by zero off the tails. -/
def extFn (w : Fin s → ℚ) (k : B) : Fn M := fun S =>
  if h : S.card < u ∨ M - u < S.card then w (bk.c.symm (k, ⟨S, h⟩)) else 0

lemma extFn_tail (w : Fin s → ℚ) (k : B) : restrictE u (bk.extFn w k) = bk.extFn w k := by
  funext S
  rw [restrictE_apply]
  split_ifs with h
  · rfl
  · simp [extFn, h]

lemma extFn_c (w : Fin s → ℚ) (r : Fin s) : bk.extFn w (bk.c r).1 (bk.c r).2.1 = w r := by
  simp only [extFn, (bk.c r).2.2, dite_true]
  congr 1
  apply bk.c.injective
  simp

lemma extFn_add (w w' : Fin s → ℚ) (k : B) :
    bk.extFn (w + w') k = bk.extFn w k + bk.extFn w' k := by
  funext S; simp only [extFn, Pi.add_apply]; split_ifs <;> simp

lemma extFn_smul (a : ℚ) (w : Fin s → ℚ) (k : B) : bk.extFn (a • w) k = a • bk.extFn w k := by
  funext S; simp only [extFn, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp

/-- Operators that keep functions supported on the tails. -/
def TailPres (X : Module.End ℚ (Fn M)) : Prop :=
  ∀ f, restrictE u f = f → restrictE u (X f) = X f

/-- Apply a block operator `X k` to block `k` of a check vector. -/
def blockAct (X : B → Module.End ℚ (Fn M)) : Module.End ℚ (Fin s → ℚ) where
  toFun w r := X (bk.c r).1 (bk.extFn w (bk.c r).1) (bk.c r).2.1
  map_add' w w' := by funext r; simp only [extFn_add, map_add, Pi.add_apply]
  map_smul' a w := by
    funext r; simp only [extFn_smul, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

lemma blockAct_apply (X : B → Module.End ℚ (Fn M)) (w : Fin s → ℚ) (r : Fin s) :
    bk.blockAct X w r = X (bk.c r).1 (bk.extFn w (bk.c r).1) (bk.c r).2.1 := rfl

lemma extFn_blockAct (X : B → Module.End ℚ (Fn M)) (hX : ∀ k, TailPres (u := u) (X k))
    (w : Fin s → ℚ) (k : B) : bk.extFn (bk.blockAct X w) k = X k (bk.extFn w k) := by
  funext S
  by_cases h : S.card < u ∨ M - u < S.card
  · simp only [extFn, h, dite_true, blockAct_apply, Equiv.apply_symm_apply]
  · have := congrFun (hX k _ (bk.extFn_tail w k)) S
    rw [restrictE_apply, ite_eq_right h] at this
    simp only [extFn, h, dite_false]
    exact this

lemma blockAct_mul (X Y : B → Module.End ℚ (Fn M)) (hY : ∀ k, TailPres (u := u) (Y k)) :
    bk.blockAct X * bk.blockAct Y = bk.blockAct (fun k => X k * Y k) := by
  refine LinearMap.ext fun w => ?_
  funext r
  rw [Module.End.mul_apply, blockAct_apply, extFn_blockAct _ _ hY, blockAct_apply,
    Module.End.mul_apply]

lemma blockAct_one : bk.blockAct (fun _ => (1 : Module.End ℚ (Fn M))) = 1 := by
  refine LinearMap.ext fun w => ?_
  funext r
  rw [blockAct_apply, Module.End.one_apply, extFn_c, Module.End.one_apply]

lemma blockAct_add (X Y : B → Module.End ℚ (Fn M)) :
    bk.blockAct (fun k => X k + Y k) = bk.blockAct X + bk.blockAct Y := by
  refine LinearMap.ext fun w => ?_
  funext r
  simp only [blockAct_apply, LinearMap.add_apply, Pi.add_apply]

lemma blockAct_smul (a : ℚ) (X : B → Module.End ℚ (Fn M)) :
    bk.blockAct (fun k => a • X k) = a • bk.blockAct X := by
  refine LinearMap.ext fun w => ?_
  funext r
  simp only [blockAct_apply, LinearMap.smul_apply, Pi.smul_apply]

lemma blockAct_sum (n : ℕ) (X : ℕ → B → Module.End ℚ (Fn M)) :
    bk.blockAct (fun k => ∑ t ∈ Finset.range n, X t k) = ∑ t ∈ Finset.range n, bk.blockAct (X t) := by
  induction n with
  | zero =>
    refine LinearMap.ext fun w => ?_
    funext r
    simp [blockAct_apply]
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    rw [bk.blockAct_add, ih]

lemma tailPres_pow {X : Module.End ℚ (Fn M)} (hX : TailPres (u := u) X) (t : ℕ) :
    TailPres (u := u) (X ^ t) := by
  induction t with
  | zero => intro f hf; simpa using hf
  | succ t ih =>
    intro f hf
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (hX f hf)

lemma blockAct_pow (X : Module.End ℚ (Fn M)) (hX : TailPres (u := u) X) (t : ℕ) :
    bk.blockAct (fun _ => X) ^ t = bk.blockAct (fun _ => X ^ t) := by
  induction t with
  | zero => rw [pow_zero, pow_zero, blockAct_one]
  | succ t ih =>
    rw [pow_succ, ih, blockAct_mul _ _ _ (fun _ => hX), pow_succ]

/-! ## Tail-preserving operators -/

lemma tailPres_checkOp : TailPres (u := u) (checkOp (m := M) u) :=
  fun f _ => restrictE_checkOp u f

lemma tailPres_aeval (p : ℚ[X]) : TailPres (u := u) (aeval (checkOp (m := M) u) p) := by
  intro f hf
  rw [restrictE_aeval, hf]

lemma tailPres_twistL (κ : Finset (Fin M)) : TailPres (u := u) (twistL κ) := by
  intro f hf
  rw [restrictE_twistL, hf]

lemma tailPres_scaleL (Λ : Fn M) : TailPres (u := u) (scaleL Λ) := by
  intro f hf
  funext S
  have := congrFun hf S
  simp only [restrictE_apply, scaleL_apply] at this ⊢
  split_ifs with h
  · rfl
  · rw [ite_eq_right h] at this
    rw [← this, mul_zero]

lemma tailPres_mul {X Y : Module.End ℚ (Fn M)} (hX : TailPres (u := u) X)
    (hY : TailPres (u := u) Y) : TailPres (u := u) (X * Y) :=
  fun f hf => by rw [Module.End.mul_apply]; exact hX _ (hY f hf)

lemma tailPres_decodeL (q : ℚ[X]) (κ : Finset (Fin M)) (Λ : Fn M) :
    TailPres (u := u) (decodeL u q κ Λ) := by
  unfold decodeL
  exact tailPres_mul (tailPres_mul (tailPres_mul (tailPres_mul (tailPres_twistL κ)
    (tailPres_aeval q)) (tailPres_scaleL Λ)) (tailPres_aeval q)) (tailPres_twistL κ)

/-! ## The character checks -/

/-- The character checks: `H r i = [same block] (-1)^{|γ ∩ S|}`. -/
def charMatrix : Matrix (Fin s) (Fin N) ℚ := fun r i =>
  if (bk.e i).1 = (bk.c r).1 then (-1 : ℚ) ^ ((bk.c r).2.1 ∩ (bk.e i).2).card else 0

lemma sum_rows (f : Fin N → ℚ) : ∑ i, f i = ∑ k : B, ∑ S : Finset (Fin M), f (bk.e.symm (k, S)) := by
  rw [← bk.e.symm.sum_comp, Fintype.sum_prod_type]

lemma charMatrix_mulVec (v : Fin N → ℚ) (r : Fin s) :
    (bk.charMatrix *ᵥ v) r = hada (bk.blockFn v (bk.c r).1) (bk.c r).2.1 := by
  simp only [Matrix.mulVec, dotProduct, charMatrix]
  rw [bk.sum_rows]
  simp only [Equiv.apply_symm_apply, ite_mul, zero_mul]
  rw [Fintype.sum_eq_single (bk.c r).1]
  · simp [hada_apply, blockFn]
  · intro k hk
    exact Finset.sum_eq_zero fun S _ => ite_eq_right hk

lemma charMatrix_transpose_mulVec (w : Fin s → ℚ) (i : Fin N) :
    (bk.charMatrixᵀ *ᵥ w) i = hada (bk.extFn w (bk.e i).1) (bk.e i).2 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, charMatrix, hada_apply]
  rw [← bk.c.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply, ite_mul, zero_mul]
  rw [Fintype.sum_eq_single (bk.e i).1]
  · rw [FTPaper.sum_eq_sum_subtype (fun T : Finset (Fin M) => T.card < u ∨ M - u < T.card)
      (g := fun δ => (-1 : ℚ) ^ ((bk.e i).2 ∩ δ).card * bk.extFn w (bk.e i).1 δ)
      (fun T hT => by simp [extFn, hT])]
    refine Finset.sum_congr rfl fun γ _ => ?_
    simp only [extFn, γ.2, ite_true, dite_true]
    rw [inter_comm]
  · intro k hk
    exact Finset.sum_eq_zero fun γ _ => ite_eq_right (Ne.symm hk)

end Blocks

end FTPaper.Claim2
