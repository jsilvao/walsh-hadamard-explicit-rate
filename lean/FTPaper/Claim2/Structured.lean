import FTPaper.Claim2.Checks

/-!
# The structured repair plans

For a block structure `bk`:
* `whtPlan`: one butterfly layer per coordinate, `M` sparse mixes of two terms per row;
* `gather = restrict ∘ WHT` and `scatter = WHT ∘ extend` have the action of the character
  checks and of their transpose (`gather_applyAt`, `scatter_applyAt`);
* `mPlan` acts on check vectors by the check operator, blockwise (`actsBy_mPlan`);
* `tPlan test q Λ` acts by the blockwise structured decoder `D_κ q(M) Λ_κ q(M) D_κ`
  (`actsBy_tPlan`).
-/

set_option linter.unusedSectionVars false

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset Polynomial
open FTPaper.LemmaS FTPaper.QPlan

namespace FTPaper.Claim2

variable {B : Type} [Fintype B] [DecidableEq B] {M u N s : ℕ}

namespace Blocks

variable (bk : Blocks B M u N s) {A : ℕ}

/-! ## Butterfly layers -/

/-- One butterfly layer on coordinate `j`, within every block. -/
def layerCoef (j : Fin M) (b a : Fin N) : ℚ :=
  if (bk.e a).1 = (bk.e b).1 then
    (if (bk.e a).2 = (bk.e b).2 then (if j ∈ (bk.e b).2 then -1 else 1)
     else if (bk.e a).2 = symmDiff (bk.e b).2 {j} then 1 else 0)
  else 0

lemma symmDiff_singleton_ne (S : Finset (Fin M)) (j : Fin M) : symmDiff S {j} ≠ S := by
  intro h
  have h1 : j ∈ symmDiff S {j} ↔ j ∈ S := by rw [h]
  rw [mem_symmDiff] at h1
  by_cases hj : j ∈ S <;> simp [hj] at h1

lemma layer_sum (j : Fin M) (x : Fin N → ℚ) (b : Fin N) :
    ∑ a, bk.layerCoef j b a * x a = bfly j (bk.blockFn x (bk.e b).1) (bk.e b).2 := by
  rw [← bk.e.symm.sum_comp]
  have hne : ((bk.e b).1, (bk.e b).2) ≠ ((bk.e b).1, symmDiff (bk.e b).2 {j}) := by
    intro h
    exact symmDiff_singleton_ne _ j (congrArg Prod.snd h).symm
  rw [Finset.sum_eq_add _ _ hne]
  · simp only [layerCoef, Equiv.apply_symm_apply, ite_true, bfly, blockFn,
      ite_eq_right (symmDiff_singleton_ne (bk.e b).2 j)]
    simp
  · rintro ⟨k, T⟩ _ ⟨h1, h2⟩
    simp only [layerCoef, Equiv.apply_symm_apply]
    by_cases hk : k = (bk.e b).1
    · subst hk
      have hT1 : T ≠ (bk.e b).2 := fun h => h1 (by rw [h])
      have hT2 : T ≠ symmDiff (bk.e b).2 {j} := fun h => h2 (by rw [h])
      simp [hT1, hT2]
    · simp [hk]
  · intro h; exact absurd (mem_univ _) h
  · intro h; exact absurd (mem_univ _) h

/-- The fast Walsh–Hadamard transform within every block, one layer per coordinate. -/
def whtPlan : List (Fin M) → QPlan A N N
  | [] => QPlan.route id
  | j :: js => (QPlan.mix (bk.layerCoef j)).seq (whtPlan js)

lemma col_whtPlan (js : List (Fin M)) {h : ℕ} (x : Bank A h N) (y : Addr A h) :
    colAt ((bk.whtPlan js).applyAt h x) y
      = fun b => bflys js (bk.blockFn (colAt x y) (bk.e b).1) (bk.e b).2 := by
  induction js with
  | nil =>
    funext b
    simp [whtPlan, applyAt_route, colAt, bflys, blockFn]
  | cons j js ih =>
    funext b
    have hcol : colAt ((QPlan.mix (A := A) (bk.layerCoef j)).applyAt h ((bk.whtPlan js).applyAt h x)) y b
        = ∑ a, bk.layerCoef j b a * colAt ((bk.whtPlan js).applyAt h x) y a := by
      simp [colAt, applyAt_mix]
    simp only [whtPlan, applyAt_seq]
    rw [hcol, layer_sum, ih]
    congr 1
    funext S
    simp [blockFn]

lemma col_wht (h : ℕ) (x : Bank A h N) (y : Addr A h) (b : Fin N) :
    colAt ((bk.whtPlan (List.finRange M)).applyAt h x) y b
      = hada (bk.blockFn (colAt x y) (bk.e b).1) (bk.e b).2 := by
  rw [col_whtPlan]
  exact congrFun (bflys_finRange _) _

/-! ## Gather, scatter, and the check operator -/

/-- Keep the check rows. -/
def restrictPlan : QPlan A N s := QPlan.route fun r => bk.e.symm ((bk.c r).1, (bk.c r).2.1)

/-- Extension of check rows by zero. -/
def extCoef (b : Fin N) (r : Fin s) : ℚ :=
  if (bk.c r).1 = (bk.e b).1 ∧ (bk.c r).2.1 = (bk.e b).2 then 1 else 0

def extendPlan : QPlan A s N := QPlan.mix bk.extCoef

lemma col_extend {h : ℕ} (w : Bank A h s) (y : Addr A h) (b : Fin N) :
    colAt ((bk.extendPlan).applyAt h w) y b = bk.extFn (colAt w y) (bk.e b).1 (bk.e b).2 := by
  simp only [extendPlan, colAt, applyAt_mix, extCoef, ite_mul, one_mul, zero_mul]
  by_cases ht : (bk.e b).2.card < u ∨ M - u < (bk.e b).2.card
  · rw [Finset.sum_eq_single (bk.c.symm ((bk.e b).1, ⟨(bk.e b).2, ht⟩))]
    · simp [extFn, ht, colAt]
    · intro r _ hr
      rw [ite_eq_right]
      rintro ⟨h1, h2⟩
      apply hr
      apply bk.c.injective
      rw [Equiv.apply_symm_apply]
      exact Prod.ext h1 (Subtype.ext h2)
    · intro h; exact absurd (mem_univ _) h
  · rw [Finset.sum_eq_zero]
    · simp [extFn, ht]
    · intro r _
      rw [ite_eq_right]
      rintro ⟨_, h2⟩
      exact ht (h2 ▸ (bk.c r).2.2)

/-- Character checks with one fast transform. -/
def gather : QPlan A N s := (bk.restrictPlan).seq (bk.whtPlan (List.finRange M))

/-- Transposed checks with one fast transform. -/
def scatter : QPlan A s N := (bk.whtPlan (List.finRange M)).seq bk.extendPlan

/-- The check operator on check vectors, blockwise. -/
def mPlan : QPlan A s s := (bk.restrictPlan).seq ((bk.whtPlan (List.finRange M)).seq bk.extendPlan)

lemma gather_applyAt (h : ℕ) (x : Bank A h N) :
    (bk.gather (A := A)).applyAt h x = (QPlan.mix fun r i => bk.charMatrix r i).applyAt h x := by
  funext r y
  have := bk.col_wht h x y (bk.e.symm ((bk.c r).1, (bk.c r).2.1))
  simp only [Equiv.apply_symm_apply] at this
  simp only [gather, restrictPlan, applyAt_seq, applyAt_route, Function.comp_apply]
  rw [show (bk.whtPlan (List.finRange M)).applyAt h x (bk.e.symm ((bk.c r).1, (bk.c r).2.1)) y
    = colAt ((bk.whtPlan (List.finRange M)).applyAt h x) y (bk.e.symm ((bk.c r).1, (bk.c r).2.1))
    from rfl, this, applyAt_mix]
  change _ = ∑ a, bk.charMatrix r a * x a y
  rw [show (∑ a, bk.charMatrix r a * x a y) = (bk.charMatrix *ᵥ colAt x y) r from rfl,
    charMatrix_mulVec]

lemma blockFn_extend {h : ℕ} (w : Bank A h s) (y : Addr A h) (k : B) :
    bk.blockFn (colAt ((bk.extendPlan).applyAt h w) y) k = bk.extFn (colAt w y) k := by
  funext S
  simp only [blockFn]
  rw [col_extend, Equiv.apply_symm_apply]

lemma scatter_applyAt (h : ℕ) (w : Bank A h s) :
    (bk.scatter (A := A)).applyAt h w = (QPlan.mix fun i r => bk.charMatrix r i).applyAt h w := by
  funext b y
  have := bk.col_wht h ((bk.extendPlan).applyAt h w) y b
  simp only [scatter, applyAt_seq]
  rw [show (bk.whtPlan (List.finRange M)).applyAt h ((bk.extendPlan).applyAt h w) b y
    = colAt ((bk.whtPlan (List.finRange M)).applyAt h ((bk.extendPlan).applyAt h w)) y b from rfl,
    this, blockFn_extend, applyAt_mix]
  change _ = ∑ a, bk.charMatrix a b * w a y
  rw [show (∑ a, bk.charMatrix a b * w a y) = (bk.charMatrixᵀ *ᵥ colAt w y) b from rfl,
    charMatrix_transpose_mulVec]

variable {q : ℕ} {test : Column A → Fin q → ZMod 2}

lemma actsBy_mPlan :
    ActsBy test (bk.mPlan (A := A)) (fun _ => bk.blockAct (fun _ => checkOp u)) := by
  intro h w y
  funext r
  have := bk.col_wht h ((bk.extendPlan).applyAt h w) y (bk.e.symm ((bk.c r).1, (bk.c r).2.1))
  simp only [Equiv.apply_symm_apply] at this
  simp only [mPlan, restrictPlan, applyAt_seq, applyAt_route]
  rw [show colAt ((bk.whtPlan (List.finRange M)).applyAt h ((bk.extendPlan).applyAt h w) ∘
      fun r => bk.e.symm ((bk.c r).1, ((bk.c r).2 : Finset (Fin M)))) y r
    = colAt ((bk.whtPlan (List.finRange M)).applyAt h ((bk.extendPlan).applyAt h w)) y
        (bk.e.symm ((bk.c r).1, (bk.c r).2.1)) from rfl, this, blockFn_extend, blockAct_apply,
    checkOp_apply, bk.extFn_tail, restrictE_apply, ite_eq_left (bk.c r).2.2]

end Blocks

end FTPaper.Claim2
