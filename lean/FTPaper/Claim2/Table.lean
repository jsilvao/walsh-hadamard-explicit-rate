import FTPaper.Claim2.Structured
import FTPaper.QTemplate

/-!
# The structured table as a plan, and its correctness

* `tPlan`: sign twist, Horner for `q(M)`, division, Horner for `q(M)`, sign twist. It acts by
  the blockwise structured decoder (`actsBy_tPlan`).
* `tablePlan`: `(U, U') ↦ (T (U - z U'), z T (U - z U'))`, the shape of `tabMatrix`.
* `isTable_struct`: the blockwise decoder is a table (`IsTable`) for the character checks.
-/

set_option linter.unusedSectionVars false

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset Polynomial
open FTPaper.LemmaS FTPaper.QPlan

namespace FTPaper.Claim2

/-- The support of a signature. -/
def supK {M : ℕ} (κ : Fin M → ZMod 2) : Finset (Fin M) := univ.filter fun j => κ j = 1

/-- `(U, U') ↦ U - z U'`. -/
def diffPlan {A s M : ℕ} (test : Column A → Fin M → ZMod 2) (z : (Fin M → ZMod 2) → ℚ) :
    QPlan A (s + s) s :=
  (QPlan.combine (fun _ => 1) (fun _ => -1)).seq
    (QPlan.scaleRows M test fun r κ => if (r : ℕ) < s then 1 else z κ)

lemma colAt_diffPlan {A s M : ℕ} (test : Column A → Fin M → ZMod 2) (z : (Fin M → ZMod 2) → ℚ)
    {h : ℕ} (w : Bank A h (s + s)) (y : Addr A h) :
    colAt ((diffPlan (s := s) test z).applyAt h w) y
      = leftPart (colAt w y) - z (∑ t, test (y t)) • rightPart (colAt w y) := by
  rw [diffPlan, applyAt_seq, ← append_parts ((QPlan.scaleRows M test _).applyAt h w),
    applyAt_combine]
  funext r
  simp only [colAt, applyAt_scaleRows, leftPart, rightPart, Function.comp_apply, Fin.val_castAdd,
    Fin.val_natAdd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [ite_eq_left r.isLt, ite_eq_right (by omega)]
  ring

variable {B : Type} [Fintype B] [DecidableEq B] {M u N s : ℕ}

namespace Blocks

variable (bk : Blocks B M u N s) {A : ℕ} (test : Column A → Fin M → ZMod 2)

/-- The sign twist `D_κ` on check rows. -/
def twistPlan : QPlan A s s :=
  QPlan.scaleRows M test fun r κ => (-1 : ℚ) ^ ((bk.c r).2.1 ∩ supK κ).card

/-- A blockwise, signature-dependent scaling of check rows. -/
def scalePlan (Λ : B → (Fin M → ZMod 2) → Fn M) : QPlan A s s :=
  QPlan.scaleRows M test fun r κ => Λ (bk.c r).1 κ (bk.c r).2.1

/-- `q(M)` by Horner's rule on the check operator. -/
def qPlan (q : ℚ[X]) : QPlan A s s := QPlan.horner bk.mPlan (fun t _ => q.coeff t) q.natDegree

/-- The structured decoder `D_κ q(M) Λ_κ q(M) D_κ`. -/
def tPlan (q : ℚ[X]) (Λ : B → (Fin M → ZMod 2) → Fn M) : QPlan A s s :=
  (bk.twistPlan test).seq ((bk.qPlan q).seq ((bk.scalePlan test Λ).seq
    ((bk.qPlan q).seq (bk.twistPlan test))))

lemma actsBy_twistPlan :
    ActsBy test (bk.twistPlan test) (fun κ => bk.blockAct (fun _ => twistL (supK κ))) := by
  refine actsBy_congr (actsBy_scaleRows _) fun κ v => ?_
  funext r
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_diagonal, blockAct_apply, twistL_apply, extFn_c]

lemma actsBy_scalePlan (Λ : B → (Fin M → ZMod 2) → Fn M) :
    ActsBy test (bk.scalePlan test Λ) (fun κ => bk.blockAct (fun k => scaleL (Λ k κ))) := by
  refine actsBy_congr (actsBy_scaleRows _) fun κ v => ?_
  funext r
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_diagonal, blockAct_apply, scaleL_apply, extFn_c]

lemma actsBy_qPlan (q : ℚ[X]) :
    ActsBy test (bk.qPlan (A := A) q) (fun _ => bk.blockAct (fun _ => aeval (checkOp u) q)) := by
  refine actsBy_congr (actsBy_horner (bk.actsBy_mPlan (test := test)) _ _) fun κ v => ?_
  have h1 : ∀ t ∈ Finset.range (q.natDegree + 1), q.coeff t • bk.blockAct (fun _ => checkOp u) ^ t
      = bk.blockAct (fun _ => q.coeff t • checkOp (m := M) u ^ t) := by
    intro t _
    rw [blockAct_pow _ _ tailPres_checkOp, ← blockAct_smul]
  rw [Finset.sum_congr rfl h1, ← blockAct_sum, aeval_eq_sum_range]

lemma blockAct_comp (X Y : B → Module.End ℚ (Fn M)) (hY : ∀ k, TailPres (u := u) (Y k))
    (v : Fin s → ℚ) : bk.blockAct X (bk.blockAct Y v) = bk.blockAct (fun k => X k * Y k) v := by
  rw [← Module.End.mul_apply, blockAct_mul _ _ _ hY]

lemma actsBy_tPlan (q : ℚ[X]) (Λ : B → (Fin M → ZMod 2) → Fn M) :
    ActsBy test (bk.tPlan test q Λ)
      (fun κ => bk.blockAct (fun k => decodeL u q (supK κ) (Λ k κ))) := by
  have h := actsBy_seq (bk.actsBy_twistPlan test) (actsBy_seq (bk.actsBy_qPlan test q)
    (actsBy_seq (bk.actsBy_scalePlan test Λ) (actsBy_seq (bk.actsBy_qPlan test q)
      (bk.actsBy_twistPlan test))))
  refine actsBy_congr h fun κ v => ?_
  simp only [LinearMap.comp_apply]
  have t5 : ∀ k, TailPres (u := u) ((fun _ : B => twistL (m := M) (supK κ)) k) :=
    fun _ => tailPres_twistL _
  rw [bk.blockAct_comp _ _ t5]
  have t4 : ∀ _k : B, TailPres (u := u) (aeval (checkOp (m := M) u) q * twistL (supK κ)) :=
    fun _ => tailPres_mul (tailPres_aeval q) (tailPres_twistL _)
  rw [bk.blockAct_comp _ _ t4]
  have t3 : ∀ k, TailPres (u := u) (scaleL (Λ k κ) * (aeval (checkOp (m := M) u) q *
      twistL (supK κ))) := fun k => tailPres_mul (tailPres_scaleL _) (t4 k)
  rw [bk.blockAct_comp _ _ t3]
  have t2 : ∀ k, TailPres (u := u) (aeval (checkOp (m := M) u) q * (scaleL (Λ k κ) *
      (aeval (checkOp (m := M) u) q * twistL (supK κ)))) :=
    fun k => tailPres_mul (tailPres_aeval q) (t3 k)
  rw [bk.blockAct_comp _ _ t2]
  simp only [decodeL, mul_assoc]

/-! ## The full table `(U, U') ↦ (T (U - z U'), z T (U - z U'))` -/

/-- The structured table. -/
def tablePlan (q : ℚ[X]) (Λ : B → (Fin M → ZMod 2) → Fn M) (z : (Fin M → ZMod 2) → ℚ) :
    QPlan A (s + s) (s + s) :=
  ((QPlan.route id).fork (QPlan.scaleRows M test fun _ κ => z κ)).seq
    ((bk.tPlan test q Λ).seq (diffPlan (s := s) test z))

lemma colAt_tablePlan (q : ℚ[X]) (Λ : B → (Fin M → ZMod 2) → Fn M) (z : (Fin M → ZMod 2) → ℚ)
    {h : ℕ} (w : Bank A h (s + s)) (y : Addr A h) :
    let κ := ∑ t, test (y t)
    let T := bk.blockAct (fun k => decodeL u q (supK κ) (Λ k κ))
    colAt ((bk.tablePlan test q Λ z).applyAt h w) y
      = Fin.append (T (leftPart (colAt w y) - z κ • rightPart (colAt w y)))
          (z κ • T (leftPart (colAt w y) - z κ • rightPart (colAt w y))) := by
  intro κ T
  rw [tablePlan, applyAt_seq, applyAt_fork, colAt_append, applyAt_route, Function.comp_id,
    applyAt_seq]
  have hT : colAt ((bk.tPlan test q Λ).applyAt h ((diffPlan (s := s) test z).applyAt h w)) y
      = T (leftPart (colAt w y) - z κ • rightPart (colAt w y)) := by
    rw [bk.actsBy_tPlan test q Λ, colAt_diffPlan]
  rw [hT]
  congr 1
  funext r
  simp only [colAt, applyAt_scaleRows, Pi.smul_apply, smul_eq_mul]
  exact congrArg _ (congrFun hT r)

/-! ## Correctness of the structured table -/

/-- **The structured decoder is a table for the character checks.** -/
theorem isTable_struct {q : ℚ[X]}
    (hq1 : ∀ f : Fn M, aeval (checkOp u) q (checkOp u f) = restrictE u f)
    (hq2 : ∀ f : Fn M, checkOp u (aeval (checkOp u) q f) = restrictE u f)
    (p : Fin N → ℚ) (z : ℚ) (κ : Finset (Fin M))
    (hp : ∀ i, p i ≠ z →
      (symmDiff (bk.e i).2 κ).card < u ∨ M - u < (symmDiff (bk.e i).2 κ).card) :
    IsTable bk.charMatrix p z
      (bk.blockAct fun k => decodeL u q κ (divW κ (fun S => p (bk.e.symm (k, S)) - z))) := by
  intro X i hi
  set g : B → Fn M := fun k S => p (bk.e.symm (k, S)) - z with hgdef
  have hY : bk.charMatrix *ᵥ (p * X) - z • (bk.charMatrix *ᵥ X)
      = bk.charMatrix *ᵥ (fun i => (p i - z) * X i) := by
    rw [← Matrix.mulVec_smul, ← Matrix.mulVec_sub]
    congr 1
    funext i
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hext : ∀ k, bk.extFn (bk.charMatrix *ᵥ (p * X) - z • (bk.charMatrix *ᵥ X)) k
      = restrictE u (hada fun S => g k S * bk.blockFn X k S) := by
    intro k
    funext S
    simp only [extFn, restrictE_apply]
    split_ifs with h
    · rw [hY, charMatrix_mulVec, Equiv.apply_symm_apply]
      rfl
    · rfl
  have hdec : ∀ k, TailPres (u := u) (decodeL u q κ (divW κ (g k))) :=
    fun k => tailPres_decodeL q κ _
  rw [charMatrix_transpose_mulVec, extFn_blockAct _ _ hdec, hext]
  have hg : ∀ S, g (bk.e i).1 S ≠ 0 →
      (symmDiff S κ).card < u ∨ M - u < (symmDiff S κ).card := by
    intro S hS
    have := hp (bk.e.symm ((bk.e i).1, S)) (sub_ne_zero.mp hS)
    rwa [Equiv.apply_symm_apply] at this
  obtain ⟨_, hb⟩ := block_table q hq1 hq2 κ (g (bk.e i).1) (bk.blockFn X (bk.e i).1) hg
  have hgi : g (bk.e i).1 (bk.e i).2 ≠ 0 := by
    simp only [hgdef, Prod.mk.eta, Equiv.symm_apply_apply]
    exact sub_ne_zero.mpr hi
  rw [hb _ hgi]
  simp [blockFn]

end Blocks

end FTPaper.Claim2
