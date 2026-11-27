import FTPaper.Claim2.PencilCost
import FTPaper.Claim2.Batch

/-!
# The routed stage with row-diagonal rectangles

`ourStageS` is the template's pencil stage built with `pencilS`. It has the same matrix as
`ourStage` (`eval_ourStageS`), hence the same frequency action, and the same calls. Its sparse
local cost is at most `rows · P` with
`P = |Free| (|Label| (m+2) + 1) + |Paid| (2m+3) + 2` (`qsparse_ourStageS`), independent of the
number of rows per label.
-/

set_option linter.unusedSectionVars false

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open OAI.Computability.NearSquareRoot.KernelPass.Plan (frequency)
open OAI.Computability.NearSquareRoot.KernelPass.Rect
open OAI.Computability.NearSquareRoot.KernelPass.Rect.Binary
open scoped OAI.Computability.NearSquareRoot.CyclotomicCode
open OAI.Computability.NearSquareRoot.BinaryQuery
open Matrix Finset
open FTPaper.Circ

namespace FTPaper.Claim2

/-- The routed pencil with row-diagonal rectangles. -/
noncomputable def ourPencilS (L b m R : ℕ) (S : System L b) :=
  pencilS (freePlansF S m) (chargedPlansF S m) (stageB₀ m)
    (stageB m (fun k : Fin R × (Fin (m + 1) → ZMod 2) => k.2))

/-- The stage as a rational plan. -/
noncomputable def ourStageS (L b m R : ℕ) (S : System L b) :
    QPlan (Charged.Axes (m := m) S.geometry) (rows L b m R) (rows L b m R) :=
  QPlan.embed (renumber (rowEquiv L b m R) (ourPencilS L b m R S))

lemma stageB_diag (m : ℕ) {W : Type} [DecidableEq W] (β : W → Fin (m + 1) → ZMod 2) :
    ∀ j k l, k ≠ l → value (stageB m β j k l) = 0 := by
  intro j k l hkl
  simp [stageB, hkl, value]

lemma stageB₀_diag (m : ℕ) {W : Type} [DecidableEq W] :
    ∀ k l : W, k ≠ l → value (stageB₀ m k l) = 0 := by
  intro k l hkl
  simp [stageB₀, hkl, value]

theorem eval_ourPencilS (L b m R : ℕ) (S : System L b) (h : ℕ) :
    (ourPencilS L b m R S).eval h = (ourPencil L b m R S).eval h :=
  eval_eq_of_block _ _ h (block_pencilS _ _ _ _ (stageB_diag m _) h)

theorem eval_ourStageS (L b m R : ℕ) (S : System L b) (h : ℕ) :
    (ourStageS L b m R S).eval h = (ourStage L b m R S).eval h := by
  simp only [ourStageS, ourStage, QPlan.eval, renumber, Plan.eval, eval_ourPencilS]

theorem applyAt_ourStageS (L b m R : ℕ) (S : System L b) (h : ℕ)
    (x : Bank (Charged.Axes (m := m) S.geometry) h (rows L b m R)) :
    (ourStageS L b m R S).applyAt h x = (ourStage L b m R S).applyAt h x := by
  simp only [QPlan.applyAt, eval_ourStageS]

/-- The row-diagonal stage has the frequency action of the routed pencil. -/
theorem frequency_ourStageS (L b m R : ℕ) (S : System L b) {h : ℕ}
    (x : Bank (Charged.Axes (m := m) S.geometry) h (rows L b m R)) (j : Fin (rows L b m R))
    (y : Addr (Charged.Axes (m := m) S.geometry) h) :
    frequency ((ourStageS L b m R S).applyAt h x) j y
      = (mismatch (∑ t, test (m + 1) (S.geometry.D - 1) (y t)) (shiftAt j) : ℚ) * frequency x j y := by
  rw [applyAt_ourStageS]
  exact frequency_ourStage' L b m R S x j y

theorem calls_ourStageS (L b m R : ℕ) (S : System L b) :
    (ourStageS L b m R S).calls = (ourPencil L b m R S).calls := by
  simp only [ourStageS, QPlan.calls_embed, calls_renumber, ourPencilS, calls_pencilS]
  rfl

/-- The pencil cost per row. -/
def pencilPerRow (L b m : ℕ) : ℕ :=
  Fintype.card (Free L b) * (Fintype.card (Label L b) * (m + 2) + 1)
    + Fintype.card (Paid L b) * (2 * (m + 1) + 1) + 2

/-- **Sparse local cost of the stage: `rows · P`.** -/
theorem qsparse_ourStageS (L b m R : ℕ) (S : System L b) :
    qsparse (ourStageS L b m R S) ≤ rows L b m R * pencilPerRow L b m := by
  have h := planSparse_pencilS (A := Charged.Axes (m := m) S.geometry) (L := Label L b)
    (W := Fin R × (Fin (m + 1) → ZMod 2)) (J := Fin (m + 1)) (freePlansF S m) (chargedPlansF S m)
    (stageB₀ m) (stageB m (fun k : Fin R × (Fin (m + 1) → ZMod 2) => k.2)) (stageB₀_diag m)
    (fun r v => planSparse_eq_zero (freeGeometryF_source_free _ _ _ _ v))
    (fun r w => planSparse_eq_zero (freeGeometryF_target_free _ _ _ _ w))
    (fun r j w v => planSparse_eq_zero (freeGeometryF_middle_free _ _ _ _ j w v))
    (fun r j v => planSparse_eq_zero (Charged.plansF_collect_free _ m j v))
    (fun r j w => planSparse_eq_zero (Charged.plansF_scatter_free _ m j w))
    (fun r j => planSparse_eq_zero (Charged.plansF_middle_free _ m))
  have hrows : Fintype.card (Label L b × (Fin R × (Fin (m + 1) → ZMod 2))) = rows L b m R := rfl
  simp only [ourStageS, QPlan.qsparse_embed, renumber, planSparse_seq, planSparse_route, zero_add,
    add_zero]
  calc planSparse (ourPencilS L b m R S) ≤ _ := h
    _ = rows L b m R * pencilPerRow L b m := by
      rw [hrows, Fintype.card_fin]
      unfold pencilPerRow
      ring

end FTPaper.Claim2
