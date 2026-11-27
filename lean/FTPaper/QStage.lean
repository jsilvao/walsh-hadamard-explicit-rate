import FTPaper.QWrap
import FTPaper.Free.R1

/-!
# Our pencil stage inside OpenAI's routing

The stage `C_β = Σ_j ½ (1 − (−1)^{β_j} Q_j)` is OpenAI's compiled rectangle pencil
(`geometricPencilF`: OpenAI's `geometricPencil` with free endpoint plans, `FTPaper/Free/`) with **dyadic** diagonal coefficients `B₀ = (m+1)/2` and `B_j = ∓1/2`, so it
lives in their own plan language. In frequency, it multiplies row `(w, k)` by the number of
mismatches between the query signature `κ(y)` and the row's shift `β k`. That is Lemma A(1).
-/

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open OAI.Computability.NearSquareRoot.KernelPass.Plan (frequency walshMatrix)
open OAI.Computability.NearSquareRoot.KernelPass.Rect (atFrequency renumber)
open OAI.Computability.NearSquareRoot.KernelPass.Rect.Binary (geometricPencilF block_geometricPencilF
  System Label)
open scoped OAI.Computability.NearSquareRoot.CyclotomicCode
open OAI.Computability.NearSquareRoot.BinaryQuery
open Matrix Finset

namespace FTPaper

/-- Constant term `(m+1)/2` on the diagonal. -/
def stageB₀ (m : ℕ) {W : Type} [DecidableEq W] : W → W → Coefficient :=
  fun k l => if k = l then ((m + 1 : ℤ), 1) else (0, 0)

/-- Query term `−(−1)^{β_j}/2` on the diagonal. -/
def stageB (m : ℕ) {W : Type} [DecidableEq W] (β : W → Fin (m + 1) → ZMod 2) :
    Fin (m + 1) → W → W → Coefficient :=
  fun j k l => if k = l then (if β k j = 0 then (-1, 1) else (1, 1)) else (0, 0)

/-- Number of coordinates where two signatures differ. -/
def mismatch {M : ℕ} (κ β : Fin M → ZMod 2) : ℕ := (univ.filter fun j => κ j ≠ β j).card

lemma half_term (κ β : ZMod 2) :
    (1 / 2 : ℚ) + (-1 : ℚ) ^ κ.val * KernelPass.value (if β = 0 then ((-1 : ℤ), 1) else (1, 1))
      = if κ ≠ β then 1 else 0 := by
  have hz : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hz κ with rfl | rfl <;> rcases hz β with rfl | rfl <;>
    simp [KernelPass.value, ZMod.val_one] <;> norm_num

/-- **The stage in frequency.** -/
theorem frequency_stage {L b m : ℕ} (S : System L b) {W : Type} [Fintype W] [DecidableEq W]
    (β : W → Fin (m + 1) → ZMod 2) {N : ℕ} (e : Label L b × W ≃ Fin N) {h : ℕ}
    (x : Bank (Charged.Axes (m := m) S.geometry) h N) (w : Label L b) (k : W)
    (y : Addr (Charged.Axes (m := m) S.geometry) h) :
    frequency ((renumber e (geometricPencilF S m (stageB₀ m) (stageB m β))).applyAt h x) (e (w, k)) y
      = (mismatch (∑ t, test (m + 1) (S.D - 1) (y t)) (β k) : ℚ) * frequency x (e (w, k)) y := by
  classical
  refine (atFrequency e _ (fun k l => KernelPass.value (stageB₀ m k l))
    (fun j k l => KernelPass.value (stageB m β j k l))
    (fun j _ => rationalLift h (query (u := S.D - 1) j))
    (fun j _ y => (-1 : ℚ) ^ ((∑ t, test (m + 1) (S.D - 1) (y t)) j).val)
    (fun w v k l => block_geometricPencilF S m _ _ h w v k l)
    (fun j _ v z => rational_frequency j v z) x w k y).trans ?_
  rw [Finset.sum_eq_single k]
  · congr 1
    set κ := ∑ t, test (m + 1) (S.D - 1) (y t)
    simp only [stageB₀, stageB, ite_true]
    have hsplit : KernelPass.value ((m + 1 : ℤ), 1) = ∑ _j : Fin (m + 1), (1 / 2 : ℚ) := by
      simp [KernelPass.value]; ring
    rw [hsplit, ← Finset.sum_add_distrib]
    have hterm : ∀ j : Fin (m + 1), (1 / 2 : ℚ) + (-1 : ℚ) ^ (κ j).val *
        KernelPass.value (if β k j = 0 then ((-1 : ℤ), 1) else (1, 1)) = if κ j ≠ β k j then 1 else 0 :=
      fun j => half_term (κ j) (β k j)
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_boole]
    simp [mismatch]
  · intro l _ hl
    simp [stageB₀, stageB, Ne.symm hl, KernelPass.value]
  · simp

end FTPaper
