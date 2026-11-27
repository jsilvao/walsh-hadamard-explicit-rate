import FTPaper.Free.Basic
import OAI.Computability.NearSquareRoot.KernelPassChargedLabels

/-!
# Free plans for charged rectangles

Adapted from OpenAI's `KernelPassCharged.lean` and `KernelPassChargedLabels.lean` (openai/math,
commit 3344da5, Apache 2.0): the collect, scatter and middle plans are chosen from `RealizesF`
statements, so they spend no gates outside calls. The private charts are copied with an `F`
suffix. Everything else is OpenAI's.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Charged

open OAI.LinearAlgebra.FiniteFourier Matrix Finset KernelNormalization SynchronizedPair
open FTPaper.Circ (planFree)
noncomputable section

variable {V T : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup T] [Module F T] {A D : ℕ}

private def pairedF (p q : V ≃ₗ[F] Bits D) :
    ((Fin 1 → V) × (Fin 1 → V)) ≃ₗ[F] Bits (D+D) :=
  (((LinearEquiv.funUnique (Fin 1) F V).trans p).prodCongr
    ((LinearEquiv.funUnique (Fin 1) F V).trans q)).trans (splitBits D D).symm

private def inputChartF (p q : V ≃ₗ[F] Bits D) : Common V T ≃ₗ[F] Bits (D+D) × T :=
  (pairedF p q).prodCongr (LinearEquiv.refl F T)

private def outputChartF (p q : V ≃ₗ[F] Bits D) : Common V T ≃ₗ[F] Bits (D+D) × T :=
  ((LinearEquiv.prodComm F _ _).trans (pairedF q p)).prodCongr (LinearEquiv.refl F T)

private theorem dot_chartsF (p q : V ≃ₗ[F] Bits D) (o i : Common V T) :
    ((outputChartF p q) o).1 ⬝ᵥ ((inputChartF p q) i).1 =
      (p (i.1.1 0) ⬝ᵥ q (o.1.2 0)) + (p (o.1.1 0) ⬝ᵥ q (i.1.2 0)) := by
  change Fin.append (q (o.1.2 0)) (p (o.1.1 0)) ⬝ᵥ
    Fin.append (p (i.1.1 0)) (q (i.1.2 0)) = _
  rw [dotProduct, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, dotProduct]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- A charged kernel with different input and output charts uses exactly
two normalized families of child axes and two zero-cost chirps. -/
theorem realizes_transferF [FiniteDimensional F T] (B : LinearMap.BilinForm F V)
    (p q : V ≃ₗ[F] Bits D) (hpq : ∀ x y, B x y = p x ⬝ᵥ q y)
    (ey ex : Bits A ≃ₗ[F] Common V T) : RealizesF (2*D) (transfer B D ey ex) := by
  classical
  let out := ey.trans (outputChartF p q)
  let inp := ex.trans (inputChartF p q)
  let χy (y : Bits A) := chirp B (ey y)
  let χx (x : Bits A) := chirp B (ex x)
  have real := ((RealizesF.sign χy).mul (RealizesF.partialChart out inp)).mul (RealizesF.sign χx)
  simp only [Nat.zero_add, Nat.add_zero] at real
  rw [two_mul]
  convert real using 1
  ext y x
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  change (primeCommonKernel (C := Fin 1) binaryRoot B 1 D) (ey y) (ex x) =
    character (χy y) * partialChart out inp y x * character (χx x)
  rw [primeCommonKernel]
  simp only [Fintype.card_unique, invOf_eq_inv, Nat.cast_ofNat, inv_one,
    Units.val_one, one_mul, Finset.univ_unique, Finset.sum_singleton]
  have dot := dot_chartsF p q (ey y) (ex x)
  rw [← hpq, ← hpq] at dot
  have normal : (w : ℂ)^(D+D) = (2 : ℂ)⁻¹ ^ D := by
    rw [← two_mul, even_child_normalization]
  change (if (ex x).2 = (ey y).2 then _ else _) = _
  by_cases he : (ex x).2 = (ey y).2
  · rw [ite_eq_left he]
    unfold partialChart
    rw [ite_eq_left (show (out y).2 = (inp x).2 from he.symm), normal]
    change _ = character (χy y) * (_ * character (((outputChartF p q) (ey y)).1 ⬝ᵥ
      ((inputChartF p q) (ex x)).1)) * character (χx x)
    rw [dot]
    have step : B ((ex x).1.1 0 - (ey y).1.1 0) ((ey y).1.2 0 - (ex x).1.2 0) =
        χy y + (B ((ex x).1.1 0) ((ey y).1.2 0) + B ((ey y).1.1 0) ((ex x).1.2 0)) + χx x := by
      simp only [map_sub, LinearMap.sub_apply, χy, χx, chirp]
      abel
    change _ * digitPhase binaryRoot (B ((ex x).1.1 0 - (ey y).1.1 0) ((ey y).1.2 0 - (ex x).1.2 0)) = _
    rw [step]
    simp only [character, AddChar.map_add_eq_mul]
    ring
  · rw [ite_eq_right he]
    unfold partialChart
    rw [ite_eq_right (show (out y).2 ≠ (inp x).2 from Ne.symm he)]
    simp


theorem realizes_sourceF (ref ex : Bits A ≃ₗ[F] Common V T) : RealizesF 0 (source ref ex) :=
  RealizesF.permutation _

theorem realizes_targetF (ref ey : Bits A ≃ₗ[F] Common V T) : RealizesF 0 (target ref ey) :=
  RealizesF.permutation _

end

open BinaryQuery

noncomputable section
variable {L b m : ℕ} (G : BitRoutingGeometry 2 L b)

/-- OpenAI's `plans`, with witnesses that spend no gates outside calls. -/
def plansF (m : ℕ) : Plans m G :=
  let base : BitLabel L b := fun _ _ => false
  let ref := chart G (m := m) 0 base
  let mid := realizes_transferF G.form (labelFrame G base false) (labelFrame G base true)
    (labelFrame_pair G base) ref ref
  let hS := fun (j : Fin (m+1)) (v : BitLabel L b) => realizes_sourceF ref (chart G j v)
  let hT := fun (j : Fin (m+1)) (v : BitLabel L b) => realizes_targetF ref (chart G j v)
  { collect := fun j v => (hS j v).choose
    scatter := fun j v => (hT j v).choose
    middle := mid.choose
    collect_calls := fun j v => Nat.eq_zero_of_le_zero (hS j v).choose_spec.1
    scatter_calls := fun j v => Nat.eq_zero_of_le_zero (hT j v).choose_spec.1
    middle_calls := mid.choose_spec.1
    block := fun j w v => by
      have compiled := ((hT j w).choose_spec.2.2.seq mid.choose_spec.2.2).seq
        (hS j v).choose_spec.2.2
      have e := (factor G.form G.D ref (chart G j w) (chart G j v)).trans (transfer_eq G j w v)
      exact (congrArg (Implements (((hT j w).choose.seq mid.choose).seq (hS j v).choose)) e).mp
        compiled }

theorem plansF_collect_free (m : ℕ) (j : Fin (m+1)) (v : BitLabel L b) :
    planFree ((plansF G m).collect j v) = 0 :=
  (realizes_sourceF _ _).choose_spec.2.1

theorem plansF_scatter_free (m : ℕ) (j : Fin (m+1)) (v : BitLabel L b) :
    planFree ((plansF G m).scatter j v) = 0 :=
  (realizes_targetF _ _).choose_spec.2.1

theorem plansF_middle_free (m : ℕ) : planFree (plansF G m).middle = 0 :=
  (realizes_transferF G.form (labelFrame G (fun _ _ => false) false)
    (labelFrame G (fun _ _ => false) true) (labelFrame_pair G (fun _ _ => false))
    (chart G (m := m) 0 (fun _ _ => false)) (chart G (m := m) 0 (fun _ _ => false))).choose_spec.2.1

/-- OpenAI's `rectangleData` with the free plans. -/
def rectangleDataF (m : ℕ) (s : Rect.Support (BitLabel L b)) :
    Rect.ChargedData (Axes (m := m) G) (BitLabel L b) (Fin (m+1)) where
  toSupport := s
  input := (plansF G m).collect
  output := (plansF G m).scatter
  common := fun _ => (plansF G m).middle
  input_free := (plansF G m).collect_calls
  output_free := (plansF G m).scatter_calls

theorem rectangleDataF_factors (m : ℕ) (s : Rect.Support (BitLabel L b)) :
    (rectangleDataF G m s).Factors (routed G m) := by
  intro h j w v _ _
  simpa only [rectangleDataF, Plan.eval, oneRow_mul, routed] using
    ((plansF G m).block j w v).oneRow_eq h

theorem rectangleDataF_calls (m : ℕ) (s : Rect.Support (BitLabel L b)) (j : Fin (m+1)) :
    ((rectangleDataF G m s).common j).calls ≤ 2*G.D := (plansF G m).middle_calls

end
end KernelPass.Charged

end NearSquareRoot
end Computability
end OAI
