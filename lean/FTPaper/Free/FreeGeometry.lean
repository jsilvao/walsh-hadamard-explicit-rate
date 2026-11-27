import FTPaper.Free.Endpoints
import FTPaper.Free.Bridge
import OAI.Computability.NearSquareRoot.KernelPassFreeGeometry

/-!
# Free endpoint plans for every free incidence of the binary system

Adapted from OpenAI's `KernelPassFreeGeometry.lean` (openai/math, commit 3344da5, Apache 2.0):
the source, target and middle plans are chosen from `RealizesF` statements, so each of them
spends no gates outside calls (`freeGeometryF_source_free`, `…_target_free`, `…_middle_free`).
Everything else is OpenAI's.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Rect.Binary

open OAI.LinearAlgebra.FiniteFourier KernelNormalization Module Matrix
open scoped Classical
open FTPaper.Circ (planFree)

noncomputable section

variable {A L b m : ℕ} (G : BitRoutingGeometry 2 L b) (R : Free L b)
  (e : Bits A ≃ₗ[ZMod 2] G.RowAddress m 1)

private abbrev HF := G.targetSpan R.val
private abbrev PF := (HF G R).orthogonalBilin G.form

private theorem dim_addF : finrank (ZMod 2) (PF G R) + finrank (ZMod 2) (HF G R) = G.D := by
  let s := G.sharedCharts R.val
  have eq : finrank (ZMod 2) (PF G R) = s.c := by
    have e' := endpointAxisEquiv ((s.dual).trans (LinearEquiv.prodComm _ _ _)) (PF G R)
      (fun x => s.mem_dual x)
    simpa using e'.finrank_eq
  rw [eq, Nat.add_comm]
  exact s.dim_eq

private def sourceMF {v : Label L b} (hv : v ∈ bitSources R.val) : Local A :=
  (((2:ℂ)⁻¹ ^ finrank (ZMod 2) (HF G R)) •
    primeSourceEndpoint (f := 1) (J := Fin m) binaryRoot 1
      (G.sourceSlice R.val R.property hv false) (G.sourceSlice R.val R.property hv true)).submatrix e e

private def targetMF {w : Label L b} (hw : w ∈ bitTargets R.val) : Local A :=
  (((2:ℂ)⁻¹ ^ finrank (ZMod 2) (PF G R)) •
    primeTargetEndpoint (f := 1) (J := Fin m) binaryRoot 1
      (G.targetSlice R.val hw false) (G.targetSlice R.val hw true)).submatrix e e

private theorem sourceRealF {v : Label L b} (hv : v ∈ bitSources R.val) :
    RealizesF (2*finrank (ZMod 2) (HF G R)) (sourceMF G R e hv) :=
  (RealizesF.geometricEndpoints (G.sourceSlice R.val R.property hv false)
    (G.sourceSlice R.val R.property hv true) e).1

private theorem targetRealF {w : Label L b} (hw : w ∈ bitTargets R.val) :
    RealizesF (2*finrank (ZMod 2) (PF G R)) (targetMF G R e hw) :=
  (RealizesF.geometricEndpoints (G.targetSlice R.val hw false) (G.targetSlice R.val hw true) e).2

set_option synthInstance.maxSize 2048 in
private theorem middleRealF (j : Fin m) {w v : Label L b}
    (hw : w ∈ bitTargets R.val) (hv : v ∈ bitSources R.val) :
    ∃ p : Plan A 1 1, p.calls = 0 ∧ planFree p = 0 ∧ ∀ h, oneRow (((targetRealF G R e hw).choose).eval h) *
      oneRow (p.eval h) * oneRow (((sourceRealF G R e hv).choose).eval h) =
      rationalLift h ((G.transfer binaryRoot 1 1 j w v).submatrix e e) := by
  have eq := normalizedFree_factorF e G.D G.form G.nondegenerate G.symm (HF G R) (dim_addF G R)
    (G.sourceSlice R.val R.property hv false) (G.sourceSlice R.val R.property hv true)
    (G.targetSlice R.val hw false) (G.targetSlice R.val hw true)
    (G.labelCharts v).pair (G.labelCharts w).pair j
  obtain ⟨mid,⟨p,hp,hf,hm⟩,eq⟩ := eq
  refine ⟨p,Nat.le_zero.mp hp,hf,fun h => ?_⟩
  have hT := (targetRealF G R e hw).choose_spec.2.2
  have hS := (sourceRealF G R e hv).choose_spec.2.2
  apply Implements.product_eq hT hm hS _ h
  exact eq.symm

/-- All three plans are selected before the number of address columns. Source
and target choices use just the incidence and are independent of the query. -/
def freeGeometryF (weight : Coefficient) : FreeData A (Label L b) (Fin m) where
  sources := (bitSources R.val).toFinset
  destinations := (bitTargets R.val).toFinset
  weight := weight
  source v := if hv : v ∈ bitSources R.val then (sourceRealF G R e hv).choose else identity
  target w := if hw : w ∈ bitTargets R.val then (targetRealF G R e hw).choose else identity
  middle j w v := if h : w ∈ bitTargets R.val ∧ v ∈ bitSources R.val then
    (middleRealF G R e j h.1 h.2).choose else identity
  middle_free j w v := by
    split
    · rename_i h
      exact (middleRealF G R e j h.1 h.2).choose_spec.1
    · rfl

theorem freeGeometryF_factors (weight : Coefficient) :
    (freeGeometryF G R e weight).Factors
      (fun h j w v => rationalLift h ((G.transfer binaryRoot 1 1 j w v).submatrix e e)) := by
  intro h j w v hv hw
  have hs : v ∈ bitSources R.val := Set.mem_toFinset.mp hv
  have ht : w ∈ bitTargets R.val := Set.mem_toFinset.mp hw
  simpa only [freeGeometryF, dite_eq_left hs, dite_eq_left ht, dite_eq_left (And.intro ht hs)] using
    (middleRealF G R e j ht hs).choose_spec.2.2 h

theorem freeGeometryF_source_calls (weight : Coefficient) (v : Label L b) :
    ((freeGeometryF G R e weight).source v).calls ≤ 2*G.D := by
  have hd := dim_addF G R
  simp only [freeGeometryF]
  split
  · rename_i hv
    exact (sourceRealF G R e hv).choose_spec.1.trans (by omega)
  · exact Nat.zero_le _

theorem freeGeometryF_target_calls (weight : Coefficient) (w : Label L b) :
    ((freeGeometryF G R e weight).target w).calls ≤ 2*G.D := by
  have hd := dim_addF G R
  simp only [freeGeometryF]
  split
  · rename_i hw
    exact (targetRealF G R e hw).choose_spec.1.trans (by omega)
  · exact Nat.zero_le _


theorem freeGeometryF_source_free (weight : Coefficient) (v : Label L b) :
    planFree ((freeGeometryF G R e weight).source v) = 0 := by
  simp only [freeGeometryF]
  split
  · rename_i hv
    exact (sourceRealF G R e hv).choose_spec.2.1
  · rfl

theorem freeGeometryF_target_free (weight : Coefficient) (w : Label L b) :
    planFree ((freeGeometryF G R e weight).target w) = 0 := by
  simp only [freeGeometryF]
  split
  · rename_i hw
    exact (targetRealF G R e hw).choose_spec.2.1
  · rfl

theorem freeGeometryF_middle_free (weight : Coefficient) (j : Fin m) (w v : Label L b) :
    planFree ((freeGeometryF G R e weight).middle j w v) = 0 := by
  simp only [freeGeometryF]
  split
  · rename_i h
    exact (middleRealF G R e j h.1 h.2).choose_spec.2.1
  · rfl

end
end KernelPass.Rect.Binary

end NearSquareRoot
end Computability
end OAI
