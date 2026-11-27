import FTPaper.Free.Basic
import OAI.Computability.NearSquareRoot.KernelPassEndpoints

/-!
# Free realizations of the normalized endpoint passes

Adapted from OpenAI's `KernelPassEndpointPair.lean` and `KernelPassEndpoints.lean` (openai/math,
commit 3344da5, Apache 2.0): `Realizes` becomes `RealizesF`. The private helpers are copied with
an `F` suffix.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass

open Matrix Finset OAI.LinearAlgebra.FiniteFourier KernelNormalization SynchronizedPair
noncomputable section

private def collapsePairF (h : ℕ) :
    PrimeCommonPair 2 1 h ≃ₗ[ZMod 2] Bits h × Bits h where
  toFun x := (x.1 0,x.2 0)
  invFun z := (fun _ => z.1, fun _ => z.2)
  left_inv x := by ext c i <;> rw [Subsingleton.elim c 0]
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def pairBitsF (h : ℕ) :
    PrimeCommonPair 2 1 h ≃ₗ[ZMod 2] Bits (h+h) :=
  (collapsePairF h).trans (splitBits h h).symm

private theorem pair_dotF {h : ℕ} (y x : PrimeCommonPair 2 1 h) :
    pairBitsF h y ⬝ᵥ pairBitsF h x =
      ∑ c, ∑ i, (x.1 c i * y.1 c i + x.2 c i * y.2 c i) := by
  change (∑ b, Fin.append (y.1 0) (y.2 0) b * Fin.append (x.1 0) (x.2 0) b) = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  simp [Finset.sum_add_distrib,mul_comm]

variable {A h : ℕ} {R : Type*} [AddCommGroup R] [Module (ZMod 2) R]
    [FiniteDimensional (ZMod 2) R]

/-- The same two-half endpoint as in the prime rectangle identity, now using
normalized Walsh children on each axis and the two actual binary charts. -/
theorem RealizesF.endpointPair_between
    (ey ex : Bits A ≃ₗ[ZMod 2] PrimeCommonPair 2 1 h × R) :
    RealizesF (2*h) (((2 : ℂ)⁻¹ ^ h •
      endpointPartial (endpointPairFourier (f := 1) (h := h) binaryRoot (1 : (ZMod 2)ˣ)) R).submatrix
      ey ex) := by
  classical
  let l := (pairBitsF h).prodCongr (LinearEquiv.refl (ZMod 2) R)
  let cy := ey.trans l
  let cx := ex.trans l
  rw [two_mul]
  have hr := RealizesF.partialChart cy cx
  convert hr using 1
  ext y x
  have hy : cy y = (pairBitsF h (ey y).1, (ey y).2) := rfl
  have hx : cx x = (pairBitsF h (ex x).1, (ex x).2) := rfl
  simp only [Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul, endpointPartial,
    KernelPass.partialChart, hy, hx]
  by_cases e : (ex x).2 = (ey y).2
  · simp only [e, ↓reduceIte]
    rw [show (w : ℂ)^(h+h) = (2 : ℂ)⁻¹^h by rw [← two_mul, even_child_normalization], pair_dotF]
    simp [endpointPairFourier, character]
  · simp [e, Ne.symm e]

theorem RealizesF.endpointPair
    (e : Bits A ≃ₗ[ZMod 2] PrimeCommonPair 2 1 h × R) :
    RealizesF (2*h) (((2 : ℂ)⁻¹ ^ h •
      endpointPartial (endpointPairFourier (f := 1) (h := h) binaryRoot (1 : (ZMod 2)ˣ)) R).submatrix
      e e) := RealizesF.endpointPair_between e e


end

noncomputable section
open OAI.LinearAlgebra.FiniteFourier KernelNormalization Matrix Module

variable {A : ℕ} {J U : Type} [Fintype J] [Fintype U]
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    {p q : E ≃ₗ[ZMod 2] ZMod 2 × (U → ZMod 2)} {H : Submodule (ZMod 2) E}
    (P : AuxiliarySlice p H) (Q : AuxiliarySlice q H) [Fintype P.C] [Fintype Q.C]

private abbrev ResidualF := EndpointLabelResidualIndex (Fin 1) J (ZMod 2) P.C Q.C

private def readChartF
    (e : Bits A ≃ₗ[ZMod 2] PrimeSpectrumDigits (Fin 1 × (J ⊕ U)) 2) :
    Bits A ≃ₗ[ZMod 2] PrimeCommonPair 2 1 (finrank (ZMod 2) H) × ResidualF (J := J) P Q :=
  e.trans (KernelEndpointCross.linear
    (KernelEndpointCross.endpointLabelAddChart (C := Fin 1) (J := J) P Q)).symm

set_option synthInstance.maxSize 512 in
/-- Each normalized physical endpoint uses at most two child calls per
shared basis direction, for every binary linear encoding of the row address. -/
theorem RealizesF.geometricEndpoints
    (e : Bits A ≃ₗ[ZMod 2] PrimeSpectrumDigits (Fin 1 × (J ⊕ U)) 2) :
    RealizesF (2 * finrank (ZMod 2) H)
      (((2 : ℂ)⁻¹ ^ finrank (ZMod 2) H • primeSourceEndpoint (f := 1) (J := J)
        binaryRoot (1 : (ZMod 2)ˣ) P Q).submatrix e e) ∧
    RealizesF (2 * finrank (ZMod 2) H)
      (((2 : ℂ)⁻¹ ^ finrank (ZMod 2) H • primeTargetEndpoint (f := 1) (J := J)
        binaryRoot (1 : (ZMod 2)ˣ) P Q).submatrix e e) := by
  classical
  let c := readChartF P Q e
  let F := endpointPartial
    (endpointPairFourier (f := 1) (h := finrank (ZMod 2) H) binaryRoot (1 : (ZMod 2)ˣ))
    (ResidualF (J := J) P Q)
  let z : ℂ := (2 : ℂ)⁻¹ ^ finrank (ZMod 2) H
  let phase := fun t => -↑((1 : (ZMod 2)ˣ)⁻¹) *
    endpointLabelCoordinateAux P Q (finBasis (ZMod 2) H).equivFun (J := J) (C := Fin 1) t
  let d := diagonal (fun t => character (phase t))
  let l := endpointLabelFinChart (C := Fin 1) (J := J) P Q
  have hs : primeSourceEndpoint (f := 1) (J := J) binaryRoot (1 : (ZMod 2)ˣ) P Q =
      reindex l l (F * d) := rfl
  have ht : primeTargetEndpoint (f := 1) (J := J) binaryRoot (1 : (ZMod 2)ˣ) P Q =
      reindex l l (d * F) := rfl
  have hd := RealizesF.sign (fun x => phase (c x))
  have hw := RealizesF.endpointPair c
  have hfirst := hw.mul hd
  have hlast := hd.mul hw
  rw [Nat.add_zero] at hfirst
  rw [Nat.zero_add] at hlast
  rw [hs, ht]
  constructor
  · convert hfirst using 1
    ext y x
    change z * (F * d) (c y) (c x) = ((z • F).submatrix c c *
      diagonal (fun t => character (phase (c t)))) y x
    simp only [d, mul_diagonal, submatrix_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc]
  · convert hlast using 1
    ext y x
    change z * (d * F) (c y) (c x) = (diagonal (fun t => character (phase (c t))) *
      (z • F).submatrix c c) y x
    simp only [d, diagonal_mul, submatrix_apply, Matrix.smul_apply, smul_eq_mul]
    exact mul_left_comm _ _ _


end
end KernelPass

end NearSquareRoot
end Computability
end OAI
