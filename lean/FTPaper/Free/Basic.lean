import FTPaper.PlanFree

/-!
# Free realizations of single-column transforms

Adapted from OpenAI's `KernelPassFactors.lean`, `KernelPassMonomial.lean` and
`KernelPassPartial.lean` (openai/math, commit 3344da5, Apache 2.0).

The change: `Realizes n M` becomes `RealizesF n M`, which also asks the witness to spend no gates
outside calls (`FTPaper.Circ.planFree p = 0`). The witnesses and proofs are OpenAI's.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass

open Matrix Finset SynchronizedPadding SynchronizedPair KernelNormalization
open scoped BigOperators
open FTPaper.Circ (planFree)

noncomputable section

variable {A k : ℕ}

/-- A single-column transform with a child-call budget and no gates outside calls. -/
def RealizesF (budget : ℕ) (M : Local A) : Prop :=
  ∃ p : Plan A 1 1, p.calls ≤ budget ∧ planFree p = 0 ∧ Implements p M

theorem RealizesF.realizes {n : ℕ} {M : Local A} (h : RealizesF n M) : Realizes n M := by
  obtain ⟨p, hp, -, hi⟩ := h
  exact ⟨p, hp, hi⟩

theorem RealizesF.mul {s t : ℕ} {M N : Local A} (hM : RealizesF s M) (hN : RealizesF t N) :
    RealizesF (s+t) (M*N) := by
  obtain ⟨p,hp,fp,ep⟩ := hM
  obtain ⟨q,hq,fq,eq⟩ := hN
  exact ⟨p.seq q, Nat.add_le_add hp hq, by simp [fp, fq], ep.seq eq⟩

theorem RealizesF.sign (φ : Bits A → ZMod 2) :
    RealizesF 0 (diagonal fun x => character (φ x)) :=
  ⟨signPass _, le_rfl, by simp, implements_sign _⟩

/-- OpenAI's `reindex_linear`, with its witness kept visible. -/
theorem reindex_linearF (e : Bits A ≃ₗ[ZMod 2] Bits A) :
    ∃ p : Plan A 1 1, p.calls = 0 ∧ planFree p = 0 ∧ Implements p (pushAddress e) := by
  let M := e.toLinearMap.toMatrix'
  have hM : M.det ≠ 0 := by
    apply IsUnit.ne_zero
    apply (Matrix.isUnit_iff_isUnit_det _).mp
    apply LinearMap.isUnit_toMatrix'_iff.mpr
    exact ⟨⟨e.toLinearMap, e.symm.toLinearMap, by ext; simp, by ext; simp⟩, rfl⟩
  let w := KernelColumn.compile M hM
  refine ⟨reindexWord w, calls_reindexWord _, by simp, ?_⟩
  have hs := implements_reindexWord w
  have hm : KernelColumn.wordMatrix w = M := KernelColumn.wordMatrix_compile _ _
  rw [hm] at hs
  have E : M.mulVec = ⇑e := funext (fun x => LinearMap.toMatrix'_mulVec _ _)
  simpa only [E] using hs

theorem RealizesF.permutation (e : Bits A ≃ₗ[ZMod 2] Bits A) :
    RealizesF 0 (pushAddress e) := by
  obtain ⟨p,h,f,e⟩ := reindex_linearF e
  exact ⟨p,h.le,f,e⟩

theorem RealizesF.partial (s : List (Fin A)) : RealizesF s.length (partialLocal s) :=
  ⟨fullConversion s, (calls_fullConversion s).le, by simp, implements_partial s⟩

/-- Change both physical address charts by applying binary linear
permutations before and after a realized matrix. -/
theorem RealizesF.submatrix {n : ℕ} {M : Local A} (hM : RealizesF n M)
    (ey ex : Bits A ≃ₗ[ZMod 2] Bits A) :
    RealizesF n (M.submatrix ey ex) := by
  have h := ((RealizesF.permutation ey.symm).mul hM).mul (RealizesF.permutation ex)
  simp only [zero_add,add_zero] at h
  have e : pushAddress (⇑ey.symm) * M * pushAddress (⇑ex) = M.submatrix ey ex := by
    ext y x
    simp only [Matrix.mul_apply, pushAddress, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, ite_mul, one_mul, zero_mul,
      Matrix.submatrix_apply]
    simp [eq_comm, LinearEquiv.eq_symm_apply]
  rwa [e] at h

variable {R : Type*} [AddCommGroup R] [Module (ZMod 2) R]

private theorem split_realizesF (k r : ℕ) :
    RealizesF k (partialChart (splitBits k r) (splitBits k r)) := by
  let axes := (List.finRange k).map (Fin.castAdd r)
  have nodup : axes.Nodup := (List.nodup_finRange k).map (Fin.castAdd_injective _ _)
  have h := RealizesF.partial axes
  have length : axes.length = k := by simp [axes]
  rw [length, partial_tensor axes nodup] at h
  suffices eq : tensorMatrix (fun b => if b ∈ axes then bitWalsh else 1) =
      partialChart (splitBits k r) (splitBits k r) by rwa [eq] at h
  ext y x
  change (∏ b, (if b ∈ axes then bitWalsh else 1) (y b) (x b)) = _
  rw [Fin.prod_univ_add]
  have hl (b : Fin k) : Fin.castAdd r b ∈ axes := by simp [axes]
  have hr (b : Fin r) : Fin.natAdd k b ∉ axes := by
    simp only [axes,List.mem_map,List.mem_finRange,true_and,not_exists]
    intro i he
    have := congrArg Fin.val he
    simp at this
    omega
  simp only [hl, hr, ↓reduceIte]
  let e := splitBits k r
  have ha : (∏ i : Fin k, walsh (y (Fin.castAdd r i)) (x (Fin.castAdd r i))) =
      (w : ℂ)^k * character ((e y).1 ⬝ᵥ (e x).1) := axis_character _ _
  rw [ha]
  unfold partialChart
  by_cases he : (e y).2 = (e x).2
  · have hc (i : Fin r) : y (Fin.natAdd k i) = x (Fin.natAdd k i) := congrFun he i
    simp [e] at he
    simp [he,hc,e, Matrix.one_apply]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp he
    change y (Fin.natAdd k i) ≠ x (Fin.natAdd k i) at hi
    have hz : (∏ j : Fin r, (1 : Matrix (ZMod 2) (ZMod 2) ℂ)
        (y (Fin.natAdd k j)) (x (Fin.natAdd k j))) = 0 :=
      prod_eq_zero (mem_univ i) (Matrix.one_apply_ne hi)
    change ¬(splitBits k r y).2 = (splitBits k r x).2 at he
    simp only [hz, mul_zero, he, ↓reduceIte]

/-- Arbitrary invertible charts on the source and destination preserve the
child budget of a partial normalized Walsh transform. -/
theorem RealizesF.partialChart [FiniteDimensional (ZMod 2) R]
    (ey ex : Bits A ≃ₗ[ZMod 2] Bits k × R) :
    RealizesF k (KernelPass.partialChart ey ex) := by
  classical
  let r := Module.finrank (ZMod 2) R
  have hdim : A = k+r := by simpa [r, Module.finrank_prod] using ey.finrank_eq
  subst A
  let b := (Module.finBasis (ZMod 2) R).equivFun
  let l := (LinearEquiv.refl (ZMod 2) (Bits k)).prodCongr b
  let cy := (ey.trans l).trans (splitBits k r).symm
  let cx := (ex.trans l).trans (splitBits k r).symm
  have h := (split_realizesF k r).submatrix cy cx
  convert h using 1
  ext y x
  have fy : splitBits k r (cy y) = ((ey y).1,b (ey y).2) :=
    (splitBits k r).apply_symm_apply _
  have fx : splitBits k r (cx x) = ((ex x).1,b (ex x).2) :=
    (splitBits k r).apply_symm_apply _
  simp only [KernelPass.partialChart, Matrix.submatrix_apply]
  split_ifs with hy hx hx
  · rw [fy,fx]
  · exact (hx (by rw [fy,fx]; exact congrArg b hy)).elim
  · rw [fy,fx] at hx
    exact (hy (b.injective hx)).elim
  · rfl

end
end KernelPass

end NearSquareRoot
end Computability
end OAI
