import OAI.Computability.NearSquareRoot.KernelBinaryTemplate

/-!
# Gates outside calls

`planFree p` counts, per address, the gates a plan spends outside child calls when compiled into
circuits (`FTPaper/QCircuit.lean`). A mix is charged densely, `o·i`. A `1×1` mix is a scaling,
which folds into circuit readouts, so it is free. Permutations (`xor`), diagonal scalings
(`scale`) and child calls are free too.
-/

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass

namespace FTPaper

namespace Circ

/-- Gates outside calls, per address, of one of OpenAI's plans. -/
def planFree {A : ℕ} : {i o : ℕ} → Plan A i o → ℕ
  | _, _, @Plan.mix _ i o _ => if i = 1 ∧ o = 1 then 0 else o * i
  | _, _, .xor _ => 0
  | _, _, .scale _ _ _ => 0
  | _, _, .child _ => 0
  | _, _, .seq p q => planFree p + planFree q
  | _, _, .parallel p q => planFree p + planFree q

variable {A : ℕ}

@[simp] theorem planFree_seq {i j o : ℕ} (p : Plan A j o) (q : Plan A i j) :
    planFree (p.seq q) = planFree p + planFree q := rfl

@[simp] theorem planFree_parallel {i j o u : ℕ} (p : Plan A i o) (q : Plan A j u) :
    planFree (p.parallel q) = planFree p + planFree q := rfl

@[simp] theorem planFree_xor (g : Fin A × Fin A) : planFree (Plan.xor g) = 0 := rfl

@[simp] theorem planFree_child (a : Fin A) : planFree (Plan.child a) = 0 := rfl

@[simp] theorem planFree_scale (q : ℕ) (test : Column A → Fin q → ZMod 2)
    (t : (Fin q → ZMod 2) → Coefficient) : planFree (Plan.scale q test t) = 0 := rfl

theorem planFree_mix {i o : ℕ} (c : Fin o → Fin i → Coefficient) :
    planFree (Plan.mix (A := A) c) = if i = 1 ∧ o = 1 then 0 else o * i := rfl

theorem planFree_mix_le {i o : ℕ} (c : Fin o → Fin i → Coefficient) :
    planFree (Plan.mix (A := A) c) ≤ o * i := by
  rw [planFree_mix]; split <;> omega

@[simp] theorem planFree_identity : planFree (identity (A := A)) = 0 := rfl

@[simp] theorem planFree_reindexWord (w : KernelColumn.Word A) : planFree (reindexWord w) = 0 := by
  induction w with
  | nil => rfl
  | cons g w ih => simp [reindexWord] at ih ⊢; exact ih

@[simp] theorem planFree_fullConversion (axes : List (Fin A)) :
    planFree (fullConversion axes) = 0 := by
  induction axes with
  | nil => rfl
  | cons a axes ih => simp [fullConversion] at ih ⊢; exact ih

@[simp] theorem planFree_signPass (φ : Bits A → ZMod 2) : planFree (signPass φ) = 0 := rfl

end Circ

end FTPaper
