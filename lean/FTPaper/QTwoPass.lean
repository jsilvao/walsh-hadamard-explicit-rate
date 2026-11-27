import FTPaper.QHorner

/-!
# The two-pass repair as a plan (paper: Lemma 4.1, plan level)

`twoPass p gather scatter table` runs the procedure of Lemma B:

* `Y₁ = p X`;
* the table maps `(gather Y₁, gather X)` to `(a, z a)`;
* `Z = scatter a`, `G = scatter (z a)`;
* output `Y₁ − p Z + G`.

That is two applications of the predictor `p` (OpenAI's `hermite` uses four).
-/

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

namespace FTPaper

namespace QPlan

variable {A W s h : ℕ}

/-- The two-pass repair. -/
def twoPass (p : QPlan A W W) (gather : QPlan A W s) (scatter : QPlan A s W)
    (table : QPlan A (s + s) (s + s)) : QPlan A W W :=
  let keep : QPlan A W W := route id
  let project : QPlan A (W + W) W := route (Fin.castAdd W)
  let syndromes := table.seq (gather.parallel gather)
  let corrected := (scatter.parallel scatter).seq syndromes
  let residual := ((combine (fun _ => -1) (fun _ => 1)).seq (p.parallel keep)).seq corrected
  ((combine (fun _ => 1) (fun _ => 1)).seq (project.fork residual)).seq (p.fork keep)

/-- **Calls of the two-pass repair:** two predictor applications. -/
theorem calls_twoPass (p : QPlan A W W) (gather : QPlan A W s) (scatter : QPlan A s W)
    (table : QPlan A (s + s) (s + s)) :
    (twoPass p gather scatter table).calls =
      2 * p.calls + 2 * gather.calls + 2 * scatter.calls + table.calls := by
  simp only [twoPass, calls_seq, calls_fork, calls_parallel, calls_combine, calls_route]
  omega

/-- **Action of the two-pass repair** on a bank. -/
theorem applyAt_twoPass (p : QPlan A W W) (gather : QPlan A W s) (scatter : QPlan A s W)
    (table : QPlan A (s + s) (s + s)) (x : Bank A h W) :
    (twoPass p gather scatter table).applyAt h x =
      let px := p.applyAt h x
      let out := table.applyAt h (Fin.append (gather.applyAt h px) (gather.applyAt h x))
      let z := scatter.applyAt h (leftPart out)
      let fz := scatter.applyAt h (rightPart out)
      fun i ω => px i ω - (p.applyAt h z) i ω + fz i ω := by
  dsimp only
  simp only [twoPass, applyAt_seq, applyAt_fork, applyAt_route, Function.comp_id,
    applyAt_parallel_parts, leftPart_append, rightPart_append, applyAt_combine]
  have proj : Fin.append (p.applyAt h x) x ∘ Fin.castAdd W = p.applyAt h x :=
    leftPart_append ..
  rw [proj]
  funext i ω
  ring

end QPlan

end FTPaper
