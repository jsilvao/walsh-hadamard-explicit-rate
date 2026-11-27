import FTPaper.RoutingOAI
import FTPaper.Free.Pencil

/-!
# Lemma R1 for the pencil with free endpoint plans

The same bound as `lemmaR1_pencil`, for `geometricPencilF`: at most `6·D·(1+b)^L` calls per row.
-/

open OAI.Computability.NearSquareRoot
open OAI.Computability.NearSquareRoot.KernelPass
open OAI.Computability.NearSquareRoot.KernelPass.Rect.Binary
open scoped OAI.Computability.NearSquareRoot.CyclotomicCode

namespace FTPaper

/-- **Lemma R1 for the free pencil.** -/
theorem lemmaR1_pencilF {L b : ℕ} (S : System L b) (m : ℕ) {W : Type} [Fintype W] [DecidableEq W]
    (B₀ : W → W → Coefficient) (B : Fin (m + 1) → W → W → Coefficient)
    (hb : 1 ≤ b) (hm : m + 1 ≤ (2 ^ b) ^ (L / 2)) :
    (geometricPencilF S m B₀ B).calls ≤ 6 * S.D * (1 + b) ^ L * ((2 ^ b) ^ L * Fintype.card W) := by
  have h := calls_geometricPencilF S m B₀ B
  have ha := routing_arith L b (m + 1) hb hm
  calc (geometricPencilF S m B₀ B).calls
      ≤ 2 * S.D * Fintype.card W *
          (2 * (2 ^ b) ^ L * (1 + b) ^ L + (m + 1) * (2 ^ L * (2 ^ b) ^ (L / 2))) := h
    _ ≤ 2 * S.D * Fintype.card W * (3 * ((2 ^ b) ^ L * (1 + b) ^ L)) :=
        Nat.mul_le_mul_left _ ha
    _ = 6 * S.D * (1 + b) ^ L * ((2 ^ b) ^ L * Fintype.card W) := by ring

end FTPaper
