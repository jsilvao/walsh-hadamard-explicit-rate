import OAI.Computability.NearSquareRoot.KernelBinaryTemplate

/-!
# Lemma R1 against OpenAI's actual routing (paper: Lemma 7.1)

Everything here is derived from OpenAI's Lean construction of the binary template
(vendored, `OAI/NOTICE.md`), not from a cost model.

* `lemmaR1_pencil`: their compiled rectangle pencil (`geometricPencil`), for **arbitrary** dyadic
  stage coefficients, uses at most `6·D·(1 + b)^L` calls per row, where `q = 2^b`, provided the
  alphabet is large enough (`m + 1 ≤ q^{L/2}`).
* `stageBound_le`: the same bound for their per-stage budget `stageBound`.
* `oai_template_cost`: their full one-level template (a plan proved `Correct`, i.e. computing
  the normalized Walsh–Hadamard transform on every row) uses at most
  `4 · clockPeriod m · 6D(1+b)^L · W + 4 · q^L · checks · A` calls on `W` rows.
-/

open OAI.Computability.NearSquareRoot
open OAI.Computability.NearSquareRoot.KernelPass
open OAI.Computability.NearSquareRoot.KernelPass.Rect.Binary
open OAI.Computability.NearSquareRoot.KernelPassSaving
open OAI.Computability.NearSquareRoot.PencilSearch
open scoped OAI.Computability.NearSquareRoot.CyclotomicCode

namespace FTPaper

/-- The arithmetic behind Lemma R1: with `m₁ ≤ q^{L/2}` and `b ≥ 1`,
`2·(q^L (1+b)^L) + m₁ · 2^L · q^{L/2} ≤ 3 · q^L (1+b)^L`. -/
lemma routing_arith (L b m₁ : ℕ) (hb : 1 ≤ b) (hm : m₁ ≤ (2 ^ b) ^ (L / 2)) :
    2 * (2 ^ b) ^ L * (1 + b) ^ L + m₁ * (2 ^ L * (2 ^ b) ^ (L / 2))
      ≤ 3 * ((2 ^ b) ^ L * (1 + b) ^ L) := by
  have h1 : m₁ * (2 ^ b) ^ (L / 2) ≤ (2 ^ b) ^ L := by
    calc m₁ * (2 ^ b) ^ (L / 2) ≤ (2 ^ b) ^ (L / 2) * (2 ^ b) ^ (L / 2) :=
          Nat.mul_le_mul_right _ hm
      _ = (2 ^ b) ^ (L / 2 + L / 2) := by rw [← pow_add]
      _ ≤ (2 ^ b) ^ L := Nat.pow_le_pow_right (Nat.one_le_two_pow) (by omega)
  have h2 : 2 ^ L ≤ (1 + b) ^ L := Nat.pow_le_pow_left (by omega) L
  have h3 : m₁ * (2 ^ L * (2 ^ b) ^ (L / 2)) ≤ (2 ^ b) ^ L * (1 + b) ^ L := by
    calc m₁ * (2 ^ L * (2 ^ b) ^ (L / 2)) = 2 ^ L * (m₁ * (2 ^ b) ^ (L / 2)) := by ring
      _ ≤ (1 + b) ^ L * (2 ^ b) ^ L := Nat.mul_le_mul h2 h1
      _ = (2 ^ b) ^ L * (1 + b) ^ L := by ring
  linarith

/-- **Lemma R1 (OpenAI's routing, any dyadic stage coefficients).** The compiled pencil on
`q^L` labels with `|W|` rows each uses at most `6·D·(1+b)^L` calls per row. -/
theorem lemmaR1_pencil {L b : ℕ} (S : System L b) (m : ℕ) {W : Type} [Fintype W] [DecidableEq W]
    (B₀ : W → W → Coefficient) (B : Fin (m + 1) → W → W → Coefficient)
    (hb : 1 ≤ b) (hm : m + 1 ≤ (2 ^ b) ^ (L / 2)) :
    (geometricPencil S m B₀ B).calls ≤ 6 * S.D * (1 + b) ^ L * ((2 ^ b) ^ L * Fintype.card W) := by
  have h := calls_geometricPencil S m B₀ B
  have ha := routing_arith L b (m + 1) hb hm
  calc (geometricPencil S m B₀ B).calls
      ≤ 2 * S.D * Fintype.card W *
          (2 * (2 ^ b) ^ L * (1 + b) ^ L + (m + 1) * (2 ^ L * (2 ^ b) ^ (L / 2))) := h
    _ ≤ 2 * S.D * Fintype.card W * (3 * ((2 ^ b) ^ L * (1 + b) ^ L)) :=
        Nat.mul_le_mul_left _ ha
    _ = 6 * S.D * (1 + b) ^ L * ((2 ^ b) ^ L * Fintype.card W) := by ring

/-- **Lemma R1 for the per-stage budget** used in OpenAI's template. -/
theorem stageBound_le (L b m D : ℕ) (hb : 1 ≤ b) (hm : m ≤ (2 ^ b) ^ (L / 2)) :
    stageBound L b m D ≤ 6 * D * (1 + b) ^ L * (labels L b * expandedWidth m) := by
  have ha := routing_arith L b m hb hm
  calc stageBound L b m D
      = 2 * D * expandedWidth m *
          (2 * labels L b * (1 + b) ^ L + m * (2 ^ L * (2 ^ b) ^ (L / 2))) := rfl
    _ ≤ 2 * D * expandedWidth m * (3 * ((2 ^ b) ^ L * (1 + b) ^ L)) := by
        apply Nat.mul_le_mul_left
        simpa [labels] using ha
    _ = 6 * D * (1 + b) ^ L * (labels L b * expandedWidth m) := by simp [labels]; ring

/-- **One level of OpenAI's template, cost derived from their Lean plan.** For every routing
system and odd `m ≥ 2` with `m ≤ q^{L/2}`, there is a plan that is `Correct`, i.e. it computes
the normalized transform on all `W = q^L · expandedWidth m` rows, and whose call count is at
most `4·clockPeriod(m)·6D(1+b)^L·W + 4·q^L·expandedChecks(m)·A`. -/
theorem oai_template_cost {L b m : ℕ} (S : System L b) (hm2 : 2 ≤ m) (hodd : m ≡ 1 [MOD 2])
    (hb : 1 ≤ b) (hm : m ≤ (2 ^ b) ^ (L / 2)) :
    ∃ t : Plan (axes m S.D) (labels L b * expandedWidth m) (labels L b * expandedWidth m),
      Correct t ∧
      t.calls ≤ 4 * clockPeriod m * (6 * S.D * (1 + b) ^ L * (labels L b * expandedWidth m))
        + 4 * labels L b * expandedChecks m * axes m S.D := by
  obtain ⟨t, ht, stage, hs, hc⟩ := compiled_system S hm2 hodd
  refine ⟨t, ht, hc.trans ?_⟩
  rw [callBound]
  have := stageBound_le L b m S.D hb hm
  have := Nat.mul_le_mul_left (4 * clockPeriod m) (hs.trans this)
  omega

end FTPaper
