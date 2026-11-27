import FTPaper.QCircuit
import FTPaper.QRouted

/-!
# The Walsh–Hadamard upper bound through our template, in OpenAI's circuit model

For every `ε > 0` there is a constant `D` such that, over every field of characteristic `0`,
`C(H^{⊗k}) ≤ D · 2^k · (1+k)^{1/2+ε}` for every `k`. Here `C` is OpenAI's `complexity`, the
number of binary linear gates.

The proof runs one template of Theorem 1 (`theorem1_routed`) through OpenAI's batch recursion
(`walsh_bound_of_plan`). The template uses `m + 1 = 2^x − 1` queries, with `x = 16^r` and
`2^r ≥ 22/ε`.
-/

open OAI.LinearAlgebra.FiniteFourier
open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open OAI.Computability.NearSquareRoot.KernelPass.Rect.Binary (System Label card_label system)
open scoped OAI.Computability.NearSquareRoot.CyclotomicCode

namespace FTPaper

/-- An explicit `x` whose routing loss is at most `ε (x + 1)`. -/
lemma exists_routing_x {ε : ℝ} (hε : 0 < ε) :
    ∃ x : ℕ, 2 ≤ x ∧ 11 * Real.sqrt (x * Real.logb 2 x) + 11 ≤ ε * (x + 1) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (22 / ε) (one_lt_two : (1 : ℝ) < 2)
  set r := n + 1 with hr
  have h2r : 22 / ε ≤ (2 : ℝ) ^ r := by
    rw [hr, pow_succ]; nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) n]
  refine ⟨16 ^ r, ?_, ?_⟩
  · calc 2 ≤ 16 := by norm_num
      _ ≤ 16 ^ r := Nat.le_self_pow (by omega) 16
  · have hx : ((16 ^ r : ℕ) : ℝ) = (2 : ℝ) ^ (4 * r) := by
      push_cast; rw [pow_mul]; norm_num
    have hlog : Real.logb 2 ((16 ^ r : ℕ) : ℝ) = 4 * r := by
      rw [hx, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; push_cast; ring
    -- `4 r ≤ 4^r`
    have h4r : (4 * r : ℝ) ≤ (4 : ℝ) ^ r := by
      have h1 : r + 1 ≤ 2 ^ r := Nat.lt_two_pow_self
      have h2 : 4 * r ≤ (r + 1) * (r + 1) := by nlinarith
      have h3 : (r + 1) * (r + 1) ≤ 2 ^ r * 2 ^ r := Nat.mul_le_mul h1 h1
      have h4 : (4 * r : ℕ) ≤ 4 ^ r := by
        calc 4 * r ≤ 2 ^ r * 2 ^ r := h2.trans h3
          _ = 4 ^ r := by rw [← mul_pow]; norm_num
      exact_mod_cast h4
    have hsq : Real.sqrt (((16 ^ r : ℕ) : ℝ) * Real.logb 2 ((16 ^ r : ℕ) : ℝ)) ≤ (8 : ℝ) ^ r := by
      rw [hlog]
      have h8 : (0 : ℝ) ≤ (8 : ℝ) ^ r := by positivity
      rw [Real.sqrt_le_left h8]
      have : ((16 ^ r : ℕ) : ℝ) * (4 * r) ≤ ((16 ^ r : ℕ) : ℝ) * (4 : ℝ) ^ r :=
        mul_le_mul_of_nonneg_left h4r (by positivity)
      calc ((16 ^ r : ℕ) : ℝ) * (4 * r) ≤ ((16 ^ r : ℕ) : ℝ) * (4 : ℝ) ^ r := this
        _ = ((8 : ℝ) ^ r) ^ 2 := by
          push_cast; rw [← mul_pow, ← pow_mul, mul_comm r 2, pow_mul]; norm_num
    have h8pos : (1 : ℝ) ≤ (8 : ℝ) ^ r := one_le_pow₀ (by norm_num)
    have hkey : 22 * (8 : ℝ) ^ r ≤ ε * ((16 ^ r : ℕ) : ℝ) := by
      have h16 : ((16 ^ r : ℕ) : ℝ) = (8 : ℝ) ^ r * (2 : ℝ) ^ r := by
        push_cast; rw [← mul_pow]; norm_num
      rw [h16]
      have := (div_le_iff₀ hε).mp h2r
      nlinarith [pow_pos (show (0 : ℝ) < 8 by norm_num) r]
    nlinarith

/-- **The saving condition for the routed template.** -/
lemma saving_of_routing {x m A : ℕ} {ε : ℝ} (hε : 0 < ε) (hx : 2 ≤ x) (hm : m + 1 = 2 ^ x - 1)
    (hxε : 11 * Real.sqrt (x * Real.logb 2 x) + 11 ≤ ε * (x + 1)) (hA : 2 * (m + 1) ≤ A) :
    2 * ((20 / 3 * Real.sqrt ((m + 1 : ℕ) : ℝ) + 40 / 9)
        * (2 : ℝ) ^ (11 * Real.sqrt (x * Real.logb 2 x) + 7) + 1)
      < ((2 * A : ℕ) : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  set s := Real.sqrt ((m + 1 : ℕ) : ℝ) with hs
  set E := 11 * Real.sqrt (x * Real.logb 2 x) + 7 with hE
  set P := (2 : ℝ) ^ E with hP
  have hs1 : 1 ≤ s := by
    rw [hs, Real.one_le_sqrt]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hP1 : 1 ≤ P := Real.one_le_rpow (by norm_num) hE0
  -- the left side
  have hL : 2 * ((20 / 3 * s + 40 / 9) * P + 1) ≤ 218 / 9 * (s * P) := by
    have hsP : 1 ≤ s * P := by nlinarith
    nlinarith
  -- the right side
  have h2x : (4 : ℝ) ≤ (2 : ℝ) ^ x := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this]; exact pow_le_pow_right₀ (by norm_num) hx
  have hm1 : ((m + 1 : ℕ) : ℝ) = (2 : ℝ) ^ x - 1 := by
    have h1 : 1 ≤ 2 ^ x := Nat.one_le_two_pow
    rw [hm]; push_cast [Nat.cast_sub h1]; ring
  have hbase : (4 : ℝ) * ((m + 1 : ℕ) : ℝ) ≤ ((2 * A : ℕ) : ℝ) := by
    have : 4 * (m + 1) ≤ 2 * A := by omega
    exact_mod_cast this
  have h4m0 : (0 : ℝ) < 4 * ((m + 1 : ℕ) : ℝ) := by positivity
  have hθ : (0 : ℝ) ≤ 1 / 2 + ε := by positivity
  have hR1 : (4 * ((m + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 2 + ε) ≤ ((2 * A : ℕ) : ℝ) ^ ((1 : ℝ) / 2 + ε) :=
    Real.rpow_le_rpow h4m0.le hbase hθ
  have hhalf : (4 * ((m + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 2) = 2 * s := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hlow : (2 : ℝ) ^ ((x : ℝ) + 1) ≤ 4 * ((m + 1 : ℕ) : ℝ) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_one, hm1]
    linarith
  have hεpow : ((2 : ℝ) ^ ((x : ℝ) + 1)) ^ ε ≤ (4 * ((m + 1 : ℕ) : ℝ)) ^ ε :=
    Real.rpow_le_rpow (by positivity) hlow hε.le
  have hεpow' : (2 : ℝ) ^ (ε * ((x : ℝ) + 1)) = ((2 : ℝ) ^ ((x : ℝ) + 1)) ^ ε := by
    rw [mul_comm, Real.rpow_mul (by norm_num)]
  have hexp : E + 4 ≤ ε * ((x : ℝ) + 1) := by rw [hE]; linarith
  have h16 : 16 * P ≤ (2 : ℝ) ^ (ε * ((x : ℝ) + 1)) := by
    calc 16 * P = (2 : ℝ) ^ (E + 4) := by
          rw [Real.rpow_add (by norm_num), hP]; norm_num; ring
      _ ≤ (2 : ℝ) ^ (ε * ((x : ℝ) + 1)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hsplit : (4 * ((m + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 2 + ε)
      = (4 * ((m + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 2) * (4 * ((m + 1 : ℕ) : ℝ)) ^ ε :=
    Real.rpow_add h4m0 _ _
  have hR : 32 * (s * P) ≤ ((2 * A : ℕ) : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
    refine le_trans ?_ hR1
    rw [hsplit, hhalf]
    have : 16 * P ≤ (4 * ((m + 1 : ℕ) : ℝ)) ^ ε := h16.trans (hεpow'.symm ▸ hεpow)
    nlinarith
  have hsP0 : 0 < s * P := by positivity
  nlinarith

/-- **For every `ε > 0`, `C(H^{⊗k}) ≤ D · 2^k (1+k)^{1/2+ε}` over every field of characteristic
`0`**, in OpenAI's model of binary linear circuits. The proof goes through our Theorem 1
template (`theorem1_routed`), compiled into OpenAI's circuit-level program model
(`walsh_bound_of_plan`). -/
theorem walsh_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ D > (0 : ℝ), ∀ (F : Type) [Field F] [CharZero F] (k : ℕ),
      (complexity (primeTransform 2 k (-1 : F)) : ℝ) ≤ D * 2 ^ k * (1 + (k : ℝ)) ^ ((1 : ℝ) / 2 + ε) := by
  obtain ⟨x, hx2, hxε⟩ := exists_routing_x hε
  have h4 : 4 ≤ 2 ^ x := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hx2
  set m := 2 ^ x - 2 with hm_def
  have hm1 : m + 1 = 2 ^ x - 1 := by omega
  have hodd : m + 1 ≡ 1 [MOD 2] := by
    have hev : 2 ∣ 2 ^ x := dvd_pow_self 2 (by omega)
    obtain ⟨t, ht⟩ := hev
    rw [hm1, ht]
    have : 2 * t - 1 = 2 * (t - 1) + 1 := by omega
    rw [this]
    simp [Nat.ModEq, Nat.add_mod]
  have hm : m + 1 ≤ 2 ^ x := by omega
  set d := 2 * (m + 2 + 2 * halfLabel x * 2 ^ alphabetExp x) with hd_def
  have hd : 2 * (m + 2 + 2 * halfLabel x * 2 ^ alphabetExp x) ≤ 10 ^ d :=
    (Nat.lt_pow_self (by norm_num)).le
  obtain ⟨p, hp, hc⟩ := theorem1_routed x m d hx2 hodd hm hd
  have hAeq := axes_eq (2 * halfLabel x) (alphabetExp x) m (system (2 * halfLabel x) (alphabetExp x))
  have hD1 : 1 ≤ (system (2 * halfLabel x) (alphabetExp x)).D := (system _ _).dimension_pos
  have hA : 2 * (m + 1) ≤
      Charged.Axes (m := m) (system (2 * halfLabel x) (alphabetExp x)).geometry := by
    rw [hAeq]; omega
  have hW : 0 < rows (2 * halfLabel x) (alphabetExp x) m (20 ^ d) := by
    rw [rows_eq]
    have : 0 < Fintype.card (Label (2 * halfLabel x) (alphabetExp x)) := by
      rw [card_label]; positivity
    positivity
  have hW' : (0 : ℝ) < rows (2 * halfLabel x) (alphabetExp x) m (20 ^ d) := by exact_mod_cast hW
  have hsave : ((2 * p.calls : ℕ) : ℝ) / (rows (2 * halfLabel x) (alphabetExp x) m (20 ^ d) : ℕ)
      < ((2 * Charged.Axes (m := m) (system (2 * halfLabel x) (alphabetExp x)).geometry : ℕ) : ℝ)
          ^ ((1 : ℝ) / 2 + ε) := by
    have h2 : ((2 * p.calls : ℕ) : ℝ) / (rows (2 * halfLabel x) (alphabetExp x) m (20 ^ d) : ℕ)
        = 2 * ((p.calls : ℝ) / (rows (2 * halfLabel x) (alphabetExp x) m (20 ^ d) : ℕ)) := by
      push_cast; ring
    rw [h2]
    refine lt_of_le_of_lt ?_ (saving_of_routing hε hx2 hm1 hxε hA)
    linarith [hc]
  exact walsh_bound_of_plan p hp (by omega) hW (by linarith) hsave

end FTPaper
