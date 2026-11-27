import FTPaper.QMain
import FTPaper.Window

/-!
# The Hoeffding window for the end-to-end template

With half-width `t` and `2t² ≥ (m+1) ln 80`, take the window `[⌈(m+1)/2 − t⌉, ⌊(m+1)/2 + t⌋]`.
Then at most a `1/40` fraction of the shifts falls outside it, so `checks ≤ rows / 40`.
-/

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open OAI.Computability.NearSquareRoot.KernelPass.Rect.Binary (Label card_label System)
open scoped OAI.Computability.NearSquareRoot.CyclotomicCode
open Finset

namespace FTPaper

/-- ZMod-2 signatures as bit vectors. -/
def toBits {M : ℕ} (γ : Fin M → ZMod 2) : Fin M → Bool := fun j => decide (γ j = 1)

lemma toBits_bijective (M : ℕ) : Function.Bijective (toBits (M := M)) := by
  constructor
  · intro γ₁ γ₂ h
    funext j
    have hj := congrFun h j
    have hz : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    simp only [toBits] at hj
    rcases hz (γ₁ j) with h1 | h1 <;> rcases hz (γ₂ j) with h2 | h2 <;> simp_all
  · intro k
    refine ⟨fun j => if k j then 1 else 0, ?_⟩
    funext j
    cases h : k j <;> simp [toBits, h]

lemma mismatch_zero_eq_weight {M : ℕ} (γ : Fin M → ZMod 2) : mismatch 0 γ = weight (toBits γ) := by
  unfold mismatch weight toBits
  congr 1
  ext j
  have hz : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hz (γ j) with h | h <;> simp [h]

/-- **At most `2^M / 40` shifts lie outside the Hoeffding window.** -/
theorem outside_card_le {M : ℕ} (hM : 0 < M) (t : ℝ) (ht : 0 ≤ t)
    (htm : M * Real.log 80 ≤ 2 * t ^ 2) :
    ((outside ⌈(M : ℝ) / 2 - t⌉₊ ⌊(M : ℝ) / 2 + t⌋₊ (0 : Fin M → ZMod 2)).card : ℝ) ≤ 2 ^ M / 40 := by
  have hcard : (outside ⌈(M : ℝ) / 2 - t⌉₊ ⌊(M : ℝ) / 2 + t⌋₊ (0 : Fin M → ZMod 2)).card
      = (univ.filter fun k : Fin M → Bool => t < |(weight k : ℝ) - M / 2|).card := by
    refine Finset.card_bij (fun γ _ => toBits γ) ?_ ?_ ?_
    · intro γ hγ
      simp only [outside, Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
      rw [mismatch_zero_eq_weight, mem_window_iff t ht] at hγ
      exact lt_of_not_ge hγ
    · intro γ₁ _ γ₂ _ h
      exact (toBits_bijective M).1 h
    · intro k hk
      obtain ⟨γ, rfl⟩ := (toBits_bijective M).2 k
      refine ⟨γ, ?_, rfl⟩
      simp only [outside, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      rw [mismatch_zero_eq_weight, mem_window_iff t ht]
      exact not_le.mpr hk
  rw [hcard]
  exact window_fraction t ht hM htm

/-- **With the Hoeffding window, `checks ≤ rows / 40`.** -/
theorem checks_le (L b m R : ℕ) (t : ℝ) (ht : 0 ≤ t) (htm : (m + 1 : ℕ) * Real.log 80 ≤ 2 * t ^ 2) :
    (checks L b m R ⌈((m + 1 : ℕ) : ℝ) / 2 - t⌉₊ ⌊((m + 1 : ℕ) : ℝ) / 2 + t⌋₊ : ℝ)
      ≤ (rows L b m R : ℝ) / 40 := by
  have h := outside_card_le (M := m + 1) (Nat.succ_pos m) t ht htm
  have hrows : (rows L b m R : ℝ) = Fintype.card (Label L b) * R * 2 ^ (m + 1) := by
    simp only [rows, Row, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, ZMod.card]
    push_cast; ring
  rw [hrows, checks, Nat.cast_mul, Nat.cast_mul]
  have hL : (0 : ℝ) ≤ Fintype.card (Label L b) * R := by positivity
  calc (Fintype.card (Label L b) : ℝ) * R *
        ((outside ⌈((m + 1 : ℕ) : ℝ) / 2 - t⌉₊ ⌊((m + 1 : ℕ) : ℝ) / 2 + t⌋₊ (0 : Fin (m + 1) → ZMod 2)).card : ℝ)
      ≤ (Fintype.card (Label L b) : ℝ) * R * (2 ^ (m + 1) / 40) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast h) hL
    _ = _ := by ring


/-- **Theorem 1 (direct conversions), end to end in OpenAI's routing.** Take an odd number `m + 1`
of queries, a routing system with `m + 1 ≤ q^{L/2}`, and the Hoeffding window with
`t = ⌈√((m+1) ln 80 / 2)⌉`. There is a plan that computes the normalized Walsh–Hadamard
transform on every row (`QPlan.Correct`), with at most
`12 (3√(m+1) + 2) · D (1 + b)^L + A/10` child calls per row. -/
theorem theorem1_direct (L b m R : ℕ) (S : System L b) (hodd : m + 1 ≡ 1 [MOD 2]) (hb : 1 ≤ b)
    (hq : m + 1 ≤ (2 ^ b) ^ (L / 2)) (hR : 0 < R) :
    ∃ p : QPlan (Charged.Axes (m := m) S.geometry) (rows L b m R) (rows L b m R),
      QPlan.Correct p ∧
      (p.calls : ℝ) / rows L b m R
        ≤ 12 * (3 * Real.sqrt ((m + 1 : ℕ) : ℝ) + 2) * S.D * (1 + b) ^ L
          + (Charged.Axes (m := m) S.geometry : ℝ) / 10 := by
  set t : ℝ := (⌈Real.sqrt (((m + 1 : ℕ) : ℝ) * Real.log 80 / 2)⌉₊ : ℝ) with ht_def
  set u := ⌈((m + 1 : ℕ) : ℝ) / 2 - t⌉₊ with hu
  set v := ⌊((m + 1 : ℕ) : ℝ) / 2 + t⌋₊ with hv
  obtain ⟨p, hp, hcalls⟩ := template_end_to_end L b m R u v S hodd hb hq
  refine ⟨p, hp, ?_⟩
  have ht0 : 0 ≤ t := Nat.cast_nonneg _
  have hsq0 : 0 ≤ Real.sqrt (((m + 1 : ℕ) : ℝ) * Real.log 80 / 2) := Real.sqrt_nonneg _
  have htm : ((m + 1 : ℕ) : ℝ) * Real.log 80 ≤ 2 * t ^ 2 := by
    have h1 : Real.sqrt (((m + 1 : ℕ) : ℝ) * Real.log 80 / 2) ≤ t := Nat.le_ceil _
    have h2 : (Real.sqrt (((m + 1 : ℕ) : ℝ) * Real.log 80 / 2)) ^ 2
        = ((m + 1 : ℕ) : ℝ) * Real.log 80 / 2 :=
      Real.sq_sqrt (by have := Real.log_nonneg (show (1 : ℝ) ≤ 80 by norm_num); positivity)
    nlinarith
  have hchk := checks_le L b m R t ht0 htm
  -- window width `v − u ≤ 2t ≤ 3√(m+1) + 2`
  have hwidth : ((v - u : ℕ) : ℝ) ≤ 3 * Real.sqrt ((m + 1 : ℕ) : ℝ) + 2 := by
    have hw := window_width_le (m := m + 1) t ht0
    have hsub : ((v - u : ℕ) : ℝ) ≤ 2 * t := by
      rcases le_total u v with h | h
      · rw [Nat.cast_sub h]; simp only [hu, hv]; exact hw
      · rw [Nat.sub_eq_zero_of_le h]; simp only [Nat.cast_zero]; linarith
    have hsqrt : Real.sqrt (((m + 1 : ℕ) : ℝ) * Real.log 80 / 2) ≤ 3 / 2 * Real.sqrt ((m + 1 : ℕ) : ℝ) := by
      have hlog : Real.log 80 / 2 ≤ 9 / 4 := by linarith [log_eighty_le]
      have hm0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      calc Real.sqrt (((m + 1 : ℕ) : ℝ) * Real.log 80 / 2)
          = Real.sqrt (((m + 1 : ℕ) : ℝ) * (Real.log 80 / 2)) := by ring_nf
        _ ≤ Real.sqrt (((m + 1 : ℕ) : ℝ) * (9 / 4)) := Real.sqrt_le_sqrt (by nlinarith)
        _ = 3 / 2 * Real.sqrt ((m + 1 : ℕ) : ℝ) := by
            rw [Real.sqrt_mul hm0, show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num,
              Real.sqrt_sq (by norm_num)]; ring
    have htle : t ≤ Real.sqrt (((m + 1 : ℕ) : ℝ) * Real.log 80 / 2) + 1 :=
      (Nat.ceil_lt_add_one hsq0).le
    linarith
  -- assemble
  have hrows0 : (0 : ℝ) < rows L b m R := by
    have : 0 < rows L b m R := Fintype.card_pos_iff.mpr ⟨⟨Classical.arbitrary _, ⟨0, hR⟩, 0⟩⟩
    exact_mod_cast this
  have hcalls' : (p.calls : ℝ) ≤ 2 * ((v - u : ℕ) : ℝ) * (6 * S.D * (1 + b) ^ L * rows L b m R)
      + 4 * (checks L b m R u v : ℝ) * (Charged.Axes (m := m) S.geometry : ℝ) := by
    exact_mod_cast hcalls
  rw [div_le_iff₀ hrows0]
  have hA : (0 : ℝ) ≤ (Charged.Axes (m := m) S.geometry : ℝ) := Nat.cast_nonneg _
  have hDb : (0 : ℝ) ≤ 6 * S.D * (1 + b) ^ L * rows L b m R := by positivity
  calc (p.calls : ℝ) ≤ 2 * ((v - u : ℕ) : ℝ) * (6 * S.D * (1 + b) ^ L * rows L b m R)
        + 4 * (checks L b m R u v : ℝ) * (Charged.Axes (m := m) S.geometry : ℝ) := hcalls'
    _ ≤ 2 * (3 * Real.sqrt ((m + 1 : ℕ) : ℝ) + 2) * (6 * S.D * (1 + b) ^ L * rows L b m R)
        + 4 * ((rows L b m R : ℝ) / 40) * (Charged.Axes (m := m) S.geometry : ℝ) := by
        gcongr
    _ = (12 * (3 * Real.sqrt ((m + 1 : ℕ) : ℝ) + 2) * S.D * (1 + b) ^ L
          + (Charged.Axes (m := m) S.geometry : ℝ) / 10) * rows L b m R := by ring

end FTPaper
