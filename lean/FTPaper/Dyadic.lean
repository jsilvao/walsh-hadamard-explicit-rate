import Mathlib

/-!
# Dyadic coefficients cannot express the window predictor

OpenAI's plan language has only dyadic coefficients, while our Horner predictor interpolates
`c ↦ (-1)^c` on a window of consecutive counts. No polynomial with coefficients in `ℤ[1/2]` does
this on four consecutive integers: after clearing the power of two, its third difference is an
integer divisible by `6`, while the third difference of `(-1)^c` is `∓8`.

This is the reason for `QPlan` (rational coefficients). Paper: Proposition 7.3.
-/

namespace FTPaper

/-- The third difference of `t^n` at an integer is divisible by `6`. -/
lemma six_dvd_third_diff (n : ℕ) (u : ℤ) :
    (6 : ℤ) ∣ (u + 3) ^ n - 3 * (u + 2) ^ n + 3 * (u + 1) ^ n - u ^ n := by
  have h2 : (2 : ℤ) ∣ (u + 3) ^ n - 3 * (u + 2) ^ n + 3 * (u + 1) ^ n - u ^ n := by
    have hA : (2 : ℤ) ∣ (u + 3) ^ n - (u + 1) ^ n := by
      have := sub_dvd_pow_sub_pow (u + 3) (u + 1) n
      rwa [show u + 3 - (u + 1) = 2 by ring] at this
    have hB : (2 : ℤ) ∣ (u + 2) ^ n - u ^ n := by
      have := sub_dvd_pow_sub_pow (u + 2) u n
      rwa [show u + 2 - u = 2 by ring] at this
    have e : (u + 3) ^ n - 3 * (u + 2) ^ n + 3 * (u + 1) ^ n - u ^ n
        = ((u + 3) ^ n - (u + 1) ^ n) - 3 * ((u + 2) ^ n - u ^ n)
          + 2 * (2 * (u + 1) ^ n - 2 * u ^ n) := by ring
    rw [e]
    exact (hA.sub (hB.mul_left 3)).add (dvd_mul_right 2 _)
  have h3 : (3 : ℤ) ∣ (u + 3) ^ n - 3 * (u + 2) ^ n + 3 * (u + 1) ^ n - u ^ n := by
    have hA : (3 : ℤ) ∣ (u + 3) ^ n - u ^ n := by
      have := sub_dvd_pow_sub_pow (u + 3) u n
      rwa [show u + 3 - u = 3 by ring] at this
    have e : (u + 3) ^ n - 3 * (u + 2) ^ n + 3 * (u + 1) ^ n - u ^ n
        = ((u + 3) ^ n - u ^ n) + 3 * ((u + 1) ^ n - (u + 2) ^ n) := by ring
    rw [e]
    exact hA.add (dvd_mul_right 3 _)
  generalize (u + 3) ^ n - 3 * (u + 2) ^ n + 3 * (u + 1) ^ n - u ^ n = x at h2 h3 ⊢
  omega

/-- Clearing a common power of two from the coefficients turns the third difference of a
polynomial into an integer combination of the third differences of the monomials. -/
lemma third_diff_sum (c : ℕ → ℚ) (z : ℕ → ℤ) (e : ℕ) (hz : ∀ i, c i * 2 ^ e = z i) (u : ℤ)
    (N : ℕ) :
    (2 : ℚ) ^ e * ((∑ i ∈ Finset.range N, c i * ((u : ℚ) + 3) ^ i)
      - 3 * (∑ i ∈ Finset.range N, c i * ((u : ℚ) + 2) ^ i)
      + 3 * (∑ i ∈ Finset.range N, c i * ((u : ℚ) + 1) ^ i)
      - (∑ i ∈ Finset.range N, c i * (u : ℚ) ^ i))
    = ((∑ i ∈ Finset.range N,
        z i * ((u + 3) ^ i - 3 * (u + 2) ^ i + 3 * (u + 1) ^ i - u ^ i) : ℤ) : ℚ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    push_cast at ih ⊢
    rw [← hz N]
    linear_combination ih

/-- **No dyadic window predictor.** A polynomial over `ℚ` whose coefficients all become integers
after multiplication by `2^e` cannot equal `(-1)^c` at four consecutive integers `c`. -/
theorem no_dyadic_window (P : Polynomial ℚ) (e : ℕ) (hP : ∀ n, ∃ z : ℤ, P.coeff n * 2 ^ e = z)
    (u : ℤ) (hval : ∀ i : ℕ, i ≤ 3 → P.eval ((u : ℚ) + i) = (-1 : ℚ) ^ (u + i)) : False := by
  choose z hz using hP
  have hev : ∀ x : ℚ, P.eval x = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * x ^ i :=
    fun x => Polynomial.eval_eq_sum_range x
  have h := third_diff_sum P.coeff z e hz u (P.natDegree + 1)
  rw [← hev, ← hev, ← hev, ← hev] at h
  set S : ℤ := ∑ i ∈ Finset.range (P.natDegree + 1),
    z i * ((u + 3) ^ i - 3 * (u + 2) ^ i + 3 * (u + 1) ^ i - u ^ i) with hS
  have h6 : (6 : ℤ) ∣ S :=
    Finset.dvd_sum fun i _ => Dvd.dvd.mul_left (six_dvd_third_diff i u) _
  have hm1 : (-1 : ℚ) ≠ 0 := by norm_num
  have v0 := hval 0 (by norm_num)
  have v1 := hval 1 (by norm_num)
  have v2 := hval 2 (by norm_num)
  have v3 := hval 3 (by norm_num)
  push_cast at v0 v1 v2 v3
  rw [add_zero] at v0
  rw [v0, v1, v2, v3, zpow_add₀ hm1, zpow_add₀ hm1, zpow_add₀ hm1] at h
  norm_num at h
  -- `h : 2^e * (-8 * (-1)^u) = S`, up to normalization
  rcases Int.even_or_odd u with hu | hu
  · rw [hu.neg_one_zpow] at h
    have hS' : S = -(2 ^ (e + 3)) := by
      have : (S : ℚ) = -(2 ^ (e + 3)) := by rw [← h]; ring
      exact_mod_cast this
    rw [hS'] at h6
    have h6' : (6 : ℤ) ∣ 2 ^ (e + 3) := (dvd_neg).mp h6
    have h6n : (6 : ℕ) ∣ 2 ^ (e + 3) := by exact_mod_cast h6'
    have h3 : 3 ∣ 2 ^ (e + 3) := dvd_trans (by norm_num) h6n
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  · rw [hu.neg_one_zpow] at h
    have hS' : S = 2 ^ (e + 3) := by
      have : (S : ℚ) = 2 ^ (e + 3) := by rw [← h]; ring
      exact_mod_cast this
    rw [hS'] at h6
    have h6n : (6 : ℕ) ∣ 2 ^ (e + 3) := by exact_mod_cast h6
    have h3 : 3 ∣ 2 ^ (e + 3) := dvd_trans (by norm_num) h6n
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

end FTPaper
