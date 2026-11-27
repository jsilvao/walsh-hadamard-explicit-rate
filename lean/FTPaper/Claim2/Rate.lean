import FTPaper.Claim2.RateStep

/-!
# The sharper rate (paper: Theorem 1.1; working label: Claim 2)

**Theorem (`walsh_claim2`).** Over every field of characteristic `0`, for every `k`,

`C(H^{⊗k}) ≤ 2^k · √(k+1) · 2^{Φ(n)}`,   `n = ⌊log₂(k+1)⌋`,   `Φ(n) = 400 √((n+2) log₂(n+2))`,

that is `C(H^{⊗k}) ≤ N √(log N) · 2^{O(√(log log N · log log log N))}` with `N = 2^k`.

The proof is a strong induction on `k`. At size `k` it uses the structured template at routing
parameter `x = ⌊n/40⌋`, which grows with `k`: the local cost is `2^{O(x)}` per row
(`xplan2_cost`), the leftover digits cost `O(h)` (`tcost_classical`), and the calls per row lose
`2^{γ(x)}` with `γ(x) = 11 √(x log₂ x) + 12` against the floor `√A`. The exponent `Φ` absorbs
`γ(x)` at every level (`Φ_step`).
-/

set_option linter.unusedSectionVars false

open OAI.LinearAlgebra.FiniteFourier
open OAI.Computability.NearSquareRoot

namespace FTPaper.Claim2

/-! ## Parameter bounds at `x` -/

lemma xrA_le (x : ℕ) (hx : 4 ≤ x) : xr x + 2 * xA x ≤ 2 ^ (2 * x + 7) := by
  have hr := xr_le x (by omega)
  have hA := xA_le x (by omega)
  have hx1 : x + 1 ≤ 2 ^ x := Nat.lt_two_pow_self
  have h4 : (2 : ℕ) ^ (2 * x) = 2 ^ x * 2 ^ x := by rw [← pow_add]; ring_nf
  have h7 : (2 : ℕ) ^ (2 * x + 7) = 128 * (2 ^ x * 2 ^ x) := by
    rw [pow_add, h4]; ring
  have hsq : (x + 1) ^ 2 ≤ 2 ^ x * 2 ^ x := by nlinarith
  have hx2 : 16 ≤ 2 ^ x := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hx
  unfold eW at hr
  rw [h7]
  nlinarith

lemma xA_ge (x : ℕ) (hx : 2 ≤ x) : 2 ^ (x + 1) ≤ 2 * xA x := by
  have h := xA_pos x
  have hm := xm2 x hx
  have : 2 ^ (x + 1) = 2 * 2 ^ x := by rw [pow_succ]; ring
  omega

/-- The loss per level. -/
noncomputable def γx (x : ℕ) : ℝ := 11 * Real.sqrt (x * Real.logb 2 x) + 12

lemma Bx_le (x : ℕ) :
    4 * Bx x ≤ Real.sqrt ((2 * xA x : ℕ) : ℝ) * (2 : ℝ) ^ γx x := by
  set m1 : ℝ := ((xm x + 1 : ℕ) : ℝ) with hm1
  have hm1pos : 1 ≤ m1 := by rw [hm1]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hsm : 1 ≤ Real.sqrt m1 := by rw [Real.one_le_sqrt]; exact hm1pos
  have hA : 4 * m1 ≤ ((2 * xA x : ℕ) : ℝ) := by
    have := xA_pos x
    rw [hm1]; push_cast
    have : ((2 * (xm x + 1) : ℕ) : ℝ) ≤ (xA x : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  have hsA : 2 * Real.sqrt m1 ≤ Real.sqrt ((2 * xA x : ℕ) : ℝ) := by
    have : Real.sqrt (4 * m1) = 2 * Real.sqrt m1 := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [← this]
    exact Real.sqrt_le_sqrt hA
  set P := (2 : ℝ) ^ (11 * Real.sqrt (x * Real.logb 2 x) + 7) with hP
  have hP1 : 1 ≤ P := Real.one_le_rpow (by norm_num) (by positivity)
  have hγ : (2 : ℝ) ^ γx x = 32 * P := by
    rw [γx, hP, show 11 * Real.sqrt (x * Real.logb 2 x) + 12
      = (11 * Real.sqrt (x * Real.logb 2 x) + 7) + 5 by ring, Real.rpow_add (by norm_num)]
    norm_num
    ring
  unfold Bx
  rw [← hP, hγ]
  -- `4 B ≤ 2√m₁ · 32 P`
  have hgoal : 4 * ((20 / 3 * Real.sqrt m1 + 40 / 9) * P + 1) ≤ 2 * Real.sqrt m1 * (32 * P) := by
    nlinarith
  calc 4 * ((20 / 3 * Real.sqrt m1 + 40 / 9) * P + 1) ≤ 2 * Real.sqrt m1 * (32 * P) := hgoal
    _ ≤ Real.sqrt ((2 * xA x : ℕ) : ℝ) * (32 * P) := by gcongr

/-! ## The exponent -/

/-- The exponent: `Φ(n) = 400 √((n+2) log₂(n+2))`. -/
noncomputable def Φ (n : ℕ) : ℝ := 400 * Real.sqrt (((n : ℝ) + 2) * Real.logb 2 ((n : ℝ) + 2))

lemma logb_ge_one' (n : ℕ) : 1 ≤ Real.logb 2 ((n : ℝ) + 2) := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_one]
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

lemma Φ_nonneg (n : ℕ) : 0 ≤ Φ n := by unfold Φ; positivity

lemma Φ_mono {n n' : ℕ} (h : n ≤ n') : Φ n ≤ Φ n' := by
  unfold Φ
  have h1 : (n : ℝ) + 2 ≤ (n' : ℝ) + 2 := by
    have : (n : ℝ) ≤ n' := by exact_mod_cast h
    linarith
  have h2 : Real.logb 2 ((n : ℝ) + 2) ≤ Real.logb 2 ((n' : ℝ) + 2) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) h1
  have h3 := logb_ge_one' n
  have h4 : ((n : ℝ) + 2) * Real.logb 2 ((n : ℝ) + 2) ≤ ((n' : ℝ) + 2) * Real.logb 2 ((n' : ℝ) + 2) :=
    mul_le_mul h1 h2 (by linarith) (by positivity)
  gcongr

lemma Φ_ge (n : ℕ) : 400 * Real.sqrt ((n : ℝ) + 2) ≤ Φ n := by
  unfold Φ
  have h3 := logb_ge_one' n
  gcongr
  nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- The core estimate: `√(N L) − √((N − y) L') ≥ √(N L)/92`. -/
lemma core_real {N y L L' : ℝ} (hN : 256 ≤ N) (hy1 : N / 41 ≤ y) (hy2 : y ≤ N / 2)
    (hL8 : 8 ≤ L) (hL' : L - 1 ≤ L') (hL'L : L' ≤ L) :
    Real.sqrt (N * L) / 92 ≤ Real.sqrt (N * L) - Real.sqrt ((N - y) * L') := by
  have hN0 : 0 ≤ N := by linarith
  have hNy : 0 ≤ N - y := by linarith
  have hL0 : 0 ≤ L' := by linarith
  have e1 : Real.sqrt (N * L) = Real.sqrt N * Real.sqrt L := Real.sqrt_mul hN0 L
  have e2 : Real.sqrt ((N - y) * L') = Real.sqrt (N - y) * Real.sqrt L' := Real.sqrt_mul hNy L'
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  have hsNy : 0 ≤ Real.sqrt (N - y) := Real.sqrt_nonneg _
  have hsNyN : Real.sqrt (N - y) ≤ Real.sqrt N := Real.sqrt_le_sqrt (by linarith)
  -- `√N − √(N−y) ≥ y/(2√N)`
  have hprod : (Real.sqrt N - Real.sqrt (N - y)) * (Real.sqrt N + Real.sqrt (N - y)) = y := by
    have a := Real.sq_sqrt hN0
    have b := Real.sq_sqrt hNy
    nlinarith
  have hdiff : y / (2 * Real.sqrt N) ≤ Real.sqrt N - Real.sqrt (N - y) := by
    rw [div_le_iff₀ (by positivity)]
    have : (Real.sqrt N - Real.sqrt (N - y)) * (Real.sqrt N + Real.sqrt (N - y))
        ≤ (Real.sqrt N - Real.sqrt (N - y)) * (2 * Real.sqrt N) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  -- `√L' ≥ (9/10) √L`
  have hL'78 : 7 / 8 * L ≤ L' := by linarith
  have hsqL : 9 / 10 * Real.sqrt L ≤ Real.sqrt L' := by
    have : Real.sqrt ((81 / 100) * L) ≤ Real.sqrt L' := Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_mul (by norm_num), show (81 / 100 : ℝ) = (9 / 10) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)] at this
  -- `y/(2√N) ≥ √N/82`
  have hyN : Real.sqrt N / 82 ≤ y / (2 * Real.sqrt N) := by
    rw [le_div_iff₀ (by positivity)]
    have : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0
    nlinarith
  have hsL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hsL' : 0 ≤ Real.sqrt L' := Real.sqrt_nonneg _
  have hLL : Real.sqrt L' ≤ Real.sqrt L := Real.sqrt_le_sqrt hL'L
  rw [e1, e2]
  have step1 : Real.sqrt L' * (Real.sqrt N - Real.sqrt (N - y))
      ≤ Real.sqrt N * Real.sqrt L - Real.sqrt (N - y) * Real.sqrt L' := by nlinarith
  have step2 : 9 / 10 * Real.sqrt L * (Real.sqrt N / 82)
      ≤ Real.sqrt L' * (Real.sqrt N - Real.sqrt (N - y)) := by
    apply mul_le_mul hsqL (hyN.trans hdiff) (by positivity) hsL'
  nlinarith

lemma sqrt_ge_45 {N L : ℝ} (hN : 256 ≤ N) (hL : 8 ≤ L) : 45 ≤ Real.sqrt (N * L) := by
  rw [Real.le_sqrt (by norm_num) (by nlinarith)]
  nlinarith

/-- **The exponent absorbs one level of the recursion.** -/
lemma Φ_step (n : ℕ) (hn : 256 ≤ n) : γx (n / 40) + Φ (n - (n / 40 + 1)) + 1 ≤ Φ n := by
  set x := n / 40 with hxdef
  have hx40 : x * 40 ≤ n := Nat.div_mul_le_self n 40
  have hxlt : n < (x + 1) * 40 := by
    have := Nat.lt_div_mul_add (a := n) (b := 40) (by norm_num)
    rw [hxdef]; linarith
  have hx6 : 6 ≤ x := by omega
  have hxn : x + 1 ≤ n := by omega
  set N : ℝ := (n : ℝ) + 2 with hNdef
  set y : ℝ := (x : ℝ) + 1 with hydef
  have hcast : (((n - (x + 1) : ℕ) : ℝ) + 2) = N - y := by
    rw [Nat.cast_sub hxn]; push_cast; rw [hNdef, hydef]; ring
  have hn' : (256 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : 256 ≤ N := by rw [hNdef]; linarith
  have hx40' : (x : ℝ) * 40 ≤ n := by exact_mod_cast hx40
  have hxlt' : (n : ℝ) < ((x : ℝ) + 1) * 40 := by exact_mod_cast hxlt
  have hy1 : N / 41 ≤ y := by rw [hNdef, hydef]; nlinarith
  have hy2 : y ≤ N / 2 := by rw [hNdef, hydef]; nlinarith
  set L := Real.logb 2 N with hLdef
  set L' := Real.logb 2 (N - y) with hL'def
  have hL8 : 8 ≤ L := by
    rw [hLdef, Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    norm_num
    linarith
  have hL' : L - 1 ≤ L' := by
    have h1 : Real.logb 2 (N / 2) ≤ L' :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
    have h2 : Real.logb 2 (N / 2) = L - 1 := by
      rw [Real.logb_div (by linarith) (by norm_num), Real.logb_self_eq_one (by norm_num)]
    linarith
  have hL'L : L' ≤ L := Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  have hcore := core_real hN hy1 hy2 hL8 hL' hL'L
  have h45 := sqrt_ge_45 hN hL8
  -- the loss `γ(x)`
  have hxpos : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hlogx : Real.logb 2 x ≤ L :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) (by rw [hNdef]; linarith)
  have hlogx0 : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hxpos
  have hγs : Real.sqrt (x * Real.logb 2 x) ≤ Real.sqrt (N * L) / 6 := by
    have h1 : (x : ℝ) * Real.logb 2 x ≤ (N * L) / 36 := by
      have : (x : ℝ) ≤ N / 40 := by rw [hNdef]; linarith
      have : (x : ℝ) * Real.logb 2 x ≤ N / 40 * L :=
        mul_le_mul this hlogx hlogx0 (by linarith)
      nlinarith
    calc Real.sqrt (x * Real.logb 2 x) ≤ Real.sqrt ((N * L) / 36) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt (N * L) / 6 := by
          rw [Real.sqrt_div' _ (by norm_num), show (36 : ℝ) = 6 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  -- assemble
  unfold γx Φ
  rw [hcast, ← hNdef]
  nlinarith


/-! ## The induction -/

lemma two_pow_rpow (n : ℕ) : (2 : ℝ) ^ ((n : ℕ) : ℝ) = (2 : ℝ) ^ n := Real.rpow_natCast 2 n

/-- **The normalized cost is at most `√(k+1) · 2^{Φ(⌊log₂(k+1)⌋)}`.** -/
theorem tcost_le (F : Type) [Field F] [CharZero F] (k : ℕ) :
    tcost F k ≤ Real.sqrt ((k : ℝ) + 1) * (2 : ℝ) ^ Φ (Nat.log 2 (k + 1)) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  set n := Nat.log 2 (k + 1) with hn
  have hk1 : k + 1 < 2 ^ (n + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hk2 : 2 ^ n ≤ k + 1 := Nat.pow_log_le_self 2 (by omega)
  have hsk : 0 ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_nonneg _
  have hk1r : (k : ℝ) + 1 < 2 ^ (n + 1) := by exact_mod_cast hk1
  have hk2r : (2 : ℝ) ^ n ≤ (k : ℝ) + 1 := by exact_mod_cast hk2
  have hsq : Real.sqrt ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1) = (k : ℝ) + 1 :=
    Real.mul_self_sqrt (by positivity)
  have hΦ0 := Φ_nonneg n
  have h2Φ : (1 : ℝ) ≤ (2 : ℝ) ^ Φ n := Real.one_le_rpow (by norm_num) hΦ0
  by_cases hsmall : n < 256
  · -- small sizes: the classical bound
    have hc := tcost_classical F k
    have hge : ((n + 2 : ℕ) : ℝ) ≤ Φ n := by
      have h1 := Φ_ge n
      have hn2 : (n : ℝ) + 2 ≤ 258 := by
        have : (n : ℝ) < 256 := by exact_mod_cast hsmall
        linarith
      have hs1 : 1 ≤ Real.sqrt ((n : ℝ) + 2) := by
        rw [Real.one_le_sqrt]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      have hs2 : Real.sqrt ((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 2) = (n : ℝ) + 2 :=
        Real.mul_self_sqrt (by positivity)
      have hs3 : Real.sqrt ((n : ℝ) + 2) ≤ 400 := by
        rw [Real.sqrt_le_left (by norm_num)]; linarith
      push_cast
      nlinarith
    have hpow : (2 : ℝ) ^ (n + 2) ≤ (2 : ℝ) ^ Φ n := by
      rw [← two_pow_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hge
    have h2k : 2 * Real.sqrt ((k : ℝ) + 1) ≤ (2 : ℝ) ^ (n + 2) := by
      have hs : Real.sqrt ((k : ℝ) + 1) ≤ (k : ℝ) + 1 := by
        rw [Real.sqrt_le_left (by positivity)]; nlinarith
      have : (2 : ℝ) ^ (n + 2) = 2 * 2 ^ (n + 1) := by rw [pow_succ]; ring
      linarith
    calc tcost F k ≤ 2 * ((k : ℝ) + 1) := hc
      _ = Real.sqrt ((k : ℝ) + 1) * (2 * Real.sqrt ((k : ℝ) + 1)) := by
          rw [show Real.sqrt ((k : ℝ) + 1) * (2 * Real.sqrt ((k : ℝ) + 1))
            = 2 * (Real.sqrt ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1)) by ring, hsq]
      _ ≤ Real.sqrt ((k : ℝ) + 1) * (2 : ℝ) ^ Φ n := by gcongr; linarith
  · -- large sizes: one level of the growing recursion
    push Not at hsmall
    set x := n / 40 with hxdef
    have hx40 : x * 40 ≤ n := Nat.div_mul_le_self n 40
    have hx6 : 6 ≤ x := by omega
    have hkr : xr x + 2 * xA x ≤ k := by
      have h1 := xrA_le x (by omega)
      have h2 : 2 ^ (2 * x + 7) ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : 2 ^ n = 2 * 2 ^ (n - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega
    obtain ⟨f, hfk, hAf, hstep⟩ := xstep F x (by omega) k hkr
    have ihf := ih f hfk
    set nf := Nat.log 2 (f + 1) with hnf
    -- the child is smaller by `2^{x+1}`
    have hnf_le : nf ≤ n - (x + 1) := by
      have hA := xA_ge x (by omega)
      have h1 : 2 ^ (x + 1) * (f + 1) ≤ k + 1 := (Nat.mul_le_mul_right _ hA).trans hAf
      have h2 : f + 1 < 2 ^ (n - x) := by
        have : 2 ^ (n + 1) = 2 ^ (x + 1) * 2 ^ (n - x) := by rw [← pow_add]; congr 1; omega
        have h3 : 2 ^ (x + 1) * (f + 1) < 2 ^ (x + 1) * 2 ^ (n - x) := by omega
        exact Nat.lt_of_mul_lt_mul_left h3
      have := Nat.log_lt_of_lt_pow (by omega) h2
      omega
    have hΦf : Φ nf ≤ Φ (n - (x + 1)) := Φ_mono hnf_le
    -- the calls term
    have hB := Bx_le x
    have hsA : Real.sqrt ((2 * xA x : ℕ) : ℝ) * Real.sqrt ((f : ℝ) + 1) ≤ Real.sqrt ((k : ℝ) + 1) := by
      rw [← Real.sqrt_mul (by positivity)]
      apply Real.sqrt_le_sqrt
      have : ((2 * xA x * (f + 1) : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hAf
      push_cast at this ⊢
      linarith
    have hcallterm : 4 * Bx x * tcost F f
        ≤ Real.sqrt ((k : ℝ) + 1) * ((2 : ℝ) ^ γx x * (2 : ℝ) ^ Φ (n - (x + 1))) := by
      have htf0 := tcost_nonneg F f
      have hpowf : (2 : ℝ) ^ Φ nf ≤ (2 : ℝ) ^ Φ (n - (x + 1)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hΦf
      calc 4 * Bx x * tcost F f
          ≤ Real.sqrt ((2 * xA x : ℕ) : ℝ) * (2 : ℝ) ^ γx x *
              (Real.sqrt ((f : ℝ) + 1) * (2 : ℝ) ^ Φ nf) := by gcongr
        _ ≤ Real.sqrt ((2 * xA x : ℕ) : ℝ) * (2 : ℝ) ^ γx x *
              (Real.sqrt ((f : ℝ) + 1) * (2 : ℝ) ^ Φ (n - (x + 1))) := by gcongr
        _ = (Real.sqrt ((2 * xA x : ℕ) : ℝ) * Real.sqrt ((f : ℝ) + 1)) *
              ((2 : ℝ) ^ γx x * (2 : ℝ) ^ Φ (n - (x + 1))) := by ring
        _ ≤ Real.sqrt ((k : ℝ) + 1) * ((2 : ℝ) ^ γx x * (2 : ℝ) ^ Φ (n - (x + 1))) := by
            gcongr
    -- the local term
    have hlocal : (2 : ℝ) ^ (14 * x + 14) + 2 * ((xr x + 2 * xA x : ℕ) : ℝ)
        ≤ Real.sqrt ((k : ℝ) + 1) / 2 := by
      have h1 := xrA_le x (by omega)
      have h1r : ((xr x + 2 * xA x : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * x + 7) := by exact_mod_cast h1
      have h2 : (2 : ℝ) ^ (2 * x + 7) ≤ (2 : ℝ) ^ (14 * x + 13) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : (2 : ℝ) ^ (14 * x + 16) ≤ (2 : ℝ) ^ (20 * x) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h4 : (2 : ℝ) ^ (20 * x) ≤ Real.sqrt ((k : ℝ) + 1) := by
        rw [Real.le_sqrt (by positivity) (by positivity), ← pow_mul]
        calc (2 : ℝ) ^ (20 * x * 2) ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
          _ ≤ (k : ℝ) + 1 := hk2r
      have e1 : (2 : ℝ) ^ (14 * x + 16) = 4 * 2 ^ (14 * x + 14) := by
        rw [show 14 * x + 16 = (14 * x + 14) + 2 by ring, pow_add]; norm_num; ring
      have e2 : (2 : ℝ) ^ (14 * x + 14) = 2 * 2 ^ (14 * x + 13) := by
        rw [show 14 * x + 14 = (14 * x + 13) + 1 by ring, pow_succ]; ring
      linarith
    -- the exponent
    have hstepΦ := Φ_step n hsmall
    have hexp : (2 : ℝ) ^ γx x * (2 : ℝ) ^ Φ (n - (x + 1)) ≤ (2 : ℝ) ^ Φ n / 2 := by
      rw [← Real.rpow_add (by norm_num)]
      have : (2 : ℝ) ^ Φ n / 2 = (2 : ℝ) ^ (Φ n - 1) := by
        rw [Real.rpow_sub (by norm_num), Real.rpow_one]
      rw [this]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    calc tcost F k
        ≤ (2 : ℝ) ^ (14 * x + 14) + 2 * ((xr x + 2 * xA x : ℕ) : ℝ) + 4 * Bx x * tcost F f := hstep
      _ ≤ Real.sqrt ((k : ℝ) + 1) / 2 +
            Real.sqrt ((k : ℝ) + 1) * ((2 : ℝ) ^ γx x * (2 : ℝ) ^ Φ (n - (x + 1))) := by
          linarith
      _ ≤ Real.sqrt ((k : ℝ) + 1) / 2 + Real.sqrt ((k : ℝ) + 1) * ((2 : ℝ) ^ Φ n / 2) := by
          gcongr
      _ ≤ Real.sqrt ((k : ℝ) + 1) * (2 : ℝ) ^ Φ n := by nlinarith

/-- **The sharper rate** (paper: Theorem 1.1). Over every field of characteristic `0`, for every `k`,
`C(H^{⊗k}) ≤ 2^k · √(k+1) · 2^{Φ(⌊log₂(k+1)⌋)}` with
`Φ(n) = 400 √((n+2) log₂(n+2))`. With `N = 2^k`, this is
`C(H^{⊗k}) ≤ N √(log N) · 2^{O(√(log log N · log log log N))}`. -/
theorem walsh_claim2 (F : Type) [Field F] [CharZero F] (k : ℕ) :
    (complexity (primeTransform 2 k (-1 : F)) : ℝ)
      ≤ 2 ^ k * Real.sqrt ((k : ℝ) + 1) * (2 : ℝ) ^ Φ (Nat.log 2 (k + 1)) := by
  have h := tcost_le F k
  unfold tcost at h
  rw [div_le_iff₀ (by positivity)] at h
  linarith


/-! ## When the bound beats the direct algorithm -/

/-- `Φ(n) + 1 ≤ n/2` once `n ≥ 2^32`. -/
lemma Φ_le_half (n : ℕ) (hn : 2 ^ 32 ≤ n) : Φ n + 1 ≤ (n : ℝ) / 2 := by
  set X : ℝ := (n : ℝ) + 2 with hXdef
  have hn' : (2 : ℝ) ^ 32 ≤ n := by exact_mod_cast hn
  have hX : (2 : ℝ) ^ 32 ≤ X := by rw [hXdef]; linarith
  have hX0 : 0 < X := by rw [hXdef]; positivity
  have hr8 : 0 ≤ X ^ ((1 : ℝ) / 8) := Real.rpow_nonneg hX0.le _
  -- `log₂ X ≤ 12 X^{1/8}`
  have hlog : Real.log X ≤ X ^ ((1 : ℝ) / 8) / (1 / 8) := Real.log_le_rpow_div hX0.le (by norm_num)
  have hlog2 : (2 : ℝ) / 3 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlogb : Real.logb 2 X ≤ 12 * X ^ ((1 : ℝ) / 8) := by
    rw [Real.logb, div_le_iff₀ (Real.log_pos one_lt_two)]
    have e : X ^ ((1 : ℝ) / 8) / (1 / 8) = 8 * X ^ ((1 : ℝ) / 8) := by ring
    nlinarith
  -- `X log₂ X ≤ 12 X^{9/8}`
  have e98 : X ^ ((9 : ℝ) / 8) = X * X ^ ((1 : ℝ) / 8) := by
    rw [show (9 : ℝ) / 8 = 1 + 1 / 8 by norm_num, Real.rpow_add hX0, Real.rpow_one]
  have hprod : X * Real.logb 2 X ≤ 12 * X ^ ((9 : ℝ) / 8) := by
    rw [e98]
    nlinarith
  -- `√(X log₂ X) ≤ (7/2) X^{9/16}`
  have hsqrt98 : Real.sqrt (X ^ ((9 : ℝ) / 8)) = X ^ ((9 : ℝ) / 16) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le]
    norm_num
  have h12 : Real.sqrt 12 ≤ 7 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hsq : Real.sqrt (X * Real.logb 2 X) ≤ 7 / 2 * X ^ ((9 : ℝ) / 16) := by
    calc Real.sqrt (X * Real.logb 2 X) ≤ Real.sqrt (12 * X ^ ((9 : ℝ) / 8)) :=
          Real.sqrt_le_sqrt hprod
      _ = Real.sqrt 12 * X ^ ((9 : ℝ) / 16) := by rw [Real.sqrt_mul (by norm_num), hsqrt98]
      _ ≤ 7 / 2 * X ^ ((9 : ℝ) / 16) := by
          gcongr
  -- `X^{9/16} ≤ X / 2^14`
  have hX716 : (2 : ℝ) ^ 14 ≤ X ^ ((7 : ℝ) / 16) := by
    have e : ((2 : ℝ) ^ 32) ^ ((7 : ℝ) / 16) = (2 : ℝ) ^ 14 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [← e]
    exact Real.rpow_le_rpow (by positivity) hX (by norm_num)
  have hsplit : X ^ ((9 : ℝ) / 16) * X ^ ((7 : ℝ) / 16) = X := by
    rw [← Real.rpow_add hX0]; norm_num
  have h916 : X ^ ((9 : ℝ) / 16) * 2 ^ 14 ≤ X := by
    calc X ^ ((9 : ℝ) / 16) * 2 ^ 14 ≤ X ^ ((9 : ℝ) / 16) * X ^ ((7 : ℝ) / 16) := by
          gcongr
      _ = X := hsplit
  have hpos916 : 0 ≤ X ^ ((9 : ℝ) / 16) := Real.rpow_nonneg hX0.le _
  unfold Φ
  rw [← hXdef]
  nlinarith

/-- **The bound of `walsh_claim2` improves on the direct algorithm** (`k 2^k` gates) once
`⌊log₂(k+1)⌋ ≥ 2^32`. -/
theorem walsh_claim2_below_trivial (k : ℕ) (hk : 2 ^ 32 ≤ Nat.log 2 (k + 1)) :
    2 ^ k * Real.sqrt ((k : ℝ) + 1) * (2 : ℝ) ^ Φ (Nat.log 2 (k + 1)) ≤ 2 ^ k * k := by
  set n := Nat.log 2 (k + 1) with hn
  have hk2 : 2 ^ n ≤ k + 1 := Nat.pow_log_le_self 2 (by omega)
  have hk2r : (2 : ℝ) ^ n ≤ (k : ℝ) + 1 := by exact_mod_cast hk2
  have hn1 : 1 ≤ n := le_trans (by norm_num) hk
  have hk1 : (1 : ℝ) ≤ k := by
    have : 2 ≤ k + 1 := le_trans (by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1) hk2
    exact_mod_cast (show 1 ≤ k by omega)
  have hhalf := Φ_le_half n hk
  -- `2^{n/2} ≤ √(k+1)`
  have hroot : (2 : ℝ) ^ ((n : ℝ) / 2) ≤ Real.sqrt ((k : ℝ) + 1) := by
    rw [Real.le_sqrt (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [show (n : ℝ) / 2 * ((2 : ℕ) : ℝ) = (n : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact hk2r
  have hΦ : (2 : ℝ) ^ Φ n ≤ (2 : ℝ) ^ ((n : ℝ) / 2) / 2 := by
    have : (2 : ℝ) ^ ((n : ℝ) / 2) / 2 = (2 : ℝ) ^ ((n : ℝ) / 2 - 1) := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_one]
    rw [this]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hsq : Real.sqrt ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1) = (k : ℝ) + 1 :=
    Real.mul_self_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_nonneg _
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have key : Real.sqrt ((k : ℝ) + 1) * (2 : ℝ) ^ Φ n ≤ k := by
    calc Real.sqrt ((k : ℝ) + 1) * (2 : ℝ) ^ Φ n
        ≤ Real.sqrt ((k : ℝ) + 1) * ((2 : ℝ) ^ ((n : ℝ) / 2) / 2) := by gcongr
      _ ≤ Real.sqrt ((k : ℝ) + 1) * (Real.sqrt ((k : ℝ) + 1) / 2) := by gcongr
      _ = ((k : ℝ) + 1) / 2 := by
          rw [show Real.sqrt ((k : ℝ) + 1) * (Real.sqrt ((k : ℝ) + 1) / 2)
            = (Real.sqrt ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1)) / 2 by ring, hsq]
      _ ≤ k := by linarith
  calc 2 ^ k * Real.sqrt ((k : ℝ) + 1) * (2 : ℝ) ^ Φ n
      = 2 ^ k * (Real.sqrt ((k : ℝ) + 1) * (2 : ℝ) ^ Φ n) := by ring
    _ ≤ 2 ^ k * k := by gcongr


end FTPaper.Claim2
