import FTPaper.LemmaS.Lattice
import FTPaper.LemmaS.Krawtchouk

/-!
# The Walsh–Hadamard transform on harmonic strings (Lemma S, string action)

`(H f)(γ) = ∑_δ (-1)^{|γ ∩ δ|} f(δ)` factors as zeta transform ∘ `(-2)^{|β|}` ∘ dual zeta
transform. The zeta transforms are `∑_l R^l / l!` and `∑_k L^k / k!` layer by layer.

So `H` maps the string of a harmonic `h` on layer `i` into itself:
`(H R^a h)(S) = β(|S| - i) · (R^{|S|-i} h)(S)`. For `c ≤ n = m - 2i` the coefficient is
`β(c) = (-2)^i (a!/c!) K_a(c; n)`.
-/

namespace FTPaper.LemmaS

open Finset

variable {m : ℕ}

/-- The Walsh–Hadamard transform on functions of subsets. -/
def hada : Module.End ℚ (Fn m) where
  toFun f γ := ∑ δ, (-1 : ℚ) ^ (γ ∩ δ).card * f δ
  map_add' f g := by funext γ; simp [mul_add, sum_add_distrib]
  map_smul' c f := by funext γ; simp [mul_sum, mul_left_comm]

lemma hada_apply (f : Fn m) (γ : Finset (Fin m)) :
    hada f γ = ∑ δ, (-1 : ℚ) ^ (γ ∩ δ).card * f δ := rfl

/-- The zeta factorization `H = Z (-2)^{|·|} Z'`, pointwise. -/
theorem hada_eq_zeta (f : Fn m) (γ : Finset (Fin m)) :
    hada f γ = ∑ β ∈ γ.powerset, (-2 : ℚ) ^ β.card * ∑ δ ∈ univ.filter (β ⊆ ·), f δ := by
  rw [hada_apply]
  symm
  simp only [mul_sum]
  rw [sum_comm' (t' := univ) (s' := fun δ => (γ ∩ δ).powerset)]
  · refine sum_congr rfl fun δ _ => ?_
    rw [← sum_mul]
    congr 1
    have := sum_pow_mul_eq_add_pow (-2 : ℚ) 1 (γ ∩ δ)
    simp only [one_pow, mul_one] at this
    rw [this]
    norm_num
  · intro β δ
    simp only [mem_powerset, mem_filter, mem_univ, true_and, and_true, subset_inter_iff]

/-- `(R^l f)(T) = l! ∑_{β ⊆ T, |β| + l = |T|} f(β)`. -/
lemma R_pow_apply (f : Fn m) (l : ℕ) (T : Finset (Fin m)) :
    (R ^ l) f T = (l.factorial : ℚ) * ∑ β ∈ T.powerset with β.card + l = T.card, f β := by
  induction l generalizing T with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, one_mul,
      add_zero]
    rw [sum_eq_single T]
    · intro β hβ hne
      simp only [mem_filter, mem_powerset] at hβ
      exact absurd (eq_of_subset_of_card_le hβ.1 hβ.2.ge) hne
    · intro h
      exact absurd (by simp) h
  | succ l ih =>
    rw [pow_succ', Module.End.mul_apply, R_apply]
    simp only [ih]
    rw [← mul_sum, Nat.factorial_succ]
    push_cast
    rw [mul_comm ((l : ℚ) + 1), mul_assoc]
    congr 1
    rw [sum_comm' (t' := T.powerset.filter (fun β => β.card + (l + 1) = T.card))
      (s' := fun β => T \ β)]
    · rw [mul_sum]
      refine sum_congr rfl fun β hβ => ?_
      simp only [mem_filter, mem_powerset] at hβ
      rw [sum_const, card_sdiff_of_subset hβ.1, nsmul_eq_mul]
      congr 1
      have : T.card - β.card = l + 1 := by omega
      rw [this]; push_cast; ring
    · intro t β
      simp only [mem_filter, mem_powerset, mem_sdiff]
      constructor
      · rintro ⟨ht, hsub, hcard⟩
        have htβ : t ∉ β := fun h => by simpa using hsub h
        have hsubT : β ⊆ T := hsub.trans (erase_subset t T)
        rw [card_erase_of_mem ht] at hcard
        have := card_pos.mpr ⟨t, ht⟩
        exact ⟨⟨ht, htβ⟩, hsubT, by omega⟩
      · rintro ⟨⟨ht, htβ⟩, hsubT, hcard⟩
        have := card_pos.mpr ⟨t, ht⟩
        refine ⟨ht, ?_, ?_⟩
        · intro x hx
          rw [mem_erase]
          exact ⟨fun h => htβ (by rw [← h]; exact hx), hsubT hx⟩
        · rw [card_erase_of_mem ht]; omega

/-- `(L^k f)(S) = k! ∑_{δ ⊇ S, |δ| = |S| + k} f(δ)`. -/
lemma L_pow_apply (f : Fn m) (k : ℕ) (S : Finset (Fin m)) :
    (L ^ k) f S
      = (k.factorial : ℚ) * ∑ δ ∈ univ.filter (fun δ => S ⊆ δ ∧ δ.card = S.card + k), f δ := by
  induction k generalizing S with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, one_mul,
      add_zero]
    rw [sum_eq_single S]
    · intro δ hδ hne
      simp only [mem_filter, mem_univ, true_and] at hδ
      exact absurd (eq_of_subset_of_card_le hδ.1 hδ.2.le).symm hne
    · intro h
      exact absurd (by simp) h
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, L_apply]
    simp only [ih]
    rw [← mul_sum, Nat.factorial_succ]
    push_cast
    rw [mul_comm ((k : ℚ) + 1), mul_assoc]
    congr 1
    rw [sum_comm' (t' := univ.filter (fun δ => S ⊆ δ ∧ δ.card = S.card + (k + 1)))
      (s' := fun δ => δ \ S)]
    · rw [mul_sum]
      refine sum_congr rfl fun δ hδ => ?_
      simp only [mem_filter, mem_univ, true_and] at hδ
      rw [sum_const, card_sdiff_of_subset hδ.1, nsmul_eq_mul]
      congr 1
      have : δ.card - S.card = k + 1 := by omega
      rw [this]; push_cast; ring
    · intro s δ
      simp only [mem_filter, mem_univ, true_and, mem_sdiff, mem_compl]
      constructor
      · rintro ⟨hs, hsub, hcard⟩
        rw [card_insert_of_notMem hs] at hcard
        exact ⟨⟨hsub (mem_insert_self s S), hs⟩, (subset_insert s S).trans hsub, by omega⟩
      · rintro ⟨⟨hsδ, hs⟩, hsub, hcard⟩
        refine ⟨hs, insert_subset hsδ hsub, ?_⟩
        rw [card_insert_of_notMem hs]; omega

/-! ## `L^k` on a harmonic string -/

/-- The coefficient of `L^k R^a h = strL n a k • R^{a-k} h`. -/
def strL (n a k : ℕ) : ℚ := (a.descFactorial k : ℚ) * ((n - a + k).descFactorial k : ℚ)

lemma L_pow_R_pow_le {h : Fn m} {i : ℕ} (hh : IsHarm h i) {a k : ℕ} (hk : k ≤ a)
    (ha : 2 * i + a ≤ m) : (L ^ k) ((R ^ a) h) = strL (m - 2 * i) a k • (R ^ (a - k)) h := by
  induction k with
  | zero => simp [strL]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih (by omega), map_smul]
    have e : a - k = (a - (k + 1)) + 1 := by omega
    rw [e, L_R_pow hh, smul_smul]
    congr 1
    unfold strL
    rw [Nat.descFactorial_succ, show m - 2 * i - a + (k + 1) = (m - 2 * i - a + k) + 1 by omega,
      Nat.succ_descFactorial_succ]
    push_cast
    have c1 : ((a - k : ℕ) : ℚ) = a - k := Nat.cast_sub (by omega)
    have c2 : ((a - (k + 1) : ℕ) : ℚ) = a - k - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have c3 : ((m - 2 * i - a : ℕ) : ℚ) = m - 2 * i - a := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [c1, c2, c3]
    ring

lemma L_pow_R_pow_gt {h : Fn m} {i : ℕ} (hh : IsHarm h i) {a k : ℕ} (hk : a < k) :
    (L ^ k) ((R ^ a) h) = 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, k = (d + 1) + a := ⟨k - a - 1, by omega⟩
  rw [pow_add, Module.End.mul_apply, L_pow_R_pow hh a, map_smul, pow_succ, Module.End.mul_apply,
    hh.2, map_zero, smul_zero]

/-! ## The string action of `H` -/

/-- The coefficient of `H R^a h` on `R^c h`. -/
def hcoef (n i a c : ℕ) : ℚ :=
  ∑ b ∈ range (min a c + 1),
    (-2 : ℚ) ^ (i + b) / ((a - b).factorial : ℚ) / ((c - b).factorial : ℚ) * strL n a (a - b)

/-- The dual zeta transform of `R^a h` at `β`. -/
lemma zetaD_R_pow {h : Fn m} {i : ℕ} (hh : IsHarm h i) {a : ℕ} (ha : 2 * i + a ≤ m)
    (β : Finset (Fin m)) :
    ∑ δ ∈ univ.filter (β ⊆ ·), (R ^ a) h δ =
      if i ≤ β.card ∧ β.card ≤ i + a then
        strL (m - 2 * i) a (i + a - β.card) / ((i + a - β.card).factorial : ℚ)
          * (R ^ (β.card - i)) h β
      else 0 := by
  have hlay : OnLayer ((R ^ a) h) (i + a) := R_pow_onLayer hh.1 a
  by_cases hβ : β.card ≤ i + a
  · set k := i + a - β.card with hk
    -- restrict to the right layer and use `L^k`
    have hsum : ∑ δ ∈ univ.filter (β ⊆ ·), (R ^ a) h δ
        = ∑ δ ∈ univ.filter (fun δ => β ⊆ δ ∧ δ.card = β.card + k), (R ^ a) h δ := by
      symm
      apply sum_subset
      · intro δ hδ
        simp only [mem_filter, mem_univ, true_and] at hδ ⊢
        exact hδ.1
      · intro δ hδ hnot
        simp only [mem_filter, mem_univ, true_and, not_and] at hδ hnot
        apply hlay
        intro hc
        exact hnot hδ (by omega)
    have hL := L_pow_apply ((R ^ a) h) k β
    have hfac : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    rw [hsum]
    by_cases hi : i ≤ β.card
    · rw [ite_eq_left ⟨hi, hβ⟩]
      rw [L_pow_R_pow_le hh (by omega) ha] at hL
      have e : a - k = β.card - i := by omega
      rw [e] at hL
      simp only [Pi.smul_apply, smul_eq_mul] at hL
      field_simp
      linarith
    · rw [ite_eq_right (fun h => hi h.1)]
      rw [L_pow_R_pow_gt hh (by omega : a < k)] at hL
      simp only [Pi.zero_apply] at hL
      have := hL.symm
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hfac
      · exact h0
  · rw [ite_eq_right (fun h => hβ h.2)]
    apply sum_eq_zero
    intro δ hδ
    simp only [mem_filter, mem_univ, true_and] at hδ
    apply hlay
    have := card_le_card hδ
    omega

/-- Summing over one shell inside `S` is a power of `R`. -/
lemma sum_shell (g : Fn m) (S : Finset (Fin m)) {w l : ℕ} (hw : w + l = S.card) :
    ∑ β ∈ S.powerset with β.card = w, g β = (R ^ l) g S / (l.factorial : ℚ) := by
  rw [R_pow_apply]
  have hfac : (l.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero l
  rw [mul_div_cancel_left₀ _ hfac]
  apply sum_congr
  · ext β
    simp only [mem_filter, mem_powerset]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  · intro _ _; rfl

/-- **The string action of `H`.** For harmonic `h` on layer `i` and `2i + a ≤ m`,
`(H R^a h)(S) = hcoef (m-2i) i a (|S|-i) · (R^{|S|-i} h)(S)` if `i ≤ |S|`, and `0` otherwise. -/
theorem hada_R_pow_apply {h : Fn m} {i : ℕ} (hh : IsHarm h i) {a : ℕ} (ha : 2 * i + a ≤ m)
    (S : Finset (Fin m)) :
    hada ((R ^ a) h) S =
      if i ≤ S.card then hcoef (m - 2 * i) i a (S.card - i) * (R ^ (S.card - i)) h S else 0 := by
  rw [hada_eq_zeta]
  simp only [zetaD_R_pow hh ha]
  -- group the subsets of `S` by their size
  rw [← sum_fiberwise_of_maps_to (g := fun β : Finset (Fin m) => β.card)
    (t := range (S.card + 1)) (fun β hβ => by
      rw [mem_powerset] at hβ; rw [mem_range]; have := card_le_card hβ; omega)]
  have hshell : ∀ w ∈ range (S.card + 1),
      ∑ β ∈ S.powerset with β.card = w, (-2 : ℚ) ^ β.card *
        (if i ≤ β.card ∧ β.card ≤ i + a then
          strL (m - 2 * i) a (i + a - β.card) / ((i + a - β.card).factorial : ℚ)
            * (R ^ (β.card - i)) h β else 0)
      = if i ≤ w ∧ w ≤ i + a then
          (-2 : ℚ) ^ w * (strL (m - 2 * i) a (i + a - w) / ((i + a - w).factorial : ℚ))
            * ((R ^ (S.card - w)) ((R ^ (w - i)) h) S / ((S.card - w).factorial : ℚ))
        else 0 := by
    intro w hw
    have hw' : w ≤ S.card := Nat.lt_succ_iff.mp (mem_range.mp hw)
    have hrw : ∀ β ∈ S.powerset.filter (fun β => β.card = w), (-2 : ℚ) ^ β.card *
        (if i ≤ β.card ∧ β.card ≤ i + a then
          strL (m - 2 * i) a (i + a - β.card) / ((i + a - β.card).factorial : ℚ)
            * (R ^ (β.card - i)) h β else 0)
        = if i ≤ w ∧ w ≤ i + a then
            (-2 : ℚ) ^ w * (strL (m - 2 * i) a (i + a - w) / ((i + a - w).factorial : ℚ))
              * (R ^ (w - i)) h β
          else 0 := by
      intro β hβ
      rw [mem_filter] at hβ
      rw [hβ.2]
      split_ifs <;> ring
    rw [sum_congr rfl hrw]
    split_ifs with hc
    · rw [← mul_sum, sum_shell _ S (by omega : w + (S.card - w) = S.card)]
    · simp
  rw [sum_congr rfl hshell]
  by_cases hiS : i ≤ S.card
  · rw [ite_eq_left hiS]
    set c := S.card - i with hc
    set F : ℕ → ℚ := fun w => if i ≤ w ∧ w ≤ i + a then
          (-2 : ℚ) ^ w * (strL (m - 2 * i) a (i + a - w) / ((i + a - w).factorial : ℚ))
            * ((R ^ (S.card - w)) ((R ^ (w - i)) h) S / ((S.card - w).factorial : ℚ))
        else 0 with hF
    have himg : ∑ w ∈ range (S.card + 1), F w
        = ∑ w ∈ (range (min a c + 1)).image (fun b => i + b), F w := by
      symm
      apply sum_subset
      · intro w hw
        rw [mem_image] at hw
        obtain ⟨b, hb, rfl⟩ := hw
        rw [mem_range] at hb ⊢
        have := min_le_right a c
        omega
      · intro w hw hnot
        simp only [hF]
        rw [ite_eq_right]
        rintro ⟨h1, h2⟩
        apply hnot
        rw [mem_image]
        refine ⟨w - i, ?_, by omega⟩
        rw [mem_range] at hw ⊢
        have : w - i ≤ min a c := le_min (by omega) (by omega)
        omega
    rw [himg, sum_image (by intro x _ y _ hxy; simpa using hxy)]
    unfold hcoef
    rw [sum_mul]
    refine sum_congr rfl fun b hb => ?_
    have hb' : b ≤ min a c := Nat.lt_succ_iff.mp (mem_range.mp hb)
    have hba : b ≤ a := hb'.trans (min_le_left a c)
    have hbc : b ≤ c := hb'.trans (min_le_right a c)
    simp only [hF]
    rw [ite_eq_left ⟨by omega, by omega⟩]
    have e1 : i + a - (i + b) = a - b := by omega
    have e2 : S.card - (i + b) = c - b := by omega
    have e3 : i + b - i = b := by omega
    rw [e1, e2, e3, ← Module.End.mul_apply, ← pow_add, show c - b + b = c by omega]
    ring
  · rw [ite_eq_right hiS]
    apply sum_eq_zero
    intro w hw
    rw [ite_eq_right]
    rintro ⟨h1, _⟩
    have := Nat.lt_succ_iff.mp (mem_range.mp hw)
    omega

end FTPaper.LemmaS
