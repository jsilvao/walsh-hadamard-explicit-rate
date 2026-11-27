import Mathlib

/-!
# Krawtchouk numbers and their two-tailed principal submatrices (Lemma S, algebraic core)

`K_a(y; n) = ∑_{j+k=a} (-1)^j C(y,j) C(n-y,k)` is the Walsh–Hadamard sum `∑_{|δ|=a} (-1)^{γ·δ}`
over `δ ∈ 𝔽₂ⁿ` at any `γ` of weight `y`. On the isotypic components of the symmetric group, the
Walsh–Hadamard transform acts through these numbers (paper: Section 9, proof of Lemma 9.1).

Main result, `kraw_twoTail_injective`. Let `n` be odd and `2ℓ ≤ n + 1`, and let
`A = {0, …, ℓ-1} ∪ {n-ℓ+1, …, n}` be two tails. Then the principal submatrix `[K_a(b)]_{a,b ∈ A}`
is invertible over `ℚ`. The proof:
* the symmetries `K_a(n-y) = (-1)^a K_a(y)` and `K_{n-a}(y) = (-1)^y K_a(y)` fold the two tails
  together (a parity split);
* `K_a` is a polynomial in `y` of degree `a` with leading coefficient `(-2)^a / a!`;
* so each half reduces to evaluating such polynomials at `ℓ` distinct points (Vandermonde).
-/

namespace FTPaper.LemmaS

open Finset Polynomial

/-- The Krawtchouk number `K_a(y; n)`. -/
def kraw (n a y : ℕ) : ℤ :=
  ∑ p ∈ antidiagonal a, (-1) ^ p.1 * (y.choose p.1 : ℤ) * ((n - y).choose p.2 : ℤ)

lemma neg_one_pow_mul_self (j : ℕ) : ((-1 : ℤ) ^ j) * (-1) ^ j = 1 := by
  rw [← mul_pow]; simp

lemma coeff_one_sub_X_pow (y j : ℕ) :
    ((1 - X : ℤ[X]) ^ y).coeff j = (-1) ^ j * (y.choose j : ℤ) := by
  have e : (1 - X : ℤ[X]) = C (-1) * (X + C (-1)) := by
    simp only [C_neg, C_1]; ring
  rw [e, mul_pow, ← C_pow, coeff_C_mul, coeff_X_add_C_pow]
  rcases le_or_gt j y with hj | hj
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [Nat.add_sub_cancel_left, pow_add]
    have := neg_one_pow_mul_self d
    calc (-1 : ℤ) ^ j * (-1) ^ d * ((-1) ^ d * ((j + d).choose j : ℤ))
        = (-1) ^ j * ((-1) ^ d * (-1) ^ d) * ((j + d).choose j : ℤ) := by ring
      _ = (-1) ^ j * ((j + d).choose j : ℤ) := by rw [this, mul_one]
  · rw [Nat.choose_eq_zero_of_lt hj]; simp

/-- The generating function: `∑_a K_a(y) X^a = (1-X)^y (1+X)^{n-y}`. -/
lemma kraw_eq_coeff (n a y : ℕ) :
    kraw n a y = ((1 - X : ℤ[X]) ^ y * (1 + X) ^ (n - y)).coeff a := by
  rw [coeff_mul]
  unfold kraw
  refine sum_congr rfl fun p _ => ?_
  rw [coeff_one_sub_X_pow, coeff_one_add_X_pow]

/-- The second formula `K_a(y) = ∑_{b ≤ a} (-2)^b C(y,b) C(n-b,a-b)`. -/
lemma kraw_eq_alt {n y : ℕ} (hy : y ≤ n) (a : ℕ) :
    kraw n a y = ∑ b ∈ range (a + 1), (-2) ^ b * (y.choose b : ℤ) * ((n - b).choose (a - b) : ℤ) := by
  rw [kraw_eq_coeff]
  have e1 : (1 - X : ℤ[X]) = C (-2) * X + (1 + X) := by
    rw [C_neg, show (C 2 : ℤ[X]) = 2 from rfl]; ring
  rw [e1, add_pow, sum_mul, finsetSum_coeff]
  have e2 : ∀ b ∈ range (y + 1),
      ((C (-2) * X) ^ b * (1 + X) ^ (y - b) * (y.choose b : ℤ[X]) * (1 + X) ^ (n - y)).coeff a
        = if b ≤ a then (-2) ^ b * (y.choose b : ℤ) * ((n - b).choose (a - b) : ℤ) else 0 := by
    intro b hb
    have hb' : b ≤ y := Nat.lt_succ_iff.mp (mem_range.mp hb)
    have : (C (-2) * X) ^ b * (1 + X) ^ (y - b) * (y.choose b : ℤ[X]) * (1 + X) ^ (n - y)
        = C ((-2) ^ b * (y.choose b : ℤ)) * (X ^ b * (1 + X) ^ (n - b)) := by
      have hnb : n - b = (y - b) + (n - y) := by omega
      rw [hnb, pow_add, mul_pow, C_mul, C_pow, ← Polynomial.C_eq_natCast, map_natCast]
      ring
    rw [this, coeff_C_mul, coeff_X_pow_mul']
    split_ifs with h
    · rw [coeff_one_add_X_pow]
    · simp
  rw [sum_congr rfl e2, ← sum_filter]
  apply sum_subset
  · intro b hb
    rw [mem_filter, mem_range] at hb
    rw [mem_range]
    omega
  · intro b hb hnot
    rw [mem_filter, mem_range] at hnot
    rw [mem_range] at hb
    have : y < b := by
      by_contra h'
      exact hnot ⟨by omega, by omega⟩
    rw [Nat.choose_eq_zero_of_lt this]; simp

/-- Symmetry in the point: `K_a(n-y) = (-1)^a K_a(y)`. -/
theorem kraw_symm_point {n a y : ℕ} (hy : y ≤ n) :
    kraw n a (n - y) = (-1) ^ a * kraw n a y := by
  unfold kraw
  rw [Nat.sub_sub_self hy, mul_sum, ← Finset.Nat.sum_antidiagonal_swap]
  refine sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  simp only [Prod.fst_swap, Prod.snd_swap]
  have hs : ((-1 : ℤ) ^ p.2) = (-1) ^ a * (-1) ^ p.1 := by
    rw [← hp, pow_add]
    have := neg_one_pow_mul_self p.1
    calc (-1 : ℤ) ^ p.2 = ((-1) ^ p.1 * (-1) ^ p.1) * (-1) ^ p.2 := by rw [this, one_mul]
      _ = _ := by ring
  rw [hs]; ring

/-- Symmetry in the index: `K_{n-a}(y) = (-1)^y K_a(y)`. -/
theorem kraw_symm_index {n a y : ℕ} (ha : a ≤ n) (hy : y ≤ n) :
    kraw n (n - a) y = (-1) ^ y * kraw n a y := by
  unfold kraw
  rw [mul_sum]
  refine sum_bij_ne_zero (fun p _ _ => (y - p.1, (n - y) - p.2)) ?_ ?_ ?_ ?_
  · intro p hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
    have h1 : p.1 ≤ y := by
      by_contra h; apply hne; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    have h2 : p.2 ≤ n - y := by
      by_contra h; apply hne; rw [Nat.choose_eq_zero_of_lt (by omega : n - y < p.2)]; simp
    simp only
    omega
  · intro p hp hne q hq hne' heq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp hq
    have h1 : p.1 ≤ y := by
      by_contra h; apply hne; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    have h2 : p.2 ≤ n - y := by
      by_contra h; apply hne; rw [Nat.choose_eq_zero_of_lt (by omega : n - y < p.2)]; simp
    have h1' : q.1 ≤ y := by
      by_contra h; apply hne'; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    have h2' : q.2 ≤ n - y := by
      by_contra h; apply hne'; rw [Nat.choose_eq_zero_of_lt (by omega : n - y < q.2)]; simp
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext (by omega) (by omega)
  · intro q hq hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have h1 : q.1 ≤ y := by
      by_contra h; apply hne; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    have h2 : q.2 ≤ n - y := by
      by_contra h; apply hne; rw [Nat.choose_eq_zero_of_lt (by omega : n - y < q.2)]; simp
    refine ⟨(y - q.1, (n - y) - q.2), ?_, ?_, ?_⟩
    · rw [Finset.HasAntidiagonal.mem_antidiagonal]; simp only; omega
    · simp only
      rw [Nat.choose_symm h1, Nat.choose_symm h2]
      intro h
      apply hne
      have hpow : (-1 : ℤ) ^ (y - q.1) ≠ 0 := pow_ne_zero _ (by norm_num)
      have : ((y.choose q.1 : ℤ)) * ((n - y).choose q.2 : ℤ) = 0 := by
        rcases mul_eq_zero.mp h with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact absurd h'' hpow
          · rw [h'', zero_mul]
        · rw [h', mul_zero]
      rw [mul_assoc, this, mul_zero, mul_zero]
    · simp only; exact Prod.ext (by omega) (by omega)
  · intro p hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h1 : p.1 ≤ y := by
      by_contra h; apply hne; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    have h2 : p.2 ≤ n - y := by
      by_contra h; apply hne; rw [Nat.choose_eq_zero_of_lt (by omega : n - y < p.2)]; simp
    simp only
    rw [Nat.choose_symm_of_eq_add (by omega : y = (y - p.1) + p.1).symm.symm,
      Nat.choose_symm_of_eq_add (by omega : n - y = ((n - y) - p.2) + p.2).symm.symm]
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h1
    have hyd : y - p.1 = d := by omega
    rw [hyd, hd, pow_add]
    have := neg_one_pow_mul_self d
    calc (-1 : ℤ) ^ p.1 * (((p.1 + d).choose p.1 : ℕ) : ℤ) * (((n - (p.1 + d)).choose p.2 : ℕ) : ℤ)
        = (-1) ^ p.1 * ((-1) ^ d * (-1) ^ d) * (((p.1 + d).choose p.1 : ℕ) : ℤ)
            * (((n - (p.1 + d)).choose p.2 : ℕ) : ℤ) := by rw [this, mul_one]
      _ = _ := by ring

/-! ## `K_a` as a polynomial in the point -/

/-- `C(X, b) = X (X-1) ⋯ (X-b+1) / b!` over `ℚ`. -/
noncomputable def choosePoly (b : ℕ) : ℚ[X] := C ((b.factorial : ℚ)⁻¹) * descPochhammer ℚ b

lemma choosePoly_eval (y b : ℕ) : (choosePoly b).eval (y : ℚ) = (y.choose b : ℚ) := by
  unfold choosePoly
  rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  have : (b.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero b
  push_cast
  field_simp

lemma choosePoly_natDegree (b : ℕ) : (choosePoly b).natDegree = b := by
  unfold choosePoly
  have : ((b.factorial : ℚ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero b)
  rw [natDegree_C_mul this, descPochhammer_natDegree]

lemma choosePoly_coeff_self (b : ℕ) : (choosePoly b).coeff b = (b.factorial : ℚ)⁻¹ := by
  unfold choosePoly
  have h1 : (descPochhammer ℚ b).coeff b = 1 := by
    have := (monic_descPochhammer ℚ b).coeff_natDegree
    rwa [descPochhammer_natDegree] at this
  rw [coeff_C_mul, h1, mul_one]

/-- The Krawtchouk polynomial `K_a(X; n) = ∑_{b ≤ a} (-2)^b C(n-b, a-b) C(X, b)`. -/
noncomputable def krawPoly (n a : ℕ) : ℚ[X] :=
  ∑ b ∈ range (a + 1), C ((-2 : ℚ) ^ b * ((n - b).choose (a - b) : ℚ)) * choosePoly b

lemma krawPoly_eval {n y : ℕ} (hy : y ≤ n) (a : ℕ) :
    (krawPoly n a).eval (y : ℚ) = (kraw n a y : ℚ) := by
  rw [kraw_eq_alt hy]
  unfold krawPoly
  rw [eval_finsetSum]
  push_cast
  refine sum_congr rfl fun b _ => ?_
  rw [eval_mul, eval_C, choosePoly_eval]
  ring

lemma krawPoly_natDegree_le (n a : ℕ) : (krawPoly n a).natDegree ≤ a := by
  unfold krawPoly
  apply natDegree_sum_le_of_forall_le
  intro b hb
  calc (C ((-2 : ℚ) ^ b * ((n - b).choose (a - b) : ℚ)) * choosePoly b).natDegree
      ≤ (choosePoly b).natDegree := natDegree_C_mul_le _ _
    _ = b := choosePoly_natDegree b
    _ ≤ a := Nat.lt_succ_iff.mp (mem_range.mp hb)

lemma krawPoly_coeff_self (n a : ℕ) : (krawPoly n a).coeff a = (-2 : ℚ) ^ a / a.factorial := by
  unfold krawPoly
  rw [finsetSum_coeff, sum_eq_single a]
  · rw [coeff_C_mul, choosePoly_coeff_self, Nat.sub_self, Nat.choose_zero_right]
    push_cast
    ring
  · intro b hb hba
    rw [coeff_C_mul]
    have hlt : b < a := lt_of_le_of_ne (Nat.lt_succ_iff.mp (mem_range.mp hb)) hba
    rw [coeff_eq_zero_of_natDegree_lt (by rw [choosePoly_natDegree]; exact hlt), mul_zero]
  · intro h
    exact absurd (mem_range.mpr (Nat.lt_succ_self a)) h

lemma krawPoly_coeff_self_ne_zero (n a : ℕ) : (krawPoly n a).coeff a ≠ 0 := by
  rw [krawPoly_coeff_self]
  have : (a.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) this

/-! ## Evaluation at distinct points (Vandermonde) -/

/-- Polynomials `P_a` (`a < ℓ`) of degree `≤ a` with nonzero `X^a`-coefficient: a vanishing
combination at `ℓ` distinct points has zero coefficients. -/
lemma coeffs_zero_of_eval {ℓ : ℕ} (P : ℕ → ℚ[X]) (hdeg : ∀ a, (P a).natDegree ≤ a)
    (hlead : ∀ a, (P a).coeff a ≠ 0) (x : Fin ℓ → ℚ) (hx : Function.Injective x) (c : ℕ → ℚ)
    (h : ∀ b, ∑ a ∈ range ℓ, c a * (P a).eval (x b) = 0) : ∀ a < ℓ, c a = 0 := by
  set Q : ℚ[X] := ∑ a ∈ range ℓ, C (c a) * P a with hQ
  have hQeval : ∀ b, Q.eval (x b) = 0 := by
    intro b
    rw [hQ, eval_finsetSum]
    simpa only [eval_mul, eval_C] using h b
  have hQ0 : Q = 0 := by
    rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
    · rw [hQ, hℓ, range_zero, sum_empty]
    · apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q hx hQeval
      rw [Fintype.card_fin]
      have : Q.natDegree ≤ ℓ - 1 := by
        rw [hQ]
        apply natDegree_sum_le_of_forall_le
        intro a ha
        exact (natDegree_C_mul_le _ _).trans ((hdeg a).trans (by have := mem_range.mp ha; omega))
      omega
  have key : ∀ d a, ℓ - 1 - a = d → a < ℓ → c a = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro a hd ha
      have hcoef : Q.coeff a = c a * (P a).coeff a := by
        rw [hQ, finsetSum_coeff, sum_eq_single a]
        · rw [coeff_C_mul]
        · intro a' ha' hne
          rw [coeff_C_mul]
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg a') hlt), mul_zero]
          · have ha'ℓ := mem_range.mp ha'
            rw [ih (ℓ - 1 - a') (by omega) a' rfl ha'ℓ, zero_mul]
        · intro hna
          exact absurd (mem_range.mpr ha) hna
      rw [hQ0, coeff_zero] at hcoef
      exact (mul_eq_zero.mp hcoef.symm).resolve_right (hlead a)
  intro a ha
  exact key _ a rfl ha

/-! ## The two-tailed submatrix -/

lemma neg_one_pow_sub_of_odd {n b : ℕ} (hn : Odd n) (hb : b ≤ n) :
    ((-1 : ℤ) ^ (n - b)) = -(-1) ^ b := by
  have h1 : ((-1 : ℤ) ^ (n - b)) * (-1) ^ b = (-1) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hb]
  have e : ((-1 : ℤ) ^ (n - b)) = (-1) ^ (n - b) * ((-1) ^ b * (-1) ^ b) := by
    rw [neg_one_pow_mul_self, mul_one]
  rw [e, ← mul_assoc, h1, hn.neg_one_pow]
  ring

/-- **The two-tailed Krawtchouk submatrix is invertible.** Let `n` be odd and `2ℓ ≤ n + 1`.
Index the columns of `[K_a(b)]` by the two tails `a < ℓ` (coefficients `c a`) and `n - a`,
`a < ℓ` (coefficients `c' a`). If the combination vanishes at every row `b` in the two tails,
all coefficients vanish. -/
theorem kraw_twoTail_injective {n ℓ : ℕ} (hn : Odd n) (hℓ : 2 * ℓ ≤ n + 1) (c c' : ℕ → ℚ)
    (h : ∀ b, b < ℓ ∨ (n - ℓ < b ∧ b ≤ n) →
      ∑ a ∈ range ℓ, (c a * (kraw n a b : ℚ) + c' a * (kraw n (n - a) b : ℚ)) = 0) :
    ∀ a < ℓ, c a = 0 ∧ c' a = 0 := by
  have hℓn : ℓ ≤ n := by obtain ⟨k, rfl⟩ := hn; omega
  -- row `b < ℓ`
  have hrow1 : ∀ b < ℓ,
      ∑ a ∈ range ℓ, (kraw n a b : ℚ) * (c a + ((-1 : ℤ) ^ b : ℤ) * c' a) = 0 := by
    intro b hb
    rw [← h b (Or.inl hb)]
    refine sum_congr rfl fun a ha => ?_
    have haℓ := mem_range.mp ha
    rw [kraw_symm_index (by omega) (by omega)]
    push_cast
    ring
  -- row `n - b`, `b < ℓ`
  have hrow2 : ∀ b < ℓ,
      ∑ a ∈ range ℓ, (kraw n a (n - b) : ℚ) * (c a - ((-1 : ℤ) ^ b : ℤ) * c' a) = 0 := by
    intro b hb
    rw [← h (n - b) (Or.inr ⟨by omega, by omega⟩)]
    refine sum_congr rfl fun a ha => ?_
    have haℓ := mem_range.mp ha
    rw [kraw_symm_index (by omega) (by omega : n - b ≤ n), neg_one_pow_sub_of_odd hn (by omega)]
    push_cast
    ring
  set s : ℕ → ℚ := fun a => c a + c' a with hs
  set t : ℕ → ℚ := fun a => c a - c' a with ht
  -- the evaluation points
  let xs : Fin ℓ → ℕ := fun b => if Even (b : ℕ) then b else n - b
  let xt : Fin ℓ → ℕ := fun b => if Even (b : ℕ) then n - b else b
  have hxs_le : ∀ b, xs b ≤ n := by intro b; simp only [xs]; split_ifs <;> omega
  have hxt_le : ∀ b, xt b ≤ n := by intro b; simp only [xt]; split_ifs <;> omega
  have hinj : ∀ (f : Fin ℓ → ℕ), (∀ b, f b = if Even (b : ℕ) then (b : ℕ) else n - b) ∨
      (∀ b, f b = if Even (b : ℕ) then n - b else (b : ℕ)) → Function.Injective f := by
    intro f hf b₁ b₂ heq
    have h1 := b₁.isLt
    have h2 := b₂.isLt
    apply Fin.ext
    rcases hf with hf | hf <;> rw [hf, hf] at heq <;>
      split_ifs at heq with e1 e2 e2 <;> omega
  have hxs_inj : Function.Injective (fun b => (xs b : ℚ)) :=
    (Nat.cast_injective).comp (hinj xs (Or.inl fun _ => rfl))
  have hxt_inj : Function.Injective (fun b => (xt b : ℚ)) :=
    (Nat.cast_injective).comp (hinj xt (Or.inr fun _ => rfl))
  have hs0 : ∀ a < ℓ, s a = 0 := by
    apply coeffs_zero_of_eval (krawPoly n) (krawPoly_natDegree_le n)
      (krawPoly_coeff_self_ne_zero n) _ hxs_inj s
    intro b
    simp only [krawPoly_eval (hxs_le b)]
    have hb := b.isLt
    by_cases he : Even (b : ℕ)
    · have hx : xs b = b := ite_eq_left he
      rw [hx]
      have := hrow1 b hb
      rw [he.neg_one_pow] at this
      rw [← this]
      refine sum_congr rfl fun a _ => ?_
      simp only [hs]; push_cast; ring
    · have hx : xs b = n - b := ite_eq_right he
      rw [hx]
      have := hrow2 b hb
      rw [(Nat.not_even_iff_odd.mp he).neg_one_pow] at this
      rw [← this]
      refine sum_congr rfl fun a _ => ?_
      simp only [hs]; push_cast; ring
  have ht0 : ∀ a < ℓ, t a = 0 := by
    apply coeffs_zero_of_eval (krawPoly n) (krawPoly_natDegree_le n)
      (krawPoly_coeff_self_ne_zero n) _ hxt_inj t
    intro b
    simp only [krawPoly_eval (hxt_le b)]
    have hb := b.isLt
    by_cases he : Even (b : ℕ)
    · have hx : xt b = n - b := ite_eq_left he
      rw [hx]
      have := hrow2 b hb
      rw [he.neg_one_pow] at this
      rw [← this]
      refine sum_congr rfl fun a _ => ?_
      simp only [ht]; push_cast; ring
    · have hx : xt b = b := ite_eq_right he
      rw [hx]
      have := hrow1 b hb
      rw [(Nat.not_even_iff_odd.mp he).neg_one_pow] at this
      rw [← this]
      refine sum_congr rfl fun a _ => ?_
      simp only [ht]; push_cast; ring
  intro a ha
  have e1 := hs0 a ha
  have e2 := ht0 a ha
  simp only [hs, ht] at e1 e2
  constructor <;> linarith

end FTPaper.LemmaS
