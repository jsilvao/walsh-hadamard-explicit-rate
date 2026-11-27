import FTPaper.LemmaS.Injective

/-!
# The fast decoder (Lemma S, degree bound)

`checkOp u = P_E ∘ H ∘ P_E` is the Walsh–Hadamard matrix restricted to the two tails
`E = {S : |S| < u ∨ m - u < |S|}`. On functions supported on `E` it has an inverse that is a
polynomial in `checkOp u` itself, of degree `< (m+1)^2` (`decoder_poly`). So the decoder costs
at most `(m+1)^2` applications of `H`, each of which is one fast Walsh–Hadamard transform.

Proof:
* On the span of the strings `R^a h` of harmonics `h` on layer `i`, `checkOp u` acts through
  the block matrix `blk m u i` (`checkOp_strSum`, from `hada_R_pow_apply`).
* Every function supported on `E` is a sum of such strings (`tails_decomp`).
* So the product of the block characteristic polynomials annihilates `checkOp u` on
  functions supported on `E` (Cayley–Hamilton, `annPoly_kills`). Its degree is at most
  `u (m + 1)`.
* `checkOp u` is injective there (`hada_tails_injective`), so the factors of `X` can be
  stripped, which leaves the inverse.
-/

namespace FTPaper.LemmaS

open Finset Polynomial

variable {m : ℕ}

/-! ## Restriction to the tails -/

/-- Restriction to the two tails `{S : |S| < u ∨ m - u < |S|}`. -/
def restrictE (u : ℕ) : Module.End ℚ (Fn m) where
  toFun f S := if S.card < u ∨ m - u < S.card then f S else 0
  map_add' f g := by funext S; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c f := by
    funext S; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

lemma restrictE_apply (u : ℕ) (f : Fn m) (S : Finset (Fin m)) :
    restrictE u f S = if S.card < u ∨ m - u < S.card then f S else 0 := rfl

lemma restrictE_idem (u : ℕ) (f : Fn m) : restrictE u (restrictE u f) = restrictE u f := by
  funext S
  simp only [restrictE_apply]
  split_ifs <;> rfl

/-- The check operator: the Walsh–Hadamard matrix on the two tails. -/
def checkOp (u : ℕ) : Module.End ℚ (Fn m) := restrictE u * hada * restrictE u

lemma checkOp_apply (u : ℕ) (f : Fn m) :
    checkOp u f = restrictE u (hada (restrictE u f)) := rfl

lemma restrictE_checkOp (u : ℕ) (f : Fn m) : restrictE u (checkOp u f) = checkOp u f :=
  restrictE_idem _ _

lemma checkOp_restrictE (u : ℕ) (f : Fn m) : checkOp u (restrictE u f) = checkOp u f := by
  rw [checkOp_apply, checkOp_apply, restrictE_idem]

/-- `checkOp` is injective on functions supported on the tails. -/
lemma checkOp_inj (hm : Odd m) {u : ℕ} (hu : 2 * u ≤ m + 1) {g : Fn m}
    (hg : restrictE u g = g) (h0 : checkOp u g = 0) : g = 0 := by
  apply hada_tails_injective hm hu g
  · intro S h1 h2
    rw [← hg, restrictE_apply, ite_eq_right (fun h => by omega)]
  · intro S hS
    have := congrFun h0 S
    rw [checkOp_apply, hg, restrictE_apply, ite_eq_left hS] at this
    exact this

/-! ## The block structure -/

/-- Block indices at harmonic level `i`: string positions `a ≤ m - 2i` whose layer `i + a`
lies in the tails. -/
def Aset (m u i : ℕ) : Finset ℕ :=
  (range (m + 1)).filter (fun a => 2 * i + a ≤ m ∧ (i + a < u ∨ m - u < i + a))

lemma mem_Aset {u i a : ℕ} :
    a ∈ Aset m u i ↔ 2 * i + a ≤ m ∧ (i + a < u ∨ m - u < i + a) := by
  rw [Aset, mem_filter, mem_range]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨by omega, h⟩

/-- The block of `checkOp` at level `i`, in the string basis. -/
noncomputable def blk (m u i : ℕ) : Matrix (Aset m u i) (Aset m u i) ℚ :=
  fun c a => hcoef (m - 2 * i) i a c

/-- Strings with coefficients: `strSum h = ∑_a R^a (h a)`. -/
noncomputable def strSum (u i : ℕ) (h : Aset m u i → Fn m) : Fn m :=
  ∑ a : Aset m u i, (R ^ (a : ℕ)) (h a)

/-- A matrix acting on string coefficients. -/
noncomputable def act {ι : Type*} [Fintype ι] (N : Matrix ι ι ℚ) (h : ι → Fn m) : ι → Fn m :=
  fun c => ∑ a, N c a • h a

section act

variable {ι : Type*} [Fintype ι]

lemma act_one [DecidableEq ι] (h : ι → Fn m) : act 1 h = h := by
  funext c
  simp only [act, Matrix.one_apply, ite_smul, one_smul, zero_smul, sum_ite_eq, mem_univ,
    ite_true]

lemma act_zero (h : ι → Fn m) : act 0 h = 0 := by
  funext c
  simp [act]

lemma act_mul (N N' : Matrix ι ι ℚ) (h : ι → Fn m) : act (N * N') h = act N (act N' h) := by
  funext c
  simp only [act, Matrix.mul_apply, sum_smul, smul_sum, smul_smul]
  rw [sum_comm]

lemma act_add (N N' : Matrix ι ι ℚ) (h : ι → Fn m) : act (N + N') h = act N h + act N' h := by
  funext c
  simp only [act, Matrix.add_apply, add_smul, sum_add_distrib, Pi.add_apply]

lemma act_smul (r : ℚ) (N : Matrix ι ι ℚ) (h : ι → Fn m) : act (r • N) h = r • act N h := by
  funext c
  simp only [act, Matrix.smul_apply, smul_eq_mul, smul_sum, smul_smul, Pi.smul_apply]

lemma act_harm {i : ℕ} (N : Matrix ι ι ℚ) {h : ι → Fn m} (hh : ∀ a, IsHarm (h a) i) (c : ι) :
    IsHarm (act N h c) i :=
  isHarm_sum _ _ (fun a _ => (hh a).smul _)

end act

lemma strSum_add {u i : ℕ} (h h' : Aset m u i → Fn m) :
    strSum u i (h + h') = strSum u i h + strSum u i h' := by
  simp only [strSum, Pi.add_apply, map_add, sum_add_distrib]

lemma strSum_smul {u i : ℕ} (r : ℚ) (h : Aset m u i → Fn m) :
    strSum u i (r • h) = r • strSum u i h := by
  simp only [strSum, Pi.smul_apply, map_smul, smul_sum]

lemma strSum_zero {u i : ℕ} : strSum u i (0 : Aset m u i → Fn m) = 0 := by
  simp [strSum]

/-- **The block action.** On strings of harmonics on layer `i`, `checkOp u` acts by `blk`. -/
lemma checkOp_strSum {u i : ℕ} (h : Aset m u i → Fn m) (hh : ∀ a, IsHarm (h a) i) :
    checkOp u (strSum u i h) = strSum u i (act (blk m u i) h) := by
  have hlay : ∀ (c a : Aset m u i) (S : Finset (Fin m)), i + (c : ℕ) ≠ S.card →
      (R ^ (c : ℕ)) (h a) S = 0 :=
    fun c a S hc => R_pow_onLayer (hh a).1 (c : ℕ) S (Ne.symm hc)
  have hres : restrictE u (strSum u i h) = strSum u i h := by
    funext T
    rw [restrictE_apply]
    split_ifs with hT
    · rfl
    · simp only [strSum, Finset.sum_apply]
      symm
      apply sum_eq_zero
      intro a _
      apply hlay a a T
      have := (mem_Aset.mp a.2).2
      omega
  funext S
  rw [checkOp_apply, hres, restrictE_apply]
  simp only [strSum, act, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hc0 : i ≤ S.card ∧ S.card - i ∈ Aset m u i
  · obtain ⟨hiS, hmem⟩ := hc0
    have htail : S.card < u ∨ m - u < S.card := by
      have := (mem_Aset.mp hmem).2
      rwa [show i + (S.card - i) = S.card by omega] at this
    have hrhs : (∑ c : Aset m u i, ∑ a : Aset m u i, blk m u i c a * (R ^ (c : ℕ)) (h a) S)
        = ∑ a : Aset m u i, blk m u i ⟨S.card - i, hmem⟩ a *
            (R ^ ((⟨S.card - i, hmem⟩ : Aset m u i) : ℕ)) (h a) S := by
      rw [sum_eq_single (⟨S.card - i, hmem⟩ : Aset m u i)]
      · intro c _ hc
        apply sum_eq_zero
        intro a _
        rw [hlay c a S, mul_zero]
        intro hcS
        apply hc
        apply Subtype.ext
        show (c : ℕ) = S.card - i
        omega
      · intro h; exact absurd (mem_univ _) h
    rw [hrhs, ite_eq_left htail]
    refine sum_congr rfl fun a _ => ?_
    have ha := (mem_Aset.mp a.2).1
    rw [hada_R_pow_apply (hh a) (by omega) S, ite_eq_left hiS]
    rfl
  · -- no string position matches the layer of `S`
    have hnone : ∀ c : Aset m u i, i + (c : ℕ) ≠ S.card := by
      intro c hcS
      apply hc0
      refine ⟨by omega, ?_⟩
      rw [show S.card - i = (c : ℕ) by omega]
      exact c.2
    rw [show (∑ c : Aset m u i, ∑ a : Aset m u i, blk m u i c a * (R ^ (c : ℕ)) (h a) S) = 0 from
      sum_eq_zero fun c _ => sum_eq_zero fun a _ => by rw [hlay c a S (hnone c), mul_zero]]
    split_ifs with htail
    · apply sum_eq_zero
      intro a _
      have ha := (mem_Aset.mp a.2).1
      rw [hada_R_pow_apply (hh a) (by omega) S]
      split_ifs with hiS
      · -- the string has already ended
        have hgt : m < 2 * i + (S.card - i) := by
          by_contra hle
          apply hc0
          refine ⟨hiS, mem_Aset.mpr ⟨by omega, ?_⟩⟩
          rwa [show i + (S.card - i) = S.card by omega]
        rw [R_pow_harm_eq_zero (hh a) hgt, Pi.zero_apply, mul_zero]
      · rfl
    · rfl

lemma checkOp_pow_strSum {u i : ℕ} (n : ℕ) (h : Aset m u i → Fn m) (hh : ∀ a, IsHarm (h a) i) :
    (checkOp u ^ n) (strSum u i h) = strSum u i (act (blk m u i ^ n) h) := by
  induction n generalizing h with
  | zero => simp [act_one]
  | succ n ih =>
    rw [pow_succ (checkOp u) n, Module.End.mul_apply, checkOp_strSum h hh,
      ih (act (blk m u i) h) (act_harm _ hh), pow_succ (blk m u i) n, act_mul]

lemma aeval_checkOp_strSum {u i : ℕ} (p : ℚ[X]) (h : Aset m u i → Fn m)
    (hh : ∀ a, IsHarm (h a) i) :
    aeval (checkOp u) p (strSum u i h) = strSum u i (act (aeval (blk m u i) p) h) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, LinearMap.add_apply, hp, hq, act_add, strSum_add]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, smul_mul_assoc, one_mul, one_mul,
      LinearMap.smul_apply, checkOp_pow_strSum n h hh, act_smul, strSum_smul]

/-- **Cayley–Hamilton on one block.** -/
lemma charpoly_kills {u i : ℕ} (h : Aset m u i → Fn m) (hh : ∀ a, IsHarm (h a) i) :
    aeval (checkOp u) (blk m u i).charpoly (strSum u i h) = 0 := by
  rw [aeval_checkOp_strSum _ h hh, Matrix.aeval_self_charpoly, act_zero, strSum_zero]

/-! ## Every function on the tails is a sum of strings -/

lemma tails_decomp {u : ℕ} (hu : 2 * u ≤ m + 1) (g : Fn m) (hg : restrictE u g = g) :
    ∃ h : (i : ℕ) → Aset m u i → Fn m, (∀ i a, IsHarm (h i a) i) ∧
      g = ∑ i ∈ range u, strSum u i (h i) := by
  classical
  have hsupp : ∀ S : Finset (Fin m), u ≤ S.card → S.card ≤ m - u → g S = 0 := by
    intro S h1 h2
    rw [← hg, restrictE_apply, ite_eq_right (fun h => by omega)]
  have hex : ∀ k, ∃ h : ℕ → Fn m, (∀ i, IsHarm (h i) i) ∧
      layerPart g k = ∑ i ∈ range (k + 1), (R ^ (k - i)) (h i) :=
    fun k => exists_strings k (layerPart_onLayer g k)
  choose Hs hHs hsum using hex
  set H : ℕ → ℕ → Fn m := fun k i =>
    if i ≤ k ∧ i + k ≤ m ∧ (k < u ∨ m - u < k) then Hs k i else 0 with hHdef
  have hHharm : ∀ k i, IsHarm (H k i) i := by
    intro k i
    simp only [hHdef]
    split_ifs
    · exact hHs k i
    · exact isHarm_zero i
  have hHsupp : ∀ k i, H k i ≠ 0 → i ≤ k ∧ i + k ≤ m ∧ (k < u ∨ m - u < k) := by
    intro k i hne
    simp only [hHdef] at hne
    split_ifs at hne with hc
    · exact hc
    · exact absurd rfl hne
  have hlayer : ∀ k ∈ range (m + 1),
      layerPart g k = ∑ i ∈ range (m + 1), (R ^ (k - i)) (H k i) := by
    intro k hk
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk)
    by_cases htail : k < u ∨ m - u < k
    · rw [hsum k]
      symm
      rw [← sum_subset (range_mono (by omega : k + 1 ≤ m + 1))]
      · refine sum_congr rfl fun i hi => ?_
        have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
        by_cases him : i + k ≤ m
        · simp only [hHdef]
          rw [ite_eq_left ⟨hik, him, htail⟩]
        · have hz : (R ^ (k - i)) (Hs k i) = 0 := R_pow_harm_eq_zero (hHs k i) (by omega)
          simp only [hHdef]
          rw [ite_eq_right (fun h => him h.2.1), map_zero, hz]
      · intro i _ hnot
        simp only [hHdef]
        rw [mem_range] at hnot
        rw [ite_eq_right (fun h => by omega), map_zero]
    · have hz : layerPart g k = 0 := by
        funext S
        simp only [layerPart, Pi.zero_apply]
        split_ifs with hS
        · push Not at htail
          exact hsupp S (by omega) (by omega)
        · rfl
      rw [hz]
      symm
      apply sum_eq_zero
      intro i _
      simp only [hHdef]
      rw [ite_eq_right (fun h => htail h.2.2), map_zero]
  have he : g = ∑ i ∈ range (m + 1), ∑ k ∈ range (m + 1), (R ^ (k - i)) (H k i) := by
    conv_lhs => rw [← sum_layerPart g]
    rw [sum_congr rfl hlayer, sum_comm]
  refine ⟨fun i a => H (i + a) i, fun i a => hHharm _ _, ?_⟩
  rw [he, ← sum_subset (range_mono (by omega : u ≤ m + 1))]
  · refine sum_congr rfl fun i hi => ?_
    have hiu : i < u := mem_range.mp hi
    have hR : strSum u i (fun a => H (i + a) i) = ∑ a ∈ Aset m u i, (R ^ a) (H (i + a) i) :=
      sum_coe_sort (Aset m u i) (fun a => (R ^ a) (H (i + a) i))
    have hR2 : ∑ a ∈ Aset m u i, (R ^ a) (H (i + a) i)
        = ∑ k ∈ (Aset m u i).image (fun a => i + a), (R ^ (k - i)) (H k i) := by
      rw [sum_image (by intro x _ y _ hxy; simpa using hxy)]
      refine sum_congr rfl fun a _ => ?_
      rw [Nat.add_sub_cancel_left]
    rw [hR, hR2]
    symm
    apply sum_subset
    · intro k hk
      rw [mem_image] at hk
      obtain ⟨a, ha, rfl⟩ := hk
      rw [mem_range]
      have := (mem_Aset.mp ha).1
      omega
    · intro k _ hnot
      by_contra hne
      have hne' : H k i ≠ 0 := fun hz => hne (by rw [hz, map_zero])
      obtain ⟨h1, h2, h3⟩ := hHsupp k i hne'
      apply hnot
      rw [mem_image]
      exact ⟨k - i, mem_Aset.mpr ⟨by omega, by rwa [show i + (k - i) = k by omega]⟩,
        Nat.add_sub_of_le h1⟩
  · intro i hi hnot
    rw [mem_range] at hi hnot
    apply sum_eq_zero
    intro k _
    by_contra hne
    have hne' : H k i ≠ 0 := fun hz => hne (by rw [hz, map_zero])
    obtain ⟨h1, h2, h3⟩ := hHsupp k i hne'
    rcases h3 with h3 | h3 <;> omega

/-! ## The annihilating polynomial and the inverse -/

/-- The product of the block characteristic polynomials. -/
noncomputable def annPoly (m u : ℕ) : ℚ[X] := ∏ i ∈ range u, (blk m u i).charpoly

lemma annPoly_monic (m u : ℕ) : (annPoly m u).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => Matrix.charpoly_monic _)

lemma annPoly_natDegree_le (m u : ℕ) : (annPoly m u).natDegree ≤ u * (m + 1) := by
  rw [annPoly, natDegree_prod_of_monic _ _ (fun _ _ => Matrix.charpoly_monic _)]
  calc ∑ i ∈ range u, (blk m u i).charpoly.natDegree
      = ∑ i ∈ range u, (Aset m u i).card := by
        refine sum_congr rfl fun i _ => ?_
        rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_coe]
    _ ≤ ∑ i ∈ range u, (m + 1) := sum_le_sum fun i _ =>
        (card_filter_le _ _).trans (by rw [card_range])
    _ = u * (m + 1) := by rw [sum_const, card_range, smul_eq_mul]

lemma annPoly_kills {u : ℕ} (hu : 2 * u ≤ m + 1) (g : Fn m) (hg : restrictE u g = g) :
    aeval (checkOp u) (annPoly m u) g = 0 := by
  obtain ⟨h, hh, rfl⟩ := tails_decomp hu g hg
  rw [map_sum]
  apply sum_eq_zero
  intro i hi
  rw [annPoly, ← prod_erase_mul _ _ hi, map_mul, Module.End.mul_apply, charpoly_kills _ (hh i),
    map_zero]

/-- **The fast decoder.** For odd `m` and `2u ≤ m + 1`, the inverse of the check operator on
functions supported on the tails is a polynomial in the check operator of degree
`< (m+1)^2`. -/
theorem decoder_poly (hm : Odd m) {u : ℕ} (hu : 2 * u ≤ m + 1) :
    ∃ q : ℚ[X], q.natDegree + 1 ≤ (m + 1) ^ 2 ∧
      (∀ f : Fn m, aeval (checkOp u) q (checkOp u f) = restrictE u f) ∧
      (∀ f : Fn m, checkOp u (aeval (checkOp u) q f) = restrictE u f) := by
  have hP0 : annPoly m u ≠ 0 := (annPoly_monic m u).ne_zero
  -- commutation with polynomials in the check operator
  have hcomm : ∀ (p : ℚ[X]) (x : Fn m),
      aeval (checkOp u) p (checkOp u x) = checkOp u (aeval (checkOp u) p x) := by
    intro p x
    have h1 : aeval (checkOp (m := m) u) (p * X) = aeval (checkOp u) p * checkOp u := by
      rw [map_mul, aeval_X]
    have h2 : aeval (checkOp (m := m) u) (X * p) = checkOp u * aeval (checkOp u) p := by
      rw [map_mul, aeval_X]
    have : aeval (checkOp (m := m) u) p * checkOp u = checkOp u * aeval (checkOp u) p := by
      rw [← h1, ← h2, mul_comm]
    exact LinearMap.congr_fun this x
  -- powers of the check operator are injective on the tails
  have hinjpow : ∀ (n : ℕ) (w : Fn m), restrictE u w = w → (checkOp u ^ n) w = 0 → w = 0 := by
    intro n
    induction n with
    | zero => intro w _ h; simpa using h
    | succ n ih =>
      intro w hw h
      rw [pow_succ, Module.End.mul_apply] at h
      exact checkOp_inj hm hu hw (ih (checkOp u w) (restrictE_checkOp u w) h)
  -- strip the factors of `X`
  obtain ⟨j₀, hj₀⟩ : ∃ j, j = (annPoly m u).natTrailingDegree := ⟨_, rfl⟩
  have htc : (annPoly m u).coeff j₀ ≠ 0 := by
    rw [hj₀]
    exact trailingCoeff_nonzero_iff_nonzero.mpr hP0
  obtain ⟨Q, hPQ⟩ : X ^ j₀ ∣ annPoly m u :=
    X_pow_dvd_iff.mpr fun d hd => coeff_eq_zero_of_lt_natTrailingDegree (by rw [← hj₀]; exact hd)
  have hQ0 : Q.coeff 0 ≠ 0 := by
    have h1 : (annPoly m u).coeff j₀ = Q.coeff 0 := by
      rw [hPQ, coeff_X_pow_mul']
      simp
    rwa [← h1]
  have hQsplit : ∀ x : Fn m, aeval (checkOp u) Q x
      = checkOp u (aeval (checkOp u) (divX Q) x) + Q.coeff 0 • x := by
    intro x
    conv_lhs => rw [← X_mul_divX_add Q]
    rw [map_add, map_mul, aeval_X, aeval_C, LinearMap.add_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply]
  -- the inverse
  have hright : ∀ g : Fn m, restrictE u g = g →
      checkOp u (aeval (checkOp u) (C (-(Q.coeff 0)⁻¹) * divX Q) g) = g := by
    intro g hg
    have hk : (checkOp u ^ j₀) (aeval (checkOp u) Q g) = 0 := by
      have := annPoly_kills hu g hg
      rw [hPQ, map_mul, map_pow, aeval_X, Module.End.mul_apply] at this
      exact this
    have hres : restrictE u (aeval (checkOp u) Q g) = aeval (checkOp u) Q g := by
      rw [hQsplit, map_add, map_smul, hg, restrictE_checkOp]
    have hQg := hinjpow j₀ _ hres hk
    rw [hQsplit] at hQg
    rw [map_mul, aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul,
      eq_neg_of_add_eq_zero_left hQg, smul_neg, smul_smul, neg_mul, inv_mul_cancel₀ hQ0,
      neg_smul, one_smul, neg_neg]
  refine ⟨C (-(Q.coeff 0)⁻¹) * divX Q, ?_, ?_, ?_⟩
  · -- degree
    have hQne : Q ≠ 0 := by rintro rfl; exact hQ0 (by simp)
    have hdegQ : Q.natDegree ≤ (annPoly m u).natDegree := by
      rw [hPQ, natDegree_mul (pow_ne_zero _ X_ne_zero) hQne, natDegree_X_pow]
      omega
    have hq : (C (-(Q.coeff 0)⁻¹) * divX Q).natDegree ≤ Q.natDegree - 1 :=
      (natDegree_C_mul_le _ _).trans natDegree_divX_eq_natDegree_tsub_one.le
    have hPdeg := annPoly_natDegree_le m u
    have hum : u ≤ m + 1 := by omega
    have : u * (m + 1) ≤ (m + 1) * (m + 1) := Nat.mul_le_mul_right _ hum
    have hpos : 0 < (m + 1) * (m + 1) := Nat.mul_pos (Nat.succ_pos m) (Nat.succ_pos m)
    rw [sq]
    omega
  · intro f
    rw [← checkOp_restrictE, hcomm, hright _ (restrictE_idem u f)]
  · intro f
    rw [← hcomm, ← checkOp_restrictE, hcomm, hright _ (restrictE_idem u f)]

end FTPaper.LemmaS
