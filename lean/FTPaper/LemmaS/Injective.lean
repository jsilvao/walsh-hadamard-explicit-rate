import FTPaper.LemmaS.Hadamard

/-!
# Character checks on the two tails are invertible (Lemma S, main theorem)

Let `m` be odd, `2u ≤ m + 1`, and let `E` be the subsets of `Fin m` of size `< u` or `> m - u`
(the two tails of the window `[u, m-u]`). The Walsh–Hadamard matrix restricted to `E × E` is
injective (`hada_tails_injective`). So character checks indexed by `E` determine any error
supported on a translate of `E`, which is the decoding step of the cheap repair (paper: Lemma 9.1 and Section 9).

The proof combines:
* the string decomposition of each layer (`exists_strings`, `strings_unique`);
* the string action of `H` (`hada_R_pow_apply`), with coefficients
  `(-2)^i (a!/c!) K_a(c; m-2i)` (`hcoef_eq_kraw`);
* the invertibility of the two-tailed Krawtchouk submatrix (`kraw_twoTail_injective`).
-/

namespace FTPaper.LemmaS

open Finset

variable {m : ℕ}

lemma cast_descFactorial_eq {n k : ℕ} (h : k ≤ n) :
    (n.descFactorial k : ℚ) = (n.factorial : ℚ) / ((n - k).factorial : ℚ) := by
  have := Nat.factorial_mul_descFactorial h
  have hf : ((n - k).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [eq_div_iff hf, mul_comm]
  exact_mod_cast this

/-- The string-action coefficient in Krawtchouk form. -/
lemma hcoef_eq_kraw {n i a c : ℕ} (ha : a ≤ n) (hc : c ≤ n) :
    hcoef n i a c = (-2 : ℚ) ^ i * ((a.factorial : ℚ) / (c.factorial : ℚ)) * (kraw n a c : ℚ) := by
  rw [kraw_eq_alt hc]
  unfold hcoef
  push_cast
  rw [mul_sum]
  symm
  have hsub : range (min a c + 1) ⊆ range (a + 1) := by
    intro b hb; rw [mem_range] at hb ⊢; have := min_le_left a c; omega
  rw [← sum_subset hsub]
  · refine sum_congr rfl fun b hb => ?_
    have hb' : b ≤ min a c := Nat.lt_succ_iff.mp (mem_range.mp hb)
    have hba : b ≤ a := hb'.trans (min_le_left a c)
    have hbc : b ≤ c := hb'.trans (min_le_right a c)
    unfold strL
    rw [show n - a + (a - b) = n - b by omega, cast_descFactorial_eq (by omega : a - b ≤ a),
      cast_descFactorial_eq (by omega : a - b ≤ n - b), show a - (a - b) = b by omega,
      show n - b - (a - b) = n - a by omega, Nat.cast_choose ℚ hbc,
      Nat.cast_choose ℚ (by omega : a - b ≤ n - b), show n - b - (a - b) = n - a by omega]
    have h1 : (b.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h2 : ((a - b).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h3 : ((c - b).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h4 : ((n - a).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h5 : (c.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp
    ring
  · intro b hb hnot
    rw [mem_range] at hb hnot
    have hcb : c < b := by
      by_contra h
      apply hnot
      have : b ≤ min a c := le_min (by omega) (by omega)
      omega
    rw [Nat.choose_eq_zero_of_lt hcb]
    simp

/-! ## Assembly -/

lemma isHarm_sum {ι : Type*} (s : Finset ι) (f : ι → Fn m) {i : ℕ}
    (hf : ∀ x ∈ s, IsHarm (f x) i) : IsHarm (∑ x ∈ s, f x) i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isHarm_zero (m := m) i
  | insert a s ha ih =>
    rw [sum_insert ha]
    have h1 := hf a (mem_insert_self a s)
    have h2 := ih (fun x hx => hf x (mem_insert_of_mem hx))
    exact And.intro (h1.1.add h2.1) (by rw [map_add, h1.2, h2.2, add_zero])

lemma onLayer_sum {ι : Type*} (s : Finset ι) (f : ι → Fn m) {k : ℕ}
    (hf : ∀ x ∈ s, OnLayer (f x) k) : OnLayer (∑ x ∈ s, f x) k := by
  intro S hS
  rw [Finset.sum_apply]
  exact sum_eq_zero fun x hx => hf x hx S hS

/-- The layer-`k` part of `e`. -/
def layerPart (e : Fn m) (k : ℕ) : Fn m := fun S => if S.card = k then e S else 0

lemma layerPart_onLayer (e : Fn m) (k : ℕ) : OnLayer (layerPart e k) k := by
  intro S hS
  simp only [layerPart]
  exact ite_eq_right hS

lemma sum_layerPart (e : Fn m) : ∑ k ∈ range (m + 1), layerPart e k = e := by
  funext S
  rw [Finset.sum_apply]
  simp only [layerPart]
  rw [sum_ite_eq]
  have : S.card < m + 1 := by have := card_le_univ S; simp at this; omega
  exact ite_eq_left (mem_range.mpr this)

/-- Reindex a sum supported on the two tails `[i, u)` and `(m-u, m-i]`. -/
lemma sum_two_tails {i u : ℕ} (hiu : i < u) (hu : 2 * u ≤ m + 1) (f : ℕ → ℚ)
    (hf : ∀ k, f k ≠ 0 → i ≤ k ∧ i + k ≤ m ∧ (k < u ∨ m - u < k)) :
    ∑ k ∈ range (m + 1), f k = ∑ a ∈ range (u - i), (f (i + a) + f (m - i - a)) := by
  rw [sum_add_distrib]
  rw [← sum_image (s := range (u - i)) (g := fun a => i + a)
    (by intro x _ y _ h; simpa using h)]
  rw [← sum_image (s := range (u - i)) (g := fun a => m - i - a)
    (by
      intro x hx y hy h
      rw [mem_coe, mem_range] at hx hy
      simp only at h
      omega)]
  rw [← sum_union]
  · symm
    apply sum_subset
    · intro k hk
      rw [mem_union, mem_image, mem_image] at hk
      rw [mem_range]
      rcases hk with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;> rw [mem_range] at ha <;> omega
    · intro k _ hnot
      by_contra hne
      obtain ⟨h1, h2, h3⟩ := hf k hne
      apply hnot
      rw [mem_union, mem_image, mem_image]
      rcases h3 with h3 | h3
      · left; exact ⟨k - i, by rw [mem_range]; omega, by omega⟩
      · right; exact ⟨m - i - k, by rw [mem_range]; omega, by omega⟩
  · rw [disjoint_left]
    intro k hk1 hk2
    rw [mem_image] at hk1 hk2
    obtain ⟨a, ha, rfl⟩ := hk1
    obtain ⟨b, hb, hab⟩ := hk2
    rw [mem_range] at ha hb
    omega

/-- **Lemma S, main theorem.** For odd `m` and `2u ≤ m + 1`, let `E` be the subsets of size
`< u` or `> m - u`. If `e` is supported on `E` and its Walsh–Hadamard transform vanishes on `E`,
then `e = 0`. That is, the character checks indexed by `E` are injective on errors supported
on `E`. -/
theorem hada_tails_injective (hm : Odd m) {u : ℕ} (hu : 2 * u ≤ m + 1) (e : Fn m)
    (hsupp : ∀ S : Finset (Fin m), u ≤ S.card → S.card ≤ m - u → e S = 0)
    (hzero : ∀ S : Finset (Fin m), (S.card < u ∨ m - u < S.card) → hada e S = 0) : e = 0 := by
  classical
  have hex : ∀ k, ∃ h : ℕ → Fn m, (∀ i, IsHarm (h i) i) ∧
      layerPart e k = ∑ i ∈ range (k + 1), (R ^ (k - i)) (h i) :=
    fun k => exists_strings k (layerPart_onLayer e k)
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
  -- every layer part is a cleaned string sum
  have hlayer : ∀ k ∈ range (m + 1),
      layerPart e k = ∑ i ∈ range (m + 1), (R ^ (k - i)) (H k i) := by
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
    · have hz : layerPart e k = 0 := by
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
  have he : e = ∑ i ∈ range (m + 1), ∑ k ∈ range (m + 1), (R ^ (k - i)) (H k i) := by
    conv_lhs => rw [← sum_layerPart e]
    rw [sum_congr rfl hlayer, sum_comm]
  -- the string action, term by term
  have hact : ∀ k i S, hada ((R ^ (k - i)) (H k i)) S =
      if i ≤ S.card then
        hcoef (m - 2 * i) i (k - i) (S.card - i) * (R ^ (S.card - i)) (H k i) S
      else 0 := by
    intro k i S
    by_cases hz : H k i = 0
    · rw [hz, map_zero, map_zero]
      simp
    · obtain ⟨h1, h2, _⟩ := hHsupp k i hz
      exact hada_R_pow_apply (hHharm k i) (by omega) S
  set G : ℕ → ℕ → Fn m := fun j i =>
    ∑ k ∈ range (m + 1), hcoef (m - 2 * i) i (k - i) (j - i) • H k i with hGdef
  have hGharm : ∀ j i, IsHarm (G j i) i :=
    fun j i => isHarm_sum _ _ (fun k _ => (hHharm k i).smul _)
  -- `H e` on a layer
  have hhadaS : ∀ S : Finset (Fin m),
      hada e S = ∑ i ∈ range (S.card + 1), (R ^ (S.card - i)) (G S.card i) S := by
    intro S
    have hS : S.card ≤ m := by simpa using card_le_univ S
    rw [he]
    simp only [map_sum, Finset.sum_apply]
    simp only [hact]
    rw [← sum_subset (range_mono (by omega : S.card + 1 ≤ m + 1))]
    · refine sum_congr rfl fun i hi => ?_
      have hiS : i ≤ S.card := Nat.lt_succ_iff.mp (mem_range.mp hi)
      simp only [hGdef, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine sum_congr rfl fun k _ => ?_
      rw [ite_eq_left hiS]
    · intro i _ hnot
      rw [mem_range] at hnot
      apply sum_eq_zero
      intro k _
      rw [ite_eq_right (by omega)]
  -- on every tail layer the harmonic components of `H e` vanish
  have hG0 : ∀ j i, (j < u ∨ m - u < j) → i ≤ j → i + j ≤ m → G j i = 0 := by
    intro j i hj hij hijm
    have hΦ : ∑ i' ∈ range (j + 1), (R ^ (j - i')) (G j i') = 0 := by
      funext S
      rw [Pi.zero_apply, Finset.sum_apply]
      by_cases hS : S.card = j
      · have := hhadaS S
        rw [hzero S (by rw [hS]; exact hj), hS] at this
        exact this.symm
      · have hlay : OnLayer (∑ i' ∈ range (j + 1), (R ^ (j - i')) (G j i')) j := by
          apply onLayer_sum
          intro i' hi'
          have := R_pow_onLayer (hGharm j i').1 (j - i')
          rwa [show i' + (j - i') = j by have := mem_range.mp hi'; omega] at this
        have := hlay S hS
        rwa [Finset.sum_apply] at this
    exact strings_unique j (G j) (hGharm j) hΦ i hij (by omega)
  -- the Krawtchouk step
  have hH0 : ∀ k i, H k i = 0 := by
    intro k i
    by_contra hne
    obtain ⟨hik, hikm, htail⟩ := hHsupp k i hne
    have hiu : i < u := by rcases htail with h | h <;> omega
    set n := m - 2 * i with hn
    set ℓ := u - i with hℓ
    have hnodd : Odd n := by
      obtain ⟨t, ht⟩ := hm
      exact ⟨t - i, by omega⟩
    have hℓn : 2 * ℓ ≤ n + 1 := by omega
    apply hne
    funext S
    rw [Pi.zero_apply]
    have key := kraw_twoTail_injective hnodd hℓn
      (fun a => (a.factorial : ℚ) * H (i + a) i S)
      (fun a => ((n - a).factorial : ℚ) * H (m - i - a) i S) ?_
    · rcases htail with h | h
      · have h1 := (key (k - i) (by omega)).1
        rw [show i + (k - i) = k by omega] at h1
        have hfac : ((k - i).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
        exact (mul_eq_zero.mp h1).resolve_left hfac
      · have h1 := (key (m - i - k) (by omega)).2
        rw [show m - i - (m - i - k) = k by omega] at h1
        have hfac : ((n - (m - i - k)).factorial : ℚ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero _
        exact (mul_eq_zero.mp h1).resolve_left hfac
    · intro b hb
      have hbn : b ≤ n := by rcases hb with hb | hb <;> omega
      have hj : i + b < u ∨ m - u < i + b := by
        rcases hb with hb | hb
        · left; omega
        · right; omega
      have hGz := hG0 (i + b) i hj (by omega) (by omega)
      have hGS := congrFun hGz S
      simp only [hGdef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hGS
      rw [sum_two_tails hiu hu _ (fun k' hk' => by
        apply hHsupp k' i
        intro hz
        apply hk'
        rw [hz, Pi.zero_apply, mul_zero])] at hGS
      have hpow : ((-2 : ℚ) ^ i) ≠ 0 := pow_ne_zero _ (by norm_num)
      have hbfac : (b.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hconv : ∑ a ∈ range ℓ,
          ((a.factorial : ℚ) * H (i + a) i S * (kraw n a b : ℚ)
            + ((n - a).factorial : ℚ) * H (m - i - a) i S * (kraw n (n - a) b : ℚ))
          = ((b.factorial : ℚ) / (-2 : ℚ) ^ i) * ∑ a ∈ range ℓ,
            (hcoef (m - 2 * i) i (i + a - i) (i + b - i) * H (i + a) i S
              + hcoef (m - 2 * i) i (m - i - a - i) (i + b - i) * H (m - i - a) i S) := by
        rw [mul_sum]
        refine sum_congr rfl fun a ha => ?_
        have haℓ := mem_range.mp ha
        rw [show i + a - i = a by omega, show i + b - i = b by omega,
          show m - i - a - i = n - a by omega,
          hcoef_eq_kraw (by omega : a ≤ n) hbn, hcoef_eq_kraw (by omega : n - a ≤ n) hbn]
        field_simp
      rw [hconv, hGS, mul_zero]
  -- conclusion
  rw [he]
  apply sum_eq_zero
  intro i _
  apply sum_eq_zero
  intro k _
  rw [hH0 k i, map_zero]

end FTPaper.LemmaS
