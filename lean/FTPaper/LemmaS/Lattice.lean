import Mathlib

/-!
# The Boolean lattice as an sl₂-module (Lemma S, structure)

Functions on the subsets of `Fin m` (the hypercube `𝔽₂^m`) carry the raising operator
`(R f)(T) = ∑_{t ∈ T} f(T \ {t})` and the lowering operator `(L f)(S) = ∑_{s ∉ S} f(S ∪ {s})`.
They satisfy `L R - R L = m - 2·|S|` and are adjoint for the standard inner product.

Consequences proved here, all over `ℚ`:
* `R` is injective on layer `k` when `2k < m`, and `L` is injective on layer `k` when `m < 2k`.
* A harmonic function `h` on layer `i` (`L h = 0`) generates a string `R^a h`. Here
  `L R^{a+1} h = (a+1)(m-2i-a) R^a h`, the string vanishes from `a = m-2i+1` on, and `R^a` is
  injective on it for `a ≤ m-2i`.
* Every function on layer `k` is `∑_{i ≤ k} R^{k-i} h_i` with each `h_i` harmonic on layer `i`.
  The components with `i + k ≤ m` are unique.
-/

namespace FTPaper.LemmaS

open Finset

variable {m : ℕ}

/-- Functions on the subsets of `Fin m`. -/
abbrev Fn (m : ℕ) := Finset (Fin m) → ℚ

/-- `f` is supported on the subsets of size `k`. -/
def OnLayer (f : Fn m) (k : ℕ) : Prop := ∀ S : Finset (Fin m), S.card ≠ k → f S = 0

/-- The raising operator `(R f)(T) = ∑_{t ∈ T} f(T \ {t})`. -/
def R : Module.End ℚ (Fn m) where
  toFun f T := ∑ t ∈ T, f (T.erase t)
  map_add' f g := by funext T; simp [sum_add_distrib]
  map_smul' c f := by funext T; simp [mul_sum]

/-- The lowering operator `(L f)(S) = ∑_{s ∉ S} f(S ∪ {s})`. -/
def L : Module.End ℚ (Fn m) where
  toFun f S := ∑ s ∈ Sᶜ, f (insert s S)
  map_add' f g := by funext S; simp [sum_add_distrib]
  map_smul' c f := by funext S; simp [mul_sum]

lemma R_apply (f : Fn m) (T : Finset (Fin m)) : R f T = ∑ t ∈ T, f (T.erase t) := rfl
lemma L_apply (f : Fn m) (S : Finset (Fin m)) : L f S = ∑ s ∈ Sᶜ, f (insert s S) := rfl

lemma onLayer_zero (k : ℕ) : OnLayer (0 : Fn m) k := fun _ _ => rfl

lemma OnLayer.add {f g : Fn m} {k : ℕ} (hf : OnLayer f k) (hg : OnLayer g k) :
    OnLayer (f + g) k := fun S hS => by simp [hf S hS, hg S hS]

lemma OnLayer.sub {f g : Fn m} {k : ℕ} (hf : OnLayer f k) (hg : OnLayer g k) :
    OnLayer (f - g) k := fun S hS => by simp [hf S hS, hg S hS]

lemma OnLayer.smul {f : Fn m} {k : ℕ} (hf : OnLayer f k) (c : ℚ) : OnLayer (c • f) k :=
  fun S hS => by simp [hf S hS]

lemma R_onLayer {f : Fn m} {k : ℕ} (hf : OnLayer f k) : OnLayer (R f) (k + 1) := by
  intro T hT
  rw [R_apply]
  apply sum_eq_zero
  intro t ht
  apply hf
  have := card_pos.mpr ⟨t, ht⟩
  rw [card_erase_of_mem ht]
  omega

lemma R_pow_onLayer {f : Fn m} {k : ℕ} (hf : OnLayer f k) (a : ℕ) :
    OnLayer ((R ^ a) f) (k + a) := by
  induction a with
  | zero => simpa using hf
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply, ← add_assoc]
    exact R_onLayer ih

lemma L_onLayer {f : Fn m} {k : ℕ} (hf : OnLayer f (k + 1)) : OnLayer (L f) k := by
  intro S hS
  rw [L_apply]
  apply sum_eq_zero
  intro s hs
  apply hf
  rw [card_insert_of_notMem (by simpa using hs)]
  omega

lemma L_onLayer_zero {f : Fn m} (hf : OnLayer f 0) : L f = 0 := by
  funext S
  rw [L_apply]
  apply sum_eq_zero
  intro s hs
  apply hf
  rw [card_insert_of_notMem (by simpa using hs)]
  omega

/-- The commutation relation `L R - R L = m - 2|S|`. -/
lemma LR_sub_RL (f : Fn m) (S : Finset (Fin m)) :
    L (R f) S - R (L f) S = ((m : ℚ) - 2 * S.card) * f S := by
  rw [L_apply, R_apply]
  simp only [R_apply, L_apply]
  have h1 : ∑ s ∈ Sᶜ, ∑ t ∈ insert s S, f ((insert s S).erase t)
      = ∑ s ∈ Sᶜ, (f S + ∑ t ∈ S, f (insert s (S.erase t))) := by
    refine sum_congr rfl fun s hs => ?_
    have hsS : s ∉ S := by simpa using hs
    rw [sum_insert hsS, erase_insert hsS]
    congr 1
    refine sum_congr rfl fun t ht => ?_
    rw [erase_insert_of_ne (fun h => hsS (by rw [h]; exact ht))]
  have h2 : ∑ t ∈ S, ∑ s ∈ (S.erase t)ᶜ, f (insert s (S.erase t))
      = ∑ t ∈ S, (f S + ∑ s ∈ Sᶜ, f (insert s (S.erase t))) := by
    refine sum_congr rfl fun t ht => ?_
    rw [compl_erase, sum_insert (by simpa using ht), insert_erase ht]
  rw [h1, h2, sum_add_distrib, sum_add_distrib, sum_const, sum_const, sum_comm, card_compl,
    Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
  have hc : S.card ≤ m := by simpa using card_le_univ S
  push_cast [hc]
  ring

/-! ## The inner product -/

/-- The standard inner product. -/
def ip (f g : Fn m) : ℚ := ∑ S, f S * g S

lemma ip_comm (f g : Fn m) : ip f g = ip g f := by
  simp only [ip, mul_comm]

lemma ip_self_nonneg (f : Fn m) : 0 ≤ ip f f :=
  sum_nonneg fun _ _ => mul_self_nonneg _

lemma eq_zero_of_ip_self {f : Fn m} (h : ip f f = 0) : f = 0 := by
  funext S
  have := (sum_eq_zero_iff_of_nonneg (fun S _ => mul_self_nonneg (f S))).mp h S (mem_univ S)
  exact mul_self_eq_zero.mp this

/-- Reindex pairs `(T, t ∈ T)` as pairs `(S, s ∉ S)`. -/
lemma sum_mem_erase (φ : Finset (Fin m) → Fin m → ℚ) :
    ∑ T, ∑ t ∈ T, φ (T.erase t) t = ∑ S, ∑ s ∈ Sᶜ, φ S s := by
  rw [sum_comm' (t' := univ) (s' := fun t => univ.filter (fun T : Finset (Fin m) => t ∈ T))
    (by intro T t; simp)]
  rw [sum_comm' (t' := univ) (s' := fun s => univ.filter (fun S : Finset (Fin m) => s ∉ S))
    (by intro S s; simp)]
  refine sum_congr rfl fun t _ => ?_
  refine sum_nbij' (fun T => T.erase t) (fun S => insert t S) ?_ ?_ ?_ ?_ ?_
  · intro T _; simp
  · intro S _; simp
  · intro T hT
    simp only [mem_filter, mem_univ, true_and] at hT
    exact insert_erase hT
  · intro S hS
    simp only [mem_filter, mem_univ, true_and] at hS
    exact erase_insert hS
  · intro T _; rfl

/-- `R` and `L` are adjoint. -/
lemma ip_R (f g : Fn m) : ip (R f) g = ip f (L g) := by
  simp only [ip, R_apply, L_apply, sum_mul, mul_sum]
  have := sum_mem_erase (m := m) (fun S s => f S * g (insert s S))
  rw [← this]
  refine sum_congr rfl fun T _ => sum_congr rfl fun t ht => ?_
  rw [insert_erase ht]

/-- `‖R f‖² = ‖L f‖² + (m - 2k)‖f‖²` on layer `k`. -/
lemma norm_R {f : Fn m} {k : ℕ} (hf : OnLayer f k) :
    ip (R f) (R f) = ip (L f) (L f) + ((m : ℚ) - 2 * k) * ip f f := by
  rw [ip_R f (R f), ← ip_R (L f) f, ip_comm (R (L f)) f]
  simp only [ip, mul_sum]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun S _ => ?_
  have hc := LR_sub_RL f S
  by_cases hS : S.card = k
  · rw [hS] at hc; linear_combination f S * hc
  · rw [hf S hS]; ring

lemma R_eq_zero_imp {f : Fn m} {k : ℕ} (hf : OnLayer f k) (hk : 2 * k < m) (h : R f = 0) :
    f = 0 := by
  have hn := norm_R hf
  rw [h] at hn
  have h0 : ip (0 : Fn m) 0 = 0 := by simp [ip]
  rw [h0] at hn
  have h1 := ip_self_nonneg (L f)
  have h2 := ip_self_nonneg f
  have hpos : (0 : ℚ) < (m : ℚ) - 2 * k := by
    have : ((2 * k : ℕ) : ℚ) < m := by exact_mod_cast hk
    push_cast at this; linarith
  have : ip f f = 0 := by nlinarith
  exact eq_zero_of_ip_self this

lemma L_eq_zero_imp {f : Fn m} {k : ℕ} (hf : OnLayer f k) (hk : m < 2 * k) (h : L f = 0) :
    f = 0 := by
  have hn := norm_R hf
  rw [h] at hn
  have h0 : ip (0 : Fn m) 0 = 0 := by simp [ip]
  rw [h0] at hn
  have h1 := ip_self_nonneg (R f)
  have h2 := ip_self_nonneg f
  have hpos : (0 : ℚ) < 2 * k - (m : ℚ) := by
    have : (m : ℚ) < ((2 * k : ℕ) : ℚ) := by exact_mod_cast hk
    push_cast at this; linarith
  have : ip f f = 0 := by nlinarith
  exact eq_zero_of_ip_self this

/-! ## Harmonic strings -/

/-- `h` is harmonic on layer `i`: supported there and killed by `L`. -/
def IsHarm (h : Fn m) (i : ℕ) : Prop := OnLayer h i ∧ L h = 0

lemma isHarm_zero (i : ℕ) : IsHarm (0 : Fn m) i := ⟨onLayer_zero i, map_zero L⟩

lemma IsHarm.smul {h : Fn m} {i : ℕ} (hh : IsHarm h i) (c : ℚ) : IsHarm (c • h) i :=
  ⟨hh.1.smul c, by rw [map_smul, hh.2, smul_zero]⟩

/-- `L R^{a+1} h = (a+1)(m - 2i - a) R^a h` for harmonic `h` on layer `i`. -/
lemma L_R_pow {h : Fn m} {i : ℕ} (hh : IsHarm h i) (a : ℕ) :
    L ((R ^ (a + 1)) h) = (((a : ℚ) + 1) * ((m : ℚ) - 2 * i - a)) • (R ^ a) h := by
  induction a with
  | zero =>
    funext S
    have hc := LR_sub_RL h S
    rw [hh.2, map_zero, Pi.zero_apply, sub_zero] at hc
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero,
      Pi.smul_apply, smul_eq_mul]
    by_cases hS : S.card = i
    · rw [hc, hS]; ring
    · rw [hc, hh.1 S hS]; ring
  | succ a ih =>
    funext S
    have hlay : OnLayer ((R ^ (a + 1)) h) (i + (a + 1)) := R_pow_onLayer hh.1 (a + 1)
    have hc := LR_sub_RL ((R ^ (a + 1)) h) S
    have e1 : (R ^ (a + 1 + 1)) h = R ((R ^ (a + 1)) h) := by
      rw [pow_succ' R (a + 1), Module.End.mul_apply]
    rw [e1]
    rw [ih, map_smul] at hc
    simp only [Pi.smul_apply, smul_eq_mul] at hc ⊢
    have e2 : R ((R ^ a) h) = (R ^ (a + 1)) h := by
      rw [pow_succ' R a, Module.End.mul_apply]
    rw [e2] at hc
    by_cases hS : S.card = i + (a + 1)
    · rw [hS] at hc; push_cast at hc ⊢; linear_combination hc
    · rw [hlay S hS] at hc ⊢; linear_combination hc

/-- A harmonic function on a layer above the middle vanishes. -/
lemma IsHarm.eq_zero_of_high {h : Fn m} {i : ℕ} (hh : IsHarm h i) (hi : m < 2 * i) : h = 0 :=
  L_eq_zero_imp hh.1 hi hh.2

/-- The string of a harmonic `h` on layer `i` ends at `R^{m-2i}`. -/
lemma R_pow_harm_eq_zero {h : Fn m} {i : ℕ} (hh : IsHarm h i) {a : ℕ} (ha : m < 2 * i + a) :
    (R ^ a) h = 0 := by
  by_cases hi : m < 2 * i
  · rw [hh.eq_zero_of_high hi, map_zero]
  push Not at hi
  -- first `a = m - 2i + 1`, then higher powers
  have hbase : (R ^ (m - 2 * i + 1)) h = 0 := by
    have hL := L_R_pow hh (m - 2 * i)
    have hz : (((m - 2 * i : ℕ) : ℚ) + 1) * ((m : ℚ) - 2 * i - ((m - 2 * i : ℕ) : ℚ)) = 0 := by
      push_cast [hi]; ring
    rw [hz, zero_smul] at hL
    exact L_eq_zero_imp (R_pow_onLayer hh.1 _) (by omega) hL
  obtain ⟨d, hd⟩ : ∃ d, a = (m - 2 * i + 1) + d := ⟨a - (m - 2 * i + 1), by omega⟩
  rw [hd, add_comm, pow_add, Module.End.mul_apply, hbase, map_zero]

/-- `L^a R^a h = (∏_{j<a} (j+1)(m-2i-j)) h` for harmonic `h` on layer `i`. -/
lemma L_pow_R_pow {h : Fn m} {i : ℕ} (hh : IsHarm h i) (a : ℕ) :
    (L ^ a) ((R ^ a) h) = (∏ j ∈ range a, (((j : ℚ) + 1) * ((m : ℚ) - 2 * i - j))) • h := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ L a, Module.End.mul_apply, L_R_pow hh a, map_smul, ih, smul_smul,
      prod_range_succ, mul_comm]

/-- `R^a` is injective on harmonic functions on layer `i` for `a ≤ m - 2i`. -/
lemma IsHarm.eq_zero_of_R_pow {h : Fn m} {i a : ℕ} (hh : IsHarm h i) (ha : 2 * i + a ≤ m)
    (h0 : (R ^ a) h = 0) : h = 0 := by
  have := L_pow_R_pow hh a
  rw [h0, map_zero] at this
  have hprod : (∏ j ∈ range a, (((j : ℚ) + 1) * ((m : ℚ) - 2 * i - j))) ≠ 0 := by
    rw [prod_ne_zero_iff]
    intro j hj
    have hj' := mem_range.mp hj
    have : ((2 * i + j : ℕ) : ℚ) < m := by exact_mod_cast (by omega : 2 * i + j < m)
    push_cast at this
    apply mul_ne_zero (by positivity)
    linarith
  exact (smul_eq_zero.mp this.symm).resolve_left hprod

/-! ## The string decomposition of a layer -/

/-- The functions supported on layer `k`, as a subspace. -/
def layer (m k : ℕ) : Submodule ℚ (Fn m) where
  carrier := {f | OnLayer f k}
  add_mem' hf hg := OnLayer.add hf hg
  zero_mem' := onLayer_zero k
  smul_mem' c _ hf := OnLayer.smul hf c

/-- Below the middle: `f = R g + h` with `h` harmonic. -/
lemma split_low {f : Fn m} {k : ℕ} (hf : OnLayer f (k + 1)) (hk : 2 * k < m) :
    ∃ g h, OnLayer g k ∧ IsHarm h (k + 1) ∧ f = R g + h := by
  let T : layer m k →ₗ[ℚ] layer m k :=
    (L ∘ₗ R).restrict (p := layer m k) (q := layer m k)
      (fun g hg => L_onLayer (R_onLayer hg))
  have hTg : ∀ g : layer m k, ((T g : layer m k) : Fn m) = L (R (g : Fn m)) := fun _ => rfl
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    have h1 : L (R (g : Fn m)) = 0 := by
      have := congrArg Subtype.val hg
      rw [hTg] at this
      simpa using this
    have h2 : ip (R (g : Fn m)) (R g) = 0 := by rw [ip_R, h1]; simp [ip]
    have h3 : R (g : Fn m) = 0 := eq_zero_of_ip_self h2
    exact Subtype.ext (R_eq_zero_imp (show OnLayer (g : Fn m) k from g.2) hk h3)
  have hsurj : Function.Surjective T := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨g, hg⟩ := hsurj ⟨L f, L_onLayer hf⟩
  have hLR : L (R (g : Fn m)) = L f := by
    have := congrArg Subtype.val hg
    rw [hTg] at this
    simpa using this
  have hg2 : OnLayer (g : Fn m) k := g.2
  refine ⟨g, f - R g, hg2, And.intro (hf.sub (R_onLayer hg2)) ?_, by abel⟩
  rw [map_sub, hLR, sub_self]

/-- Above the middle: `f = R g`. -/
lemma split_high {f : Fn m} {k : ℕ} (hf : OnLayer f (k + 1)) (hk : m < 2 * (k + 1)) :
    ∃ g, OnLayer g k ∧ f = R g := by
  let T : layer m (k + 1) →ₗ[ℚ] layer m (k + 1) :=
    (R ∘ₗ L).restrict (p := layer m (k + 1)) (q := layer m (k + 1))
      (fun g hg => R_onLayer (L_onLayer hg))
  have hTg : ∀ g : layer m (k + 1), ((T g : layer m (k + 1)) : Fn m) = R (L (g : Fn m)) :=
    fun _ => rfl
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    have h1 : R (L (g : Fn m)) = 0 := by
      have := congrArg Subtype.val hg
      rw [hTg] at this
      simpa using this
    have h2 : ip (L (g : Fn m)) (L g) = 0 := by
      rw [← ip_R, h1]; simp [ip]
    have h3 : L (g : Fn m) = 0 := eq_zero_of_ip_self h2
    exact Subtype.ext (L_eq_zero_imp (show OnLayer (g : Fn m) (k + 1) from g.2) hk h3)
  have hsurj : Function.Surjective T := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨g, hg⟩ := hsurj ⟨f, hf⟩
  have hRL : R (L (g : Fn m)) = f := by
    have := congrArg Subtype.val hg
    rw [hTg] at this
    simpa using this
  exact ⟨L g, L_onLayer (show OnLayer (g : Fn m) (k + 1) from g.2), hRL.symm⟩

/-- **String decomposition.** Every `f` on layer `k` is `∑_{i ≤ k} R^{k-i} h_i` with `h_i`
harmonic on layer `i`. -/
theorem exists_strings (k : ℕ) {f : Fn m} (hf : OnLayer f k) :
    ∃ h : ℕ → Fn m, (∀ i, IsHarm (h i) i) ∧ f = ∑ i ∈ range (k + 1), (R ^ (k - i)) (h i) := by
  induction k generalizing f with
  | zero =>
    refine ⟨fun i => if i = 0 then f else 0, fun i => ?_, by simp⟩
    by_cases hi : i = 0
    · subst hi
      simp only [↓reduceIte]
      exact And.intro hf (L_onLayer_zero hf)
    · simp only [hi, ↓reduceIte]
      exact isHarm_zero i
  | succ k ih =>
    by_cases hk : 2 * k < m
    · obtain ⟨g, h', hg, hh', rfl⟩ := split_low hf hk
      obtain ⟨hg', hhg, hsum⟩ := ih hg
      refine ⟨fun i => if i = k + 1 then h' else hg' i, fun i => ?_, ?_⟩
      · by_cases hi : i = k + 1
        · subst hi; simp only [↓reduceIte]; exact hh'
        · simp only [hi, ↓reduceIte]; exact hhg i
      · rw [sum_range_succ, hsum, map_sum]
        simp only [Nat.sub_self, pow_zero, Module.End.one_apply, ↓reduceIte]
        congr 1
        refine sum_congr rfl fun i hi => ?_
        have hik : i ≠ k + 1 := by have := mem_range.mp hi; omega
        simp only [hik, ↓reduceIte]
        have e : k + 1 - i = (k - i) + 1 := by have := mem_range.mp hi; omega
        rw [e, pow_succ', Module.End.mul_apply]
    · push Not at hk
      obtain ⟨g, hg, rfl⟩ := split_high hf (by omega)
      obtain ⟨hg', hhg, hsum⟩ := ih hg
      refine ⟨fun i => if i = k + 1 then 0 else hg' i, fun i => ?_, ?_⟩
      · by_cases hi : i = k + 1
        · subst hi; simp only [↓reduceIte]; exact isHarm_zero (k + 1)
        · simp only [hi, ↓reduceIte]; exact hhg i
      · rw [sum_range_succ, hsum, map_sum]
        simp only [↓reduceIte, map_zero, add_zero]
        refine sum_congr rfl fun i hi => ?_
        have hik : i ≠ k + 1 := by have := mem_range.mp hi; omega
        simp only [hik, ↓reduceIte]
        have e : k + 1 - i = (k - i) + 1 := by have := mem_range.mp hi; omega
        rw [e, pow_succ', Module.End.mul_apply]

/-- **Uniqueness of the string components.** If `∑_{i ≤ k} R^{k-i} h_i = 0` with each `h_i`
harmonic on layer `i`, then `h_i = 0` whenever `i + k ≤ m`. -/
theorem strings_unique (k : ℕ) (h : ℕ → Fn m) (hh : ∀ i, IsHarm (h i) i)
    (h0 : ∑ i ∈ range (k + 1), (R ^ (k - i)) (h i) = 0) : ∀ i ≤ k, i + k ≤ m → h i = 0 := by
  induction k generalizing h with
  | zero =>
    intro i hi _
    have : i = 0 := by omega
    subst this
    simpa using h0
  | succ k ih =>
    -- apply `L`
    have hL : ∑ i ∈ range (k + 1),
        (R ^ (k - i)) (((((k - i : ℕ) : ℚ) + 1) * ((m : ℚ) - 2 * i - (k - i : ℕ))) • h i) = 0 := by
      have := congrArg L h0
      rw [map_sum, map_zero, sum_range_succ, Nat.sub_self, pow_zero, Module.End.one_apply,
        (hh (k + 1)).2, add_zero] at this
      rw [← this]
      refine sum_congr rfl fun i hi => ?_
      have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
      have e : k + 1 - i = (k - i) + 1 := by omega
      rw [e, L_R_pow (hh i), map_smul]
    have hrec := ih _ (fun i => (hh i).smul _) hL
    -- the components with `i ≤ k`
    have hlow : ∀ i ≤ k, i + (k + 1) ≤ m → h i = 0 := by
      intro i hi him
      have := hrec i hi (by omega)
      have hc : (((k - i : ℕ) : ℚ) + 1) * ((m : ℚ) - 2 * i - (k - i : ℕ)) ≠ 0 := by
        apply mul_ne_zero (by positivity)
        have : ((i + (k + 1) : ℕ) : ℚ) ≤ m := by exact_mod_cast him
        push_cast [hi] at this ⊢
        linarith
      exact (smul_eq_zero.mp this).resolve_left hc
    intro i hi him
    rcases Nat.lt_or_ge i (k + 1) with hlt | hge
    · exact hlow i (by omega) him
    · have hik : i = k + 1 := by omega
      subst hik
      -- every other term of the sum vanishes
      have hrest : ∑ j ∈ range (k + 1), (R ^ (k + 1 - j)) (h j) = 0 := by
        apply sum_eq_zero
        intro j hj
        have hjk := mem_range.mp hj
        by_cases hjm : j + (k + 1) ≤ m
        · rw [hlow j (by omega) hjm, map_zero]
        · exact R_pow_harm_eq_zero (hh j) (by omega)
      rw [sum_range_succ, hrest, zero_add, Nat.sub_self, pow_zero, Module.End.one_apply] at h0
      exact h0

end FTPaper.LemmaS
