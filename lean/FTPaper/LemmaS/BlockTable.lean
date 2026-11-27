import FTPaper.LemmaS.Butterfly

/-!
# The structured table on one block (Lemma S, decoding)

At a frequency with signature `κ`, the predictor is wrong only on rows `S` of a block with
`S ∆ κ` in the tails. The error `e = g ⊙ X` (with `g = p - z`) is seen through the syndrome
`y = P_E H e`. The table is the FIXED operator `q(M) · Λ · q(M)` between two sign twists `D_κ`:

`decodeL u q κ Λ = D_κ · q(M) · Λ · q(M) · D_κ`,

where `q(M)` inverts the check operator `M` on the tails (`decoder_poly`) and `Λ` divides by
`g` on the translated tails. `block_table`: the lift `H (decodeL y)` equals `X` on every row
where the predictor is wrong, and `decodeL y` is supported on the tails.
-/

namespace FTPaper.LemmaS

open Finset Polynomial

variable {m : ℕ}

/-! ## Parities -/

lemma neg_one_pow_card_symmDiff {α : Type*} [DecidableEq α] (A B : Finset α) :
    (-1 : ℚ) ^ (symmDiff A B).card = (-1) ^ A.card * (-1) ^ B.card := by
  have hd : Disjoint (A \ B) (B \ A) := disjoint_sdiff_sdiff
  have hs : (symmDiff A B).card = (A \ B).card + (B \ A).card := by
    rw [Finset.symmDiff_def, card_union_eq_card_add_card.mpr hd]
  have h1 := card_sdiff_add_card_inter A B
  have h2 := card_sdiff_add_card_inter B A
  rw [inter_comm B A] at h2
  rw [← pow_add, ← h1, ← h2, hs]
  have : (A \ B).card + (A ∩ B).card + ((B \ A).card + (A ∩ B).card)
      = ((A \ B).card + (B \ A).card) + 2 * (A ∩ B).card := by ring
  rw [this, pow_add (-1 : ℚ) ((A \ B).card + (B \ A).card) (2 * (A ∩ B).card), pow_mul,
    neg_one_sq, one_pow, mul_one, pow_add]

lemma char_symmDiff (γ β κ : Finset (Fin m)) :
    (-1 : ℚ) ^ (γ ∩ symmDiff β κ).card = (-1) ^ (γ ∩ β).card * (-1) ^ (γ ∩ κ).card := by
  have : γ ∩ symmDiff β κ = symmDiff (γ ∩ β) (γ ∩ κ) := inf_symmDiff_distrib_left γ β κ
  rw [this, neg_one_pow_card_symmDiff]

/-! ## Twists and scalings -/

/-- The sign twist `D_κ f (S) = (-1)^{|S ∩ κ|} f(S)`. -/
def twistL (κ : Finset (Fin m)) : Module.End ℚ (Fn m) where
  toFun f S := (-1 : ℚ) ^ (S ∩ κ).card * f S
  map_add' f g := by funext S; simp only [Pi.add_apply]; ring
  map_smul' c f := by funext S; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma twistL_apply (κ : Finset (Fin m)) (f : Fn m) (S : Finset (Fin m)) :
    twistL κ f S = (-1 : ℚ) ^ (S ∩ κ).card * f S := rfl

/-- Pointwise scaling by `Λ`. -/
def scaleL (Λ : Fn m) : Module.End ℚ (Fn m) where
  toFun f S := Λ S * f S
  map_add' f g := by funext S; simp only [Pi.add_apply]; ring
  map_smul' c f := by funext S; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma scaleL_apply (Λ : Fn m) (f : Fn m) (S : Finset (Fin m)) : scaleL Λ f S = Λ S * f S := rfl

lemma twistL_hada (κ : Finset (Fin m)) (e : Fn m) :
    twistL κ (hada e) = hada (fun S => e (symmDiff S κ)) := by
  classical
  funext γ
  simp only [twistL_apply, hada_apply, mul_sum]
  let σ : Finset (Fin m) ≃ Finset (Fin m) :=
    ⟨fun β => symmDiff β κ, fun β => symmDiff β κ,
      fun β => symmDiff_symmDiff_cancel_right κ β, fun β => symmDiff_symmDiff_cancel_right κ β⟩
  conv_rhs => rw [← σ.sum_comp]
  refine sum_congr rfl fun β _ => ?_
  simp only [σ, Equiv.coe_fn_mk, symmDiff_symmDiff_cancel_right, char_symmDiff]
  ring

lemma hada_twistL (κ : Finset (Fin m)) (b : Fn m) (β : Finset (Fin m)) :
    hada (twistL κ b) β = hada b (symmDiff β κ) := by
  simp only [hada_apply, twistL_apply]
  refine sum_congr rfl fun γ _ => ?_
  rw [inter_comm (symmDiff β κ) γ, char_symmDiff, inter_comm β γ]
  ring

lemma restrictE_twistL (u : ℕ) (κ : Finset (Fin m)) (f : Fn m) :
    restrictE u (twistL κ f) = twistL κ (restrictE u f) := by
  funext S
  simp only [restrictE_apply, twistL_apply]
  split_ifs <;> simp

lemma restrictE_aeval (u : ℕ) (p : ℚ[X]) (f : Fn m) :
    restrictE u (aeval (checkOp u) p f) = aeval (checkOp u) p (restrictE u f) := by
  have hc : Commute (restrictE (m := m) u) (checkOp u) := by
    refine LinearMap.ext fun f => ?_
    simp only [Module.End.mul_apply, restrictE_checkOp, checkOp_restrictE]
  have : restrictE (m := m) u * aeval (checkOp u) p = aeval (checkOp u) p * restrictE u := by
    rw [aeval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, (hc.pow_right i).eq]
  exact LinearMap.congr_fun this f

/-! ## The block decoder -/

/-- The table on one block: `D_κ · q(M) · Λ · q(M) · D_κ`. -/
noncomputable def decodeL (u : ℕ) (q : ℚ[X]) (κ : Finset (Fin m)) (Λ : Fn m) :
    Module.End ℚ (Fn m) :=
  twistL κ * aeval (checkOp u) q * scaleL Λ * aeval (checkOp u) q * twistL κ

/-- The division weights at signature `κ`: `1 / g(δ ∆ κ)` where `g ≠ 0`. -/
noncomputable def divW (κ : Finset (Fin m)) (g : Fn m) : Fn m :=
  fun δ => if g (symmDiff δ κ) = 0 then 0 else (g (symmDiff δ κ))⁻¹

/-- **The structured table is correct on one block.** -/
theorem block_table {u : ℕ} (q : ℚ[X])
    (hq1 : ∀ f : Fn m, aeval (checkOp u) q (checkOp u f) = restrictE u f)
    (hq2 : ∀ f : Fn m, checkOp u (aeval (checkOp u) q f) = restrictE u f)
    (κ : Finset (Fin m)) (g X : Fn m)
    (hg : ∀ S, g S ≠ 0 → (symmDiff S κ).card < u ∨ m - u < (symmDiff S κ).card) :
    let a := decodeL u q κ (divW κ g) (restrictE u (hada fun S => g S * X S))
    restrictE u a = a ∧ ∀ β, g β ≠ 0 → hada a β = X β := by
  intro a
  set e' : Fn m := fun S => g (symmDiff S κ) * X (symmDiff S κ) with he'def
  have he' : restrictE u e' = e' := by
    funext S
    rw [restrictE_apply]
    split_ifs with h
    · rfl
    · simp only [he'def]
      by_cases hgS : g (symmDiff S κ) = 0
      · rw [hgS, zero_mul]
      · exfalso
        apply h
        have := hg _ hgS
        rwa [symmDiff_symmDiff_cancel_right] at this
  -- step 1: `q(M) (D_κ y) = e'`
  have h1 : twistL κ (restrictE u (hada fun S => g S * X S)) = checkOp u e' := by
    rw [← restrictE_twistL, twistL_hada, checkOp_apply, he']
  have h2 : aeval (checkOp u) q (twistL κ (restrictE u (hada fun S => g S * X S))) = e' := by
    rw [h1, hq1, he']
  -- step 2: divide
  set x' : Fn m := scaleL (divW κ g) e' with hx'def
  have hx'val : ∀ β, g β ≠ 0 → x' (symmDiff β κ) = X β := by
    intro β hβ
    simp only [hx'def, scaleL_apply, divW, he'def, symmDiff_symmDiff_cancel_right]
    rw [ite_eq_right hβ]
    field_simp
  have hx' : restrictE u x' = x' := by
    funext S
    rw [restrictE_apply]
    split_ifs with h
    · rfl
    · have := congrFun he' S
      rw [restrictE_apply, ite_eq_right h] at this
      simp only [hx'def, scaleL_apply, ← this, mul_zero]
  -- step 3: `b = q(M) x'` is supported on the tails, and `M b = x'`
  set b := aeval (checkOp u) q x' with hbdef
  have hb : restrictE u b = b := by rw [hbdef, restrictE_aeval, hx']
  have hcb : checkOp u b = x' := by rw [hbdef, hq2, hx']
  have ha : a = twistL κ b := by
    simp only [a, decodeL, Module.End.mul_apply]
    rw [h2]
  constructor
  · rw [ha, restrictE_twistL, hb]
  · intro β hβ
    rw [ha, hada_twistL]
    have htail := hg β hβ
    have := congrFun hcb (symmDiff β κ)
    rw [checkOp_apply, hb, restrictE_apply, ite_eq_left htail] at this
    rw [this, hx'val β hβ]

end FTPaper.LemmaS
