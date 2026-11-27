import Mathlib

/-!
# Limits of the template method: charged rectangles (paper: Theorem 1.5(3))

Routing of the [OAI §5.2] type: every label `v` carries a vector `d v` from a finite set `𝔻`
(in [OAI], `𝔻 = 𝔽₂^D`), a relation `B` ("orthogonal") that no label has with itself, and a
decomposition of the identity on labels into weighted rectangles `I × J`: *charged* ones
(`C`) and *free* ones (`F`), where free rectangles only contain pairs `(v, w)` with
`B (d v) (d w)`.

`charged_card_ge`: there are at least `|V| / |𝔻|` charged rectangles.
-/

open Matrix Finset

namespace FTPaper

variable {K V : Type*} [Field K] [Fintype V] [DecidableEq V]

/-- The `0/1` matrix of the rectangle `R.1 × R.2`. -/
def rect (R : Finset V × Finset V) : Matrix V V K :=
  Matrix.of fun v w => if v ∈ R.1 ∧ w ∈ R.2 then 1 else 0

/-- **Theorem 3(3), combinatorial core.** If the identity matrix on the labels is a weighted sum
of charged rectangles `C` and free rectangles `F`, free rectangles only contain `B`-related
pairs, and no label is `B`-related to itself, then `|V| ≤ |𝔻| · |C|`. -/
theorem charged_card_ge {𝔻 : Type*} [Fintype 𝔻] [DecidableEq 𝔻] [Nonempty 𝔻]
    (d : V → 𝔻) (B : 𝔻 → 𝔻 → Prop) (hB : ∀ v, ¬ B (d v) (d v))
    (C F : Finset (Finset V × Finset V)) (wC wF : Finset V × Finset V → K)
    (hfree : ∀ R ∈ F, ∀ v ∈ R.1, ∀ w ∈ R.2, B (d v) (d w))
    (hdecomp : (1 : Matrix V V K) = ∑ R ∈ C, wC R • rect R + ∑ R ∈ F, wF R • rect R) :
    Fintype.card V ≤ Fintype.card 𝔻 * C.card := by
  classical
  -- pigeonhole: a fiber `S` of `d` with `|V| ≤ |𝔻| |S|`
  obtain ⟨y, hy⟩ : ∃ y : 𝔻,
      Fintype.card V ≤ Fintype.card 𝔻 * (univ.filter fun v => d v = y).card := by
    by_contra h
    simp only [not_exists, not_le] at h
    have hlt : ∑ y : 𝔻, Fintype.card 𝔻 * (univ.filter fun v => d v = y).card
        < ∑ _y : 𝔻, Fintype.card V :=
      Finset.sum_lt_sum_of_nonempty univ_nonempty fun y _ => h y
    rw [← Finset.mul_sum, ← Finset.card_eq_sum_card_fiberwise (fun v _ => mem_univ (d v)),
      Finset.sum_const, Finset.card_univ, smul_eq_mul, card_univ] at hlt
    exact lt_irrefl _ hlt
  set S := univ.filter fun v => d v = y with hS
  -- on `S × S` no free rectangle contributes
  have hfree0 : ∀ R ∈ F, ∀ v w : S, (rect R : Matrix V V K) v.1 w.1 = 0 := by
    intro R hR v w
    have hv : d v.1 = y := (Finset.mem_filter.mp v.2).2
    have hw : d w.1 = y := (Finset.mem_filter.mp w.2).2
    simp only [rect, of_apply]
    split_ifs with h
    · exact absurd (by have := hfree R hR v.1 h.1 w.1 h.2; rwa [hw, ← hv] at this) (hB v.1)
    · rfl
  -- so the identity on `S` factors through the charged rectangles
  let U : Matrix S C K := Matrix.of fun v R => if v.1 ∈ R.1.1 then 1 else 0
  let W : Matrix C S K := Matrix.of fun R w => wC R.1 * if w.1 ∈ R.1.2 then 1 else 0
  have hone : (1 : Matrix S S K) = U * W := by
    funext v w
    have h := congrFun (congrFun hdecomp v.1) w.1
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h
    have hF : ∑ R ∈ F, wF R * (rect R : Matrix V V K) v.1 w.1 = 0 :=
      Finset.sum_eq_zero fun R hR => by rw [hfree0 R hR v w, mul_zero]
    rw [hF, add_zero] at h
    have h1 : (1 : Matrix S S K) v w = (1 : Matrix V V K) v.1 w.1 := by
      simp only [Matrix.one_apply, Subtype.ext_iff]
    rw [h1, h, Matrix.mul_apply, ← Finset.sum_coe_sort C]
    refine Finset.sum_congr rfl fun R _ => ?_
    simp only [rect, of_apply, U, W]
    by_cases h1 : v.1 ∈ R.1.1 <;> by_cases h2 : w.1 ∈ R.1.2 <;> simp [h1, h2]
  have hrank : Fintype.card S ≤ C.card := by
    calc Fintype.card S = (1 : Matrix S S K).rank := Matrix.rank_one.symm
      _ = (U * W).rank := by rw [hone]
      _ ≤ U.rank := Matrix.rank_mul_le_left U W
      _ ≤ Fintype.card C := Matrix.rank_le_card_width U
      _ = C.card := Fintype.card_coe C
  have hcardS : Fintype.card S = S.card := Fintype.card_coe S
  calc Fintype.card V ≤ Fintype.card 𝔻 * S.card := hy
    _ ≤ Fintype.card 𝔻 * C.card := Nat.mul_le_mul_left _ (hcardS ▸ hrank)

/-- **Theorem 3(3), [OAI] form.** With label vectors in `𝔽₂^D`, at least `|V| / 2^D` charged
rectangles are needed. -/
theorem charged_card_ge_pow {D : ℕ} (d : V → (Fin D → ZMod 2))
    (B : (Fin D → ZMod 2) → (Fin D → ZMod 2) → Prop) (hB : ∀ v, ¬ B (d v) (d v))
    (C F : Finset (Finset V × Finset V)) (wC wF : Finset V × Finset V → K)
    (hfree : ∀ R ∈ F, ∀ v ∈ R.1, ∀ w ∈ R.2, B (d v) (d w))
    (hdecomp : (1 : Matrix V V K) = ∑ R ∈ C, wC R • rect R + ∑ R ∈ F, wF R • rect R) :
    Fintype.card V ≤ 2 ^ D * C.card := by
  have h := charged_card_ge d B hB C F wC wF hfree hdecomp
  simpa [Fintype.card_fun, ZMod.card] using h

/-- **Theorem 3(3), pairing form** (paper: Theorem 1.5(3)). For any pairing on `𝔽₂^D` that is
nonzero on each `(d v, d v)`: if the pairing vanishes on every free rectangle, there are at least
`|V| / 2^D` charged rectangles. In OpenAI's routing, `⟨d v, d v⟩ = 1` and the free rectangles are
those on which the pairing vanishes. -/
theorem charged_card_ge_pairing {D : ℕ} (d : V → (Fin D → ZMod 2))
    (pair : (Fin D → ZMod 2) → (Fin D → ZMod 2) → ZMod 2) (hself : ∀ v, pair (d v) (d v) ≠ 0)
    (C F : Finset (Finset V × Finset V)) (wC wF : Finset V × Finset V → K)
    (hfree : ∀ R ∈ F, ∀ v ∈ R.1, ∀ w ∈ R.2, pair (d v) (d w) = 0)
    (hdecomp : (1 : Matrix V V K) = ∑ R ∈ C, wC R • rect R + ∑ R ∈ F, wF R • rect R) :
    Fintype.card V ≤ 2 ^ D * C.card :=
  charged_card_ge_pow d (fun x y => pair x y = 0) hself C F wC wF hfree hdecomp

end FTPaper
