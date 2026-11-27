import FTPaper.QTheorem1

/-!
# Theorem 1 template: correctness and exact call count (direct conversions)
-/

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open OAI.Computability.NearSquareRoot.KernelPass.Plan (frequency walshMatrix)
open OAI.Computability.NearSquareRoot.KernelPass.Rect (renumber)
open OAI.Computability.NearSquareRoot.KernelPass.Rect.Binary (geometricPencilF System Label card_label)
open scoped OAI.Computability.NearSquareRoot.CyclotomicCode
open OAI.Computability.NearSquareRoot.BinaryQuery
open Matrix Finset Polynomial

namespace FTPaper

/-- Rows: a label, a copy index, and a shift. -/
abbrev Row (L b m R : ℕ) := Label L b × (Fin R × (Fin (m + 1) → ZMod 2))

/-- Number of rows in one batch. -/
abbrev rows (L b m R : ℕ) : ℕ := Fintype.card (Row L b m R)

/-- The numbering of rows. -/
noncomputable def rowEquiv (L b m R : ℕ) : Row L b m R ≃ Fin (rows L b m R) := Fintype.equivFin _

/-- The shift carried by a numbered row. -/
noncomputable def shiftAt {L b m R : ℕ} (i : Fin (rows L b m R)) : Fin (m + 1) → ZMod 2 :=
  ((rowEquiv L b m R).symm i).2.2

/-- The routed pencil with our coefficients. -/
noncomputable def ourPencil (L b m R : ℕ) (S : System L b) :=
  geometricPencilF S m (stageB₀ m) (stageB m (fun k : Fin R × (Fin (m + 1) → ZMod 2) => k.2))

/-- The stage as a rational plan. -/
noncomputable def ourStage (L b m R : ℕ) (S : System L b) :
    QPlan (Charged.Axes (m := m) S.geometry) (rows L b m R) (rows L b m R) :=
  QPlan.embed (renumber (rowEquiv L b m R) (ourPencil L b m R S))

/-- Number of check rows: every label and copy, times the shifts outside the window. -/
abbrev checks (L b m R u v : ℕ) : ℕ :=
  Fintype.card (Label L b) * R * (outside u v (0 : Fin (m + 1) → ZMod 2)).card

/-- Predictor multiplier of row `i` at signature `κ`. -/
noncomputable def predMult (L b m R u v : ℕ) (i : Fin (rows L b m R)) (κ : Fin (m + 1) → ZMod 2) : ℚ :=
  ∑ t ∈ Finset.range (v - u + 1), (winPoly u v (shiftAt i)).coeff t * (mismatch κ (shiftAt i) : ℚ) ^ t

lemma predMult_eq (L b m R u v : ℕ) (i : Fin (rows L b m R)) (κ : Fin (m + 1) → ZMod 2) :
    predMult L b m R u v i κ = (winPoly u v (shiftAt i)).eval (mismatch κ (shiftAt i) : ℚ) :=
  horner_sum_eval u v _ _

/-- At most `checks` rows are wrongly predicted at any signature. -/
lemma card_wrong_le (L b m R u v : ℕ) (κ : Fin (m + 1) → ZMod 2) :
    (univ.filter fun i : Fin (rows L b m R) => predMult L b m R u v i κ ≠ sgnZ κ).card
      ≤ checks L b m R u v := by
  classical
  have hsub : (univ.filter fun i : Fin (rows L b m R) => predMult L b m R u v i κ ≠ sgnZ κ)
      ⊆ univ.filter fun i : Fin (rows L b m R) => shiftAt i ∈ outside u v κ := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    simp only [outside, Finset.mem_filter, Finset.mem_univ, true_and]
    intro hw
    exact hi (by rw [predMult_eq, winPoly_window u v κ _ hw.1 hw.2])
  have hcount : (univ.filter fun i : Fin (rows L b m R) => shiftAt i ∈ outside u v κ).card
      = Fintype.card (Label L b) * R * (outside u v κ).card := by
    rw [← Finset.card_map (rowEquiv L b m R).symm.toEmbedding]
    have : (univ.filter fun i : Fin (rows L b m R) => shiftAt i ∈ outside u v κ).map
        (rowEquiv L b m R).symm.toEmbedding
        = (univ : Finset (Label L b)) ×ˢ ((univ : Finset (Fin R)) ×ˢ outside u v κ) := by
      ext ⟨w, r, γ⟩
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_product,
        Equiv.coe_toEmbedding, shiftAt]
      constructor
      · rintro ⟨i, hi, he⟩
        have hi' := (Finset.mem_filter.mp hi).2
        rw [he] at hi'
        exact hi'
      · intro hγ
        refine ⟨rowEquiv L b m R (w, r, γ), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simp⟩
        simpa using hγ
    rw [this, Finset.card_product, Finset.card_product, Finset.card_univ, Finset.card_univ,
      Fintype.card_fin, mul_assoc]
  calc _ ≤ _ := Finset.card_le_card hsub
    _ = _ := hcount
    _ = checks L b m R u v := by rw [card_outside]

/-- Vandermonde nodes `1, 2, …, rows`. -/
def node {n : ℕ} (i : Fin n) : ℚ := (i : ℕ) + 1

lemma node_injective (n : ℕ) : Function.Injective (node (n := n)) := by
  intro i j h
  simp only [node, add_left_inj, Nat.cast_inj] at h
  exact Fin.ext h

/-- The check matrix. -/
noncomputable def checkMatrix (L b m R u v : ℕ) : Matrix (Fin (checks L b m R u v)) (Fin (rows L b m R)) ℚ :=
  Matrix.of fun r i => node i ^ (r : ℕ)

lemma exists_tables (L b m R u v : ℕ) (κ : Fin (m + 1) → ZMod 2) :
    ∃ T, IsTable (checkMatrix L b m R u v) (fun i => predMult L b m R u v i κ) (sgnZ κ) T := by
  classical
  exact exists_table_vandermonde node (node_injective _) (card_wrong_le L b m R u v κ)

/-- The table at signature `κ`. -/
noncomputable def table (L b m R u v : ℕ) (κ : Fin (m + 1) → ZMod 2) :=
  Classical.choose (exists_tables L b m R u v κ)

/-- **The repaired batch (direct conversions).** -/
noncomputable def batch (L b m R u v : ℕ) (S : System L b) :
    QPlan (Charged.Axes (m := m) S.geometry) (rows L b m R) (rows L b m R) :=
  QPlan.twoPass (QPlan.horner (ourStage L b m R S) (fun t i => (winPoly u v (shiftAt i)).coeff t) (v - u))
    (QPlan.mix fun r i => checkMatrix L b m R u v r i) (QPlan.mix fun i r => checkMatrix L b m R u v r i)
    (QPlan.spectralTable (test (m + 1) (S.D - 1))
      fun κ => QPlan.tabMatrix (table L b m R u v κ) (sgnZ κ))

theorem frequency_ourStage (L b m R : ℕ) (S : System L b) {h : ℕ}
    (x : Bank (Charged.Axes (m := m) S.geometry) h (rows L b m R)) (i : Fin (rows L b m R))
    (y : Addr (Charged.Axes (m := m) S.geometry) h) :
    frequency ((ourStage L b m R S).applyAt h x) i y
      = (mismatch (∑ t, test (m + 1) (S.D - 1) (y t)) (shiftAt i) : ℚ) * frequency x i y := by
  obtain ⟨⟨w, k⟩, rfl⟩ := (rowEquiv L b m R).surjective i
  have := frequency_stage S (fun k : Fin R × (Fin (m + 1) → ZMod 2) => k.2) (rowEquiv L b m R) x w k y
  simpa [ourStage, ourPencil, QPlan.applyAt_embed, shiftAt] using this

/-- **The batch multiplies every frequency by the product of query signs.** -/
theorem frequency_ourBatch (L b m R u v : ℕ) (S : System L b) {h : ℕ}
    (x : Bank (Charged.Axes (m := m) S.geometry) h (rows L b m R)) (i : Fin (rows L b m R))
    (y : Addr (Charged.Axes (m := m) S.geometry) h) :
    frequency ((batch L b m R u v S).applyAt h x) i y
      = sgnZ (∑ t, test (m + 1) (S.D - 1) (y t)) * frequency x i y := by
  refine QPlan.frequency_batch (ourStage L b m R S) (test (m + 1) (S.D - 1))
    (fun i κ => (mismatch κ (shiftAt i) : ℚ)) (fun x j y => frequency_ourStage L b m R S x j y)
    (fun t i => (winPoly u v (shiftAt i)).coeff t) (v - u) sgnZ (checkMatrix L b m R u v)
    (table L b m R u v) (fun κ => ?_) x i y
  exact Classical.choose_spec (exists_tables L b m R u v κ)


/-- **Theorem 1 template, correctness.** After OpenAI's two zero-call outer passes, the batch
computes the normalized Walsh–Hadamard transform on every row, at every child width. -/
theorem template_correct (L b m R u v : ℕ) (S : System L b) (hodd : m + 1 ≡ 1 [MOD 2]) :
    ∃ front back : Plan (Charged.Axes (m := m) S.geometry) 1 1, front.calls = 0 ∧ back.calls = 0 ∧
      QPlan.Correct (QPlan.wrap front back (batch L b m R u v S)) := by
  apply QPlan.correct_of_product (m := m + 1) (u := S.geometry.D - 1) hodd
  intro h x i y
  exact frequency_ourBatch L b m R u v S x i y

/-- **Theorem 1 template, exact call count.** -/
theorem template_calls (L b m R u v : ℕ) (S : System L b)
    (front back : Plan (Charged.Axes (m := m) S.geometry) 1 1) (hf : front.calls = 0)
    (hb : back.calls = 0) :
    (QPlan.wrap front back (batch L b m R u v S)).calls
      = 2 * (v - u) * (ourPencil L b m R S).calls
        + 2 * (checks L b m R u v + checks L b m R u v) * Charged.Axes (m := m) S.geometry := by
  have hb2 : (batch L b m R u v S).calls
      = 2 * (v - u) * (ourStage L b m R S).calls
        + 2 * (checks L b m R u v + checks L b m R u v) * Charged.Axes (m := m) S.geometry :=
    QPlan.calls_batch (A := Charged.Axes (m := m) S.geometry) _ _ _ _ _ _
  rw [QPlan.calls_wrap _ _ _ hf hb, hb2]
  simp only [ourStage, QPlan.calls_embed,
    OAI.Computability.NearSquareRoot.KernelPass.Rect.calls_renumber]

/-- **Theorem 1 template, end to end.** For every routing system with `m + 1 ≤ q^{L/2}`, an odd
number `m + 1` of queries, and any window `[u, v]`, there is a correct rational plan on all
`rows` rows whose child calls are at most
`2 (v − u) · 6 D (1 + b)^L · rows + 4 · checks · A`. -/
theorem template_end_to_end (L b m R u v : ℕ) (S : System L b) (hodd : m + 1 ≡ 1 [MOD 2])
    (hb : 1 ≤ b) (hq : m + 1 ≤ (2 ^ b) ^ (L / 2)) :
    ∃ p : QPlan (Charged.Axes (m := m) S.geometry) (rows L b m R) (rows L b m R),
      QPlan.Correct p ∧
      p.calls ≤ 2 * (v - u) * (6 * S.D * (1 + b) ^ L * rows L b m R)
        + 4 * checks L b m R u v * Charged.Axes (m := m) S.geometry := by
  obtain ⟨front, back, hf, hb', hc⟩ := template_correct L b m R u v S hodd
  refine ⟨_, hc, ?_⟩
  rw [template_calls L b m R u v S front back hf hb']
  have hR1 := lemmaR1_pencilF S m (stageB₀ m) (stageB m (fun k : Fin R × (Fin (m + 1) → ZMod 2) => k.2))
    hb hq
  have hrows : (2 ^ b) ^ L * Fintype.card (Fin R × (Fin (m + 1) → ZMod 2)) = rows L b m R := by
    simp only [rows, Row, Fintype.card_prod, card_label]
  rw [hrows] at hR1
  have : 2 * (v - u) * (ourPencil L b m R S).calls ≤ 2 * (v - u) * (6 * S.D * (1 + b) ^ L * rows L b m R) :=
    Nat.mul_le_mul_left _ hR1
  nlinarith [this]

end FTPaper
