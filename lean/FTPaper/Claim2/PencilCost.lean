import FTPaper.Claim2.SparsePencil
import FTPaper.Claim2.Local

/-!
# Sparse local cost of the row-diagonal pencil

* `planSparse_le_planFree`: the sparse count never exceeds the dense one. So OpenAI's free
  single-row endpoint plans (dense count `0`) are free here too.
* `planSparse_pencilS`: with free endpoint plans and diagonal coefficients, the pencil spends
  at most `R · (|F| (|L| (|J| + 1) + 1) + |C| (2|J| + 1) + 2)` gates per address outside calls,
  where `R = |L × W|` is its number of rows. Per row this is polynomial in the number of
  labels, rectangles and queries, and independent of the number of rows per label.
-/

set_option linter.unusedSectionVars false

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open OAI.Computability.NearSquareRoot.KernelPass.Rect
open Matrix Finset

namespace FTPaper.Claim2

open FTPaper.Circ

/-! ## General facts -/

lemma rowCost_le_dense {i o : ℕ} (c : Fin o → Fin i → ℚ) : rowCost c ≤ o * i := by
  unfold rowCost
  calc ∑ b, ((univ.filter fun a => c b a ≠ 0).card - 1) ≤ ∑ _b : Fin o, i :=
        Finset.sum_le_sum fun b _ => by
          have := card_filter_le (univ : Finset (Fin i)) (fun a => c b a ≠ 0)
          simp only [card_univ, Fintype.card_fin] at this
          omega
    _ = o * i := by simp

lemma rowCost_one {c : Fin 1 → Fin 1 → ℚ} : rowCost c = 0 := by
  unfold rowCost
  apply Finset.sum_eq_zero
  intro b _
  have := card_filter_le (univ : Finset (Fin 1)) (fun a => c b a ≠ 0)
  simp only [card_univ, Fintype.card_fin] at this
  omega

/-- **The sparse count never exceeds the dense count.** -/
theorem planSparse_le_planFree {A : ℕ} : ∀ {i o : ℕ} (p : Plan A i o), planSparse p ≤ planFree p
  | _, _, @Plan.mix _ i o c => by
    rw [planFree_mix]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      simp only [planSparse, rowCost_one, le_refl]
    · exact rowCost_le_dense _
  | _, _, .xor _ => le_refl _
  | _, _, .scale _ _ _ => le_refl _
  | _, _, .child _ => le_refl _
  | _, _, .seq p q => by
    simp only [planSparse, planFree_seq]
    exact Nat.add_le_add (planSparse_le_planFree p) (planSparse_le_planFree q)
  | _, _, .parallel p q => by
    simp only [planSparse, planFree_parallel]
    exact Nat.add_le_add (planSparse_le_planFree p) (planSparse_le_planFree q)

lemma planSparse_eq_zero {A i o : ℕ} {p : Plan A i o} (hp : planFree p = 0) : planSparse p = 0 :=
  Nat.eq_zero_of_le_zero (hp ▸ planSparse_le_planFree p)

variable {A : ℕ} {L W J F C : Type} [Fintype L] [Fintype W] [Fintype J] [Fintype F] [Fintype C]
  [DecidableEq L] [DecidableEq W]

@[simp] lemma planSparse_seq {i j o : ℕ} (p : Plan A j o) (q : Plan A i j) :
    planSparse (p.seq q) = planSparse p + planSparse q := rfl

@[simp] lemma planSparse_parallel {i j o u : ℕ} (p : Plan A i o) (q : Plan A j u) :
    planSparse (p.parallel q) = planSparse p + planSparse q := rfl

lemma planSparse_mix_le {i o k : ℕ} (c : Fin o → Fin i → Coefficient)
    (hc : ∀ b, (univ.filter fun a => value (c b a) ≠ 0).card ≤ k + 1) :
    planSparse (Plan.mix (A := A) c) ≤ o * k :=
  FTPaper.QPlan.rowCost_le_of hc

@[simp] lemma planSparse_route {i o : ℕ} (r : Fin o → Fin i) :
    planSparse (Plan.route (A := A) r) = 0 := by
  have := planSparse_mix_le (A := A) (k := 0)
    (fun b a => if a = r b then ((1 : ℤ), 0) else (0, 0)) (fun b => by
      calc (univ.filter fun a => value (if a = r b then ((1 : ℤ), 0) else (0, 0)) ≠ 0).card
          ≤ ({r b} : Finset _).card := card_le_card fun a ha => by
            simp only [mem_filter, mem_univ, true_and] at ha
            by_cases h : a = r b
            · simp [h]
            · simp [h, value] at ha
        _ = 0 + 1 := by simp)
  exact Nat.eq_zero_of_le_zero (by simpa [Plan.route] using this)

@[simp] lemma planSparse_fork {i o u : ℕ} (p : Plan A i o) (q : Plan A i u) :
    planSparse (p.fork q) = planSparse p + planSparse q := by
  simp [Plan.fork]

@[simp] lemma planSparse_emptyPlan {i o : ℕ} : planSparse (emptyPlan (A := A) (i := i) (o := o)) = 0 := by
  have := planSparse_mix_le (A := A) (k := 0) (i := i) (o := o) (fun _ _ => ((0 : ℤ), 0))
    (fun b => by simp [value])
  exact Nat.eq_zero_of_le_zero (by simpa [emptyPlan] using this)

lemma planSparse_addPlan_le {i o : ℕ} (p q : Plan A i o) :
    planSparse (addPlan p q) ≤ planSparse p + planSparse q + o := by
  have := planSparse_mix_le (A := A) (k := 1) (i := o + o) (o := o)
    (fun b => Fin.append (fun a => if b = a then ((1 : ℤ), 0) else (0, 0))
      (fun a => if b = a then ((1 : ℤ), 0) else (0, 0))) (fun b => by
    calc (univ.filter fun a => value (Fin.append (fun a => if b = a then ((1 : ℤ), 0) else (0, 0))
            (fun a => if b = a then ((1 : ℤ), 0) else (0, 0)) a) ≠ 0).card
          ≤ ({Fin.castAdd o b, Fin.natAdd o b} : Finset _).card := card_le_card fun a ha => by
            simp only [mem_filter, mem_univ, true_and] at ha
            refine Fin.addCases (fun l hl => ?_) (fun l hl => ?_) a ha
            · simp only [Fin.append_left] at hl
              by_cases h : b = l
              · simp [h]
              · simp [h, value] at hl
            · simp only [Fin.append_right] at hl
              by_cases h : b = l
              · simp [h]
              · simp [h, value] at hl
      _ ≤ 1 + 1 := card_le_two)
  simp only [addPlan, planSparse_seq, planSparse_fork]
  omega

lemma planSparse_totalList_le {i o : ℕ} : ∀ ps : List (Plan A i o),
    planSparse (totalList ps) ≤ (ps.map planSparse).sum + ps.length * o
  | [] => by simp [totalList]
  | p :: ps => by
    have h1 := planSparse_addPlan_le p (totalList ps)
    have h2 := planSparse_totalList_le ps
    simp only [totalList, List.foldr_cons, List.map_cons, List.sum_cons, List.length_cons] at h1 h2 ⊢
    rw [Nat.succ_mul]
    omega

lemma planSparse_total_le {i o : ℕ} {K : Type} [Fintype K] (p : K → Plan A i o) :
    planSparse (total p) ≤ ∑ k, planSparse (p k) + Fintype.card K * o := by
  have h := planSparse_totalList_le (List.ofFn (p ∘ (Fintype.equivFin K).symm))
  simp only [List.map_ofFn, List.sum_ofFn, List.length_ofFn] at h
  have hs : ∑ j : Fin (Fintype.card K), (planSparse ∘ p ∘ (Fintype.equivFin K).symm) j
      = ∑ k, planSparse (p k) :=
    (Fintype.equivFin K).symm.sum_comp (fun k => planSparse (p k))
  unfold total
  rw [hs] at h
  exact h

@[simp] lemma planSparse_times (c : Coefficient) (p : Plan A 1 1) :
    planSparse (times c p) = planSparse p := by
  have : planSparse (Plan.mix (A := A) (fun _ _ : Fin 1 => c)) = 0 := rowCost_one
  simp [times, this]

lemma planSparse_rows : ∀ (n : ℕ) (p : Fin n → Plan A 1 1),
    planSparse (Rect.rows n p) = ∑ j, planSparse (p j)
  | 0, p => by simp [Rect.rows, planSparse, rowCost]
  | n + 1, p => by
    rw [Rect.rows, planSparse_parallel, planSparse_rows n, Fin.sum_univ_castSucc]

lemma planSparse_diagonal {I : Type} [Fintype I] (p : I → Plan A 1 1) :
    planSparse (Rect.diagonal p) = ∑ j, planSparse (p j) := by
  rw [Rect.diagonal, planSparse_rows]
  exact (Fintype.equivFin I).symm.sum_comp (fun j => planSparse (p j))

/-- A mixing with at most `k + 1` nonzero coefficients per row. -/
lemma planSparse_mixing_le {I O : Type} [Fintype I] [Fintype O] (c : O → I → Coefficient) (k : ℕ)
    (hc : ∀ b, (univ.filter fun a => value (c b a) ≠ 0).card ≤ k + 1) :
    planSparse (mixing (A := A) c) ≤ Fintype.card O * k := by
  apply planSparse_mix_le
  intro b
  calc (univ.filter fun a => value (c ((Fintype.equivFin O).symm b)
          ((Fintype.equivFin I).symm a)) ≠ 0).card
      = (univ.filter fun a => value (c ((Fintype.equivFin O).symm b) a) ≠ 0).card :=
        card_equiv (Fintype.equivFin I).symm (by simp)
    _ ≤ k + 1 := hc _

/-! ## The rectangles and the pencil -/

lemma planSparse_side (active : Finset L) (p : L → Single A) (hp : ∀ v, planSparse (p v) = 0) :
    planSparse (side (W := W) active p) = 0 := by
  unfold side
  rw [planSparse_diagonal]
  apply Finset.sum_eq_zero
  intro u _
  split
  · exact hp _
  · exact planSparse_emptyPlan

lemma planSparse_dentries_le (p : L × W → L × W → Plan A 1 1) :
    planSparse (dentries p) ≤ ∑ k : L × L × W, planSparse (p (k.1, k.2.2) (k.2.1, k.2.2))
      + Fintype.card (L × W) * Fintype.card L := by
  classical
  unfold dentries
  rw [planSparse_seq, planSparse_seq, planSparse_diagonal]
  have h1 := planSparse_mixing_le (A := A) (fun (b : L × W) (k : L × L × W) =>
      if k.1 = b.1 ∧ k.2.2 = b.2 then ((1 : ℤ), 0) else (0, 0)) (Fintype.card L) (fun b => by
    calc (univ.filter fun k : L × L × W => value (if k.1 = b.1 ∧ k.2.2 = b.2 then ((1 : ℤ), 0)
            else (0, 0)) ≠ 0).card
        ≤ (univ.image fun v : L => (b.1, v, b.2)).card := card_le_card fun k hk => by
          simp only [mem_filter, mem_univ, true_and, value_pick, ne_eq, ite_eq_right_iff,
            one_ne_zero, imp_false, not_not] at hk
          obtain ⟨w, v, l⟩ := k
          simp only at hk
          simp [hk.1, hk.2]
      _ ≤ Fintype.card L := by simpa using card_image_le (s := (univ : Finset L))
      _ ≤ Fintype.card L + 1 := Nat.le_succ _)
  have h2 := planSparse_mixing_le (A := A) (fun (k : L × L × W) (a : L × W) =>
      if k.2.1 = a.1 ∧ k.2.2 = a.2 then ((1 : ℤ), 0) else (0, 0)) 0 (fun k => by
    calc (univ.filter fun a : L × W => value (if k.2.1 = a.1 ∧ k.2.2 = a.2 then ((1 : ℤ), 0)
            else (0, 0)) ≠ 0).card
        ≤ ({(k.2.1, k.2.2)} : Finset (L × W)).card := card_le_card fun a ha => by
          simp only [mem_filter, mem_univ, true_and, value_pick, ne_eq, ite_eq_right_iff,
            one_ne_zero, imp_false, not_not] at ha
          obtain ⟨v, l⟩ := a
          simp only at ha
          simp [ha.1, ha.2]
      _ = 0 + 1 := by simp)
  omega

/-- **A free rectangle with free endpoint plans.** -/
lemma planSparse_freeS_le (src dst : Finset L) (weight : Coefficient)
    (B : J → W → W → Coefficient) (S T : L → Single A) (M : J → L → L → Single A)
    (hS : ∀ v, planSparse (S v) = 0) (hT : ∀ w, planSparse (T w) = 0)
    (hM : ∀ j w v, planSparse (M j w v) = 0) :
    planSparse (freeS src dst weight B S T M)
      ≤ Fintype.card (L × L × W) * Fintype.card J + Fintype.card (L × W) * Fintype.card L := by
  unfold freeS
  rw [planSparse_seq, planSparse_seq, planSparse_side _ _ hT, planSparse_side _ _ hS, zero_add,
    add_zero]
  refine (planSparse_dentries_le (A := A) (L := L) (W := W) _).trans ?_
  dsimp only
  have hentry : ∀ k : L × L × W, planSparse (times weight (total fun j =>
      times (B j k.2.2 k.2.2) (M j k.1 k.2.1))) ≤ Fintype.card J := by
    intro k
    rw [planSparse_times]
    refine (planSparse_total_le _).trans ?_
    simp [hM]
  have := Finset.sum_le_sum fun k (_ : k ∈ (univ : Finset (L × L × W))) => hentry k
  simp only [Finset.sum_const, card_univ, smul_eq_mul] at this
  omega

lemma planSparse_fanoutS (T : Finset L) (weight : Coefficient) (dstOut : L → Plan A 1 1)
    (hd : ∀ w, planSparse (dstOut w) = 0) : planSparse (fanoutS (W := W) T weight dstOut) = 0 := by
  classical
  unfold fanoutS
  rw [planSparse_seq, planSparse_diagonal]
  have h1 : ∑ b : L × W, planSparse (if b.1 ∈ T then times weight (dstOut b.1) else emptyPlan) = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    split
    · rw [planSparse_times, hd]
    · exact planSparse_emptyPlan
  have h2 := planSparse_mixing_le (A := A) (fun (b : L × W) (l : W) =>
      if b.2 = l then ((1 : ℤ), 0) else (0, 0)) 0 (fun b => by
    calc (univ.filter fun l : W => value (if b.2 = l then ((1 : ℤ), 0) else (0, 0)) ≠ 0).card
        ≤ ({b.2} : Finset W).card := card_le_card fun l hl => by
          simp only [mem_filter, mem_univ, true_and, value_pick, ne_eq, ite_eq_right_iff,
            one_ne_zero, imp_false, not_not] at hl
          simp [hl]
      _ = 0 + 1 := by simp)
  omega

lemma planSparse_collectS_le (S : Finset L) (B : W → W → Coefficient) (srcIn : L → Plan A 1 1)
    (hs : ∀ v, planSparse (srcIn v) = 0) :
    planSparse (collectS S B srcIn) ≤ Fintype.card W * Fintype.card L := by
  classical
  unfold collectS
  rw [planSparse_seq, planSparse_diagonal]
  have h1 : ∑ a : L × W, planSparse (if a.1 ∈ S then times (B a.2 a.2) (srcIn a.1) else emptyPlan) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    split
    · rw [planSparse_times, hs]
    · exact planSparse_emptyPlan
  have h2 := planSparse_mixing_le (A := A) (fun (k : W) (a : L × W) =>
      if a.2 = k then ((1 : ℤ), 0) else (0, 0)) (Fintype.card L) (fun k => by
    calc (univ.filter fun a : L × W => value (if a.2 = k then ((1 : ℤ), 0) else (0, 0)) ≠ 0).card
        ≤ (univ.image fun v : L => (v, k)).card := card_le_card fun a ha => by
          simp only [mem_filter, mem_univ, true_and, value_pick, ne_eq, ite_eq_right_iff,
            one_ne_zero, imp_false, not_not] at ha
          obtain ⟨v, l⟩ := a
          simp only at ha
          simp [ha]
      _ ≤ Fintype.card L := by simpa using card_image_le (s := (univ : Finset L))
      _ ≤ Fintype.card L + 1 := Nat.le_succ _)
  omega

/-- **A charged rectangle with free endpoint plans.** -/
lemma planSparse_chargedS_le (S T : Finset L) (weight : Coefficient) (B : W → W → Coefficient)
    (srcIn dstOut : L → Plan A 1 1) (common : Plan A 1 1)
    (hs : ∀ v, planSparse (srcIn v) = 0) (hd : ∀ w, planSparse (dstOut w) = 0)
    (hc : planSparse common = 0) :
    planSparse (chargedS S T weight B srcIn dstOut common) ≤ Fintype.card W * Fintype.card L := by
  unfold chargedS
  rw [planSparse_seq, planSparse_seq, planSparse_fanoutS _ _ _ hd, planSparse_diagonal]
  simp only [hc, Finset.sum_const_zero, zero_add]
  exact planSparse_collectS_le _ _ _ hs

lemma planSparse_constantPart (B₀ : W → W → Coefficient)
    (hB₀ : ∀ k l, k ≠ l → value (B₀ k l) = 0) :
    planSparse (constantPart (A := A) (L := L) B₀) = 0 := by
  classical
  unfold constantPart
  have := planSparse_mixing_le (A := A) (fun b a : L × W => if b.1 = a.1 then B₀ b.2 a.2 else (0, 0))
    0 (fun b => by
    calc (univ.filter fun a : L × W => value (if b.1 = a.1 then B₀ b.2 a.2 else (0, 0)) ≠ 0).card
        ≤ ({b} : Finset (L × W)).card := card_le_card fun a ha => by
          simp only [mem_filter, mem_univ, true_and] at ha
          obtain ⟨w, k⟩ := b
          obtain ⟨v, l⟩ := a
          by_cases h1 : w = v
          · by_cases h2 : k = l
            · simp [h1, h2]
            · simp [h1, hB₀ k l h2] at ha
          · simp [h1, value] at ha
      _ = 0 + 1 := by simp)
  omega

/-- **The row-diagonal pencil with free endpoint plans.** -/
theorem planSparse_pencilS (Frees : F → FreeData A L J) (Charged : C → ChargedData A L J)
    (B₀ : W → W → Coefficient) (B : J → W → W → Coefficient)
    (hB₀ : ∀ k l, k ≠ l → value (B₀ k l) = 0)
    (hfS : ∀ r v, planSparse ((Frees r).source v) = 0)
    (hfT : ∀ r w, planSparse ((Frees r).target w) = 0)
    (hfM : ∀ r j w v, planSparse ((Frees r).middle j w v) = 0)
    (hcI : ∀ r j v, planSparse ((Charged r).input j v) = 0)
    (hcO : ∀ r j w, planSparse ((Charged r).output j w) = 0)
    (hcC : ∀ r j, planSparse ((Charged r).common j) = 0) :
    planSparse (pencilS Frees Charged B₀ B)
      ≤ Fintype.card (L × W) * (Fintype.card F * (Fintype.card L * (Fintype.card J + 1) + 1)
          + Fintype.card C * (2 * Fintype.card J + 1) + 2) := by
  unfold pencilS
  have hA1 := planSparse_addPlan_le (constantPart (A := A) (L := L) B₀)
    (addPlan (total fun r => freeS (Frees r).sources (Frees r).destinations (Frees r).weight B
      (Frees r).source (Frees r).target (Frees r).middle)
    (total fun r => total fun j => chargedS (Charged r).sources (Charged r).destinations
      (Charged r).weight (B j) ((Charged r).input j) ((Charged r).output j) ((Charged r).common j)))
  have hA2 := planSparse_addPlan_le
    (total fun r => freeS (A := A) (Frees r).sources (Frees r).destinations (Frees r).weight B
      (Frees r).source (Frees r).target (Frees r).middle)
    (total fun r => total fun j => chargedS (A := A) (Charged r).sources (Charged r).destinations
      (Charged r).weight (B j) ((Charged r).input j) ((Charged r).output j) ((Charged r).common j))
  have hCP := planSparse_constantPart (A := A) (L := L) B₀ hB₀
  have hTF := planSparse_total_le (fun r => freeS (A := A) (Frees r).sources (Frees r).destinations
    (Frees r).weight B (Frees r).source (Frees r).target (Frees r).middle)
  have hTC := planSparse_total_le (fun r => total fun j => chargedS (A := A) (Charged r).sources
    (Charged r).destinations (Charged r).weight (B j) ((Charged r).input j) ((Charged r).output j)
    ((Charged r).common j))
  have hF : ∑ r, planSparse (freeS (A := A) (Frees r).sources (Frees r).destinations
      (Frees r).weight B (Frees r).source (Frees r).target (Frees r).middle)
      ≤ Fintype.card F * (Fintype.card (L × L × W) * Fintype.card J
          + Fintype.card (L × W) * Fintype.card L) := by
    calc _ ≤ ∑ _r : F, (Fintype.card (L × L × W) * Fintype.card J
          + Fintype.card (L × W) * Fintype.card L) :=
          Finset.sum_le_sum fun r _ => planSparse_freeS_le _ _ _ _ _ _ _ (hfS r) (hfT r) (hfM r)
      _ = _ := by rw [Finset.sum_const, card_univ, smul_eq_mul]
  have hC : ∑ r, planSparse (total fun j => chargedS (A := A) (Charged r).sources
      (Charged r).destinations (Charged r).weight (B j) ((Charged r).input j) ((Charged r).output j)
      ((Charged r).common j))
      ≤ Fintype.card C * (Fintype.card J * (Fintype.card W * Fintype.card L)
          + Fintype.card J * Fintype.card (L × W)) := by
    calc _ ≤ ∑ _r : C, (Fintype.card J * (Fintype.card W * Fintype.card L)
          + Fintype.card J * Fintype.card (L × W)) := by
          refine Finset.sum_le_sum fun r _ => (planSparse_total_le _).trans ?_
          have : ∑ j, planSparse (chargedS (A := A) (Charged r).sources (Charged r).destinations
              (Charged r).weight (B j) ((Charged r).input j) ((Charged r).output j)
              ((Charged r).common j)) ≤ ∑ _j : J, Fintype.card W * Fintype.card L :=
            Finset.sum_le_sum fun j _ => planSparse_chargedS_le _ _ _ _ _ _ _
              (hcI r j) (hcO r j) (hcC r j)
          rw [Finset.sum_const, card_univ, smul_eq_mul] at this
          omega
      _ = _ := by rw [Finset.sum_const, card_univ, smul_eq_mul]
  -- arithmetic
  have hLLW : Fintype.card (L × L × W) = Fintype.card L * Fintype.card (L × W) :=
    Fintype.card_prod _ _
  have hWL : Fintype.card W * Fintype.card L = Fintype.card (L × W) := by
    rw [Fintype.card_prod, mul_comm]
  rw [hLLW] at hF
  rw [hWL] at hC
  have key : Fintype.card F * (Fintype.card L * Fintype.card (L × W) * Fintype.card J
        + Fintype.card (L × W) * Fintype.card L) + Fintype.card F * Fintype.card (L × W)
      + (Fintype.card C * (Fintype.card J * Fintype.card (L × W)
        + Fintype.card J * Fintype.card (L × W)) + Fintype.card C * Fintype.card (L × W))
      + Fintype.card (L × W) + Fintype.card (L × W)
      = Fintype.card (L × W) * (Fintype.card F * (Fintype.card L * (Fintype.card J + 1) + 1)
          + Fintype.card C * (2 * Fintype.card J + 1) + 2) := by ring
  omega

end FTPaper.Claim2
