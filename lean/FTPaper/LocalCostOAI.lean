import FTPaper.Free.R1

/-!
# Gates outside calls of OpenAI's combinators and of the free pencil

Explicit, dense upper bounds on `planFree` for OpenAI's plan combinators (`route`, `fork`,
`collect`, `perRow`, `addPlan`, `total`, `rows`, `diagonal`, `mixing`, `entries`, `side`, `free`,
`charged`, `pencil`, `renumber`). With free single-row plans, the pencil `geometricPencilF`
spends at most `20 (|free rects| + |charged rects| + 1)(m + 2) R³` gates per address outside calls,
where `R` is its number of rows.
-/

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open OAI.Computability.NearSquareRoot.KernelPass.Rect
open OAI.Computability.NearSquareRoot.KernelPass.Rect.Binary
open scoped OAI.Computability.NearSquareRoot.CyclotomicCode
open Finset

namespace FTPaper

namespace Circ

variable {A : ℕ}

theorem planFree_route {i o : ℕ} (r : Fin o → Fin i) :
    planFree (Plan.route (A := A) r) ≤ o * i :=
  planFree_mix_le _

theorem planFree_fork {i o u : ℕ} (p : Plan A i o) (q : Plan A i u) :
    planFree (p.fork q) ≤ planFree p + planFree q + 2 * i * i := by
  have h := planFree_route (A := A) (Fin.append (id : Fin i → Fin i) id)
  simp only [Plan.fork, planFree_seq, planFree_parallel]
  nlinarith

theorem planFree_collect {i : ℕ} : ∀ (n : ℕ) (p : Fin n → Plan A i 1),
    planFree (Plan.collect n p) ≤ ∑ j, planFree (p j) + n * (2 * i * i)
  | 0, p => by simp [Plan.collect, planFree_mix]
  | n + 1, p => by
    rw [Plan.collect]
    have h1 := planFree_fork (Plan.collect n fun j => p j.castSucc) (p (Fin.last n))
    have h2 := planFree_collect n (fun j => p j.castSucc)
    rw [Fin.sum_univ_castSucc]
    nlinarith

theorem planFree_perRow {n : ℕ} (p : Fin n → Plan A 1 1) :
    planFree (Plan.perRow p) ≤ ∑ j, planFree (p j) + n * n + 2 * n * n * n := by
  have h := planFree_collect n (fun j => (p j).seq (Plan.route (A := A) (i := n) (fun _ => j)))
  have hr : ∀ j : Fin n, planFree ((p j).seq (Plan.route (A := A) (i := n) (fun _ => j)))
      ≤ planFree (p j) + n := by
    intro j
    have := planFree_route (A := A) (i := n) (o := 1) (fun _ => j)
    simp only [planFree_seq]
    omega
  have hs : ∑ j, planFree ((p j).seq (Plan.route (A := A) (i := n) (fun _ => j)))
      ≤ ∑ j, planFree (p j) + n * n := by
    calc ∑ j, planFree ((p j).seq (Plan.route (A := A) (i := n) (fun _ => j)))
        ≤ ∑ j : Fin n, (planFree (p j) + n) := Finset.sum_le_sum fun j _ => hr j
      _ = ∑ j, planFree (p j) + n * n := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
  unfold Plan.perRow
  nlinarith

theorem planFree_perRow_free {n : ℕ} (p : Fin n → Plan A 1 1) (hp : ∀ j, planFree (p j) = 0) :
    planFree (Plan.perRow p) ≤ n * n + 2 * n * n * n := by
  have := planFree_perRow p
  simp only [hp, Finset.sum_const_zero, zero_add] at this
  exact this

theorem planFree_convertBank (A n : ℕ) :
    planFree (Plan.convertBank A n) ≤ n * n + 2 * n * n * n :=
  planFree_perRow_free _ (fun _ => planFree_fullConversion _)

theorem planFree_emptyPlan {i o : ℕ} : planFree (emptyPlan (A := A) (i := i) (o := o)) ≤ o * i :=
  planFree_mix_le _

theorem planFree_emptyPlan_one : planFree (emptyPlan (A := A) (i := 1) (o := 1)) = 0 := rfl

theorem planFree_addPlan {i o : ℕ} (p q : Plan A i o) :
    planFree (addPlan p q) ≤ planFree p + planFree q + 2 * o * o + 2 * i * i := by
  have h1 := planFree_fork p q
  have h2 := planFree_mix_le (A := A) (i := o + o) (o := o)
    (fun b => Fin.append (fun a => if b = a then ((1 : ℤ), 0) else (0, 0))
      (fun a => if b = a then ((1 : ℤ), 0) else (0, 0)))
  simp only [addPlan, planFree_seq]
  nlinarith

theorem planFree_totalList {i o : ℕ} : ∀ ps : List (Plan A i o),
    planFree (totalList ps) ≤ (ps.map planFree).sum + ps.length * (2 * o * o + 2 * i * i) + o * i
  | [] => by simpa [totalList] using planFree_emptyPlan (A := A) (i := i) (o := o)
  | p :: ps => by
    have h1 := planFree_addPlan p (totalList ps)
    have h2 := planFree_totalList ps
    simp only [totalList, List.foldr_cons, List.map_cons, List.sum_cons, List.length_cons] at h1 h2 ⊢
    nlinarith

theorem planFree_total {i o : ℕ} {K : Type} [Fintype K] (p : K → Plan A i o) :
    planFree (total p) ≤ ∑ k, planFree (p k) + Fintype.card K * (2 * o * o + 2 * i * i) + o * i := by
  have h := planFree_totalList (List.ofFn (p ∘ (Fintype.equivFin K).symm))
  simp only [List.map_ofFn, List.sum_ofFn, List.length_ofFn] at h
  have hs : ∑ j : Fin (Fintype.card K), (planFree ∘ p ∘ (Fintype.equivFin K).symm) j
      = ∑ k, planFree (p k) :=
    (Fintype.equivFin K).symm.sum_comp (fun k => planFree (p k))
  unfold total
  rw [hs] at h
  exact h

@[simp] theorem planFree_times (c : Coefficient) (p : Plan A 1 1) :
    planFree (times c p) = planFree p := by
  simp [times, planFree_mix]

theorem planFree_rows : ∀ (n : ℕ) (p : Fin n → Plan A 1 1),
    planFree (rows n p) = ∑ j, planFree (p j)
  | 0, p => by simp [rows, planFree_mix]
  | n + 1, p => by
    rw [rows, planFree_parallel, planFree_rows n, Fin.sum_univ_castSucc]

theorem planFree_diagonal {I : Type} [Fintype I] (p : I → Plan A 1 1) :
    planFree (diagonal p) = ∑ j, planFree (p j) := by
  rw [diagonal, planFree_rows]
  exact (Fintype.equivFin I).symm.sum_comp (fun j => planFree (p j))

theorem planFree_mixing {I O : Type} [Fintype I] [Fintype O] (c : O → I → Coefficient) :
    planFree (mixing (A := A) c) ≤ Fintype.card O * Fintype.card I :=
  planFree_mix_le _

theorem planFree_entries {I O : Type} [Fintype I] [Fintype O] (p : O → I → Plan A 1 1) :
    planFree (entries p) ≤ Fintype.card O * (Fintype.card O * Fintype.card I) +
      ∑ b, ∑ a, planFree (p b a) + (Fintype.card O * Fintype.card I) * Fintype.card I := by
  classical
  unfold entries
  simp only [planFree_seq, planFree_diagonal]
  have h1 := planFree_mixing (A := A) (fun b (k : O × I) => if k.1 = b then ((1 : ℤ), 0) else (0, 0))
  have h2 := planFree_mixing (A := A) (fun (k : O × I) a => if k.2 = a then ((1 : ℤ), 0) else (0, 0))
  have hc : Fintype.card (O × I) = Fintype.card O * Fintype.card I := Fintype.card_prod _ _
  have h1' := h1.trans (le_of_eq (by rw [hc]) :
    Fintype.card O * Fintype.card (O × I) ≤ Fintype.card O * (Fintype.card O * Fintype.card I))
  have h2' := h2.trans (le_of_eq (by rw [hc]) :
    Fintype.card (O × I) * Fintype.card I ≤ (Fintype.card O * Fintype.card I) * Fintype.card I)
  have hs : ∑ j : O × I, planFree (p j.1 j.2) = ∑ b, ∑ a, planFree (p b a) :=
    Fintype.sum_prod_type _
  rw [hs]
  omega

/-- A bank side with free endpoint plans is free. -/
theorem planFree_side {L W : Type} [Fintype L] [Fintype W] [DecidableEq L]
    (active : Finset L) (p : L → Single A) (hp : ∀ v, planFree (p v) = 0) :
    planFree (side (W := W) active p) = 0 := by
  unfold side
  rw [planFree_diagonal]
  apply Finset.sum_eq_zero
  intro u _
  split
  · exact hp _
  · exact planFree_emptyPlan_one


/-! ## Rectangle plans and the pencil -/

section Pencil

variable {L W J F C : Type} [Fintype L] [Fintype W] [Fintype J] [Fintype F] [Fintype C]
  [DecidableEq L] [DecidableEq W]

omit [DecidableEq W] in
/-- **A free rectangle with free endpoint plans.** -/
theorem planFree_freePlan (r : FreeData A L J) (B : J → W → W → Coefficient)
    (hS : ∀ v, planFree (r.source v) = 0) (hT : ∀ w, planFree (r.target w) = 0)
    (hM : ∀ j w v, planFree (r.middle j w v) = 0) :
    planFree (r.plan B) ≤ 2 * Fintype.card (L × W) ^ 3 +
      (4 * Fintype.card J + 1) * Fintype.card (L × W) ^ 2 := by
  classical
  unfold FreeData.plan free
  simp only [planFree_seq, planFree_side _ _ hS, planFree_side _ _ hT, zero_add, add_zero]
  refine (planFree_entries _).trans ?_
  have hentry : ∀ b a : L × W, planFree (times r.weight
      (total fun j => times (B j b.2 a.2) (r.middle j b.1 a.1))) ≤ 4 * Fintype.card J + 1 := by
    intro b a
    rw [planFree_times]
    refine (planFree_total _).trans ?_
    simp only [planFree_times, hM, Finset.sum_const_zero, zero_add]
    omega
  have hsum : ∑ b : L × W, ∑ a : L × W, planFree (times r.weight
      (total fun j => times (B j b.2 a.2) (r.middle j b.1 a.1)))
      ≤ ∑ _b : L × W, ∑ _a : L × W, (4 * Fintype.card J + 1) :=
    Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun a _ => hentry b a
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  nlinarith

/-- A bound on one entry of a charged rectangle: `if c then times w p else emptyPlan`. -/
theorem planFree_ite_times (c : Prop) [Decidable c] (w : Coefficient) (p : Plan A 1 1)
    (hp : planFree p = 0) : planFree (if c then times w p else emptyPlan) = 0 := by
  split
  · rw [planFree_times, hp]
  · exact planFree_emptyPlan_one

/-- **A charged rectangle with free endpoint plans.** -/
theorem planFree_chargedPlan (r : ChargedData A L J) (B : J → W → W → Coefficient)
    (hI : ∀ j v, planFree (r.input j v) = 0) (hO : ∀ j w, planFree (r.output j w) = 0)
    (hC : ∀ j, planFree (r.common j) = 0) :
    planFree (r.plan B) ≤ Fintype.card J * (4 * Fintype.card (L × W) ^ 2 * Fintype.card W
      + 4 * Fintype.card (L × W) ^ 2) + Fintype.card (L × W) ^ 2 := by
  classical
  unfold ChargedData.plan
  refine (planFree_total _).trans ?_
  have hc : ∀ j, planFree (charged r.sources r.destinations r.weight (B j) (r.input j)
      (r.output j) (r.common j)) ≤ 4 * Fintype.card (L × W) ^ 2 * Fintype.card W := by
    intro j
    unfold charged
    simp only [planFree_seq, planFree_diagonal, hC, Finset.sum_const_zero, zero_add]
    have h1 := planFree_entries (A := A) (O := L × W) (I := W)
      (fun w k => if w.1 ∈ r.destinations ∧ w.2 = k then times r.weight (r.output j w.1)
        else emptyPlan)
    have h2 := planFree_entries (A := A) (O := W) (I := L × W)
      (fun k v => if v.1 ∈ r.sources then times (B j k v.2) (r.input j v.1) else emptyPlan)
    simp only [planFree_ite_times _ _ _ (hO j _), planFree_ite_times _ _ _ (hI j _),
      Finset.sum_const_zero, add_zero] at h1 h2
    have hRW : Fintype.card (L × W) * Fintype.card W ^ 2
        ≤ Fintype.card (L × W) ^ 2 * Fintype.card W := by
      rcases Nat.eq_zero_or_pos (Fintype.card L) with h | h
      · rw [Fintype.card_prod, h]; simp
      · have hW : Fintype.card W ≤ Fintype.card (L × W) := by
          rw [Fintype.card_prod]; exact Nat.le_mul_of_pos_left _ h
        have := Nat.mul_le_mul_left (Fintype.card (L × W) * Fintype.card W) hW
        nlinarith
    show planFree (entries (A := A) (O := L × W) (I := W) (fun (w : L × W) (k : W) =>
        if w.1 ∈ r.destinations ∧ w.2 = k then times r.weight (r.output j w.1) else emptyPlan)) +
      planFree (entries (A := A) (O := W) (I := L × W) (fun (k : W) (v : L × W) =>
        if v.1 ∈ r.sources then times (B j k v.2) (r.input j v.1) else emptyPlan)) ≤ _
    nlinarith
  have hsum : ∑ j, planFree (charged r.sources r.destinations r.weight (B j) (r.input j)
      (r.output j) (r.common j)) ≤ Fintype.card J * (4 * Fintype.card (L × W) ^ 2 * Fintype.card W) := by
    calc _ ≤ ∑ _j : J, 4 * Fintype.card (L × W) ^ 2 * Fintype.card W := Finset.sum_le_sum fun j _ => hc j
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  nlinarith



/-- The arithmetic of the pencil bound. -/
lemma pencil_arith {R Wc Jc nF nC pA1 pA2 pCP pTF pTC sF sC : ℕ}
    (hA1 : pA1 ≤ pCP + pA2 + 2 * R * R + 2 * R * R) (hA2 : pA2 ≤ pTF + pTC + 2 * R * R + 2 * R * R)
    (hCP : pCP ≤ R * R) (hTF : pTF ≤ sF + nF * (2 * R * R + 2 * R * R) + R * R)
    (hTC : pTC ≤ sC + nC * (2 * R * R + 2 * R * R) + R * R)
    (hF : sF ≤ nF * (2 * R ^ 3 + (4 * Jc + 1) * R ^ 2))
    (hC : sC ≤ nC * (Jc * (4 * R ^ 2 * Wc + 4 * R ^ 2) + R ^ 2)) (hRW : R ^ 2 * Wc ≤ R ^ 3) :
    pA1 ≤ 20 * (nF + nC + 1) * (Jc + 1) * R ^ 3 := by
  have hR23 : R ^ 2 ≤ R ^ 3 := by
    rcases Nat.eq_zero_or_pos R with h0 | hpos
    · subst h0; simp
    · calc R ^ 2 = R ^ 2 * 1 := by ring
        _ ≤ R ^ 2 * R := Nat.mul_le_mul_left _ hpos
        _ = R ^ 3 := by ring
  have hsq : R * R ≤ R ^ 3 := by nlinarith
  have e1 : nF * (2 * R ^ 3 + (4 * Jc + 1) * R ^ 2) ≤ nF * ((4 * Jc + 3) * R ^ 3) := by
    apply Nat.mul_le_mul_left
    nlinarith
  have e2 : nC * (Jc * (4 * R ^ 2 * Wc + 4 * R ^ 2) + R ^ 2) ≤ nC * ((8 * Jc + 1) * R ^ 3) := by
    apply Nat.mul_le_mul_left
    have : Jc * (R ^ 2 * Wc) ≤ Jc * R ^ 3 := Nat.mul_le_mul_left _ hRW
    have : Jc * R ^ 2 ≤ Jc * R ^ 3 := Nat.mul_le_mul_left _ hR23
    nlinarith
  have e3 : nF * (2 * R * R + 2 * R * R) ≤ nF * (4 * R ^ 3) := by
    apply Nat.mul_le_mul_left; nlinarith
  have e4 : nC * (2 * R * R + 2 * R * R) ≤ nC * (4 * R ^ 3) := by
    apply Nat.mul_le_mul_left; nlinarith
  have hfin : (nF * ((4 * Jc + 3) * R ^ 3) + nF * (4 * R ^ 3)) + (nC * ((8 * Jc + 1) * R ^ 3)
      + nC * (4 * R ^ 3)) + 13 * R ^ 3 ≤ 20 * (nF + nC + 1) * (Jc + 1) * R ^ 3 := by
    ring_nf
    nlinarith [Nat.zero_le (nF * Jc * R ^ 3), Nat.zero_le (nC * Jc * R ^ 3), Nat.zero_le (Jc * R ^ 3),
      Nat.zero_le (nF * R ^ 3), Nat.zero_le (nC * R ^ 3), Nat.zero_le (R ^ 3)]
  nlinarith

/-- **The pencil with free endpoint plans.** -/
theorem planFree_pencil (Frees : F → FreeData A L J) (Charged : C → ChargedData A L J)
    (B₀ : W → W → Coefficient) (B : J → W → W → Coefficient)
    (hfS : ∀ r v, planFree ((Frees r).source v) = 0) (hfT : ∀ r w, planFree ((Frees r).target w) = 0)
    (hfM : ∀ r j w v, planFree ((Frees r).middle j w v) = 0)
    (hcI : ∀ r j v, planFree ((Charged r).input j v) = 0)
    (hcO : ∀ r j w, planFree ((Charged r).output j w) = 0)
    (hcC : ∀ r j, planFree ((Charged r).common j) = 0) :
    planFree (pencil Frees Charged B₀ B) ≤ 20 * (Fintype.card F + Fintype.card C + 1) *
      (Fintype.card J + 1) * Fintype.card (L × W) ^ 3 := by
  classical
  unfold pencil
  have hA1 := planFree_addPlan (constantPart (A := A) (L := L) B₀)
    (addPlan (total fun r => (Frees r).plan B) (total fun r => (Charged r).plan B))
  have hA2 := planFree_addPlan (total fun r => (Frees r).plan B) (total fun r => (Charged r).plan B)
  have hCP : planFree (constantPart (A := A) (L := L) B₀) ≤
      Fintype.card (L × W) * Fintype.card (L × W) := planFree_mixing _
  have hTF := planFree_total (fun r => (Frees r).plan B)
  have hTC := planFree_total (fun r => (Charged r).plan B)
  have hF : ∑ r, planFree ((Frees r).plan B) ≤ Fintype.card F *
      (2 * Fintype.card (L × W) ^ 3 + (4 * Fintype.card J + 1) * Fintype.card (L × W) ^ 2) := by
    calc _ ≤ ∑ _r : F, (2 * Fintype.card (L × W) ^ 3 +
          (4 * Fintype.card J + 1) * Fintype.card (L × W) ^ 2) :=
          Finset.sum_le_sum fun r _ => planFree_freePlan (Frees r) B (hfS r) (hfT r) (hfM r)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hC : ∑ r, planFree ((Charged r).plan B) ≤ Fintype.card C *
      (Fintype.card J * (4 * Fintype.card (L × W) ^ 2 * Fintype.card W
        + 4 * Fintype.card (L × W) ^ 2) + Fintype.card (L × W) ^ 2) := by
    calc _ ≤ ∑ _r : C, (Fintype.card J * (4 * Fintype.card (L × W) ^ 2 * Fintype.card W
          + 4 * Fintype.card (L × W) ^ 2) + Fintype.card (L × W) ^ 2) :=
          Finset.sum_le_sum fun r _ => planFree_chargedPlan (Charged r) B (hcI r) (hcO r) (hcC r)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  -- numeric part
  have hRW : Fintype.card (L × W) ^ 2 * Fintype.card W ≤ Fintype.card (L × W) ^ 3 := by
    rw [Fintype.card_prod]
    rcases Nat.eq_zero_or_pos (Fintype.card L) with h0 | hpos
    · rw [h0]; simp
    · have hW : Fintype.card W ≤ Fintype.card L * Fintype.card W := Nat.le_mul_of_pos_left _ hpos
      calc (Fintype.card L * Fintype.card W) ^ 2 * Fintype.card W
          ≤ (Fintype.card L * Fintype.card W) ^ 2 * (Fintype.card L * Fintype.card W) :=
            Nat.mul_le_mul_left _ hW
        _ = _ := by ring
  exact pencil_arith hA1 hA2 hCP hTF hTC hF hC hRW

end Pencil

/-! ## The free pencil of our template -/

/-- **The free pencil spends at most `20 (|free| + |charged| + 1)(m + 2) R³` gates per address
outside calls.** -/
theorem planFree_geometricPencilF {L b : ℕ} (S : System L b) (m : ℕ) {W : Type} [Fintype W]
    [DecidableEq W] (B₀ : W → W → Coefficient) (B : Fin (m + 1) → W → W → Coefficient) :
    planFree (geometricPencilF S m B₀ B) ≤ 20 * (Fintype.card (Free L b) + Fintype.card (Paid L b) + 1)
      * (m + 2) * Fintype.card (Label L b × W) ^ 3 := by
  have h := planFree_pencil (A := Charged.Axes (m := m) S.geometry) (L := Label L b) (W := W)
    (J := Fin (m + 1)) (freePlansF S m) (chargedPlansF S m) B₀ B
    (fun r v => freeGeometryF_source_free _ _ _ _ v)
    (fun r w => freeGeometryF_target_free _ _ _ _ w)
    (fun r j w v => freeGeometryF_middle_free _ _ _ _ j w v)
    (fun r j v => Charged.plansF_collect_free _ m j v)
    (fun r j w => Charged.plansF_scatter_free _ m j w)
    (fun r j => Charged.plansF_middle_free _ m)
  simpa [Fintype.card_fin, geometricPencilF] using h

/-- Free bit rectangles: at most `((b+1) 2^b)^L`. -/
theorem card_free_le (L b : ℕ) : Fintype.card (Free L b) ≤ ((b + 1) * 2 ^ b) ^ L := by
  classical
  have h1 : Fintype.card (Free L b) ≤ Fintype.card (OAI.LinearAlgebra.FiniteFourier.BitRectangle L b) :=
    Fintype.card_subtype_le _
  have hrec : ∀ c : Option (Fin b),
      Fintype.card (OAI.LinearAlgebra.FiniteFourier.BitRecord b c) ≤ 2 ^ b := by
    intro c
    cases c with
    | none => simp [OAI.LinearAlgebra.FiniteFourier.BitRecord, OAI.LinearAlgebra.FiniteFourier.BitLetter]
    | some i =>
      simp only [OAI.LinearAlgebra.FiniteFourier.BitRecord, Fintype.card_prod, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin]
      calc 2 ^ (i : ℕ) * 2 = 2 ^ ((i : ℕ) + 1) := by ring
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) i.isLt
  have h2 : Fintype.card (OAI.LinearAlgebra.FiniteFourier.BitRectangle L b) ≤ ((b + 1) * 2 ^ b) ^ L := by
    simp only [OAI.LinearAlgebra.FiniteFourier.BitRectangle, Fintype.card_sigma, Fintype.card_pi]
    calc ∑ c : Fin L → Option (Fin b), ∏ i, Fintype.card (OAI.LinearAlgebra.FiniteFourier.BitRecord b (c i))
        ≤ ∑ _c : Fin L → Option (Fin b), ∏ _i : Fin L, 2 ^ b :=
          Finset.sum_le_sum fun c _ => Finset.prod_le_prod fun i _ => hrec (c i)
      _ = ((b + 1) * 2 ^ b) ^ L := by
          simp [Finset.prod_const, Finset.card_univ, Fintype.card_option, mul_pow]
  exact h1.trans h2

/-- Charged rectangles: at most `2^L (2^b)^{L/2}`. -/
theorem card_paid_le (L b : ℕ) : Fintype.card (Paid L b) ≤ 2 ^ L * (2 ^ b) ^ (L / 2) :=
  OAI.LinearAlgebra.FiniteFourier.card_chargedRectangle_le L b (L / 2)

end Circ

end FTPaper
