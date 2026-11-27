import FTPaper.Claim2.Sparse

/-!
# Plans that act address by address (paper: Section 9, use in the template)

A plan `ActsBy test p F` if at every address `y` it maps the column of a bank at `y` by the
linear map `F κ`, where `κ = ∑_t test (y t)` is the signature of `y`. Mixes act by their
matrix, row scalings by a diagonal, and sequential composition composes. The Horner plan
with constant coefficients acts by `∑_t c_t (F κ)^t`.

Also: sparse costs of the basic combinators.
-/

open OAI.Computability.NearSquareRoot OAI.Computability.NearSquareRoot.KernelPass
open Matrix Finset

namespace FTPaper

namespace QPlan

variable {A h : ℕ}

/-- The column of a bank at an address. -/
def colAt {n : ℕ} (x : Bank A h n) (y : Addr A h) : Fin n → ℚ := fun a => x a y

lemma colAt_append {n n' : ℕ} (x : Bank A h n) (x' : Bank A h n') (y : Addr A h) :
    colAt (Fin.append x x') y = Fin.append (colAt x y) (colAt x' y) := by
  funext r
  refine Fin.addCases (fun l => ?_) (fun l => ?_) r <;> simp [colAt]

/-- `p` acts at every address `y` by `F (signature of y)`. -/
def ActsBy {i o q : ℕ} (test : Column A → Fin q → ZMod 2) (p : QPlan A i o)
    (F : (Fin q → ZMod 2) → (Fin i → ℚ) →ₗ[ℚ] (Fin o → ℚ)) : Prop :=
  ∀ h (x : Bank A h i) (y : Addr A h), colAt (p.applyAt h x) y = F (∑ t, test (y t)) (colAt x y)

variable {q : ℕ} {test : Column A → Fin q → ZMod 2}

theorem actsBy_mix {i o : ℕ} (c : Fin o → Fin i → ℚ) :
    ActsBy test (QPlan.mix (A := A) c) (fun _ => Matrix.mulVecLin (Matrix.of c)) := by
  intro h x y
  funext b
  simp [colAt, applyAt_mix, Matrix.mulVec, dotProduct]

theorem actsBy_scaleRows {n : ℕ} (t : Fin n → (Fin q → ZMod 2) → ℚ) :
    ActsBy test (QPlan.scaleRows (A := A) q test t)
      (fun κ => Matrix.mulVecLin (Matrix.diagonal fun b => t b κ)) := by
  intro h x y
  funext b
  simp [colAt, applyAt_scaleRows, Matrix.mulVec_diagonal]

theorem actsBy_seq {i j o : ℕ} {p : QPlan A j o} {p' : QPlan A i j}
    {F : (Fin q → ZMod 2) → (Fin j → ℚ) →ₗ[ℚ] (Fin o → ℚ)}
    {G : (Fin q → ZMod 2) → (Fin i → ℚ) →ₗ[ℚ] (Fin j → ℚ)}
    (hp : ActsBy test p F) (hp' : ActsBy test p' G) :
    ActsBy test (p.seq p') (fun κ => F κ ∘ₗ G κ) := by
  intro h x y
  rw [applyAt_seq, hp, hp']
  rfl

theorem actsBy_congr {i o : ℕ} {p : QPlan A i o}
    {F G : (Fin q → ZMod 2) → (Fin i → ℚ) →ₗ[ℚ] (Fin o → ℚ)} (hp : ActsBy test p F)
    (hFG : ∀ κ v, F κ v = G κ v) : ActsBy test p G := by
  intro h x y
  rw [hp, hFG]

/-- The Horner plan with constant coefficients. -/
theorem actsBy_horner {N : ℕ} {stage : QPlan A N N}
    {F : (Fin q → ZMod 2) → Module.End ℚ (Fin N → ℚ)} (hs : ActsBy test stage F)
    (c : ℕ → ℚ) (n : ℕ) :
    ActsBy test (horner stage (fun t _ => c t) n)
      (fun κ => ∑ t ∈ Finset.range (n + 1), c t • F κ ^ t) := by
  intro h x y
  have key : ∀ (c : ℕ → ℚ) (n : ℕ), ∃ V : Bank A h N,
      (hornerPair stage (fun t _ => c t) n).applyAt h x = Fin.append V x ∧
      ∀ y, colAt V y = (∑ t ∈ Finset.range (n + 1), c t • F (∑ t, test (y t)) ^ t) (colAt x y) := by
    intro c n
    induction n generalizing c with
    | zero =>
      refine ⟨fun b z => c 0 * x b z, ?_, fun y => ?_⟩
      · rw [hornerPair, applyAt_fork, applyAt_diagMix, applyAt_route]
        rfl
      · funext b
        simp [colAt]
    | succ n ih =>
      obtain ⟨V, hV, hVy⟩ := ih (fun t => c (t + 1))
      refine ⟨fun b z => stage.applyAt h V b z + c 0 * x b z, ?_, fun y => ?_⟩
      · rw [hornerPair]
        rw [applyAt_seq]
        rw [show hornerPair stage (fun t => (fun t _ => c t) (t + 1)) n
          = hornerPair stage (fun t (_ : Fin N) => c (t + 1)) n from rfl, hV,
          applyAt_hornerStep]
      · have hcol : colAt (fun b z => stage.applyAt h V b z + c 0 * x b z) y
            = colAt (stage.applyAt h V) y + c 0 • colAt x y := by
          funext b; simp [colAt]
        rw [hcol, hs, hVy]
        set G := F (∑ t, test (y t))
        have hmat : (∑ t ∈ Finset.range (n + 1 + 1), c t • G ^ t)
            = G * (∑ t ∈ Finset.range (n + 1), c (t + 1) • G ^ t) + c 0 • 1 := by
          rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero]
          congr 1
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [mul_smul_comm, ← pow_succ']
        rw [hmat, LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply,
          Module.End.one_apply]
  obtain ⟨V, hV, hVy⟩ := key c n
  rw [horner, applyAt_seq, hV, applyAt_route]
  have : Fin.append V x ∘ Fin.castAdd N = V := by
    funext b; simp
  rw [this, hVy]

/-! ## Sparse costs of the basic combinators -/

open Circ

lemma rowCost_le_of {i o k : ℕ} {c : Fin o → Fin i → ℚ}
    (hc : ∀ b, (univ.filter fun a => c b a ≠ 0).card ≤ k + 1) : rowCost c ≤ o * k := by
  unfold rowCost
  calc ∑ b, ((univ.filter fun a => c b a ≠ 0).card - 1) ≤ ∑ _b : Fin o, k :=
        Finset.sum_le_sum fun b _ => by have := hc b; omega
    _ = o * k := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

@[simp] lemma qsparse_seq {i j o : ℕ} (p : QPlan A j o) (p' : QPlan A i j) :
    qsparse (p.seq p') = qsparse p + qsparse p' := rfl

@[simp] lemma qsparse_parallel {i j o u : ℕ} (p : QPlan A i o) (p' : QPlan A j u) :
    qsparse (p.parallel p') = qsparse p + qsparse p' := rfl

@[simp] lemma qsparse_scaleRows {n : ℕ} (t : Fin n → (Fin q → ZMod 2) → ℚ) :
    qsparse (QPlan.scaleRows (A := A) q test t) = 0 := rfl

@[simp] lemma qsparse_embed {i o : ℕ} (p : Plan A i o) : qsparse (QPlan.embed p) = planSparse p := rfl

lemma qsparse_mix {i o : ℕ} (c : Fin o → Fin i → ℚ) : qsparse (QPlan.mix (A := A) c) = rowCost c :=
  rfl

@[simp] lemma qsparse_route {i o : ℕ} (r : Fin o → Fin i) : qsparse (route (A := A) r) = 0 := by
  rw [route, qsparse_mix]
  have := rowCost_le_of (k := 0) (c := fun b a => if a = r b then (1 : ℚ) else 0) (fun b => by
    calc (univ.filter fun a => (if a = r b then (1 : ℚ) else 0) ≠ 0).card ≤ ({r b} : Finset _).card :=
          card_le_card fun a ha => by
            simp only [mem_filter, mem_univ, true_and, ne_eq, ite_eq_right_iff, one_ne_zero,
              imp_false, not_not] at ha
            simp [ha]
      _ = 0 + 1 := by simp)
  omega

@[simp] lemma qsparse_fork {i o u : ℕ} (p : QPlan A i o) (p' : QPlan A i u) :
    qsparse (p.fork p') = qsparse p + qsparse p' := by
  simp [fork]

@[simp] lemma qsparse_diagMix {N : ℕ} (c : Fin N → ℚ) : qsparse (diagMix (A := A) c) = 0 := by
  rw [diagMix, qsparse_mix]
  have := rowCost_le_of (k := 0) (c := fun b a => if a = b then c b else 0) (fun b => by
    calc (univ.filter fun a => (if a = b then c b else 0) ≠ 0).card ≤ ({b} : Finset _).card :=
          card_le_card fun a ha => by
            simp only [mem_filter, mem_univ, true_and, ne_eq, ite_eq_right_iff, not_forall] at ha
            simp [ha.1]
      _ = 0 + 1 := by simp)
  omega

lemma qsparse_combine_le {W : ℕ} (u v : Fin W → ℚ) : qsparse (combine (A := A) u v) ≤ W := by
  rw [combine, qsparse_mix]
  have := rowCost_le_of (k := 1) (c := fun b => Fin.append (fun a => if a = b then u b else 0)
    (fun a => if a = b then v b else 0)) (fun b => by
    calc (univ.filter fun a => Fin.append (fun a => if a = b then u b else 0)
            (fun a => if a = b then v b else 0) a ≠ 0).card
          ≤ ({Fin.castAdd W b, Fin.natAdd W b} : Finset _).card := card_le_card fun a ha => by
            simp only [mem_filter, mem_univ, true_and] at ha
            refine Fin.addCases (fun l hl => ?_) (fun l hl => ?_) a ha
            · simp only [Fin.append_left, ne_eq, ite_eq_right_iff, not_forall] at hl
              simp [hl.1]
            · simp only [Fin.append_right, ne_eq, ite_eq_right_iff, not_forall] at hl
              simp [hl.1]
      _ ≤ 1 + 1 := card_le_two)
  omega

lemma qsparse_hornerStep_le {N : ℕ} (stage : QPlan A N N) (c : Fin N → ℚ) :
    qsparse (hornerStep stage c) ≤ qsparse stage + N := by
  have := qsparse_combine_le (A := A) (fun _ : Fin N => (1 : ℚ)) c
  simp only [hornerStep, qsparse_seq, qsparse_fork, qsparse_parallel, qsparse_route]
  omega

lemma qsparse_hornerPair_le {N : ℕ} (stage : QPlan A N N) (c : ℕ → Fin N → ℚ) (n : ℕ) :
    qsparse (hornerPair stage c n) ≤ n * (qsparse stage + N) := by
  induction n generalizing c with
  | zero => simp [hornerPair]
  | succ n ih =>
    have h1 := qsparse_hornerStep_le stage (c 0)
    have h2 := ih (fun t => c (t + 1))
    simp only [hornerPair, qsparse_seq]
    rw [Nat.succ_mul]
    omega

lemma qsparse_horner_le {N : ℕ} (stage : QPlan A N N) (c : ℕ → Fin N → ℚ) (n : ℕ) :
    qsparse (horner stage c n) ≤ n * (qsparse stage + N) := by
  have := qsparse_hornerPair_le stage c n
  simp only [horner, qsparse_seq, qsparse_route, zero_add]
  exact this


end QPlan

end FTPaper
