import FTPaper.QFeedback
import OAI.LinearAlgebra.FiniteFourier.PrimeTemplatePass
import OAI.LinearAlgebra.FiniteFourier.PrimeTemplateReindex

/-!
# From plans to circuits

Every rational plan compiles into OpenAI's circuit-level program model `PrimeTemplateProgram`
(`OAI/LinearAlgebra/FiniteFourier/PrimeTemplate.lean`), over any field of characteristic `0`.

A `KernelPass` axis carries two bits per column, so `2h` bits at child width `h`. We split each
axis `a` into the half-axes `(a,0)` and `(a,1)`, of `h` bits each. A child call is `2^{-h}`
times the product of two half-axis calls (`child_eq`). Hence a plan with `σ` child calls is a
program with `2σ` calls on `h`-digit axes over `2A` half-axes. That holds at **every** `h ≥ 1`,
which is what OpenAI's batch recursion needs.
-/

open OAI.LinearAlgebra.FiniteFourier
open OAI.Computability.NearSquareRoot
open Matrix Finset

namespace FTPaper

namespace Circ

open KernelPass

variable {K : Type} [Field K] [CharZero K]

/-! ## Half-axis calls -/

/-- Agreement of two addresses away from one half-axis. -/
def AgreeOff {A h : ℕ} (p : Fin A × Fin 2) (y x : Addr A h) : Prop :=
  ∀ c b j, (b, j) ≠ p → y c b j = x c b j

/-- One unnormalized half-axis call on a single row. -/
noncomputable def halfMat {A h : ℕ} (p : Fin A × Fin 2) :
    Matrix (Fin 1 × Addr A h) (Fin 1 × Addr A h) K := by
  classical
  exact fun y x => if AgreeOff p y.2 x.2 then
    ∏ c, (-1 : K) ^ ((y.2 c p.1 p.2).val * (x.2 c p.1 p.2).val) else 0

/-- The other half-axes of an address. -/
abbrev Rest (A h : ℕ) (p : Fin A × Fin 2) := Fin h → {q : Fin A × Fin 2 // q ≠ p} → ZMod 2

/-- Split a one-row address into one half-axis and the rest. -/
def halfSplit {A h : ℕ} (p : Fin A × Fin 2) : Fin 1 × Addr A h ≃ (Fin h → Fin 2) × Rest A h p where
  toFun y := (fun c => y.2 c p.1 p.2, fun c q => y.2 c q.1.1 q.1.2)
  invFun ut := (0, fun c b j => if hq : (b, j) = p then ut.1 c else ut.2 c ⟨(b, j), hq⟩)
  left_inv y := by
    obtain ⟨i, y⟩ := y
    refine Prod.ext (Subsingleton.elim _ _) ?_
    funext c b j
    by_cases hq : (b, j) = p
    · subst hq; simp
    · simp [hq]
  right_inv ut := by
    obtain ⟨u, t⟩ := ut
    refine Prod.ext ?_ ?_
    · funext c; simp
    · funext c q
      obtain ⟨q, hq⟩ := q
      simp [hq]

lemma card_rest (A h : ℕ) (p : Fin A × Fin 2) :
    Fintype.card (Rest A h p) = 2 ^ ((2 * A - 1) * h) := by
  have hq : Fintype.card {q : Fin A × Fin 2 // q ≠ p} = 2 * A - 1 := by
    simp [Fintype.card_prod, mul_comm]
  simp only [Rest, Fintype.card_fun, hq, ZMod.card, Fintype.card_fin]
  rw [← pow_mul, mul_comm]

omit [CharZero K] in
lemma halfMat_eq {A h : ℕ} (p : Fin A × Fin 2) :
    halfMat (K := K) (h := h) p = Matrix.reindex (halfSplit p).symm (halfSplit p).symm
      (Matrix.blockDiagonal fun _ : Rest A h p => primeTransform 2 h (-1 : K)) := by
  classical
  ext y x
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.blockDiagonal_apply]
  simp only [halfMat, halfSplit, Equiv.coe_fn_mk]
  have hiff : AgreeOff p y.2 x.2 ↔
      ((fun c (q : {q : Fin A × Fin 2 // q ≠ p}) => y.2 c q.1.1 q.1.2) =
        fun c q => x.2 c q.1.1 q.1.2) := by
    constructor
    · intro hA
      funext c q
      exact hA c q.1.1 q.1.2 q.2
    · intro hE c b j hbj
      exact congrFun (congrFun hE c) ⟨(b, j), hbj⟩
  by_cases h1 : AgreeOff p y.2 x.2
  · have h2 := hiff.mp h1
    simp only [h1, h2, ite_true]
    rfl
  · have h2 : ¬ _ := fun hE => h1 (hiff.mpr hE)
    simp [h1, h2]

omit [CharZero K] in
/-- **A half-axis call is one call of OpenAI's program model.** -/
theorem program_halfMat {A h : ℕ} (p : Fin A × Fin 2) :
    PrimeTemplateProgram 2 h (2 ^ ((2 * A - 1) * h)) (-1 : K) (halfMat (h := h) p) 0 1 := by
  rw [halfMat_eq]
  exact (PrimeTemplateProgram.axis_blockDiagonal (Rest A h p) (card_rest A h p)).reindex _ _

/-! ## A child call is two half-axis calls -/

lemma zmod2_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by
  revert t; decide

/-- The normalized two-bit entry over `K`. -/
lemma pairEntry_cast (u v : Fin 2 → ZMod 2) :
    ((pairEntry u v : ℚ) : K) =
      (1 / 2) * ((-1 : K) ^ ((u 0).val * (v 0).val) * (-1 : K) ^ ((u 1).val * (v 1).val)) := by
  rcases zmod2_cases (u 0) with h0 | h0 <;> rcases zmod2_cases (u 1) with h1 | h1 <;>
    rcases zmod2_cases (v 0) with h2 | h2 <;> rcases zmod2_cases (v 1) with h3 | h3 <;>
    simp (config := { decide := true }) [pairEntry, h0, h1, h2, h3, ZMod.val_one]

omit [CharZero K] in
lemma childEntry_cast {A : ℕ} (a : Fin A) (y x : Column A) :
    ((childEntry a y x : ℚ) : K) =
      if (∀ b ≠ a, x b = y b) then ((pairEntry (y a) (x a) : ℚ) : K) else 0 := by
  unfold childEntry
  split_ifs <;> simp

/-- **A child call is `2^{-h}` times two half-axis calls.** -/
theorem child_eq {A h : ℕ} (a : Fin A) :
    ((Plan.child (A := A) a).eval h).map (Rat.castHom K)
      = ((1 / 2 : K) ^ h) • (halfMat (a, 0) * halfMat (h := h) (a, 1)) := by
  classical
  ext ⟨i, y⟩ ⟨j, x⟩
  change (((∏ c, childEntry a (y c) (x c) : ℚ)) : K) =
    ((1 / 2 : K) ^ h) * ∑ z, halfMat (K := K) (a, 0) (i, y) z * halfMat (a, 1) z (j, x)
  rw [Rat.cast_prod]
  -- the left side
  have hL : (∏ c, ((childEntry a (y c) (x c) : ℚ) : K)) =
      if (∀ c, ∀ b ≠ a, x c b = y c b) then
        ∏ c, ((1 / 2 : K) * ((-1 : K) ^ ((y c a 0).val * (x c a 0).val) *
          (-1 : K) ^ ((y c a 1).val * (x c a 1).val))) else 0 := by
    simp only [childEntry_cast]
    rw [Finset.prod_ite_zero]
    simp only [Finset.mem_univ, true_implies, pairEntry_cast]
  rw [hL]
  -- the unique middle address
  set z₀ : Fin 1 × Addr A h := (0, fun c b k => if (b, k) = (a, 0) then x c b k else y c b k)
    with hz₀
  have h01 : ((a, 0) : Fin A × Fin 2) ≠ (a, 1) := by simp
  have hsum : ∑ z : Fin 1 × Addr A h, halfMat (K := K) (a, 0) (i, y) z * halfMat (a, 1) z (j, x)
      = halfMat (K := K) (a, 0) (i, y) z₀ * halfMat (a, 1) z₀ (j, x) := by
    apply Finset.sum_eq_single z₀
    · intro z _ hz
      by_cases h1 : AgreeOff (a, 0) y z.2
      · by_cases h2 : AgreeOff (a, 1) z.2 x
        · exfalso
          apply hz
          refine Prod.ext (Subsingleton.elim _ _) ?_
          funext c b k
          simp only [hz₀]
          by_cases hbk : (b, k) = (a, 0)
          · rw [ite_eq_left hbk]
            have := h2 c b k (by rw [hbk]; exact h01)
            exact this
          · rw [ite_eq_right hbk]
            exact (h1 c b k hbk).symm
        · simp [halfMat, h2]
      · simp [halfMat, h1]
    · simp
  rw [hsum]
  -- evaluate the two factors
  have hA0 : AgreeOff (a, 0) y z₀.2 := by
    intro c b k hbk
    simp only [hz₀, ite_eq_right hbk]
  have hagree : AgreeOff (a, 1) z₀.2 x ↔ ∀ c, ∀ b ≠ a, x c b = y c b := by
    constructor
    · intro hA c b hb
      funext k
      have := hA c b k (by intro e; exact hb (congrArg Prod.fst e))
      simp only [hz₀] at this
      rw [ite_eq_right (by intro e; exact hb (congrArg Prod.fst e))] at this
      exact this.symm
    · intro hA c b k hbk
      simp only [hz₀]
      by_cases e : (b, k) = (a, 0)
      · rw [ite_eq_left e]
      · rw [ite_eq_right e]
        by_cases hb : b = a
        · subst hb
          exfalso
          rcases (show k = 0 ∨ k = 1 by fin_cases k <;> simp) with hk | hk
          · exact e (by rw [hk])
          · exact hbk (by rw [hk])
        · exact (congrFun (hA c b hb) k).symm
  have hv0 : ∀ c, z₀.2 c a 0 = x c a 0 := fun c => by simp [hz₀]
  have hv1 : ∀ c, z₀.2 c a 1 = y c a 1 := fun c => by
    simp only [hz₀]; rw [ite_eq_right (by simp)]
  by_cases hX : ∀ c, ∀ b ≠ a, x c b = y c b
  · rw [ite_eq_left hX]
    simp only [halfMat, ite_eq_left hA0, ite_eq_left (hagree.mpr hX), hv0, hv1]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  · rw [ite_eq_right hX]
    simp [halfMat, show ¬ AgreeOff (a, 1) z₀.2 x from fun h => hX (hagree.mp h)]


/-! ## Free pieces: wiring, diagonals, dense mixes -/

omit [CharZero K] in
theorem realizable_one (J : Type) [DecidableEq J] : RealizableAtMost (1 : Matrix J J K) 0 := by
  refine ⟨0, le_rfl, ⟨.nil, fun i => .scaled 1 (.inl i)⟩, ?_⟩
  ext i j
  simp [Circuit.matrix, Circuit.eval, Readout.eval, Matrix.one_apply, Pi.single_apply]

omit [CharZero K] in
theorem realizable_diagonal {J : Type} [DecidableEq J] (d : J → K) :
    RealizableAtMost (Matrix.diagonal d) 0 := by
  refine ⟨0, le_rfl, ⟨.nil, fun i => .scaled (d i) (.inl i)⟩, ?_⟩
  ext i j
  by_cases h : i = j <;> simp [Circuit.matrix, Circuit.eval, Readout.eval, h]

omit [CharZero K] in
theorem realizable_mono {I O : Type} {M : Matrix O I K} {s t : ℕ}
    (h : RealizableAtMost M s) (hst : s ≤ t) : RealizableAtMost M t := by
  obtain ⟨r, hr, p, hp⟩ := h
  exact ⟨r, hr.trans hst, p, hp⟩

omit [CharZero K] in
theorem program_cast {ℓ f F : ℕ} {ζ : K} {I O : Type} {M : Matrix O I K} {c c' s s' : ℕ}
    (hp : PrimeTemplateProgram ℓ f F ζ M c s) (hc : c = c') (hs : s = s') :
    PrimeTemplateProgram ℓ f F ζ M c' s' := by
  subst hc; subst hs; exact hp

lemma card_addr (A h : ℕ) : Fintype.card (Addr A h) = 2 ^ (2 * A * h) := by
  simp only [Addr, Column, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [← pow_mul, ← pow_mul]
  ring_nf

omit [CharZero K] in
/-- A dense row mixing at every address. -/
theorem program_mixing {A h i o : ℕ} (C : Matrix (Fin o) (Fin i) K) :
    PrimeTemplateProgram 2 h (2 ^ ((2 * A - 1) * h)) (-1 : K)
      (Matrix.blockDiagonal fun _ : Addr A h => C) (o * i * 2 ^ (2 * A * h)) 0 := by
  classical
  refine .localCircuit (realizable_mono ((realizableAtMost_card_mul_card C).blockDiagonal (Addr A h)) ?_)
  rw [card_addr, Fintype.card_fin, Fintype.card_fin, mul_comm]

/-! ## Direct sums -/

/-- `Fin (o+u) × X` as a sum of two banks. -/
def sumBank (o u : ℕ) (X : Type) : (Fin o × X) ⊕ (Fin u × X) ≃ Fin (o + u) × X :=
  (Equiv.sumProdDistrib (Fin o) (Fin u) X).symm.trans (Equiv.prodCongr finSumFinEquiv (Equiv.refl X))

theorem map_directSum {i j o u : ℕ} {X : Type} (M : Matrix (Fin o × X) (Fin i × X) ℚ)
    (N : Matrix (Fin u × X) (Fin j × X) ℚ) :
    (directSum M N).map (Rat.castHom K) =
      Matrix.reindex (sumBank o u X) (sumBank i j X)
        (Matrix.fromBlocks (M.map (Rat.castHom K)) 0 0 (N.map (Rat.castHom K))) := by
  ext ⟨b, y⟩ ⟨a, x⟩
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
  refine Fin.addCases (fun l => ?_) (fun r => ?_) b <;>
    refine Fin.addCases (fun k => ?_) (fun k => ?_) a <;>
    simp [directSum, sumBank, Matrix.fromBlocks, Equiv.sumProdDistrib]

omit [CharZero K] in
/-- **Running two programs on separate banks.** -/
theorem program_directSum {ℓ f F : ℕ} {ζ : K} {i j o u : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    {M : Matrix (Fin o × X) (Fin i × X) K} {N : Matrix (Fin u × X) (Fin j × X) K} {c d s t : ℕ}
    (hM : PrimeTemplateProgram ℓ f F ζ M c s) (hN : PrimeTemplateProgram ℓ f F ζ N d t) :
    PrimeTemplateProgram ℓ f F ζ
      (Matrix.reindex (sumBank o u X) (sumBank i j X) (Matrix.fromBlocks M 0 0 N)) (c + d) (s + t) := by
  classical
  have h1 := hM.fromBlocks_one (Fin u × X)
  have h2 := (hN.fromBlocks_one (Fin i × X)).reindex (Equiv.sumComm _ _) (Equiv.sumComm _ _)
  have hswap : Matrix.reindex (Equiv.sumComm _ _) (Equiv.sumComm _ _)
      (Matrix.fromBlocks N 0 0 (1 : Matrix (Fin i × X) (Fin i × X) K)) = Matrix.fromBlocks 1 0 0 N := by
    rw [Matrix.reindex_apply]
    exact Matrix.fromBlocks_submatrix_sum_swap_sum_swap _ _ _ _
  rw [hswap] at h2
  have h3 := h1.serial h2
  have h4 : PrimeTemplateProgram ℓ f F ζ (Matrix.fromBlocks M 0 0 N) (c + d) (s + t) := by
    convert h3 using 1
    rw [Matrix.fromBlocks_multiply]
    simp
  exact h4.reindex _ _

/-! ## OpenAI's plans -/

lemma xorColumn_involutive {A : ℕ} (g : Fin A × Fin A) (u : Column A) :
    xorColumn g (xorColumn g u) = u := by
  funext a j
  have hcancel : ∀ t r : ZMod 2, t + r + r = t := by decide
  unfold xorColumn
  by_cases hg : g.1 ≠ g.2 ∧ a = g.1
  · obtain ⟨hne, rfl⟩ := hg
    have h1 : (g.1 ≠ g.2 ∧ g.1 = g.1) := ⟨hne, rfl⟩
    have h2 : ¬ (g.1 ≠ g.2 ∧ g.2 = g.1) := fun h => h.1 h.2.symm
    rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right h2]
    exact hcancel _ _
  · simp only [ite_eq_right hg]

/-- **Every OpenAI plan compiles into OpenAI's circuit-level program model**, with two
half-axis calls per child call and `planFree p` gates per address outside calls. -/
theorem program_plan {A : ℕ} (h : ℕ) : ∀ {i o : ℕ} (p : Plan A i o),
    PrimeTemplateProgram 2 h (2 ^ ((2 * A - 1) * h)) (-1 : K)
      ((p.eval h).map (Rat.castHom K)) (planFree p * 2 ^ (2 * A * h)) (2 * p.calls)
  | _, _, @Plan.mix _ i o c => by
    classical
    have hM : ((Plan.mix (A := A) c).eval h).map (Rat.castHom K)
        = Matrix.blockDiagonal fun _ : Addr A h => Matrix.of fun b a => ((value (c b a) : ℚ) : K) := by
      ext ⟨b, y⟩ ⟨a, x⟩
      change (((if x = y then value (c b a) else 0 : ℚ)) : K) =
        Matrix.blockDiagonal (fun _ : Addr A h => Matrix.of fun b a => ((value (c b a) : ℚ) : K))
          (b, y) (a, x)
      rw [Matrix.blockDiagonal_apply]
      by_cases hxy : x = y
      · subst hxy; simp
      · simp [hxy, Ne.symm hxy]
    rw [hM]
    by_cases h11 : i = 1 ∧ o = 1
    · -- a `1×1` mix is a scaling: no gates
      obtain ⟨rfl, rfl⟩ := h11
      have hD : (Matrix.blockDiagonal fun _ : Addr A h =>
            Matrix.of fun b a => ((value (c b a) : ℚ) : K))
          = Matrix.diagonal fun _ : Fin 1 × Addr A h => ((value (c 0 0) : ℚ) : K) := by
        ext ⟨b, y⟩ ⟨a, x⟩
        have hb : b = 0 := Subsingleton.elim _ _
        have ha : a = 0 := Subsingleton.elim _ _
        subst hb; subst ha
        rw [Matrix.blockDiagonal_apply, Matrix.diagonal_apply]
        by_cases hyx : y = x
        · subst hyx; simp
        · have e : ((0 : Fin 1), y) ≠ (0, x) := fun e => hyx (congrArg Prod.snd e)
          simp [hyx, e]
      rw [hD]
      exact program_cast (.localCircuit (realizable_diagonal _)) (by simp [planFree_mix])
        (by simp [Plan.calls])
    · exact program_cast (program_mixing _) (by simp [planFree_mix, h11]) (by simp [Plan.calls])
  | _, _, .xor g => by
    classical
    let σ : Fin 1 × Addr A h ↪ Fin 1 × Addr A h :=
      ⟨fun ix => (ix.1, fun c => xorColumn g (ix.2 c)), by
        intro u v huv
        simp only [Prod.mk.injEq] at huv
        refine Prod.ext huv.1 ?_
        funext c
        have := congrFun huv.2 c
        rw [← xorColumn_involutive g (u.2 c), this, xorColumn_involutive]⟩
    have hM : ((Plan.xor (A := A) g).eval h).map (Rat.castHom K)
        = (1 : Matrix (Fin 1 × Addr A h) (Fin 1 × Addr A h) K).submatrix id σ := by
      ext ⟨b, y⟩ ⟨a, x⟩
      have hab : b = a := Subsingleton.elim _ _
      subst hab
      change (((if y = xorColumn g ∘ x then 1 else 0 : ℚ)) : K) =
        (1 : Matrix (Fin 1 × Addr A h) (Fin 1 × Addr A h) K) (b, y) (b, fun c => xorColumn g (x c))
      rw [Matrix.one_apply]
      by_cases hyx : y = xorColumn g ∘ x
      · have e : (b, y) = (b, fun c => xorColumn g (x c)) := by rw [hyx]; rfl
        rw [ite_eq_left hyx, ite_eq_left e]
        simp
      · have e : (b, y) ≠ (b, fun c => xorColumn g (x c)) := fun e => hyx (congrArg Prod.snd e)
        rw [ite_eq_right hyx, ite_eq_right e]
        simp
    rw [hM]
    exact program_cast (.localCircuit ((realizable_one _).submatrix id σ)) (by simp [planFree])
      (by simp [Plan.calls])
  | _, _, .scale q test t => by
    classical
    have hM : ((Plan.scale (A := A) q test t).eval h).map (Rat.castHom K)
        = Matrix.diagonal fun ix : Fin 1 × Addr A h => ((value (t (∑ c, test (ix.2 c))) : ℚ) : K) := by
      ext ⟨b, y⟩ ⟨a, x⟩
      have hab : b = a := Subsingleton.elim _ _
      subst hab
      change (((if x = y then value (t (∑ c, test (x c))) else 0 : ℚ)) : K) =
        Matrix.diagonal (fun ix : Fin 1 × Addr A h => ((value (t (∑ c, test (ix.2 c))) : ℚ) : K))
          (b, y) (b, x)
      rw [Matrix.diagonal_apply]
      by_cases hxy : x = y
      · subst hxy; simp
      · have e : (b, y) ≠ (b, x) := fun e => hxy (congrArg Prod.snd e).symm
        rw [ite_eq_right hxy, ite_eq_right e]
        simp
    rw [hM]
    exact program_cast (.localCircuit (realizable_diagonal _)) (by simp [planFree])
      (by simp [Plan.calls])
  | _, _, .child a => by
    rw [child_eq]
    have h2 := ((program_halfMat (K := K) (h := h) (a, 0)).serial (program_halfMat (a, 1))).diagonal
      (fun _ => (1 / 2 : K) ^ h) (fun _ => 1)
    have h3 : PrimeTemplateProgram 2 h (2 ^ ((2 * A - 1) * h)) (-1 : K)
        (((1 / 2 : K) ^ h) • (halfMat (a, 0) * halfMat (h := h) (a, 1))) (0 + 0) (1 + 1) := by
      convert h2 using 1
      ext o i
      simp [Matrix.smul_apply]
    exact program_cast h3 (by simp [planFree]) (by simp [Plan.calls])
  | _, _, .seq p q => by
    have hp := program_plan h p
    have hq := program_plan h q
    rw [Plan.eval, Matrix.map_mul]
    exact program_cast (hp.serial hq) (by simp [planFree]; ring) (by simp [Plan.calls]; ring)
  | _, _, .parallel p q => by
    have hp := program_plan h p
    have hq := program_plan h q
    rw [Plan.eval, map_directSum]
    exact program_cast (program_directSum hp hq) (by simp [planFree]; ring) (by simp [Plan.calls]; ring)


/-! ## Rational plans -/

/-- Gates outside calls, per address, of a rational plan (dense count for mixes). -/
def qfree {A : ℕ} : {i o : ℕ} → QPlan A i o → ℕ
  | _, _, @QPlan.mix _ i o _ => o * i
  | _, _, .scaleRows _ _ _ => 0
  | _, _, .embed p => planFree p
  | _, _, .seq p q => qfree p + qfree q
  | _, _, .parallel p q => qfree p + qfree q

/-- **Every rational plan compiles into OpenAI's circuit-level program model**, over any field of
characteristic `0`, with `2·calls` half-axis calls and `qfree p` gates per address outside
calls. -/
theorem program_qplan {A : ℕ} (h : ℕ) : ∀ {i o : ℕ} (p : QPlan A i o),
    PrimeTemplateProgram 2 h (2 ^ ((2 * A - 1) * h)) (-1 : K)
      ((p.eval h).map (Rat.castHom K)) (qfree p * 2 ^ (2 * A * h)) (2 * p.calls)
  | _, _, @QPlan.mix _ i o c => by
    classical
    have hM : ((QPlan.mix (A := A) c).eval h).map (Rat.castHom K)
        = Matrix.blockDiagonal fun _ : Addr A h => Matrix.of fun b a => ((c b a : ℚ) : K) := by
      ext ⟨b, y⟩ ⟨a, x⟩
      change (((if x = y then c b a else 0 : ℚ)) : K) =
        Matrix.blockDiagonal (fun _ : Addr A h => Matrix.of fun b a => ((c b a : ℚ) : K)) (b, y) (a, x)
      rw [Matrix.blockDiagonal_apply]
      by_cases hxy : x = y
      · subst hxy; simp
      · simp [hxy, Ne.symm hxy]
    rw [hM]
    exact program_cast (program_mixing _) (by simp [qfree]) (by simp [QPlan.calls])
  | _, _, @QPlan.scaleRows _ n q test t => by
    classical
    have hM : ((QPlan.scaleRows (A := A) q test t).eval h).map (Rat.castHom K)
        = Matrix.diagonal fun ix : Fin n × Addr A h => ((t ix.1 (∑ c, test (ix.2 c)) : ℚ) : K) := by
      ext ⟨b, y⟩ ⟨a, x⟩
      change (((if b = a ∧ x = y then t b (∑ c, test (x c)) else 0 : ℚ)) : K) =
        Matrix.diagonal (fun ix : Fin n × Addr A h => ((t ix.1 (∑ c, test (ix.2 c)) : ℚ) : K))
          (b, y) (a, x)
      rw [Matrix.diagonal_apply]
      by_cases hba : b = a
      · subst hba
        by_cases hxy : x = y
        · subst hxy; simp
        · have e : (b, y) ≠ (b, x) := fun e => hxy (congrArg Prod.snd e).symm
          rw [ite_eq_right (fun hc => hxy hc.2), ite_eq_right e]
          simp
      · have e : (b, y) ≠ (a, x) := fun e => hba (congrArg Prod.fst e)
        rw [ite_eq_right (fun hc => hba hc.1), ite_eq_right e]
        simp
    rw [hM]
    exact program_cast (.localCircuit (realizable_diagonal _)) (by simp [qfree])
      (by simp [QPlan.calls])
  | _, _, .embed p => by
    exact program_cast (program_plan h p) (by simp [qfree]) (by simp [QPlan.calls])
  | _, _, .seq p q => by
    have hp := program_qplan h p
    have hq := program_qplan h q
    rw [QPlan.eval, Matrix.map_mul]
    exact program_cast (hp.serial hq) (by simp [qfree]; ring) (by simp [QPlan.calls]; ring)
  | _, _, .parallel p q => by
    have hp := program_qplan h p
    have hq := program_qplan h q
    rw [QPlan.eval, map_directSum]
    exact program_cast (program_directSum hp hq) (by simp [qfree]; ring)
      (by simp [QPlan.calls]; ring)

/-! ## The target is a batch of Walsh–Hadamard transforms -/

/-- Positions of the bits of an address. -/
def bitIndex (A h : ℕ) : Fin h × (Fin A × Fin 2) ≃ Fin (2 * A * h) :=
  ((Equiv.prodCongr (Equiv.refl (Fin h)) finProdFinEquiv).trans finProdFinEquiv).trans
    (finCongr (by ring))

/-- An address as a bit vector. -/
def flat (A h : ℕ) : Addr A h ≃ (Fin (2 * A * h) → Fin 2) where
  toFun y d := y ((bitIndex A h).symm d).1 ((bitIndex A h).symm d).2.1 ((bitIndex A h).symm d).2.2
  invFun v c a j := v (bitIndex A h (c, (a, j)))
  left_inv y := by
    funext c a j
    simp only [Equiv.symm_apply_apply]
    rfl
  right_inv v := by
    funext d
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]
    rfl

lemma flat_apply (A h : ℕ) (y : Addr A h) (c : Fin h) (a : Fin A) (j : Fin 2) :
    flat A h y (bitIndex A h (c, (a, j))) = y c a j := by
  show y ((bitIndex A h).symm (bitIndex A h (c, (a, j)))).1
    ((bitIndex A h).symm (bitIndex A h (c, (a, j)))).2.1
    ((bitIndex A h).symm (bitIndex A h (c, (a, j)))).2.2 = y c a j
  rw [Equiv.symm_apply_apply]

/-- Rows and addresses as the index of a block-diagonal batch. -/
def batchIndex (A W h : ℕ) : Fin W × Addr A h ≃ (Fin (2 * A * h) → Fin 2) × Fin W :=
  (Equiv.prodComm _ _).trans (Equiv.prodCongr (flat A h) (Equiv.refl (Fin W)))

/-- **OpenAI's target is `2^{-Ah}` times `W` copies of `H^{⊗2Ah}`.** -/
theorem target_eq (A W h : ℕ) :
    (target A W h).map (Rat.castHom K) =
      ((1 / 2 : K) ^ (A * h)) • Matrix.reindex (batchIndex A W h).symm (batchIndex A W h).symm
        (Matrix.blockDiagonal fun _ : Fin W => primeTransform 2 (2 * A * h) (-1 : K)) := by
  classical
  ext ⟨b, y⟩ ⟨a, x⟩
  change (((if a = b then ∏ c, ∏ j, pairEntry (y c j) (x c j) else 0 : ℚ)) : K) = _
  rw [Matrix.smul_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    Matrix.blockDiagonal_apply]
  simp only [batchIndex, Equiv.trans_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    rw [ite_eq_left rfl, ite_eq_left rfl, Rat.cast_prod]
    simp only [Rat.cast_prod, pairEntry_cast, primeTransform_apply]
    have hP : ∏ d : Fin (2 * A * h), (-1 : K) ^ ((flat A h y d).val * (flat A h x d).val)
        = ∏ c : Fin h, ∏ j : Fin A, ∏ k : Fin 2, (-1 : K) ^ ((y c j k).val * (x c j k).val) := by
      have e1 : ∏ c : Fin h, ∏ j : Fin A, ∏ k : Fin 2, (-1 : K) ^ ((y c j k).val * (x c j k).val)
          = ∏ p : Fin h × (Fin A × Fin 2),
              (-1 : K) ^ ((y p.1 p.2.1 p.2.2).val * (x p.1 p.2.1 p.2.2).val) := by
        rw [Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun c _ => ?_
        rw [Fintype.prod_prod_type]
      rw [e1]
      symm
      exact Fintype.prod_equiv (bitIndex A h) _ _ (fun q => by
        obtain ⟨c, j, k⟩ := q
        rw [flat_apply, flat_apply]
        rfl)
    rw [hP]
    simp only [Fin.prod_univ_two, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [← pow_mul, mul_comm A h]
  · rw [ite_eq_right hab, ite_eq_right (Ne.symm hab)]
    simp

/-- **A correct rational plan is a program for `W` copies of `H^{⊗2Ah}`.** -/
theorem program_batch {A W : ℕ} (p : QPlan A W W) (hp : QPlan.Correct p) (h : ℕ) :
    PrimeTemplateProgram 2 h (2 ^ ((2 * A - 1) * h)) (-1 : K)
      (Matrix.blockDiagonal fun _ : Fin W => primeTransform 2 (2 * A * h) (-1 : K))
      (qfree p * 2 ^ (2 * A * h)) (2 * p.calls) := by
  have h1 := program_qplan (K := K) h p
  rw [hp h, target_eq] at h1
  have h2 := (h1.diagonal (fun _ => (2 : K) ^ (A * h)) (fun _ => 1)).reindex
    (batchIndex A W h) (batchIndex A W h)
  convert h2 using 1
  ext u v
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Matrix.smul_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply]
  simp only [Equiv.symm_symm, Equiv.apply_symm_apply, smul_eq_mul, one_mul]
  rw [← mul_assoc, ← mul_pow]
  norm_num

/-- **OpenAI's batch inequality from a correct rational plan.** -/
theorem kernelBatch_of_correct {A W : ℕ} (p : QPlan A W W) (hp : QPlan.Correct p) :
    PrimeKernelBatch 2 (2 * A) W (2 * p.calls) (qfree p) (-1 : K) := by
  apply primeKernelBatch_of_template
  intro f _
  exact ⟨qfree p * 2 ^ (2 * A * f), le_rfl, 2 * p.calls, le_rfl, program_batch p hp f⟩

end Circ

/-- **From one correct rational plan to a bound for every Walsh–Hadamard transform.** If a
correct plan on `W` rows over `A` axes saves calls, `2σ/W < (2A)^θ`, then over every field of
characteristic `0`, `C(H^{⊗k}) ≤ D · 2^k · (1+k)^θ` for every `k`, with one constant `D`. -/
theorem walsh_bound_of_plan {A W : ℕ} (p : QPlan A W W) (hp : QPlan.Correct p) (hA : 0 < A)
    (hW : 0 < W) {θ : ℝ} (hθ : 0 ≤ θ)
    (hsave : ((2 * p.calls : ℕ) : ℝ) / W < ((2 * A : ℕ) : ℝ) ^ θ) :
    ∃ D > (0 : ℝ), ∀ (F : Type) [Field F] [CharZero F] (k : ℕ),
      (complexity (primeTransform 2 k (-1 : F)) : ℝ) ≤ D * 2 ^ k * (1 + (k : ℝ)) ^ θ := by
  obtain ⟨D, hD, hb⟩ := uniform_primeTransform_bound_of_batch (ℓ := 2) (A := 2 * A) (W := W)
    (σ := 2 * p.calls) (C := Circ.qfree p) (by norm_num) (by omega) hW hθ hsave
  refine ⟨D, hD, fun F _ _ k => ?_⟩
  have := hb F (-1 : F) (Circ.kernelBatch_of_correct (K := F) p hp) k
  simpa using this

end FTPaper
