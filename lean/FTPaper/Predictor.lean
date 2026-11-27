import Mathlib

/-!
# Lemma A: the window predictor is a polynomial in one operator

Paper: Lemma 3.1 (binary case, `ℓ = 2`).

* `count_eq`, `parity`: the operator `C_β = ∑ⱼ ½(1 − (−1)^{βⱼ} Qⱼ)` has eigenvalue the shifted
  count `|k ⊕ β|`, and `(−1)^{|k ⊕ β|} = (−1)^{|k|} (−1)^{|β|}`.
* `exists_window_poly`: interpolation on the window `[u, v]` with degree `≤ v − u`.
* `aeval_diag`: a polynomial in an operator diagonalized by `S` is diagonalized by `S`.
* `predictor_correct`: **Lemma A, operator level** — there is a polynomial `π` of degree
  `≤ v − u` with `S (π(C_β) x) ν = (−1)^{|k ν|} · S x ν` whenever the shifted count at `ν`
  lies in the window, i.e. `π(C_β)` agrees with `F = ∏ Qⱼ` there.
* `card_window_complement`: the exceptional shifts at frequency `ν` are the translate
  `k ν ⊕ E` of one fixed set, so their number does not depend on `ν`.
* `horner_eq`: Horner's rule evaluates `π(C) x` with `natDegree π` applications of `C`.
-/

open Finset Polynomial

namespace FTPaper

variable {K : Type*} [Field K]

/-- `sgn b = (−1)^b` for a bit `b`. -/
def sgn (b : Bool) : K := if b then -1 else 1

@[simp] lemma sgn_false : (sgn false : K) = 1 := rfl
@[simp] lemma sgn_true : (sgn true : K) = -1 := rfl

lemma sgn_xor (a b : Bool) : (sgn (xor a b) : K) = sgn a * sgn b := by
  cases a <;> cases b <;> simp

variable {m : ℕ}

/-- Hamming weight of a bit vector. -/
def weight (k : Fin m → Bool) : ℕ := (univ.filter fun j => k j = true).card

/-- The shifted count `c_β(ν) = |k ⊕ β|` (Hamming distance). -/
def shiftedCount (k β : Fin m → Bool) : ℕ := weight fun j => xor (k j) (β j)

lemma neg_one_pow_weight (k : Fin m → Bool) : (-1 : K) ^ weight k = ∏ j, (sgn (k j) : K) := by
  have h : ∀ j, (sgn (k j) : K) = if k j = true then -1 else 1 := by
    intro j; cases k j <;> simp
  simp_rw [h]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, weight]

/-- Parity of the shifted count. -/
theorem parity (k β : Fin m → Bool) :
    (-1 : K) ^ shiftedCount k β = (-1) ^ weight k * (-1) ^ weight β := by
  rw [shiftedCount, neg_one_pow_weight, neg_one_pow_weight, neg_one_pow_weight,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => sgn_xor _ _

/-- The multiplier of `C_β` at a frequency with bits `k` is the shifted count. -/
theorem count_eq [CharZero K] (k β : Fin m → Bool) :
    ∑ j, (1 / 2 : K) * (1 - sgn (β j) * sgn (k j)) = (shiftedCount k β : K) := by
  have h : ∀ j, (1 / 2 : K) * (1 - sgn (β j) * sgn (k j))
      = if xor (k j) (β j) = true then 1 else 0 := by
    intro j
    cases k j <;> cases β j <;> norm_num
  simp_rw [h]
  rw [Finset.sum_boole]
  simp [shiftedCount, weight]

/-- Interpolation on the window `[u, v]` with degree at most `v − u` (distinct nodes in
characteristic 0). -/
theorem exists_window_poly [CharZero K] (u v : ℕ) (target : ℕ → K) :
    ∃ π : K[X], π.natDegree ≤ v - u ∧ ∀ c, u ≤ c → c ≤ v → π.eval (c : K) = target c := by
  classical
  have hinj : Set.InjOn (fun c : ℕ => (c : K)) (Finset.Icc u v : Set ℕ) :=
    fun a _ b _ h => Nat.cast_injective h
  refine ⟨Lagrange.interpolate (Finset.Icc u v) (fun c : ℕ => (c : K)) target, ?_, ?_⟩
  · set π := Lagrange.interpolate (Finset.Icc u v) (fun c : ℕ => (c : K)) target
    have hdeg := Lagrange.degree_interpolate_lt (s := Finset.Icc u v)
      (v := fun c : ℕ => (c : K)) target hinj
    by_cases hπ : π = 0
    · simp [hπ]
    · have hlt := (Polynomial.natDegree_lt_iff_degree_lt hπ).mpr hdeg
      rw [Nat.card_Icc] at hlt
      omega
  · intro c hu hv
    exact Lagrange.eval_interpolate_at_node target hinj (Finset.mem_Icc.mpr ⟨hu, hv⟩)

variable {𝒜 𝒩 : Type*}

/-- Powers of an operator diagonalized by `S`. -/
lemma pow_diag (S : (𝒜 → K) ≃ₗ[K] (𝒩 → K)) (A : Module.End K (𝒜 → K)) (a : 𝒩 → K)
    (hA : ∀ x, S (A x) = a * S x) (n : ℕ) (x : 𝒜 → K) :
    S ((A ^ n) x) = a ^ n * S x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, hA, pow_succ, mul_assoc]

/-- A polynomial in an operator diagonalized by `S` is diagonalized by `S`. -/
theorem aeval_diag (S : (𝒜 → K) ≃ₗ[K] (𝒩 → K)) (A : Module.End K (𝒜 → K)) (a : 𝒩 → K)
    (hA : ∀ x, S (A x) = a * S x) (π : K[X]) (x : 𝒜 → K) :
    S (Polynomial.aeval A π x) = (fun ν => π.eval (a ν)) * S x := by
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, map_sum]
  funext ν
  simp only [LinearMap.smul_apply, map_smul, pow_diag S A a hA, Finset.sum_apply, Pi.smul_apply,
    Pi.mul_apply, Pi.pow_apply, smul_eq_mul, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Lemma A, operator level.** Commuting queries `Qⱼ` with multipliers `(−1)^{kⱼ(ν)}`;
`C_β = ∑ⱼ ½(1 − (−1)^{βⱼ} Qⱼ)`. Some polynomial `π` of degree `≤ v − u` makes `π(C_β)`
agree with the target multiplier `(−1)^{|k(ν)|}` (that of `F = ∏ Qⱼ`) at every frequency
whose shifted count lies in `[u, v]`. -/
theorem predictor_correct [CharZero K] (S : (𝒜 → K) ≃ₗ[K] (𝒩 → K))
    (Q : Fin m → Module.End K (𝒜 → K)) (k : 𝒩 → Fin m → Bool)
    (hQ : ∀ j x, S (Q j x) = (fun ν => sgn (k ν j)) * S x)
    (β : Fin m → Bool) (u v : ℕ) :
    let C : Module.End K (𝒜 → K) := ∑ j, (1 / 2 : K) • (LinearMap.id - (sgn (β j) : K) • Q j)
    ∃ π : K[X], π.natDegree ≤ v - u ∧
      ∀ x ν, u ≤ shiftedCount (k ν) β → shiftedCount (k ν) β ≤ v →
        S (Polynomial.aeval C π x) ν = (-1) ^ weight (k ν) * S x ν := by
  intro C
  have hC : ∀ x, S (C x) = (fun ν => (shiftedCount (k ν) β : K)) * S x := by
    intro x
    funext ν
    show S (C x) ν = (shiftedCount (k ν) β : K) * S x ν
    rw [← count_eq (k ν) β]
    simp only [C, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
      LinearMap.sub_apply, LinearMap.id_apply, map_sum, map_smul, map_sub, hQ, Pi.mul_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨π, hdeg, hπ⟩ :=
    exists_window_poly u v (fun c => (-1 : K) ^ c * (-1) ^ weight β)
  refine ⟨π, hdeg, fun x ν hu hv => ?_⟩
  rw [aeval_diag S C _ hC π x, Pi.mul_apply, hπ _ hu hv, parity]
  have hsq : ((-1 : K) ^ weight β) * (-1) ^ weight β = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  calc (-1 : K) ^ weight (k ν) * (-1) ^ weight β * (-1) ^ weight β * S x ν
      = (-1) ^ weight (k ν) * ((-1) ^ weight β * (-1) ^ weight β) * S x ν := by ring
    _ = (-1) ^ weight (k ν) * S x ν := by rw [hsq, mul_one]

/-- The exceptional shifts at a frequency with bits `k` are `k ⊕ E` for the fixed set
`E = {γ : |γ| ∉ [u, v]}`; in particular their number is independent of `k`. -/
theorem card_window_complement (k : Fin m → Bool) (u v : ℕ) :
    (univ.filter fun β : Fin m → Bool => ¬ (u ≤ shiftedCount k β ∧ shiftedCount k β ≤ v)).card
      = (univ.filter fun γ : Fin m → Bool => ¬ (u ≤ weight γ ∧ weight γ ≤ v)).card := by
  refine Finset.card_bij (fun β _ => fun j => xor (k j) (β j)) ?_ ?_ ?_
  · intro β hβ
    simpa [shiftedCount] using hβ
  · intro β₁ _ β₂ _ h
    funext j
    have := congrFun h j
    simpa using this
  · intro γ hγ
    refine ⟨fun j => xor (k j) (γ j), ?_, ?_⟩
    · have : (fun j => xor (k j) (xor (k j) (γ j))) = γ := by funext j; simp
      simpa [shiftedCount, this] using hγ
    · funext j; simp

/-- **Horner's rule.** `π(C) x = c₀ x + C (c₁ x + C (⋯ C (c_D x)))`: the fold has one
application of `C` (one pencil stage) per element of a list of length `natDegree π`. -/
theorem horner_eq {M : Type*} [AddCommGroup M] [Module K M] (C : Module.End K M) (x : M)
    (π : K[X]) :
    (List.map π.coeff (List.range π.natDegree)).foldr (fun c V => c • x + C V)
        (π.coeff π.natDegree • x) = Polynomial.aeval C π x := by
  have key : ∀ (f : ℕ → K) (n : ℕ) (V : M),
      (List.map f (List.range n)).foldr (fun c V => c • x + C V) V
        = ∑ h ∈ Finset.range n, f h • (C ^ h) x + (C ^ n) V := by
    intro f n
    induction n with
    | zero => intro V; simp
    | succ n ih =>
      intro V
      rw [List.range_succ, List.map_append, List.foldr_append, ih, Finset.sum_range_succ]
      simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, map_add, map_smul,
        pow_succ, Module.End.mul_apply]
      abel
  rw [key, Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, LinearMap.add_apply,
    LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, map_smul]

/-- The Horner list has exactly `natDegree π` entries (pencil stages). -/
theorem horner_stages (π : K[X]) : (List.map π.coeff (List.range π.natDegree)).length = π.natDegree := by
  simp

end FTPaper
