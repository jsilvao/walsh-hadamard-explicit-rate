import Mathlib

/-!
# Two-application repair (paper: Lemma 4.1)

Setting: a field `K`, a finite set `ι` of rows, `s` linear checks `H : Matrix (Fin s) ι K`.

* **Per frequency** (`output_eq`, `exists_table`): if the predictor multiplier `p i` differs
  from the target `z` only on rows where `H` is injective, a linear "table" recovers the
  input on those rows from the two check vectors, and the output
  `p X - p Z + z Z` (with `Z = Hᵀ a`) equals `z X` on *every* row.
* **Operator level** (`repair_correct`): for batches of arrays, an arbitrary conversion
  `S : (𝒜 → K) ≃ₗ (𝒩 → K)` diagonalizing the row predictors `P i` and the target `F`,
  the two-application procedure returns `F (X i)` for every row `i`.
* **Vandermonde checks** (`separatesOn_vandermonde`): `H r i = node i ^ r` with distinct
  nodes is injective on every support of size at most `s`.
-/

open Matrix Finset

namespace FTPaper

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] {s : ℕ}

/-- `H` is injective on vectors supported on `J`. -/
def SeparatesOn (H : Matrix (Fin s) ι K) (J : Set ι) : Prop :=
  ∀ e : ι → K, (∀ i, i ∉ J → e i = 0) → H *ᵥ e = 0 → e = 0

/-- The spectral table at one frequency: from the two check vectors `H (p X)` and `H X`
it produces `a` with `(Hᵀ a) i = X i` on every row where the predictor is wrong. -/
def IsTable (H : Matrix (Fin s) ι K) (p : ι → K) (z : K)
    (T : (Fin s → K) →ₗ[K] (Fin s → K)) : Prop :=
  ∀ X : ι → K, ∀ i, p i ≠ z → (Hᵀ *ᵥ T (H *ᵥ (p * X) - z • (H *ᵥ X))) i = X i

/-- **Per-frequency correctness.** The two-application output equals the target on every row. -/
theorem output_eq {H : Matrix (Fin s) ι K} {p : ι → K} {z : K}
    {T : (Fin s → K) →ₗ[K] (Fin s → K)} (hT : IsTable H p z T) (X : ι → K) :
    p * X - p * (Hᵀ *ᵥ T (H *ᵥ (p * X) - z • (H *ᵥ X)))
      + z • (Hᵀ *ᵥ T (H *ᵥ (p * X) - z • (H *ᵥ X))) = z • X := by
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hi : p i = z
  · rw [hi]; ring
  · rw [hT X i hi]; ring

/-- A sum of terms vanishing off `P` is the sum over the subtype `{i // P i}`. -/
lemma sum_eq_sum_subtype {M : Type*} [AddCommMonoid M] {g : ι → M} (P : ι → Prop)
    [DecidablePred P] (hg : ∀ i, ¬ P i → g i = 0) :
    ∑ i, g i = ∑ j : {i // P i}, g j := by
  rw [← Fintype.sum_subtype_add_sum_subtype P g]
  have : ∑ j : {i // ¬ P i}, g j = 0 := Finset.sum_eq_zero (fun j _ => hg j.1 j.2)
  rw [this, add_zero]

/-- **Existence of the table.** If `H` is injective on the error support, a linear table exists. -/
theorem exists_table {H : Matrix (Fin s) ι K} {p : ι → K} {z : K}
    (hH : SeparatesOn H {i | p i ≠ z}) : ∃ T, IsTable H p z T := by
  classical
  -- columns of `H` on the error support
  let M : Matrix (Fin s) {i // p i ≠ z} K := Matrix.of fun r j => H r j
  -- extension by zero and its image under `H`
  let ext : ({i // p i ≠ z} → K) → ι → K := fun x i => if h : p i ≠ z then x ⟨i, h⟩ else 0
  have hext : ∀ x, H *ᵥ ext x = M *ᵥ x := by
    intro x
    funext r
    simp only [mulVec, dotProduct]
    rw [sum_eq_sum_subtype (fun i => p i ≠ z)]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      simp [M, ext, j.2]
    · intro i hi
      simp [ext, hi]
  -- injectivity of `M`
  have hinj : LinearMap.ker (Matrix.toLin' M) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    rw [Matrix.toLin'_apply] at hx
    have he : ext x = 0 := hH (ext x) (fun i hi => by
        simp only [Set.mem_ofPred_eq, not_not] at hi
        simp [ext, hi]) (by rw [hext]; exact hx)
    funext j
    have := congrFun he j.1
    simpa [ext, j.2] using this
  -- a left inverse `L` of `M`
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' M) hinj
  let L : Matrix {i // p i ≠ z} (Fin s) K := LinearMap.toMatrix' g
  have hLM : L * M = 1 := by
    have h := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h
  -- the table: recover `e = (p - z) X` on the support, divide by `p - z`, then lift by `Lᵀ`
  let Dg : Matrix {i // p i ≠ z} {i // p i ≠ z} K := Matrix.diagonal fun j => (p j - z)⁻¹
  refine ⟨Matrix.toLin' (Lᵀ * Dg * L), ?_⟩
  intro X i hi
  -- the combined check vector is `M` applied to `(p - z) X` restricted to the support
  have hy : H *ᵥ (p * X) - z • (H *ᵥ X) = M *ᵥ (fun j => (p j - z) * X j) := by
    rw [← hext]
    funext r
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Pi.mul_apply,
      Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : p k ≠ z
    · simp only [ext]; rw [dite_eq_left hk]; ring
    · have hk' : p k = z := not_not.mp hk
      simp only [ext]; rw [dite_eq_right hk, hk']; ring
  have hdiv : Dg *ᵥ (fun j => (p j - z) * X j) = fun j : {i // p i ≠ z} => X j := by
    funext j
    rw [Matrix.mulVec_diagonal]
    have : p j - z ≠ 0 := sub_ne_zero.mpr j.2
    field_simp
  -- evaluate `Hᵀ (Lᵀ Dg L y)` at a row of the support
  have hrow : ∀ v : Fin s → K, (Hᵀ *ᵥ v) i = (Mᵀ *ᵥ v) ⟨i, hi⟩ := by
    intro v
    simp [mulVec, dotProduct, M, Matrix.transpose_apply]
  rw [Matrix.toLin'_apply, hy, hrow]
  have h1 : (Lᵀ * Dg * L) *ᵥ (M *ᵥ fun j => (p j - z) * X j) = Lᵀ *ᵥ (fun j : {i // p i ≠ z} => X j) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hLM, Matrix.mul_one, ← Matrix.mulVec_mulVec,
      hdiv]
  rw [h1, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hLM, Matrix.transpose_one,
    Matrix.one_mulVec]

/-! ## Operator level -/

variable {𝒜 𝒩 : Type*}

/-- **Lemma B, operator level.** Rows are arrays `𝒜 → K`; `S` converts to frequencies `𝒩`;
`S (P i x) = p i * S x` and `S (F x) = z * S x` (pointwise products). With a table at
every frequency, the two-application procedure returns `F (X i)` on every row. -/
theorem repair_correct
    (S : (𝒜 → K) ≃ₗ[K] (𝒩 → K))
    (P : ι → (𝒜 → K) →ₗ[K] (𝒜 → K)) (p : ι → 𝒩 → K) (hP : ∀ i x, S (P i x) = p i * S x)
    (F : (𝒜 → K) →ₗ[K] (𝒜 → K)) (z : 𝒩 → K) (hF : ∀ x, S (F x) = z * S x)
    (H : Matrix (Fin s) ι K)
    (T : 𝒩 → (Fin s → K) →ₗ[K] (Fin s → K))
    (hT : ∀ ν, IsTable H (fun i => p i ν) (z ν) (T ν))
    (X : ι → 𝒜 → K) (i : ι) :
    let Y1 : ι → 𝒜 → K := fun j => P j (X j)
    let a : 𝒩 → Fin s → K := fun ν =>
      T ν (fun r => S (∑ j, H r j • Y1 j) ν - z ν * S (∑ j, H r j • X j) ν)
    let Z : ι → 𝒜 → K := fun j => ∑ r, H r j • S.symm (fun ν => a ν r)
    let G : ι → 𝒜 → K := fun j => ∑ r, H r j • S.symm (fun ν => z ν * a ν r)
    Y1 i - P i (Z i) + G i = F (X i) := by
  intro Y1 a Z G
  apply S.injective
  rw [hF]
  funext ν
  -- spectral coefficients of the input rows at `ν`
  let Xh : ι → K := fun j => S (X j) ν
  have hcheck : (fun r => S (∑ j, H r j • Y1 j) ν - z ν * S (∑ j, H r j • X j) ν)
      = H *ᵥ ((fun j => p j ν) * Xh) - z ν • (H *ᵥ Xh) := by
    funext r
    simp [Y1, Xh, map_sum, map_smul, hP, mulVec, dotProduct, Finset.sum_apply, mul_left_comm]
  have hZ : S (Z i) ν = (Hᵀ *ᵥ a ν) i := by
    simp [Z, map_sum, map_smul, mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_apply]
  have hG : S (G i) ν = z ν * (Hᵀ *ᵥ a ν) i := by
    simp [G, map_sum, map_smul, mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_apply,
      Finset.mul_sum, mul_left_comm]
  have ha : a ν = T ν (H *ᵥ ((fun j => p j ν) * Xh) - z ν • (H *ᵥ Xh)) := by
    show T ν _ = _
    rw [hcheck]
  have key := congrFun (output_eq (hT ν) Xh) i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at key
  have hY : S (Y1 i) ν = p i ν * Xh i := by
    simp [Y1, Xh, hP]
  have hPZ : S (P i (Z i)) ν = p i ν * S (Z i) ν := by
    rw [hP]; rfl
  calc S (Y1 i - P i (Z i) + G i) ν
      = S (Y1 i) ν - S (P i (Z i)) ν + S (G i) ν := by
        simp only [map_add, map_sub, Pi.add_apply, Pi.sub_apply]
    _ = p i ν * Xh i - p i ν * (Hᵀ *ᵥ a ν) i + z ν * (Hᵀ *ᵥ a ν) i := by
        rw [hY, hPZ, hZ, hG]
    _ = z ν * Xh i := by rw [ha]; exact key
    _ = (z * S (X i)) ν := rfl

/-! ## Vandermonde checks -/

/-- Vandermonde checks `H r i = node i ^ r` with distinct nodes separate every support of
size at most `s`. -/
theorem separatesOn_vandermonde [DecidableEq ι] (node : ι → K) (hnode : Function.Injective node)
    (J : Finset ι) (hJ : J.card ≤ s) :
    SeparatesOn (Matrix.of fun (r : Fin s) i => node i ^ (r : ℕ)) (J : Set ι) := by
  classical
  intro e he hHe
  funext i₀
  by_cases hi₀ : i₀ ∈ J
  · -- the polynomial vanishing on the other nodes of `J`
    let f : Polynomial K := ∏ j ∈ J.erase i₀, (Polynomial.X - Polynomial.C (node j))
    have hdeg : f.natDegree < s := by
      have h1 : f.natDegree ≤ ∑ j ∈ J.erase i₀, (Polynomial.X - Polynomial.C (node j)).natDegree :=
        Polynomial.natDegree_prod_le _ _
      have h2 : ∑ j ∈ J.erase i₀, (Polynomial.X - Polynomial.C (node j)).natDegree
          = (J.erase i₀).card := by
        simp
      have h3 : (J.erase i₀).card < J.card := Finset.card_erase_lt_of_mem hi₀
      omega
    -- pairing `e` with the coefficients of `f` gives zero
    have hzero : ∑ i, e i * f.eval (node i) = 0 := by
      have hk : ∀ k : Fin s, ∑ i, e i * node i ^ (k : ℕ) = 0 := by
        intro k
        have := congrFun hHe k
        simpa [mulVec, dotProduct, mul_comm] using this
      calc ∑ i, e i * f.eval (node i)
          = ∑ i, e i * ∑ k ∈ Finset.range s, f.coeff k * node i ^ k := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Polynomial.eval_eq_sum_range' hdeg]
        _ = ∑ k ∈ Finset.range s, f.coeff k * ∑ i, e i * node i ^ k := by
            simp only [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => ?_))
            ring
        _ = 0 := by
            refine Finset.sum_eq_zero (fun k hk' => ?_)
            have hks : k < s := Finset.mem_range.mp hk'
            rw [hk ⟨k, hks⟩, mul_zero]
    -- only the term `i₀` survives
    have hsingle : ∑ i, e i * f.eval (node i) = e i₀ * f.eval (node i₀) := by
      refine Finset.sum_eq_single i₀ (fun i _ hne => ?_) (fun h => absurd (Finset.mem_univ _) h)
      by_cases hiJ : i ∈ J
      · have : f.eval (node i) = 0 := by
          simp only [f, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
            Polynomial.eval_C]
          exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, hiJ⟩) (sub_self _)
        rw [this, mul_zero]
      · rw [he i (by simpa using hiJ), zero_mul]
    have hne : f.eval (node i₀) ≠ 0 := by
      simp only [f, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      exact Finset.prod_ne_zero_iff.mpr (fun j hj =>
        sub_ne_zero.mpr (hnode.ne (Finset.ne_of_mem_erase hj).symm))
    have : e i₀ * f.eval (node i₀) = 0 := by rw [← hsingle]; exact hzero
    simpa [hne] using this
  · exact he i₀ (by simpa using hi₀)

/-- **Lemma B, usable form.** With Vandermonde checks on distinct nodes, a table exists at
every frequency where the predictor is wrong on at most `s` rows. -/
theorem exists_table_vandermonde [DecidableEq ι] [DecidableEq K] (node : ι → K) (hnode : Function.Injective node)
    {p : ι → K} {z : K} (hcard : (Finset.univ.filter fun i => p i ≠ z).card ≤ s) :
    ∃ T, IsTable (Matrix.of fun (r : Fin s) i => node i ^ (r : ℕ)) p z T := by
  apply exists_table
  have h := separatesOn_vandermonde node hnode _ hcard
  simpa using h

end FTPaper
