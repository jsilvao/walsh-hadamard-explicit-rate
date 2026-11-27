import FTPaper.LemmaS.Decoder

/-!
# The fast Walsh–Hadamard transform (Lemma S, gates)

One butterfly on coordinate `j` maps `y` to `S ↦ (-1)^{[j ∈ S]} y(S) + y(S ∆ {j})`. Applying
one butterfly for each coordinate gives the Walsh–Hadamard transform `hada` (`bflys_finRange`).
Each butterfly output has two terms, so the transform costs `m` gates per entry.

The proof goes through the partial transform `pwht J`, along the coordinates in `J`:
`pwht J x (S) = ∑_{P ⊆ J} (-1)^{|(S \ P) ∩ J|} x(S ∆ P)`.
-/

namespace FTPaper.LemmaS

open Finset

variable {m : ℕ}

/-- One butterfly on coordinate `j`. -/
def bfly (j : Fin m) (y : Fn m) : Fn m :=
  fun S => (if j ∈ S then (-1 : ℚ) else 1) * y S + y (symmDiff S {j})

/-- The partial Walsh–Hadamard transform along the coordinates in `J`. -/
def pwht (J : Finset (Fin m)) (x : Fn m) : Fn m :=
  fun S => ∑ P ∈ J.powerset, (-1 : ℚ) ^ ((S \ P) ∩ J).card * x (symmDiff S P)

lemma pwht_empty (x : Fn m) : pwht ∅ x = x := by
  funext S
  simp only [pwht, powerset_empty, sum_singleton, inter_empty, card_empty, pow_zero, one_mul]
  rw [← bot_eq_empty, symmDiff_bot]

lemma pwht_insert {j : Fin m} {J : Finset (Fin m)} (hj : j ∉ J) (x : Fn m) :
    pwht (insert j J) x = bfly j (pwht J x) := by
  classical
  funext S
  simp only [pwht, bfly]
  rw [powerset_insert, sum_union]
  · rw [sum_image]
    · rw [mul_sum]
      congr 1
      swap
      · -- the subsets containing `j`
        refine sum_congr rfl fun P hP => ?_
        have hPJ : P ⊆ J := mem_powerset.mp hP
        have hjP : j ∉ P := fun h => hj (hPJ h)
        have h1 : symmDiff S (insert j P) = symmDiff (symmDiff S {j}) P := by
          ext t
          simp only [mem_symmDiff, mem_insert, mem_singleton]
          by_cases htj : t = j
          · subst htj; simp [hjP]
          · simp [htj]
        have h2 : ((S \ insert j P) ∩ insert j J).card = ((symmDiff S {j} \ P) ∩ J).card := by
          congr 1
          ext t
          simp only [mem_inter, mem_sdiff, mem_insert, mem_symmDiff, mem_singleton]
          by_cases htj : t = j
          · subst htj; simp [hj]
          · simp [htj]
        rw [h1, h2]
      · -- the subsets of `J`
        refine sum_congr rfl fun P hP => ?_
        have hPJ : P ⊆ J := mem_powerset.mp hP
        have hjP : j ∉ P := fun h => hj (hPJ h)
        by_cases hjS : j ∈ S
        · have h1 : (S \ P) ∩ insert j J = insert j ((S \ P) ∩ J) := by
            ext t
            simp only [mem_inter, mem_sdiff, mem_insert]
            by_cases htj : t = j
            · subst htj; simp [hjS, hjP]
            · simp [htj]
          rw [h1, card_insert_of_notMem (fun h => hj (mem_inter.mp h).2), pow_succ,
            ite_eq_left hjS]
          ring
        · have h1 : (S \ P) ∩ insert j J = (S \ P) ∩ J := by
            ext t
            simp only [mem_inter, mem_sdiff, mem_insert]
            by_cases htj : t = j
            · subst htj; simp [hjS]
            · simp [htj]
          rw [h1, ite_eq_right hjS, one_mul]
    · intro P hP Q hQ hPQ
      have hjP : j ∉ P := fun h => hj (mem_powerset.mp hP h)
      have hjQ : j ∉ Q := fun h => hj (mem_powerset.mp hQ h)
      rw [← erase_insert hjP, ← erase_insert hjQ]
      exact congrArg (fun T => T.erase j) hPQ
  · rw [disjoint_left]
    intro P hP hP'
    rw [mem_image] at hP'
    obtain ⟨Q, _, rfl⟩ := hP'
    exact hj (mem_powerset.mp hP (mem_insert_self j Q))

lemma sdiff_symmDiff_self (S P : Finset (Fin m)) : S \ symmDiff S P = S ∩ P := by
  ext t
  simp only [mem_inter, mem_symmDiff, mem_sdiff]
  tauto

lemma pwht_univ (x : Fn m) : pwht univ x = hada x := by
  classical
  funext S
  rw [pwht, powerset_univ, hada_apply]
  let e : Finset (Fin m) ≃ Finset (Fin m) :=
    ⟨fun P => symmDiff S P, fun P => symmDiff S P,
      fun P => symmDiff_symmDiff_cancel_left S P, fun P => symmDiff_symmDiff_cancel_left S P⟩
  rw [← e.sum_comp]
  refine sum_congr rfl fun P _ => ?_
  simp only [e, Equiv.coe_fn_mk, inter_univ]
  rw [sdiff_symmDiff_self, symmDiff_symmDiff_cancel_left]

/-- Butterflies along a list of coordinates, the last one first. -/
def bflys : List (Fin m) → Fn m → Fn m
  | [], x => x
  | j :: js, x => bfly j (bflys js x)

lemma bflys_eq_pwht : ∀ (js : List (Fin m)), js.Nodup → ∀ x : Fn m, bflys js x = pwht js.toFinset x
  | [], _, x => by simp [bflys, pwht_empty]
  | j :: js, hnd, x => by
    rw [List.nodup_cons] at hnd
    rw [bflys, bflys_eq_pwht js hnd.2 x, List.toFinset_cons,
      pwht_insert (by simpa using hnd.1)]

/-- **The fast Walsh–Hadamard transform.** One butterfly per coordinate gives `hada`. -/
theorem bflys_finRange (x : Fn m) : bflys (List.finRange m) x = hada x := by
  rw [bflys_eq_pwht _ (List.nodup_finRange m), ← pwht_univ]
  congr 1
  ext j
  simp

end FTPaper.LemmaS
