# Lean companion

Machine-checked proofs of the results in the paper (`../paper/latex/main.pdf`). The labels used below and in the file headers (Lemma A, Theorem 1, Corollary R2, …) are working labels; `../paper/latex/README.md` maps them to the paper's numbering.

## Pins

- **Lean:** v4.34.1.
- **Mathlib:** `d13f23b7`. These are the same versions as `openai/math/lean` and the Big O Speedrun verifier, so the files can later be ported into that library.

## Build

```sh
export PATH="$HOME/.elan/bin:$PATH"   # elan is installed but not on PATH by default
lake exe cache get                    # once: downloads prebuilt Mathlib (~7.7 GB, already done)
lake build                            # compiles FTPaper/
lake env lean CheckAxioms.lean        # prints the axioms each theorem depends on
```

`CheckAxioms.lean` must show only `propext`, `Classical.choice` and `Quot.sound` for every theorem, with no `sorryAx`. Those are also the only axioms the Big O Speedrun verifier allows.

## What is proved

All 102 theorems build with no warnings. `CheckAxioms.lean` shows only the standard axioms for each.

### Lemma B: two-application repair (`FTPaper/Repair.lean`, any field)

| Lean theorem | Statement |
|---|---|
| `output_eq` | Per frequency: if the table recovers the input on the rows where the predictor is wrong, the output `pX − pZ + zZ` equals `zX` on every row. |
| `exists_table` | If the checks `H` are injective on the error support, such a linear table exists. |
| `repair_correct` | **Operator level.** Batches of arrays and any linear-equivalence conversion `S` that diagonalizes the row predictors and the target `F`. The 7-step procedure of the paper's Section 4 returns `F (X i)` for every row. |
| `separatesOn_vandermonde` | Vandermonde checks with distinct nodes are injective on every support of size ≤ s. |
| `exists_table_vandermonde` | So a table exists whenever the predictor is wrong on ≤ s rows. |

### Lemma A: window predictor (`FTPaper/Predictor.lean`, characteristic 0)

| Lean theorem | Statement |
|---|---|
| `count_eq`, `parity` | `C_β = Σⱼ ½(1 − (−1)^{βⱼ}Qⱼ)` has multiplier \|k ⊕ β\| (the shifted count). Also (−1)^{\|k⊕β\|} = (−1)^{\|k\|}·(−1)^{\|β\|}. |
| `exists_window_poly` | Interpolation on the window [u, v] with degree ≤ v − u. |
| `aeval_diag` | A polynomial in an operator diagonalized by `S` is diagonalized by `S`. |
| `predictor_correct` | **Operator level.** Some π of degree ≤ v − u makes π(C_β) agree with the target multiplier (−1)^{\|k(ν)\|} at every frequency whose shifted count is in the window. |
| `card_window_complement` | The exceptional shifts at each frequency form a translate of one fixed set, so their number is the same at every frequency. |
| `horner_eq`, `horner_stages` | Horner's rule computes π(C)x with exactly `natDegree π` applications of C, one pencil stage each. |

### Lemma C and Theorem 1, cost part (`FTPaper/Feedback.lean`)

| Lean theorem | Statement |
|---|---|
| `feedbackCost_eq` | Closed form of the feedback cost recursion: `w·Σ_{i≤g}(2/G)^i + (2/G)^{g+1}·W·A`. |
| `feedbackCost_div_le` | Per row: ≤ `(w/W)/(1 − 2/G) + (2/G)^{g+1}·A`. |
| `one_level_cost` | With w = 2DρW and G = 20: ≤ `(10/9)·2Dρ + (1/10)^{g+1}·A`. |

### Theorem 3(3): charged rectangles (`FTPaper/Limits.lean`)

| Lean theorem | Statement |
|---|---|
| `charged_card_ge` | Labels carry vectors in a finite set 𝔻, and free rectangles contain only related pairs, while no label is related to itself. Then any decomposition of the identity into charged and free rectangles has at least \|V\|/\|𝔻\| charged rectangles. |
| `charged_card_ge_pow` | The [OAI] form, with 𝔻 = 𝔽₂^D: at least \|V\|/2^D charged rectangles. |
| `charged_card_ge_pairing` | Pairing form (paper: Theorem 1.5(3)): if a pairing on 𝔽₂^D is nonzero on each (d v, d v) and vanishes on every free rectangle, there are at least \|V\|/2^D charged rectangles. |

### Theorem 1: window and constant (`FTPaper/Window.lean`)

| Lean theorem | Statement |
|---|---|
| `sum_exp_weight` | The generating function of the centered weight: `Σ_γ exp(λ(\|γ\| − m/2)) = (2 cosh(λ/2))^m`. |
| `card_tail_le` | Chernoff–Hoeffding: `#{γ : t < \|\|γ\| − m/2\|} ≤ 2·2^m·exp(−2t²/m)`. |
| `window_fraction` | If `2t² ≥ m ln 80`, at most `2^m/40` shifts lie outside the window. |
| `mem_window_iff`, `window_width_le` | The integer window is exactly `{c : \|c − m/2\| ≤ t}`, and it has width ≤ 2t. |
| `log_eighty_le` | `ln 80 ≤ 9/2`. |
| `theorem1_bound` | Theorem 1's constant: calls per row ≤ `(20/3·√m + 40/9)·ρ + 1`. |

### Corollary R2: routing parameters (`FTPaper/Routing.lean`)

| Lean theorem | Statement |
|---|---|
| `routing_alphabet` | The alphabet is large enough: `q^{L/2} ≥ 2^x`. |
| `routing_exponent_le` | `log₂(6D(1+log₂q)^L) ≤ 11√(x log₂ x) + 7` for integers x ≥ 2. |

### Theorem 3(2): batching (`FTPaper/Batching.lean`, OpenAI's circuit model)

| Lean theorem | Statement |
|---|---|
| `split_step` | `C(H^{⊗(a+h)}) ≤ 2C·2^{a+h}√a + 2^a·C(H^{⊗h})`, given a batch of W ≤ 2^h copies of `H^{⊗a}` costing ≤ `C·W·2^a·√a`. |
| `batching_sufficient` | Batches of `W ≤ 2^{γa}` copies at cost `O(W 2^a √a)` give `C(H^{⊗k}) = O(2^k √k)`. |
| `batching_necessary` | The converse, with W = 1. |

Here `complexity` and `primeTransform` come from 12 modules of `openai/math`, vendored unchanged in `OAI/` (Apache 2.0). See `OAI/NOTICE.md`.

### Lemma R1 against OpenAI's actual routing (`FTPaper/RoutingOAI.lean`)

| Lean theorem | Statement |
|---|---|
| `lemmaR1_pencil` | OpenAI's compiled pencil (`geometricPencil`), for any dyadic stage coefficients: ≤ 6·D·(1+b)^L calls per row, if m + 1 ≤ q^{L/2}. |
| `stageBound_le` | The same bound for their per-stage budget. |
| `oai_template_cost` | Their full one-level template (a plan proved `Correct`): calls ≤ 4·clockPeriod(m)·6D(1+b)^L·W + 4·q^L·checks·A. |

### OpenAI's stage count and dyadic coefficients (`FTPaper/Compare.lean`, `FTPaper/Dyadic.lean`)

| Lean theorem | Statement |
|---|---|
| `two_radius_le_degree` | OpenAI's window `[⌊μ−B⌋, ⌈μ+B⌉]` has width at least `2B`. |
| `oai_stages_ge`, `oai_stages_ge_real` | Paper Proposition 1.4: `4·clockPeriod(m) ≥ 8⌈√(2m⌈log₂ 2m⌉)⌉ ≥ 11.3·√(m log₂ 2m)`, the stage count of OpenAI's one-level template. |
| `six_dvd_third_diff`, `third_diff_sum` | The third difference of `t^n` at an integer is divisible by 6; clearing `2^e` from dyadic coefficients. |
| `no_dyadic_window` | Paper Proposition 7.3: no polynomial with coefficients in `ℤ[1/2]` equals `(−1)^c` at four consecutive integers. This is why `QPlan` has rational coefficients. |

These build on 155 vendored modules of `openai/math`, all Mathlib-only. That is the import closure of `KernelBinaryTemplate`; see `OAI/NOTICE.md`. A full build of those modules takes about 12 minutes.

### Theorem 1 end to end in OpenAI's routing (`FTPaper/Q*.lean`)

We use a rational-coefficient plan language `QPlan` (`QPlan.lean`). It keeps OpenAI's semantics and call counting, and it can `embed` any of their plans unchanged.

| File | Key theorems |
|---|---|
| `QHorner.lean` | `applyAt_horner`, `calls_horner`: the Horner predictor uses exactly `n` stages |
| `QTwoPass.lean` | `applyAt_twoPass`, `calls_twoPass`: the two-pass repair |
| `QFreq.lean` | `frequency_horner`, `frequency_spectralTable`: action in frequency coordinates |
| `QTemplate.lean` | `frequency_batch`: the repaired batch multiplies every frequency by the target sign. `calls_batch`: its exact call count |
| `QWrap.lean` | `correct_of_product`: with OpenAI's outer passes, the result is `Correct` |
| `QStage.lean` | `frequency_stage`: OpenAI's routed pencil with our dyadic coefficients is our stage `C_β` |
| `QMain.lean` | `template_correct`, `template_calls`, `template_end_to_end` |
| `QHoeffding.lean` | `checks_le`, and **`theorem1_direct`**: a correct plan with ≤ `12(3√(m+1)+2)·D(1+b)^L + A/10` calls per row |
| `QFeedback.lean` | `rowAction_of_correct`, `restrict`, `spectralVia` (conversions by any correct plan), `fbPlan` (the feedback family: level `j` on `20^j` copies converts with level `j−1`), `correct_fbPlan`, `calls_fbPlan_le`, **`theorem1`**: a correct plan with ≤ `(20/3·√(m+1) + 40/9)·6D(1+b)^L + 1` calls per row when `A ≤ 10^d`, and **`theorem1_explicit`**: the same for OpenAI's `system L b`, with `D ≤ 2 + L·2^b` |
| `QRouted.lean` | **`theorem1_routed`**: with Corollary R2's parameters (`2^x ≥ m+1`), at most `(20/3·√(m+1) + 40/9)·2^{11√(x log₂ x)+7} + 1` calls per row |

### From plans to circuits (`FTPaper/QCircuit.lean`, `FTPaper/QUpper.lean`)

Every rational plan compiles into OpenAI's circuit-level program model `PrimeTemplateProgram`, over any field of characteristic 0. A child call on a 2h-bit axis is `2^{-h}` times two calls on h-bit half-axes (`child_eq`). So `σ` child calls become `2σ` half-axis calls over `2A` half-axes, at every `h ≥ 1`.

| Theorem | Statement |
|---|---|
| `Circ.program_plan`, `Circ.program_qplan` | every OpenAI plan, and every rational plan, is a `PrimeTemplateProgram` with `2·calls` calls and `free·2^{2Ah}` local gates |
| `Circ.target_eq`, `Circ.program_batch` | a `Correct` plan is a program for `W` copies of `H^{⊗2Ah}` |
| `Circ.kernelBatch_of_correct` | OpenAI's batch inequality `PrimeKernelBatch 2 (2A) W (2σ) C (-1)` |
| `walsh_bound_of_plan` | if `2σ/W < (2A)^θ`, then `C(H^{⊗k}) ≤ D·2^k·(1+k)^θ` for all `k`, over every field of characteristic 0 |
| **`walsh_upper`** | for every `ε > 0`: `C(H^{⊗k}) ≤ D·2^k·(1+k)^{1/2+ε}`, via our Theorem 1 template |

### An explicit rate (`FTPaper/Free/`, `LocalCost*.lean`, `ExplicitRecursion.lean`, `ExplicitRate.lean`)

An explicit rate needs an explicit bound on the gates outside calls. In OpenAI's routing the single-row endpoint plans are chosen by `Classical.choose`, so nothing bounds their local cost. `FTPaper/Free/` rederives them with `RealizesF n M := ∃ p, p.calls ≤ n ∧ planFree p = 0 ∧ Implements p M`. The witnesses and identities are OpenAI's (adapted copies, Apache 2.0; see `OAI/NOTICE.md`). Our stage now uses the resulting pencil `geometricPencilF`, with the same semantics (`block_geometricPencilF`) and call bound (`lemmaR1_pencilF`).

| Theorem | Statement |
|---|---|
| `Circ.planFree_geometricPencilF` | the pencil spends at most `20(|free| + |charged| + 1)(m+2)R³` gates per address outside calls |
| `Circ.qfree_fbPlan_le` | the feedback family spends at most `(2K+3)N_d³` |
| `paddedKernelConstantX`, `primeTransform_bound_paddedX` | OpenAI's private padded recursion, made public with its explicit constant |
| `xT_le` | for the template at parameter `x ≥ 12`, the constant is at most `2^{2^{3x}}` |
| **`walsh_explicit_rate`** | for `x ≥ 12` and `log₂(1+k) ≥ 2^{4x}`: `C(H^{⊗k}) ≤ 2^k (1+k)^{1/2 + 3ε(x)}`, `ε(x) = (11√(x log₂ x) + 11)/(x+1)` |
| **`walsh_explicit_rate_k`** | the same with `x = ⌊log₂ log₂(1+k)/4⌋`, whenever `log₂ log₂(1+k) ≥ 48` |
| **`walsh_rate_asymptotic`** | with `ℓ = ⌊log₂ ⌊log₂(1+k)⌋⌋ ≥ 48`: `C(H^{⊗k}) ≤ 2^k (1+k)^{1/2 + 200√(log₂ ℓ / ℓ)}` |
| **`template_floor`** (`Floor.lean`) | if `C(H^{⊗k}) ≥ c·2^k·√k` (OpenAI's lower bound, as a hypothesis), every correct plan has `2σ/W ≥ √(2A)` |
