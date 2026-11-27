# An explicit rate for the logarithmic exponent of the Walsh–Hadamard transform

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24575295.svg)](https://doi.org/10.5281/zenodo.24575295)

OpenAI's manuscript *The logarithmic exponent of finite Fourier transforms* (November 2026) proves, for the Walsh–Hadamard transform on N points, a lower bound of `c·N·√(log N)` gates and, for every ε > 0, an upper bound of `C_ε·N·(log N)^(1/2+ε)`. It does not quantify the `o(1)` in the exponent.

This repository makes that `o(1)` explicit over fields of characteristic 0 and checks every step in Lean 4:

> For every field `K` of characteristic 0 and every `k` with `ℓ = ⌊log₂⌊log₂(1+k)⌋⌋ ≥ 48`,
> `C_K(H^{⊗k}) ≤ 2^k (1+k)^{1/2 + 200·√(log₂ℓ / ℓ)}`.
>
> Lean: `FTPaper.walsh_rate_asymptotic`.

- **Paper:** [`paper/latex/main.pdf`](paper/latex/main.pdf), source in `paper/latex/`.
- **Lean development:** [`lean/`](lean/), pinned to Lean v4.34.1 and Mathlib `d13f23b7`, the same pins as openai/math.
- **Archived on Zenodo:** [10.5281/zenodo.24575295](https://doi.org/10.5281/zenodo.24575295) (all versions; v1.0.1 is [10.5281/zenodo.24575296](https://doi.org/10.5281/zenodo.24575296)).

## Checking the proofs

```sh
cd lean
lake exe cache get                  # prebuilt Mathlib
lake build                          # about 9,100 jobs
lake env lean CheckAxioms.lean      # axioms of the 104 named results
```

Every result depends only on `propext`, `Classical.choice` and `Quot.sound`. The main statements are about OpenAI's definitions `complexity` (least number of binary linear gates) and `primeTransform`. Appendix A of the paper quotes those definitions and the main statements.

## Contents

- `lean/FTPaper/`: our development, about 6,500 lines.
- `lean/OAI/`: 156 modules of [openai/math](https://github.com/openai/math), unchanged. They are © OpenAI under Apache-2.0; see `lean/OAI/NOTICE.md`. The files `lean/FTPaper/Free/` and `lean/FTPaper/ExplicitRecursion.lean` are adapted copies of OpenAI code, and each file states its source and changes.
- `paper/latex/`: the paper.

## Use of AI tools

This work was developed with extensive use of Claude (Anthropic); see the statement in the paper. OpenAI's manuscript was itself produced by an AI model.

## License

Apache-2.0 (`LICENSE`).
