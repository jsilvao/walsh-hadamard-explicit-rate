# An explicit rate for the logarithmic exponent of the Walsh–Hadamard transform

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24575295.svg)](https://doi.org/10.5281/zenodo.24575295)

OpenAI's manuscript *The logarithmic exponent of finite Fourier transforms* (November 2026) proves, for the Walsh–Hadamard transform on N points, a lower bound of `c·N·√(log N)` gates and, for every ε > 0, an upper bound of `C_ε·N·(log N)^(1/2+ε)`. It does not quantify the `o(1)` in the exponent.

This repository makes that `o(1)` explicit over fields of characteristic 0 and checks every step in Lean 4:

> For every field `K` of characteristic 0 and every `k`,
> `C_K(H^{⊗k}) ≤ 2^k · √(k+1) · 2^{Φ(n)}` with `n = ⌊log₂(k+1)⌋` and `Φ(n) = 400·√((n+2)·log₂(n+2))`.
>
> That is, `C_K(H^{⊗k}) ≤ N (log N)^{1/2 + O(√(log log log N / log log N))}` for `N = 2^k`.
>
> Lean: `FTPaper.Claim2.walsh_claim2`.

The first version of the paper (v1.x) proved the weaker `N (log N)^{1/2 + O(√(log⁽⁴⁾N / log⁽³⁾N))}` with a fixed template (`FTPaper.walsh_rate_asymptotic`, still included as Theorem 1.2). Version 2 lets the template grow with `N`. For that, the work outside recursive calls had to become polynomial in the number of queries: the repair now uses character checks on the two Hamming tails with a polynomial decoder, and OpenAI's routing pencil is rebuilt to touch only the entries it needs.

- **Paper:** [`paper/latex/main.pdf`](paper/latex/main.pdf), source in `paper/latex/`. Paper DOI: [10.5281/zenodo.24575298](https://doi.org/10.5281/zenodo.24575298) (always the latest version).
- **Lean development:** [`lean/`](lean/), pinned to Lean v4.34.1 and Mathlib `d13f23b7`, the same pins as openai/math.
- **Archived on Zenodo:** [10.5281/zenodo.24575295](https://doi.org/10.5281/zenodo.24575295) (all versions; v2.0.0 is [10.5281/zenodo.24600561](https://doi.org/10.5281/zenodo.24600561), v1.0.1 is [10.5281/zenodo.24575296](https://doi.org/10.5281/zenodo.24575296)).

## Checking the proofs

```sh
cd lean
lake exe cache get                  # prebuilt Mathlib
lake build                          # about 9,100 jobs
lake env lean CheckAxioms.lean      # axioms of the 143 named results
```

Every result depends only on `propext`, `Classical.choice` and `Quot.sound`. The main statements are about OpenAI's definitions `complexity` (least number of binary linear gates) and `primeTransform`. Appendix A of the paper quotes those definitions and the main statements.

## Contents

- `lean/FTPaper/`: our development, about 11,900 lines in 58 files.
- `lean/OAI/`: 156 modules of [openai/math](https://github.com/openai/math), unchanged. They are © OpenAI under Apache-2.0; see `lean/OAI/NOTICE.md`. The files `lean/FTPaper/Free/`, `lean/FTPaper/ExplicitRecursion.lean`, `lean/FTPaper/Claim2/SparsePencil.lean` and `lean/FTPaper/Claim2/Sparse.lean` adapt OpenAI code, and each file states its source and changes.
- `paper/latex/`: the paper.

## Use of AI tools

This work was assisted by Claude (Anthropic); see the statement in the paper, which describes the author's role. OpenAI's manuscript was itself produced by an AI model.

## License

Apache-2.0 (`LICENSE`).
