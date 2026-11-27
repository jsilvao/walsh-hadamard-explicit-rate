# The paper (LaTeX)

`main.tex` and `references.bib` build `main.pdf` (17 pages). Every theorem, proposition, lemma and corollary in it has a Lean proof, and the Lean names follow each statement.

## Template

ACM's `acmart` class with the options `acmsmall,nonacm`:
- `acmsmall` is ACM's single-column journal layout, the format of ACM Transactions on Computation Theory (TOCT).
- `nonacm` removes ACM's copyright block and reference-format box, so the arXiv version does not look like an ACM publication.

To switch targets:
- **ACM journal (for example TOCT):** remove `nonacm`. Then add the CCS concepts (`\begin{CCSXML}…`, `\ccsdesc`) and the journal metadata ACM asks for at submission. The body stays the same.
- **CCC (LIPIcs):** move the body into the `lipics-v2021` class. Only the preamble and front matter change.

## Build

```sh
latexmk -pdf main.tex
```

This needs `acmart`, `fancyvrb` and `array`, which are in TeX Live and MiKTeX.

`./make-arxiv.sh` builds `arxiv-upload.tar.gz` (`main.tex` + `main.bbl`). That archive is the arXiv upload. arXiv does not run BibTeX, so the `.bbl` file must be included.

## Before submitting: things only the author can do

1. **Read the whole paper.** arXiv holds the author fully responsible for everything in it, however it was produced.
2. **Check every reference yourself.** Each entry in `references.bib` was checked on 2026-11-27 against a DOI, publisher or archive record:
   - OpenAI, *The logarithmic exponent of finite Fourier transforms*, github.com/openai/math, preprint of 2026-11-24. The cited numbers (Thm 1.1, Lemmas 4.2–4.4, §4.1–4.2, §5.1–5.4, p. 2) were checked against its PDF.
   - OpenAI, openai/math repository README, for the "raw research data" description.
   - Big O Speedrun verifier PR #223, merged 2026-11-25.
   - Alman and Rao, STOC 2023, doi:10.1145/3564246.3585188.
   - Morgenstern, JACM 20(2):305–306, 1973.
   - Hoeffding, JASA 58(301):13–30, 1963.
   - de Moura and Ullrich, CADE-28, LNCS 12699, pp. 625–635, 2021.
   - The mathlib Community, CPP 2020, pp. 367–381.
   - Proctor, SIAM J. Algebraic Discrete Methods 3(2):275–280, 1982, doi:10.1137/0603026 (added for version 2).
   - Go, European Journal of Combinatorics 23(4):399–429, 2002 (added for version 2).
   - MacWilliams and Sloane, *The Theory of Error-Correcting Codes*, North-Holland Mathematical Library 16, 1977 (added for version 2).
3. **The "Use of AI tools" section** must be accurate when you submit. arXiv requires significant use of generative AI to be reported, and AI tools cannot be authors.
4. **arXiv categories.** Primary `cs.CC` (Computational Complexity). `cs.LO` (Logic in Computer Science) is a reasonable cross-list for the formalization. A first-time submitter needs a personal endorsement from an established author in `cs`.
5. **The repository** is public: https://github.com/jsilvao/walsh-hadamard-explicit-rate.

## Numbering: working labels → this paper

`lean/README.md` and some Lean docstrings use working labels for the results. This table maps them to the paper's numbering.

| working label | paper |
|---|---|
| Claim 2 (sharper rate, `Claim2/Rate.lean`) | Theorem 1.1 |
| Theorem 5 (explicit rate, fixed template) | Theorem 1.2 |
| Corollary 1′ (circuit form) | Corollary 1.3 |
| Theorem 1 (one level) | Theorem 1.4 |
| comparison with OpenAI's stage count | Proposition 1.5 |
| polynomial local cost (`Claim2/Level.lean`) | Theorem 1.6 |
| Theorem 3 (limits) | Theorem 1.7 |
| OpenAI's padded recursion, explicit constant | Lemma 2.1 |
| Lemma A (predictor) | Lemma 3.1 |
| Lemma B (two-pass repair) | Lemma 4.1 |
| Lemma C (feedback) | Lemma 5.1 |
| Lemma R1 (one stage) | Lemma 7.1 |
| Corollary R2 (routing parameters) | Corollary 7.2 |
| dyadic impossibility (`Dyadic.lean`) | Proposition 7.3 |
| compilation into circuits (`QCircuit.lean`) | Lemma 8.1, Corollary 8.2 |
| local-cost bounds (`LocalCost*.lean`) | Lemma 8.3 |
| Lemma S: checks on the tails (`LemmaS/Injective.lean`) | Lemma 9.1 |
| Lemma S: decoder polynomial (`LemmaS/Decoder.lean`) | Lemma 9.2 |
| fast transform (`LemmaS/Butterfly.lean`) | Lemma 9.3 |
| structured table (`LemmaS/BlockTable.lean`, `Claim2/Table.lean`) | Lemma 9.4 |
| sparse compilation (`Claim2/Sparse.lean`) | Lemma 10.1 |
| row-diagonal pencil (`Claim2/SparsePencil.lean`, `PencilCost.lean`) | Lemma 10.2 |
| one step of the growing recursion (`Claim2/RateStep.lean`) | Lemma 11.1 |
