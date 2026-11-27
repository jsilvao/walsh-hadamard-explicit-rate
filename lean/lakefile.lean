import Lake
open Lake DSL

/-! Formalization companion for the notes in `../notes/`.
Toolchain and Mathlib are pinned to the same versions as `openai/math/lean`
(Lean v4.34.1, Mathlib d13f23b7), so the files can later be ported into that library
or checked by the Big O Speedrun verifier. -/

package FTPaper where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

/-- Vendored modules from `openai/math` (Apache 2.0), see `OAI/NOTICE.md`. -/
lean_lib OAI where
  globs := #[.submodules `OAI]

@[default_target]
lean_lib FTPaper where
