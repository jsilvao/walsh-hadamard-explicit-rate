# Vendored files

The files under `OAI/` are copied unchanged from https://github.com/openai/math
(directories `lean/OAI/LinearAlgebra/FiniteFourier/` and `lean/OAI/Computability/NearSquareRoot/`, commit `3344da59991ed94f9ba711217b29c1d760badfa6`).
They are licensed under the Apache License 2.0, copyright OpenAI. See
https://github.com/openai/math/blob/main/LICENSE.

They are the import closure of `OAI.Computability.NearSquareRoot.KernelBinaryTemplate` (which contains the earlier closure of `PrimeBatch` and `CircuitParallel`), plus `LinearAlgebra/FiniteFourier/PrimeTemplatePass.lean` for the circuit bridge. That is 156 modules (71 in `Computability/NearSquareRoot`, 85 in `LinearAlgebra/FiniteFourier`), depending only on Mathlib. Every file is byte-identical to the upstream commit.
We use them for OpenAI's circuit model (`complexity`, binary linear gates) and its
composition, batching and Kronecker lemmas. Before vendoring we audited them for
`#eval`, `run_cmd`, `IO`, `initialize`, `unsafe`, `extern`, `implemented_by`,
`native_decide`, `sorry` and `axiom`. None occur.

## Adapted copies outside `OAI/`

Some of OpenAI's proofs are copied, with changes, into our own files (Apache 2.0, same upstream commit):

- `FTPaper/Free/Basic.lean`, `Endpoints.lean`, `Bridge.lean`, `FreeGeometry.lean`, `Charged.lean` and `Pencil.lean` come from `KernelPassFactors`, `KernelPassMonomial`, `KernelPassPartial`, `KernelPassEndpointPair`, `KernelPassEndpoints`, `KernelPassBridge`, `KernelPassFreeGeometry`, `KernelPassCharged`, `KernelPassChargedLabels` and `KernelPassGeometry`. The change: `Realizes` becomes `RealizesF`, which also asks the witness to spend no gates outside calls. Private helpers are copied with an `F` suffix.
- `FTPaper/ExplicitRecursion.lean` comes from `LinearAlgebra/FiniteFourier/PrimeKernel.lean`. The change: the private padded recursion and its constant are public, with an `X` suffix.

Each file states its source and changes in its header.
