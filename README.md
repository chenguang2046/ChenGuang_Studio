# analytic_core
A Lean 4 formalisation library. 99 standalone slices, each self-contained, each build-verified.
## What this is
analytic_core is a library of 99 independent formalisation slices — 64 base slices and 35 challenge slices — written in Lean 4 against mathlib.
Each slice is self-contained. No slice imports another slice as a foundation. There is no shared dependency layer above mathlib itself. Every slice can be compiled, read, checked, or replaced on its own.
This is a deliberate design choice, not an artefact of how the library grew. A library whose parts depend on one another can only be verified as a whole: one broken piece and nothing builds. Here each slice stands or falls alone, and the total can be inspected piece by piece.
## Status
The base layer is complete and compiles clean.
The connecting passage — the part that carries structure across the slices rather than beside them — is in progress. This repository contains what is built, not what is planned.
## Requirements
- Lean 4.34.0 (lean-toolchain pins leanprover/lean4:v4.34.0)
- mathlib v4.34.0 (pinned in lakefile.toml, locked in lake-manifest.json)
## Build
```bash
lake exe cache get     # fetch mathlib oleans, first run only
lake build             # build the default targets
```
To check the full collection directly:
```
lake env lean Slices_99/All_Slices.lean
lake env lean Base_64/All_Slices.lean
```
Both are expected to exit with code 0.
Layout
.
├── lakefile.toml
├── lean-toolchain
├── lake-manifest.json
├── LICENSE
├── Slices_99/
│   ├── All_Slices.lean    # imports the full collection
│   ├── lakefile.toml
│   ├── Universal_Slice_001 … 031
│   ├── Zeta_Slice_001 … 010
│   ├── Elliptic_Slice_001 … 006
│   ├── Elliptic_Ext_Slice_001 … 005
│   ├── Analytic_Check.lean
│   └── Challenge_*.lean   # 35 challenge slices
└── Base_64/
    ├── All_Slices.lean
    └── base slices and toolchain
Correctness
No sorry, no admit, no axiom declarations anywhere in the library.
Axiom audit over the compiled collection reports only the three standard axioms:
propext, Classical.choice, Quot.sound
A small number of early slices additionally depend on Lean.ofReduceBool through native_decide. Every such occurrence is listed in Slices_99/AXIOMS.md with its file and line. Nothing is hidden behind a blanket claim.
Scope
This repository formalises a base layer. It does not assert the resolution of any open problem, and no part of it should be read as such an assertion. What it offers is a checked foundation: statements that compile, proofs that close, and a structure that can be inspected without trusting the author.
If a claim is not in this repository as compiling Lean code, it is not being made.
Licence
MIT. Copyright (c) 2026 Chen Yong. See LICENSE.
