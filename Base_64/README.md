# Base_64

Lean 4 + mathlib formalizations of 64 foundational slices: no `sorry` / `admit`, and `#print axioms`
reports only the three standard axioms.

## Overview

`Base_64` is the 64-slice foundational subset of the `chenguang-core` repository. Every slice is
accepted by the Lean kernel, contains no `sorry` / `admit`, and its `#print axioms` audit reports
only the three standard axioms:

```
propext, Classical.choice, Quot.sound
```

## Requirements

- Lean 4.34.0 (`lean-toolchain` pins `leanprover/lean4:v4.34.0`)
- mathlib v4.34.0

## Layout

```
Base_64/
|-- All_Slices.lean        # umbrella module importing all 64 slices
|-- lean-toolchain         # pinned Lean toolchain
|-- Universal_Slice_001.lean ... Universal_Slice_031.lean  # 31 universal slices
|-- Zeta_Slice_001.lean ... Zeta_Slice_009.lean            # 10 zeta slices (incl. 002B)
|-- Elliptic_Slice_001.lean ... Elliptic_Slice_006.lean    # 6 elliptic-curve slices
|-- BSD_Ext_Slice_001.lean ... BSD_Ext_Slice_005.lean      # 5 extended slices
+-- GoldbachCheck.lean, PhiFull_v4.lean, ...               # remaining foundational slices
```

## Usage

Toolchain and dependencies are pinned by `lean-toolchain` / `lake-manifest.json`. From the
repository root:

```bash
lake exe cache get   # fetch prebuilt mathlib cache (recommended, saves hours)
lake build           # build all modules of Base_64 and Bounty_Probe
```

Build this sub-library only:

```bash
lake build Base_64
```

Axiom audit: after building, run `#print axioms` on the target modules (audit commands are
already included in `All_Slices.lean` and individual slices). All slices are expected to report
only the standard axioms listed above.

## License

Released under the MIT License, Copyright (c) 2026 Chen Yong. See [LICENSE](../LICENSE) in the
repository root.
