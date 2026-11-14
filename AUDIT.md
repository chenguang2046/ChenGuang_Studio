# Audit & publication checks

This file records the mechanical checks performed on this repository before
publication. All items are reproducible with plain text search plus `lake build`.

## Hygiene invariants

| Check | Method | Result |
| --- | --- | --- |
| No unfinished proofs | search for `sorry` / `admit` used as terms in all 73 `.lean` files | 0 (remaining hits are prose inside comments) |
| No custom axioms | search for `axiom` / `constant` declarations | 0 declarations |
| No `TODO` markers | search for `TODO` | 0 |
| Axiom audit | `#print axioms` on the main theorem of each probe and on the verified PNT prerequisites | only `propext`, `Classical.choice`, `Quot.sound` |
| No placeholders in headers | search for internal codenames and leftover scaffolding notes | none |

## Contents

- `Base_64/` — 65 `.lean` files: 64 slices, plus `All_Slices.lean` (umbrella) and this directory's `README.md`.
- `Bounty_Probe/` — 6 self-contained probe files, mathlib-only dependencies:

| File | Statement | Build |
| --- | --- | --- |
| `ChenGuang_OEIS_A113250.lean` | odd-indexed terms of OEIS A113250 are perfect squares | ok |
| `ChenGuang_OEIS_A248802.lean` | the least prime factor of `2 ^ (2 ^ (10 * n + 2) + 2) + 3` is `67` | ok |
| `ChenGuang_Erdos_1052.lean` | every unitary perfect number is even (Erdős 1052) | ok |
| `ChenGuang_Erdos_11_Sample_100.lean` | Erdős 11 for every `n ≤ 100` with `4 ∤ n`, by an explicit witness table | ok |
| `ChenGuang_Erdos_91.lean` | Erdős 91: distance-set and minimiser API, abstract lemmas, `d 1 = 0` | ok |
| `ChenGuang_MahlerPopken_3n.lean` | `‖3 ^ n‖ = 3 * n` for `n ≥ 1` (Mahler–Popken) | ok |

## Axiom audit detail

`lake build Bounty_Probe` followed by `#print axioms` on the main statement of each
file reports, for all six files,

```
[propext, Classical.choice, Quot.sound]
```

The same three axioms are what the slices in `Base_64/` report.

## Scope discipline

Statements whose tooling is absent from mathlib v4.34.0 are declared out of
scope in the module header. They are neither axiomatized nor left as `sorry`.
See `Base_64/PrimeNumberTheorem.lean`: the PNT prerequisites are formalized and
verified, while the main asymptotic assertion is explicitly marked out of scope.

`ChenGuang_Erdos_11_Sample_100.lean` proves the finite sample `n ≤ 100` only, and
proves it by exhibiting one witness pair `(k, l)` per `n` (`k` squarefree,
`n = k + 2 ^ l`), the squarefreeness of `k` being visible from its shape; the general
statement of Erdős 11 remains open and is not claimed here.

`ChenGuang_Erdos_91.lean` proves only the layer independent of the values of `d 8` and
`d 9`: the distance-set and minimiser definitions mirroring the upstream signatures,
the abstract lemmas used by every reduction through `d 8` / `d 9`
(`minimalDistinctDistances_le_of_witness`, `distinctDistances_mono`,
`minimalDistinctDistances_monotone_of_witness`, `not_uniqueMinimizer_iff`), and
`d 1 = 0`. The explicit configurations of the reference are not reproduced, so
`d 9 ≤ 4` and `4 ≤ d 9` are both open; neither is axiomatized nor assumed.

## Build

```bash
lake exe cache get
lake build
```

`Bounty_Probe` was built and verified against mathlib v4.34.0. `Base_64` requires
the full prebuilt mathlib cache (`lake exe cache get`) because several imported
mathlib modules are distributed only as cached `.olean.private` files, which a
partial local cache cannot satisfy; this is an environment prerequisite, not a
defect in the slices.

## License

MIT, Copyright (c) 2026 Chen Yong. See [LICENSE](LICENSE).
