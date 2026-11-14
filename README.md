# chenguang-core

Lean 4 formalizations of analytic building blocks: special values and
functional equations for Dirichlet L-functions and the Riemann zeta
function, meromorphic continuation, elliptic-curve slices, and a small
set of standalone probe files on known OEIS / open-problem statements.

Every module in this repository compiles with:

- **zero `sorry`** (no unfinished proofs)
- **zero custom axioms** — `#print axioms` reports only the three
  standard Lean axioms: `propext`, `Classical.choice`, `Quot.sound`

## Requirements

- Lean `v4.34.0` (pinned by `lean-toolchain`)
- mathlib `v4.34.0` (pinned by `lake-manifest.json`)

## Quick start

```bash
git clone <this-repo-url> chenguang-core
cd chenguang-core
lake exe cache get   # download prebuilt mathlib oleans (strongly recommended)
lake build
```

`lake build` builds every module of both libraries. To build one only:

```bash
lake build Base_64        # analytic slices
lake build Bounty_Probe   # standalone probes
```

Without `lake exe cache get`, Lake will build mathlib from source, which
takes hours on a typical machine.

## Layout

```
chenguang-core/
├── lakefile.lean           # two libraries: Base_64, Bounty_Probe
├── lean-toolchain          # Lean v4.34.0
├── lake-manifest.json      # mathlib pinned by commit
├── Base_64.lean            # entry module of the Base_64 library
├── Base_64/                # analytic slices
│   ├── All_Slices.lean     # umbrella file importing every slice
│   ├── Universal_Slice_001..031.lean
│   ├── Zeta_Slice_001..009.lean
│   ├── Elliptic_Slice_001..006.lean
│   ├── BSD_Ext_Slice_001..005.lean
│   └── CompletedLFunctionFE.lean, DirichletMain.lean, GammaLogDeriv.lean, ...
└── Bounty_Probe/           # standalone probes, mathlib-only dependencies
```

## Probes

`Bounty_Probe/` holds six self-contained files. Each depends on mathlib only and
each ends in a `#print axioms` audit that reports the three standard axioms.

| File | Statement |
| --- | --- |
| `ChenGuang_OEIS_A113250.lean` | the odd-indexed terms of OEIS A113250 are perfect squares |
| `ChenGuang_OEIS_A248802.lean` | the least prime factor of `2 ^ (2 ^ (10 * n + 2) + 2) + 3` is `67` |
| `ChenGuang_Erdos_1052.lean` | every unitary perfect number is even (Erdős 1052) |
| `ChenGuang_Erdos_11_Sample_100.lean` | Erdős 11 for every `n ≤ 100` with `4 ∤ n`, by an explicit witness table |
| `ChenGuang_Erdos_91.lean` | Erdős 91: distance-set and minimiser API, abstract lemmas, and `d 1 = 0` |
| `ChenGuang_MahlerPopken_3n.lean` | `‖3 ^ n‖ = 3 * n` for `n ≥ 1` (Mahler–Popken) |

Four of them are complete proofs of the stated theorem: A113250, A248802, Erdős 1052
and Mahler–Popken. Two are honest partial results, and the gap is named in the file
header rather than hidden. Erdős 11 is a finite sample: for each `n ≤ 100` with
`4 ∤ n` the file exhibits a pair `(k, l)` with `k` squarefree and `n = k + 2 ^ l`.
The witnesses are chosen so squarefreeness is *seen* rather than computed (`k` is a
prime, a product of two distinct primes, or `1`), so the certificate is one table of
branches closed by `interval_cases`, with a corollary covering all odd `n ≤ 100`.
Erdős 91 formalises the layer that does not depend on the values of `d 8` and `d 9`:
the distance-set and minimiser vocabulary matching the upstream signatures, the
abstract lemmas every reduction through `d 8` / `d 9` rests on (an upper bound from an
explicit witness, monotonicity under deleting points, and the witness form of failing
uniqueness), and `d 1 = 0`. The two explicit configurations of the reference are not
reproduced, so `d 9 ≤ 4` and `4 ≤ d 9` are both left open, not axiomatised, and no
claim depends on them.

## Axiom audit

The slices carry `#print axioms` commands; after `lake build`, they
report only the three standard axioms listed above. To audit a module
interactively:

```bash
lake env lean Base_64/All_Slices.lean
```

## Scope and honesty notes

Propositions that mathlib does not yet provide the tooling for are
**declared out of scope** in the module header rather than axiomatized
or left as `sorry`. See `Base_64/PrimeNumberTheorem.lean` for an
example: the PNT prerequisites are formalized and verified; the main
assertion ψ(x) ~ x is explicitly marked out of scope.

## License

MIT, Copyright (c) 2026 Chen Yong. See [LICENSE](LICENSE).
