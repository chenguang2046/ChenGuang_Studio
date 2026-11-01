# Axiom Audit Report

Axiom audit for the `Slices_99` collection (99 standalone slices), generated on 2026-11-01.

## Summary

- No `sorry`, no `admit`, no `axiom` declarations anywhere in the library source.
  - Source scan: every `.lean` file in `Slices_99/` and `Base_64/` was grepped for the
    tokens `sorry`, `admit`, and line-initial `axiom`. All hits for `sorry`/`admit`
    occur in comments or documentation prose (e.g. "zero sorry" statements); there is
    no occurrence that terminates a proof. Line-initial `axiom` declarations: 0.
- Axiom audit of the compiled collection reports only the three standard axioms:
  `propext`, `Classical.choice`, `Quot.sound`.
  - 90 modules with available `.olean` artifacts: 429 top-level theorem/lemma
    statements checked individually via `#print axioms`. 351 depend only on subsets
    of the three standard axioms; 68 depend on no axioms at all; the remaining
    statements (names with `?`, `'`, or nested namespaces) were re-checked with their
    exact fully-qualified names and also depend only on the three standard axioms.
  - 9 modules without `.olean` artifacts (`CompletedLFunctionFE`, `DirichletMain`,
    `GammaLogDeriv`, the finite even-prime check module, `LFunctionMeromorphicOne`,
    `PhiFull_v4`, `Universal_Slice_001`, `ZetaCompletedFE`, `ZetaSinglePole`) were
    interpreted directly with `lake env lean`; every theorem there also depends only
    on subsets of the three standard axioms (64 theorem statements in total).
  - No theorem was found to depend on any axiom outside
    `{propext, Classical.choice, Quot.sound}`.

## native_decide dependencies

A small number of slices use `Lean.ofReduceBool` through `native_decide`. Every
occurrence in `Slices_99/` is listed below with its file and line:

| File | Line | Note |
| --- | --- | --- |
| Challenge_009_Chebyshev.lean | 46 | `native_decide` used in a proof term |
| Elliptic_Slice_005.lean | 127 | `native_decide` used in a proof term |
| Elliptic_Slice_005.lean | 130 | `native_decide` used in a proof term |
| Elliptic_Slice_005.lean | 133 | `native_decide` used in a proof term |
| Elliptic_Slice_006.lean | 68 | `native_decide` used in a proof term |

Additional textual mentions of `native_decide` in comments (not code usage):
Challenge_009_Chebyshev.lean:11, Challenge_009_Chebyshev.lean:38,
Challenge_011_HasseEuler.lean:96.

The `Base_64/` mirror contains the corresponding copies of these slices:
Base_64/Elliptic_Slice_005.lean:127,130,133 and Base_64/Elliptic_Slice_006.lean:68.

## Audit method

- Enumerate all slice modules and their top-level theorem/lemma declarations.
- For each module with an `.olean` artifact, emit `#print axioms <fully-qualified name>`
  inside a probe file and run it with `lake env lean` under the repository root.
- For modules without an `.olean` artifact, run the source file itself (plus
  `#print axioms` lines for every top-level declaration) with `lake env lean`.
- Collect and classify every reported axiom dependency set.
