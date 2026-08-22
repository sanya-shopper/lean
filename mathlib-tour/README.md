# mathlib-tour

A small companion to the core-Lean [`primer/`](../primer), showing **what mathlib
buys you**. The primer deliberately uses no mathlib — it builds in seconds and has
zero dependencies. This project pays the cost of mathlib (a large dependency) to
show what that cost purchases: shorter proofs, and theorems core Lean can't even
state.

Everything in `MathlibTour.lean` type-checks; `lake build` is the proof.

## What it shows

| Example | The point |
|---------|-----------|
| `(k+1)*(k+1) = k*k + 2*k + 1 := by ring` | The primer needed a manual `simp only [Nat.succ_mul, Nat.mul_succ]; omega` for this; mathlib's **`ring`** does any commutative-ring identity in one word. |
| `sumOdd_eq` with `ring` | The primer's showcase induction, with the algebra step now a single `ring`. |
| `∑ i ∈ Finset.range n, (2*i+1) = n^2` | Core Lean has no `∑` notation; mathlib has finite sums (`Finset`) and the lemmas to compute them. |
| `Irrational (Real.sqrt 2)` | A statement core Lean cannot express — `Real.sqrt` and `Irrational` are mathlib. The proof is the library's `irrational_sqrt_two`. |
| dice probability in `ℚ` | Honest discrete probability: `\|event\| / \|space\|` as an actual **rational** over a `Finset`, not the integer cross-multiplication the primer used to stay mathlib-free. |

## Build

Pinned to mathlib `v4.33.0` (matching the toolchain in `lean-toolchain`), so it
reuses the Lean 4.33.0 you already have.

```bash
cd mathlib-tour
lake exe cache get     # download mathlib's prebuilt oleans (~6 GB, once)
lake build             # first `import Mathlib` load takes a few minutes
```

Nothing regenerable lands in the repo: mathlib source + its ~6 GB of oleans go to
the shared package store (`../../_lean-packages/v4.33.0`, set as `packagesDir` in
`lakefile.toml`), and build output goes to `../../_buildoutput/lean/mathlib-tour`.
Both are rebuildable caches, not source.
