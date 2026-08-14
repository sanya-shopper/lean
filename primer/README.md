# Lean 4 primer & cookbook

A hands-on companion to `PRIMER.md`. Everything here is **plain Lean 4 (v4.33.0),
no mathlib** — it builds in seconds and works offline. The four chapters are
real, type-checked Lean; `lake build` is the proof that every example and every
theorem in them actually goes through.

## Prerequisites

You already have the toolchain (verified on this machine):

```
elan 4.2.3    lean 4.33.0    lake 5.0.0
```

If you ever need it elsewhere: install [`elan`](https://github.com/leanprover/elan)
(the Lean toolchain manager), and it fetches the version pinned in
`lean-toolchain` automatically.

## Build and run

```bash
cd primer
lake build                        # type-checks ALL chapters = checks all proofs
lake env lean Primer/Basics.lean  # run one chapter, printing its #eval/#check output
```

A clean `lake build` exit code of 0 means every theorem in the project is
proved — there is no separate "test" step, because in Lean *the build is the
verification*. (The `#eval` lines also serve as executable spot-checks.)

## The four chapters

| File | What it teaches |
|------|-----------------|
| `Primer/Basics.lean` | Definitions, functions, recursion, algebraic data types, structures, `#eval`/`#check`. The programming-language half of Lean. |
| `Primer/Proofs.lean` | Propositions as types; the workhorse tactics `rfl`, `decide`, `simp`, `omega`, `induction`; `sorry` as a hole. |
| `Primer/BitVec.lean` | Fixed-width `BitVec 32` arithmetic — modular add, XOR/AND/NOT, rotation — and the actual SHA-256 building blocks (`Ch`, `Maj`, `Sigma0/1`, `sigma0/1`). Where `decide` stops and SAT (`bv_decide`) begins. |
| `Primer/Spec.lean` | The **verify-your-own-code** workflow: an invariant that travels with the data as a proof, a monotonicity theorem, and a fast implementation proved equal to a reference model. |
| `Primer/Diff.lean` | The atom of differential cryptanalysis: XOR/AND/modular-add difference algebra (exact vs data-dependent) and why *checking* a collision is trivial while *reasoning* about it is the content. Ties to the survey. |
| `Primer/Josephus.lean` | A real theorem, proved: the Josephus closed form `J(2^m+l)=2l+1` from Knuth's *Concrete Mathematics*, three formulations machine-checked to agree, with the "rotate the binary numeral left by one bit" view echoing `rotr`. |
| `Primer/Probability.lean` | Discrete probability as exact counting (no mathlib): Monty Hall (switching wins 2/3), de Méré's 1654 problem, and the birthday paradox threshold (exactly 23 people, via `native_decide` on ~60-digit `Nat`s). |

## Cookbook: recipes you can copy

**Evaluate an expression.** `#eval (List.range 10).map (· * 2)`

**Check a type without running.** `#check List.map`

**Prove something true by computation.** `example : 2 + 2 = 4 := by rfl`

**Prove a decidable fact by brute force.** `example : 7 * 6 = 42 := by decide`

**Prove linear arithmetic.** `example (a b : Nat) : a + b = b + a := by omega`

**Prove a `∀` statement by induction.** See `length_map` in `Proofs.lean`.

**Verify a fast function equals a reference.** See `sumTo_correct` in `Spec.lean`
— the general pattern for "my optimized version matches the obvious one."

**Reason about 32-bit machine words (crypto).** See `BitVec.lean`. For facts
quantified over *all* `2^32` words, `decide` is too slow; the tactic is
`bv_decide` (bitblast to SAT, check an LRAT certificate), which needs
`import Std.Tactic.BVDecide` (bundled with the toolchain).

## How this maps to "verifying properties of my projects"

The realistic loop, illustrated by `Spec.lean`:

1. **Model** the pure core of your algorithm/data structure as Lean functions
   (or re-implement it directly in Lean).
2. **State** the properties you care about as `theorem`s.
3. **Prove** them — leaning on `simp`/`omega`/`decide` first, hand-guiding only
   what automation can't close. `#eval` gives you a fast spot-check loop while
   you work.

Lean will not ingest an existing Rust/Python/C repo and certify it (that's the
domain of SMT tools like Dafny/Why3 or model checkers like TLA+ — see
`PRIMER.md` §6). Its sweet spot is a critical pure kernel you model in Lean and
prove correct for *all* inputs.

## Next steps

- **Add mathlib** when you need real mathematics: add a `require mathlib`
  dependency in your `lakefile` (heavier build, but the vast library becomes
  available). Fetch prebuilt oleans with `lake exe cache get` to avoid a long
  compile.
- **Editor**: VS Code + the Lean 4 extension gives you the live **infoview**
  (the goal state as you move your cursor), which is the single biggest ergonomic
  jump over the CLI.
- **`bv_decide` for crypto**: add `import Std.Tactic.BVDecide` and try the
  32-bit identities noted in `BitVec.lean`.
