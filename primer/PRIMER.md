# A Conceptual Primer on the Lean 4 Theorem Prover

*For a reader with a strong math and software-engineering background who has
never used an interactive theorem prover. Companion runnable examples live in
`Primer/*.lean`; see `README.md` to build and run them.*

> **The canonical, expanded version of this primer is the typeset PDF**
> (`../lean-primer.pdf`, built from `../lean-primer.tex`): it adds a
> proof-checking diagram, worked code throughout, a section on Lean's C FFI and
> editor support, the proved Josephus example, and a cited bibliography. This
> Markdown is the lighter mirror.

## 1. What Lean 4 actually is

Lean 4 is two things wearing one coat: a **dependently-typed functional
programming language** and an **interactive theorem prover (ITP)** — a tool in
which a human writes proofs step by step while the machine checks each move.
Crucially, it is *the same language* for both jobs. You do not switch from a
"programming dialect" to a "proof dialect"; you write ordinary functions and you
write proofs using the same syntax, type system, and tooling.

This unification rests on the **Curry–Howard correspondence**, the observation
that logic and computation are two views of one structure. Under it, a
*proposition* (a mathematical statement) is a *type*, and a *proof* of that
proposition is a *term* (a value) of that type — that is, a program. "Every
natural number has a successor" is a type; a proof is a function producing the
required data. Consequently, **type-checking is proof-checking**: to confirm a
proof is valid, Lean checks that the term really has the claimed type, exactly
as a compiler checks that `add` has type `Int → Int → Int`. A theorem with no
valid term simply cannot be constructed and type-checked.

What makes this trustworthy is Lean's **small trusted kernel**: a compact,
carefully audited core that does nothing but verify that fully-elaborated terms
inhabit their stated types. All the convenient machinery — tactics, automation,
syntax sugar — runs *outside* the kernel and ultimately emits a term the kernel
re-checks. So you can use elaborate, even buggy, automation without endangering
soundness: a wrong proof produces a term the kernel rejects. The trust you must
extend is limited to that small piece, not the vast surrounding toolchain.

To make "dependently-typed functional programming language" concrete: the
functional half is ordinary functions, recursion, and algebraic data types,

```lean
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
```

and the dependent half lets a *type mention a value*, so the type-checker (not a
runtime check) enforces, e.g., that `Vector.append : Vector α m → Vector α n →
Vector α (m + n)` really does produce a vector of length `m + n`. Because types
can talk about values, a type can *be* a theorem — and proving it means building
a term of that type, which the kernel then checks:

```lean
theorem two_plus_two : 2 + 2 = 4 := by rfl        -- `by …` runs tactics that
theorem succ_gt (n : Nat) : n < n + 1 := by omega  -- assemble the proof term
```

That is all "theorem prover" means operationally: **proving = constructing a
term; checking = type-checking that term** against the proposition-as-type.

## 2. Lean vs. TLA+

If you know TLA+, the contrast sharpens the picture, because the two tools answer
*different questions*.

**TLA+** is a *specification language*. You model a system — often a concurrent
or distributed one — as a state machine evolving over time, and you state
properties in temporal logic (invariants that must always hold, liveness
properties that must eventually hold, refinement between an abstract and a
concrete design). You then check those properties primarily by **model
checking**: the TLC checker exhaustively explores a *finite* state space and
reports a concrete counterexample trace if a property fails. (TLA+ also has
TLAPS, a proof system, but model checking is the dominant workflow.) TLA+ shines
at finding subtle design bugs in protocols, invariants, and interleavings —
bounded, automatic, counterexample-producing.

**Lean** is a *foundational proof assistant plus programming language*. You do
not primarily explore states; you **prove** statements deductively about
(possibly infinite) mathematical objects, and you can also write verified
programs. Lean has no built-in temporal logic and no automatic state-space
exploration. A theorem like "for *all* natural numbers `n`, this property holds"
is established by deduction — induction, rewriting, algebra — not by trying
cases.

The mental shift is this: TLA+/TLC is **bounded, automatic, and finds
counterexamples** by exhaustive finite search; Lean is **unbounded,
manual-plus-tactic-assisted, and yields no counterexamples** unless you
deliberately search for them. Lean can *feel* a little model-checker-ish for
finite, decidable propositions — `#eval` runs code, and `decide`/`native_decide`
settle decidable claims by actual computation — but this is evaluation of a
decision procedure, not state-space exploration of a temporal spec.

Reach for **TLA+** when the question is "does my concurrent/distributed design
have a bad interleaving or a broken invariant?" Reach for **Lean** when the
question is "is this statement true for all inputs, and can I build a
machine-checked proof?" — or when you want a program that carries a proof of its
own correctness.

## 3. Lean vs. Haskell

For a Haskell or ML programmer, Lean will feel familiar at first, which makes it
a good stepping stone. The shared vocabulary is large: both are pure functional
languages with **type classes** (Lean calls them the same), **algebraic data
types**, **`do` notation**, **monads**, and strong **type inference**.

The differences are where Lean's power lives. First, Lean has **full dependent
types**: types may depend on *values*. `Vector α n` — a list of `α` with length
`n` in its type — is a routine Lean type, letting the type system enforce that
concatenation produces length `m + n`. Haskell approximates this only with heavy
extensions. Second, Lean functions are **total by default**: the system performs
termination checking, so a "function" that might loop forever or crash on some
input is rejected unless you opt out. Haskell, by contrast, embraces laziness and
partiality — `undefined` and non-termination inhabit every type. Totality is not
pedantry here: a partial "proof" would be worthless, so totality is what lets a
function double as a proof. Third, precisely because types can encode
propositions, Lean's types **can express theorems**, which Haskell's cannot in
any practical sense.

And Lean is a *real* programming language, not a proof toy: it compiles to C and
produces efficient executables, and Lean itself is largely written in Lean. So
the verified programs you write are genuinely runnable, not merely models.

## 4. The proof experience

Proofs come in two intertwined styles. **Term mode** builds the proof term
directly, like writing an expression: you literally hand Lean a value of the
proposition's type. **Tactic mode** — the more common style for nontrivial
proofs — instead runs a sequence of *tactics*, small commands that transform the
proof state, and Lean assembles the underlying term for you behind the scenes.

The experience is interactive. As your cursor rests inside a proof, the editor's
**infoview** displays the current **goal state**: the hypotheses you currently
have (the "context") and the proposition you still must prove. Each tactic you
write updates this display, so you are always looking at what remains to be done.
**Tactics** are the moves. A conceptual sampling: `rfl` closes a goal that holds
"by reflexivity" (both sides compute to the same thing); `simp` simplifies using
a database of rewrite rules; `decide` settles a decidable proposition by running
its decision procedure; `induction` performs structural induction; `omega` is a
decision procedure for linear arithmetic over integers and naturals. You do not
memorize these so much as reach for the one that fits the goal in front of you.

Finally, `sorry` is a **hole**: a placeholder that admits any goal without proof.
It lets you sketch a proof's structure and fill gaps later — but Lean loudly
warns that a `sorry` remains, because such a proof is not actually complete.

## 5. mathlib

**mathlib** is the community-maintained mathematical library for Lean: a very
large, coherent body of formalized mathematics — algebra, analysis, topology,
number theory — together with the lemmas, type-class hierarchies, and automation
tuned to work with them. It matters because serious mathematical proofs rest on
mountains of prerequisite results; mathlib supplies them already proven and
integrated, so you build on a foundation rather than reconstructing it.

The tradeoff is weight. mathlib is a **large dependency** that takes time to
build and pulls in a lot of structure. For small verification experiments —
proving facts about your own data structures or a numeric kernel — you often do
**not** need it; core Lean together with the standard library (Std / **Batteries**)
is enough and far lighter. (The runnable examples in this primer use *no*
mathlib for exactly this reason.) Pull mathlib in when your work genuinely leans
on established mathematics.

## 6. Where Lean fits for verifying your own code

Be clear-eyed about what Lean does and does not do for software verification.
Lean is **excellent** for proving properties of *pure functions*, for
establishing *algorithmic and data-structure invariants*, and for verifying
*math-heavy kernels* — a sorting routine, a balanced-tree operation, a
cryptographic or numeric core — that you **re-implement or model in Lean**. There
you can prove, for all inputs, that the output satisfies its specification.

What Lean is **not** is a push-button verifier for an *arbitrary existing* Rust,
Python, or C codebase. It will not ingest your repository and certify it.
Automatically discharging verification conditions over existing imperative code
is more the domain of **SMT**-backed tools — *Satisfiability Modulo Theories*
solvers that automatically decide formulas in arithmetic, arrays, and the like —
as used by **Dafny** or **Why3**, or of model checkers such as TLA+. Lean's
automation is real but not magic; expecting it to prove your Rust correct "for
free" will disappoint. The productive framing is: port or model the critical
piece into Lean, verify it there, and treat that as the trustworthy specification
or reference.

## 7. How the pieces fit

The through-line is the Curry–Howard identity of *programs and proofs*, enforced
by a *small kernel* and made pleasant by *elaboration*, *tactics*, and the
*infoview*. Everything else — dependent types, totality, type classes, mathlib —
serves that identity: dependent types let a value's properties live in its type,
totality makes functions safe to read as proofs, and mathlib supplies the
mathematics to build on. Placed among its neighbors, Lean answers "is this true
for all cases, provably?" where TLA+ answers "does this design misbehave in some
reachable state?" and Haskell answers "can I write this program elegantly?" —
three overlapping but distinct questions.

### Glossary

- **Kernel** — the small, trusted core that checks whether a term has its claimed
  type; the only component that must be trusted for soundness.
- **Term** — a value/program; under Curry–Howard, also a proof.
- **Proposition** — a statement to be proved; realized as a type whose terms are
  its proofs.
- **Tactic** — a command that transforms the proof state, used to build a proof
  term interactively (e.g. `simp`, `induction`, `omega`).
- **Dependent type** — a type that depends on a value (e.g. length-indexed
  vectors), the feature that lets types express theorems.
- **`Prop` vs `Type`** — `Prop` is the universe of propositions (proofs are
  interchangeable, "proof-irrelevant"); `Type` is the universe of ordinary data.
  Both are kinds of `Sort`.
- **`Sort`** — the overarching universe hierarchy; `Prop` and the `Type` levels
  are its inhabitants.
- **`decide`** — a tactic that proves a decidable proposition by running its
  decision procedure.
- **`Decidable`** — a type class marking propositions for which an algorithm can
  compute true/false, enabling `decide`.
- **Elaboration** — the process that turns concise surface syntax (with implicit
  arguments, tactics, inference) into a fully explicit term the kernel can check.
- **mathlib** — the large community library of formalized mathematics for Lean.
- **elan / lake** — the toolchain manager (`elan`, which installs and selects
  Lean versions) and the build system/package manager (`lake`).
