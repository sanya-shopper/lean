/-
Primer 4 — Spec & verify: the workflow you'd use on your own code.

The realistic pattern for "verify a property of my project" in Lean is:
  1. Model the algorithm/data structure as pure Lean functions (a *reference
     model*), or re-implement the pure core directly in Lean.
  2. State the properties you care about as theorems.
  3. Prove them — with automation (simp/omega/decide) where possible.

Lean is NOT a push-button verifier for arbitrary existing Rust/Python/C.
It verifies models and pure functions you express in Lean. (For pushbutton
verification of imperative code, SMT-backed tools like Dafny/Why3 or a model
checker like TLA+ fit better — see the primer's system comparison.)

Worked example: a tiny stack, with an invariant we prove holds.
-/

namespace Demo

-- A bounded counter with a documented invariant: value ≤ cap.
structure Counter where
  value : Nat
  cap   : Nat
  inv   : value ≤ cap        -- the invariant travels WITH the data as a proof

def mk (cap : Nat) : Counter := { value := 0, cap := cap, inv := Nat.zero_le cap }

-- `incr` refuses to exceed the cap; it returns a Counter that still satisfies inv.
def incr (c : Counter) : Counter :=
  if h : c.value < c.cap then
    { value := c.value + 1, cap := c.cap, inv := h }
  else
    c

-- Property 1: incr never breaks the invariant. It's true *by construction* —
-- the `inv` field could not have been built otherwise — so this is immediate.
theorem incr_preserves_inv (c : Counter) : (incr c).value ≤ (incr c).cap :=
  (incr c).inv

-- Property 2: incr never decreases the value (monotonicity).
-- `dsimp only` reduces the record-projection on the `if` branches so `omega`
-- sees plain `c.value ≤ c.value + 1`.
theorem incr_monotone (c : Counter) : c.value ≤ (incr c).value := by
  unfold incr
  split
  · simp        -- then-branch: reduces the projection and closes c.value ≤ c.value+1
  · omega       -- else-branch: goal is c.value ≤ c.value

-- Property 3: an "optimized" implementation matching a reference model.
-- A classic verification shape: a fast tail-recursive accumulator version is
-- proved equal to the obvious-but-slow recursive reference. (We stay in linear
-- arithmetic so core Lean's `omega` suffices — no mathlib `ring` needed.)
def sumTo : Nat → Nat                      -- reference model
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

def sumToAcc : Nat → Nat → Nat             -- "optimized" tail-recursive version
  | 0,     acc => acc
  | n + 1, acc => sumToAcc n (acc + (n + 1))

-- The key generalization lemma (note `generalizing acc`): the accumulator
-- version equals the reference plus whatever is already accumulated.
theorem sumToAcc_eq (n acc : Nat) : sumToAcc n acc = sumTo n + acc := by
  induction n generalizing acc with
  | zero => simp [sumToAcc, sumTo]
  | succ k ih => simp only [sumToAcc, sumTo, ih]; omega

theorem sumTo_correct (n : Nat) : sumToAcc n 0 = sumTo n := by
  simp [sumToAcc_eq]

-- Spot-check by evaluation before/alongside proving (fast feedback loop):
#eval (List.range 20).all (fun n => sumToAcc n 0 = sumTo n)   -- true

end Demo
