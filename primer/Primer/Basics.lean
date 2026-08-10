/-
Primer 1 — Basics: definitions, functions, evaluation, and checking types.

Run just this file:      lake env lean Primer/Basics.lean
Build the whole project: lake build

`#eval` runs a computation; `#check` reports a type; `#print` shows a definition.
These commands print to the Lean infoview (in an editor) or to stdout on the CLI.
-/

-- A plain definition. Lean infers the type `Nat` (natural number).
def answer := 42

#eval answer            -- 42
#check answer           -- answer : Nat

-- A function. Types are written after `:`. `Nat → Nat` is a function type.
def double (n : Nat) : Nat := n + n

#eval double 21         -- 42
#check double           -- double : Nat → Nat

-- Pattern matching and recursion. Lean checks this terminates.
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

#eval fib 10            -- 55
#eval (List.range 10).map fib   -- [0, 1, 1, 2, 3, 5, 8, 13, 21, 34]

-- Algebraic data types, like Haskell's `data`.
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α

def size {α : Type} : Tree α → Nat
  | .leaf => 0
  | .node l _ r => size l + 1 + size r

def example_tree : Tree Nat :=
  .node (.node .leaf 1 .leaf) 2 (.node .leaf 3 .leaf)

#eval size example_tree   -- 3

-- Structures (records) with named fields.
structure Point where
  x : Nat
  y : Nat

def origin : Point := { x := 0, y := 0 }

#eval origin.x            -- 0
