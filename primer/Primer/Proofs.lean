/-
Primer 2 — Proofs: propositions as types, and the common tactics.

A `theorem` (or `example`) states a proposition and gives a proof term.
`by ...` enters tactic mode; the goal state evolves as tactics run.

Key tactics used below:
  rfl        — closes goals true by computation/definition
  simp       — simplify using rewrite lemmas
  decide     — decide a Decidable proposition by running it
  omega      — linear arithmetic over Nat/Int
  induction  — proof by induction, with a case per constructor
-/

-- Proof by computation: both sides reduce to the same normal form.
theorem two_plus_two : 2 + 2 = 4 := by rfl

-- A decidable proposition, checked by actually evaluating it.
example : (7 * 6 = 42) ∧ (3 < 10) := by decide

-- Linear arithmetic. `omega` handles goals rfl/decide cannot.
example (n : Nat) : n + 0 = n := by omega
example (a b : Nat) : a + b = b + a := by omega

-- Universally quantified statement proved by induction on a list.
-- Property: mapping then taking length = taking length. (length is preserved.)
theorem length_map {α β : Type} (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.map, List.length, ih]

-- Reversing twice is the identity. `simp` with the library lemma closes it.
theorem reverse_reverse {α : Type} (xs : List α) :
    xs.reverse.reverse = xs := by
  simp

-- A property of our own function: `twice n` is always even.
def twice (n : Nat) : Nat := n + n

-- `omega` doesn't know what `twice` is, so unfold it first, then it's linear.
theorem twice_even (n : Nat) : ∃ k, twice n = 2 * k :=
  ⟨n, by unfold twice; omega⟩

-- `sorry` is an accepted-but-unproven hole. Uncomment to see the warning:
-- theorem hard_thing : ∀ n : Nat, n < n + 1 := sorry
theorem succ_gt (n : Nat) : n < n + 1 := by omega
