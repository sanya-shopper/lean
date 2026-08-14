/-
Primer 7 — Discrete probability as exact counting.

No mathlib, no real numbers. A probability over a finite, equally-likely sample
space is `favorable / total`, both natural numbers; and a claim like "p > 1/2"
becomes the exact inequality `2 * favorable > total`. That makes famous
probability facts into things the machine can *check*, not just estimate.
-/

-- The sample space of rolling two dice: all 36 ordered pairs.
-- `flatMap` (a.k.a. bind) pairs each `a` with every `b`; `map` builds the pair.
def twoDice : List (Nat × Nat) :=
  [1,2,3,4,5,6].flatMap (fun a => [1,2,3,4,5,6].map (fun b => (a, b)))

-- Count the outcomes satisfying a predicate — the numerator of a probability.
def countWhere (xs : List α) (p : α → Bool) : Nat := (xs.filter p).length

#eval twoDice.length                                   -- 36  (the denominator)
#eval countWhere twoDice (fun d => d.1 + d.2 == 7)      -- 6   ⇒ P(sum = 7) = 6/36 = 1/6

example : twoDice.length = 36 := by decide
example : countWhere twoDice (fun d => d.1 + d.2 == 7) = 6 := by decide

/-
MONTY HALL. Enumerate the 9 equally-likely `(car, firstPick)` games. The host
then opens a goat door and offers a switch. Switching wins EXACTLY when your
first pick was wrong (`car ≠ pick`) — so it wins 6/9 = 2/3, staying 3/9 = 1/3.
-/
def games : List (Nat × Nat) :=
  [0,1,2].flatMap (fun car => [0,1,2].map (fun pick => (car, pick)))

example : games.length = 9
        ∧ countWhere games (fun g => g.1 == g.2) = 3       -- staying wins
        ∧ countWhere games (fun g => g.1 != g.2) = 6 := by  -- switching wins
  decide

/-
DE MÉRÉ (1654) — the problem that started probability theory. He assumed the two
bets were equal (4 is to 6 as 24 is to 36); Pascal and Fermat showed they differ:
  • P(at least one 6 in 4 rolls of one die)          > 1/2
  • P(at least one double-6 in 24 rolls of two dice) < 1/2
"P > 1/2" means favorable outcomes exceed half the total, i.e. `2 * fav > total`.
Favorable = total − (no success), and no success = 5^4 (resp. 35^24).
-/
example : 2 * (6 ^ 4  - 5 ^ 4)  > 6 ^ 4  := by decide          -- 1342 > 1296  ✓ (>1/2)
example : 2 * (36 ^ 24 - 35 ^ 24) < 36 ^ 24 := by native_decide  -- just under 1/2

/-
THE BIRTHDAY PARADOX. Among n people (365 equally-likely birthdays), the
probability that all differ is  ∏_{i<n} (365 − i) / 365^n.  A collision is more
likely than not once  2 * (that numerator) < 365^n.  The numbers are ~60 digits,
so `native_decide` compiles the arithmetic (Lean `Nat` is arbitrary precision).
-/
def noCollisionNum : Nat → Nat
  | 0 => 1
  | n + 1 => (365 - n) * noCollisionNum n

-- The collision probability first passes 1/2 at EXACTLY 23 people — not at 22:
theorem birthday_threshold :
    2 * noCollisionNum 23 < 365 ^ 23 ∧ 2 * noCollisionNum 22 ≥ 365 ^ 22 := by
  native_decide
