import Mathlib

/-
mathlib-tour — what mathlib buys you, shown next to the core-Lean primer.

The primer (../primer) uses NO mathlib *on purpose*: it builds in seconds and has
zero dependencies. This companion shows the same ideas with mathlib, where proofs
get shorter and statements core Lean can't even express become routine.

Build: `lake exe cache get` then `lake build` (needs the ~6 GB mathlib olean
cache; the first `import Mathlib` load takes a few minutes).
-/

-- 1) THE ALGEBRA STEP, IN ONE WORD ------------------------------------------
-- In Primer/Proofs.lean, proving (k+1)² = k²+2k+1 needed a manual
--   `simp only [Nat.succ_mul, Nat.mul_succ]; omega`.
-- With mathlib's `ring`, any commutative-(semi)ring identity is one tactic:
example (k : Nat) : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring

-- 2) THE SAME sumOdd_eq, with the algebra step discharged by `ring` ----------
def sumOdd : Nat → Nat
  | 0 => 0
  | n + 1 => sumOdd n + (2 * n + 1)

theorem sumOdd_eq (n : Nat) : sumOdd n = n * n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumOdd, ih]; ring   -- vs. the primer's manual lemma

-- 2b) BETTER: state it as an actual finite SUM. Core Lean has no `∑` notation;
-- mathlib does, together with the lemmas to compute it:  ∑_{i<n} (2i+1) = n².
example (n : Nat) : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

-- 3) A THEOREM CORE LEAN CAN'T EVEN STATE: √2 is irrational ------------------
-- `Real.sqrt`, `Irrational`, and this proof all live in mathlib.
example : Irrational (Real.sqrt 2) := irrational_sqrt_two

-- 4) HONEST DISCRETE PROBABILITY: rationals and Finset, not integer tricks ---
-- Two dice, faces 0..5 as `Fin 6`. The event "faces sum to 5" (i.e. the pips
-- 1..6 sum to 7) has probability |event| / |space| computed as an actual ℚ.
open Finset in
example :
    ((univ.filter fun p : Fin 6 × Fin 6 => p.1.val + p.2.val = 5).card : ℚ) / 36 = 1 / 6 := by
  have hcard : (univ.filter fun p : Fin 6 × Fin 6 => p.1.val + p.2.val = 5).card = 6 := by
    decide
  rw [hcard]; norm_num
