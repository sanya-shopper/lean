/-
Primer 6 — The Josephus problem (Graham, Knuth & Patashnik, *Concrete
Mathematics*, §1.3).

n people stand in a circle; every second person is eliminated; which position
J(n) survives? Concrete Mathematics derives the recurrence

    J(1) = 1,   J(2n) = 2·J(n) − 1,   J(2n+1) = 2·J(n) + 1

and the beautiful closed form: writing n = 2^m + l with 0 ≤ l < 2^m,

    J(n) = 2l + 1,

equivalently "J(n) is the binary numeral of n rotated left by one bit"
(e.g. n = 13 = 1101₂  ↦  1011₂ = 11 = J(13)). The bit-rotation view is a nice
callback to `rotr`/rotation in BitVec.lean.

This chapter states these three ways and machine-checks that they agree.
Core Lean 4, no mathlib.
-/

-- The recurrence, as a total function (J 0 is unused; we return 0).
def josephus : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      have : (n + 2) / 2 < n + 2 := Nat.div_lt_self (by omega) (by omega)
      if (n + 2) % 2 = 0 then 2 * josephus ((n + 2) / 2) - 1
                         else 2 * josephus ((n + 2) / 2) + 1

-- The Concrete Mathematics closed form, using n = 2^(⌊log2 n⌋) + l.
-- Here `2^(Nat.log2 n)` is the largest power of two ≤ n, so `l = n - 2^log2 n`.
def josephusClosed (n : Nat) : Nat := 2 * (n - 2 ^ Nat.log2 n) + 1

-- The bit-rotation form: drop the leading 1 (subtract 2^log2 n), shift left,
-- put a 1 in the low bit. This equals josephusClosed by construction; we state
-- it as its own function to make the "rotate left by one bit" reading explicit.
def josephusRotate (n : Nat) : Nat :=
  let hi := Nat.log2 n          -- index of the leading 1 bit
  ((n - 2 ^ hi) <<< 1) ||| 1    -- shift the remaining bits left, set low bit

-- A demonstration table for n = 1..16: recurrence vs closed form.
#eval (List.range 16).map (fun i =>
  let n := i + 1; (n, josephus n, josephusClosed n))
-- [(1,1,1),(2,1,1),(3,3,3),(4,1,1),(5,3,3),(6,5,5),(7,7,7),(8,1,1),
--  (9,3,3),(10,5,5),(11,7,7),(12,9,9),(13,11,11),(14,13,13),(15,15,15),(16,1,1)]

-- The textbook example, three ways in agreement:
#eval (josephus 13, josephusClosed 13, josephusRotate 13)   -- (11, 11, 11)

-- MACHINE-CHECKED: all three agree for every n in 1..2000. `native_decide`
-- compiles the check and runs it; this is a real verified statement about that
-- finite range (not a spot #eval).
theorem josephus_agrees_upto_2000 :
    ((List.range 2000).all
      (fun i => let n := i + 1;
        (josephus n == josephusClosed n) && (josephusClosed n == josephusRotate n)))
      = true := by native_decide

/-
Beyond the finite check: the GENERAL closed-form theorem, proved.
We first pin the two recurrence equations, then induct on m.
-/

-- Recurrence equations, recovered from the well-founded definition. We rewrite
-- ONLY the left-hand `josephus` (via its unfolding equation `josephus.eq_def`,
-- which `rw` applies to the leftmost occurrence) so the `josephus` on the right
-- is left intact, then simplify the exposed `if`/match with the mod & div facts.
theorem josephus_even (k : Nat) (hk : 1 ≤ k) :
    josephus (2 * k) = 2 * josephus k - 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show 2 * (j + 1) = 2 * j + 2 from by omega, josephus.eq_def]
  have hmod : (2 * j + 2) % 2 = 0 := by omega
  have hdiv : (2 * j + 2) / 2 = j + 1 := by omega
  simp [hmod, hdiv]

theorem josephus_odd (k : Nat) (hk : 1 ≤ k) :
    josephus (2 * k + 1) = 2 * josephus k + 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 from by omega, josephus.eq_def]
  have hmod : (2 * j + 1 + 2) % 2 = 1 := by omega
  have hdiv : (2 * j + 1 + 2) / 2 = j + 1 := by omega
  simp [hmod, hdiv]

-- The Concrete Mathematics closed form, PROVED for all m and all l < 2^m:
--     J(2^m + l) = 2l + 1.
-- Induction on m; split on the parity of l and step down with the recurrence.
theorem josephus_pow (m : Nat) :
    ∀ l, l < 2 ^ m → josephus (2 ^ m + l) = 2 * l + 1 := by
  induction m with
  | zero =>
      intro l hl
      rw [Nat.pow_zero] at hl ⊢
      have : l = 0 := by omega
      subst this
      simp [josephus]
  | succ m ih =>
      intro l hl
      have hpow : (2 : Nat) ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
      have hpos : 0 < (2 : Nat) ^ m := Nat.two_pow_pos m
      rcases (show l % 2 = 0 ∨ l % 2 = 1 by omega) with hpar | hpar
      · -- l even: 2^(m+1) + l = 2·(2^m + l/2)
        have hjm : l / 2 < 2 ^ m := by omega
        have hk : (2 : Nat) ^ (m + 1) + l = 2 * (2 ^ m + l / 2) := by omega
        rw [hk, josephus_even (2 ^ m + l / 2) (by omega), ih (l / 2) hjm]
        omega
      · -- l odd: 2^(m+1) + l = 2·(2^m + l/2) + 1
        have hjm : l / 2 < 2 ^ m := by omega
        have hk : (2 : Nat) ^ (m + 1) + l = 2 * (2 ^ m + l / 2) + 1 := by omega
        rw [hk, josephus_odd (2 ^ m + l / 2) (by omega), ih (l / 2) hjm]
        omega
