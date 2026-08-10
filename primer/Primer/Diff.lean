/-
Primer 5 — Differences: the atom of differential cryptanalysis, in Lean.

This file illustrates the *shape* of "formalizing the learning" that broke the
earlier hash functions (MD4/MD5/SHA-0/SHA-1). Two things are worth separating:

  * CHECKING a collision is trivial and decidable — recompute and compare.
  * REASONING about how a difference propagates (the actual cryptanalytic
    content) is where the mathematics lives.

Everything here is core Lean 4 (no mathlib). It is a teaching sketch, not an
attack: it shows the primitives a real formalization (e.g. of the Lipmaa–Moriai
modular-addition differential probability, survey §5 target B1) would build on.
-/

-- An XOR difference between two words is just their XOR.
def diff (x x' : BitVec 32) : BitVec 32 := x ^^^ x'

-- FACT 1 (exact): XOR with a constant key passes a difference through unchanged,
-- Δ(x ⊕ k) = Δx, since (x⊕k) ⊕ (x'⊕k) = x ⊕ x'. This is why constant/key
-- addition is "free" for the attacker under XOR differences. Holds for ALL
-- inputs — brute-forced here over 4 bits (4096 cases; `decide` over three 8-bit
-- vars is 16.7M cases and times out). Over 32 bits it is a one-line `bv_decide`
-- (see BitVec.lean) — that's the whole reason bitblasting beats enumeration.
example : ∀ x x' k : BitVec 4, (x ^^^ k) ^^^ (x' ^^^ k) = x ^^^ x' := by decide

-- FACT 2 (data-dependent): AND does NOT pass a difference through
-- deterministically. With the SAME input difference Δx = 1, the output
-- difference of `x &&& y` depends on the actual value of y — so a given output
-- difference has probability < 1. This is the source of the per-step conditions
-- whose probabilities multiply into an attack's complexity.
#eval ((1#8 &&& 1#8) ^^^ (0#8 &&& 1#8))   -- 1  (y=1: difference survives)
#eval ((1#8 &&& 0#8) ^^^ (0#8 &&& 0#8))   -- 0  (y=0: difference killed)

-- FACT 3 (modular addition is the hard case): the differential probability of
-- x + y over all inputs with fixed input differences lies strictly between 0
-- and 1 and is NOT determined by the input differences alone — computing it is
-- exactly the Lipmaa–Moriai problem. We only illustrate non-determinism: same
-- input difference Δ=1 on the first operand, two different output differences.
#eval diff (0b0001#32 + 0b0001#32) (0b0000#32 + 0b0001#32)   -- 0x03: 2 vs 1
#eval diff (0b0111#32 + 0b0001#32) (0b0110#32 + 0b0001#32)   -- 0x0f: 8 vs 7 (carry ran)

-- COLLISION CHECKING is decidable and cheap: for concrete f and a concrete pair,
-- "do they collide?" is just evaluation — verifying a published collision
-- certificate needs no cleverness.
def toyMix (m : BitVec 32) : BitVec 32 := (m <<< 3) ^^^ (m >>> 5) ^^^ m
def toyCompress (m : BitVec 32) : BitVec 8 := (toyMix m).truncate 8
def collides (m m' : BitVec 32) : Bool := toyCompress m == toyCompress m'

-- A toy near-collision on the low byte, checked by pure computation:
#eval collides 0x00000000#32 0x00000020#32   -- (recomputed & compared)

-- The point: that last check is trivial; FACTS 1–3 are the content. A
-- retrospective formalization of the broken-SHA learning is essentially the
-- project of turning FACTS 2–3 (and their multi-round composition) into
-- machine-checked probability statements — none of which exists yet in any
-- proof assistant (survey §2, §5).
