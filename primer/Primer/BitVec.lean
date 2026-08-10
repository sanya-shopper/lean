/-
Primer 3 — BitVec: the fixed-width machine-integer world that crypto lives in.

`BitVec n` is an n-bit vector with wraparound arithmetic — exactly the model
you need for SHA-256, which is built from 32-bit words under:
  * addition mod 2^32
  * bitwise XOR / AND / NOT
  * right-rotation and right-shift

Everything here is core Lean 4 (no mathlib). This file is a warm-up for the
kind of reasoning a SHA-256 formalization needs; it is NOT SHA-256 itself.

`decide` proves finite BitVec facts by evaluation. For statements quantified
over ALL 2^32 words, `decide` is far too slow — that is exactly where a SAT
backend (`bv_decide`, which bitblasts to CNF and checks an LRAT certificate)
takes over. See the cookbook notes on `bv_decide`.
-/

-- 32-bit words, written with a width suffix.
#eval (0xdeadbeef#32)                 -- 3735928559
#check (0#32)                          -- 0#32 : BitVec 32

-- Modular addition wraps at 2^32.
#eval (0xffffffff#32) + (1#32)         -- 0  (wraps)

-- Bitwise operations.
#eval (0b1100#8) &&& (0b1010#8)        -- 8   (AND -> 0b1000)
#eval (0b1100#8) ||| (0b1010#8)        -- 14  (OR  -> 0b1110)
#eval (0b1100#8) ^^^ (0b1010#8)        -- 6   (XOR -> 0b0110)

-- Right rotation, the workhorse of SHA-256's Sigma functions.
def rotr (x : BitVec 32) (n : Nat) : BitVec 32 :=
  (x >>> n) ||| (x <<< (32 - n))

#eval rotr (1#32) 1                    -- 2147483648  (bit 0 -> bit 31)

-- SHA-256's building blocks, as pure BitVec functions.
-- Note: Greek capital `Σ` is a reserved token in Lean (the Sigma type), so we
-- spell these `Sigma0`/`Sigma1`; lowercase `sigma0`/`sigma1` for the small ones.
def Ch     (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ ((~~~x) &&& z)
def Maj    (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
def Sigma0 (x : BitVec 32) : BitVec 32 := rotr x 2  ^^^ rotr x 13 ^^^ rotr x 22
def Sigma1 (x : BitVec 32) : BitVec 32 := rotr x 6  ^^^ rotr x 11 ^^^ rotr x 25
def sigma0 (x : BitVec 32) : BitVec 32 := rotr x 7  ^^^ rotr x 18 ^^^ (x >>> 3)
def sigma1 (x : BitVec 32) : BitVec 32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

-- Ch is a bitwise "select": where x's bit is 1 pick y, else pick z.
-- Sanity checks by evaluation:
#eval Ch 0xffffffff#32 0xaaaaaaaa#32 0x55555555#32   -- 2863311530 (= y)
#eval Ch 0x00000000#32 0xaaaaaaaa#32 0x55555555#32   -- 1431655765 (= z)

-- Small proved properties, decided by evaluation on concrete inputs.
example : Ch 0xffffffff#32 0xaaaaaaaa#32 0x55555555#32 = 0xaaaaaaaa#32 := by decide
example : Maj 0#32 0#32 0#32 = 0#32 := by decide

-- A genuinely universal bit-identity holds for ALL 8-bit x (256 cases),
-- which `decide` CAN enumerate by brute force: x XOR x = 0.
example : ∀ x : BitVec 8, x ^^^ x = 0#8 := by decide

-- The same over 32 bits is a 2^32-case statement: `decide` is impractical,
-- and this is the frontier where `bv_decide` (SAT/bitblasting) is the tool.
-- It needs `import Std.Tactic.BVDecide` (bundled with the toolchain). With that:
--   example (x : BitVec 32) : x ^^^ x = 0#32 := by bv_decide
-- solves instantly because XOR is one gate per bit — no 2^32 enumeration.
