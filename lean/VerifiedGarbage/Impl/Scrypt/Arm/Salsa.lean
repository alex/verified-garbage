import VerifiedGarbage.TCB.Arm.Isa

/-!
# The Salsa20/8 Core: 32-bit ARM implementation

`vg_salsa20_8(b = r0, scratch = r1)`: replaces the 64 bytes at `b` by their
Salsa20/8 Core (RFC 7914 §3).

The contract gives no room to save callee-saved registers (`scratch` is only
64 bytes, and the taint analysis does not handle stack frames), so only
`r2` and `r3` are used, and the sixteen words live in memory:

* the input is copied to `scratch`, word `k` at `4k`, and stays in `b`;
* each line `x[i] ^= R(x[j] + x[k], n)` of the four fully unrolled double
  rounds loads `x[j]` and `x[k]`, adds them, loads `x[i]`, exclusive-ors in
  the sum rotated left by `n` (right by `32 - n`, as the second operand's
  shift) and stores `x[i]` back;
* finally word `k` of `b` becomes the sum of the input's and `scratch`'s.

Every address is `r0` or `r1` plus a constant, and there are no branches, so
only the pointers can affect timing.
-/

namespace VG.Impl.Scrypt.Arm

open VG.Arm

/-- `x[i] ^= R(x[j] + x[k], n)`, with `x` in `scratch`. -/
def line (i j k n : Nat) : List Instr :=
  [.ldr .r2 .r1 (4 * j), .ldr .r3 .r1 (4 * k), .dp .add .r2 .r2 (.reg .r3),
   .ldr .r3 .r1 (4 * i), .dp .eor .r3 .r3 (.shifted .r2 .ror (32 - n)), .str .r3 .r1 (4 * i)]

/-- The lines `(i, j, k, n)` of a double round (a column round and a row
round), in the order of RFC 7914 §3. -/
def lines : List (Nat × Nat × Nat × Nat) := [
  (4, 0, 12, 7), (8, 4, 0, 9), (12, 8, 4, 13), (0, 12, 8, 18),
  (9, 5, 1, 7), (13, 9, 5, 9), (1, 13, 9, 13), (5, 1, 13, 18),
  (14, 10, 6, 7), (2, 14, 10, 9), (6, 2, 14, 13), (10, 6, 2, 18),
  (3, 15, 11, 7), (7, 3, 15, 9), (11, 7, 3, 13), (15, 11, 7, 18),
  (1, 0, 3, 7), (2, 1, 0, 9), (3, 2, 1, 13), (0, 3, 2, 18),
  (6, 5, 4, 7), (7, 6, 5, 9), (4, 7, 6, 13), (5, 4, 7, 18),
  (11, 10, 9, 7), (8, 11, 10, 9), (9, 8, 11, 13), (10, 9, 8, 18),
  (12, 15, 14, 7), (13, 12, 15, 9), (14, 13, 12, 13), (15, 14, 13, 18)]

def doubleRound : Prog isa := .block (lines.flatMap fun (i, j, k, n) => line i j k n)

/-- `n` double rounds. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) doubleRound

/-- Copy word `k` of the input to `scratch`. -/
def copyWord (k : Nat) : List Instr := [.ldr .r2 .r0 (4 * k), .str .r2 .r1 (4 * k)]

def copy : List Instr := (List.range 16).flatMap copyWord

/-- Add word `k` of the input to word `k` of the rounds' result, into `b`. -/
def finishWord (k : Nat) : List Instr :=
  [.ldr .r2 .r1 (4 * k), .ldr .r3 .r0 (4 * k), .dp .add .r2 .r2 (.reg .r3), .str .r2 .r0 (4 * k)]

def finish : List Instr := (List.range 16).flatMap finishWord

def salsa : Prog isa := .seq (.block copy) (.seq (rounds 4) (.block finish))

end VG.Impl.Scrypt.Arm
