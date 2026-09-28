import VerifiedGarbage.TCB.AArch64.Isa

/-!
# The Salsa20/8 Core: AArch64 implementation

`vg_salsa20_8(b = x0, scratch = x1)`: replaces the 64 bytes at `b` by their
Salsa20/8 Core (RFC 7914 §3).

* Word `k` lives in `w(k + 2)` (`x2`–`x17`) throughout; the four double
  rounds are fully unrolled.
* `w1` is the temporary of every line `x[i] ^= R(x[j] + x[k], n)` (a
  rotation left by `n` is a rotation right by `32 - n`). `scratch` is never
  used, so its pointer `x1` is free.
* The input stays in `b` until the final addition, which re-reads word `k`
  into `w1` just before storing word `k` of the result over it.
* Only caller-saved registers are used and nothing is saved.
* Every address is `x0` plus a constant, and there are no branches, so only
  the pointers can affect timing.
-/

namespace VG.Impl.Scrypt.AArch64

open VG.AArch64

/-- The register holding word `k`. -/
def wreg (k : Nat) : Reg :=
  [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17].getD k .x2

/-- `x[i] ^= R(x[j] + x[k], n)`. -/
def line (i j k n : Nat) : List Instr :=
  [.add .w .x1 (wreg j) (wreg k), .ror .w .x1 .x1 (32 - n),
   .logic .eor .w (wreg i) (wreg i) .x1]

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

/-- Load the input into the registers. -/
def load : List Instr := (List.range 16).flatMap fun k => [.ldr .w (wreg k) .x0 (4 * k)]

/-- Add word `k` of the input (re-read from `b` into `w1`) to word `k` of the
rounds' result, and store the sum over it. -/
def finishWord (k : Nat) : List Instr :=
  [.ldr .w .x1 .x0 (4 * k), .add .w (wreg k) (wreg k) .x1, .str .w (wreg k) .x0 (4 * k)]

def finish : List Instr := (List.range 16).flatMap finishWord

def salsa : Prog isa := .seq (.block load) (.seq (rounds 4) (.block finish))

end VG.Impl.Scrypt.AArch64
