import VerifiedGarbage.TCB.X86.Isa

/-!
# The Salsa20/8 Core: x86 (32-bit) implementation

`vg_salsa20_8(b = [esp + 4], scratch = [esp + 8])`, every argument on the
stack (cdecl): replaces the 64 bytes at `b` by their Salsa20/8 Core
(RFC 7914 §3).

As on 32-bit ARM (`Impl/Scrypt/Arm/Salsa.lean`), the contract gives no room
to save callee-saved registers (`scratch` is only 64 bytes), so only `eax`
(`b`), `ecx` (`scratch`) and `edx` are used, and the sixteen words live in
memory:

* the input is copied to `scratch`, word `k` at `4k`, and stays in `b`;
* each line `x[i] ^= R(x[j] + x[k], n)` of the four fully unrolled double
  rounds loads `x[j]`, adds `x[k]`, rotates the sum left by `n` (right by
  `32 - n`), exclusive-ors in `x[i]` and stores it back to `x[i]`;
* finally word `k` of `b` becomes the sum of the input's and `scratch`'s.

Every address is `esp`, `eax` or `ecx` plus a constant, and there are no
branches, so only the pointers can affect timing.
-/

namespace VG.Impl.Scrypt.X86

open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `x[i] ^= R(x[j] + x[k], n)`, with `x` in `scratch`. -/
def line (i j k n : Nat) : List Instr :=
  [.mov .edx (.mem (at_ .ecx (4 * j))), .alu .add .edx (.mem (at_ .ecx (4 * k))),
   .shift .ror .edx (32 - n), .alu .xor .edx (.mem (at_ .ecx (4 * i))), .store (at_ .ecx (4 * i)) .edx]

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
def copyWord (k : Nat) : List Instr :=
  [.mov .edx (.mem (at_ .eax (4 * k))), .store (at_ .ecx (4 * k)) .edx]

/-- Loading the pointers, then copying the input. -/
def copy : List Instr :=
  [.mov .eax (.mem (at_ .esp 4)), .mov .ecx (.mem (at_ .esp 8))] ++ (List.range 16).flatMap copyWord

/-- Add word `k` of the input to word `k` of the rounds' result, into `b`. -/
def finishWord (k : Nat) : List Instr :=
  [.mov .edx (.mem (at_ .ecx (4 * k))), .alu .add .edx (.mem (at_ .eax (4 * k))),
   .store (at_ .eax (4 * k)) .edx]

def finish : List Instr := (List.range 16).flatMap finishWord

def salsa : Prog isa := .seq (.block copy) (.seq (rounds 4) (.block finish))

end VG.Impl.Scrypt.X86
