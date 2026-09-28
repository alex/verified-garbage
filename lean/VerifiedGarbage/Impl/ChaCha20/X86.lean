import VerifiedGarbage.TCB.X86.Isa

/-!
# ChaCha20 block function: x86 (32-bit) implementation

`vg_chacha20_block(state, buf)`, cdecl: the arguments are at `[esp + 4]` and
`[esp + 8]`.

With only seven usable registers, the state lives in memory:
* `buf[0..64)` is the working state: the input state is copied there, each
  quarter round loads its four words into `eax, ebx, ecx, edx` and stores them
  back, and finally the input state (re-read from `state`) is added in place,
  leaving the result.
* `esi` points to `buf` and `edi` to `state`; both are loaded from their
  argument slots, and `buf[64..76)` holds the saved `ebx, esi, edi`.
* Every address is `esp`, `esi`, `edi` or `eax` (while it holds `buf`) plus a
  constant, and there are no branches, so only the pointers can affect timing.
-/

namespace VG.Impl.ChaCha20.X86

open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- The quarter round (RFC 8439 §2.1) on `eax, ebx, ecx, edx`. A rotation left
by `k` is a rotation right by `32 - k`. -/
def qr : List Instr := [
  .alu .add .eax (.reg .ebx), .alu .xor .edx (.reg .eax), .shift .ror .edx 16,
  .alu .add .ecx (.reg .edx), .alu .xor .ebx (.reg .ecx), .shift .ror .ebx 20,
  .alu .add .eax (.reg .ebx), .alu .xor .edx (.reg .eax), .shift .ror .edx 24,
  .alu .add .ecx (.reg .edx), .alu .xor .ebx (.reg .ecx), .shift .ror .ebx 25]

/-- `QUARTERROUND(x, y, z, w)` (RFC 8439 §2.2) on the words in `buf`. -/
def quarter (x y z w : Nat) : Prog isa := .block (
  [.mov .eax (.mem (at_ .esi (4 * x))), .mov .ebx (.mem (at_ .esi (4 * y))),
   .mov .ecx (.mem (at_ .esi (4 * z))), .mov .edx (.mem (at_ .esi (4 * w)))] ++ qr ++
  [.store (at_ .esi (4 * x)) .eax, .store (at_ .esi (4 * y)) .ebx,
   .store (at_ .esi (4 * z)) .ecx, .store (at_ .esi (4 * w)) .edx])

/-- `inner_block` (RFC 8439 §2.3.1): a column round and a diagonal round. -/
def doubleRound : Prog isa :=
  .seq (quarter 0 4 8 12) <| .seq (quarter 1 5 9 13) <| .seq (quarter 2 6 10 14) <|
  .seq (quarter 3 7 11 15) <| .seq (quarter 0 5 10 15) <| .seq (quarter 1 6 11 12) <|
  .seq (quarter 2 7 8 13) (quarter 3 4 9 14)

/-- `n` double rounds. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) doubleRound

/-- Load the pointers (into `eax` and `ecx`), save `ebx, esi, edi` in `buf`,
and move the pointers to `esi` and `edi`. -/
def save : List Instr := [
  .mov .eax (.mem (at_ .esp 8)), .mov .ecx (.mem (at_ .esp 4)), .store (at_ .eax 64) .ebx,
  .store (at_ .eax 68) .esi, .store (at_ .eax 72) .edi, .mov .esi (.reg .eax),
  .mov .edi (.reg .ecx)]

/-- Copy word `k` of the input state to `buf`. -/
def copyWord (k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .edi (4 * k))), .store (at_ .esi (4 * k)) .eax]

def copy : List Instr := (List.range 16).flatMap copyWord

/-- Add word `k` of the input state into `buf`. -/
def addWord (k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esi (4 * k))), .alu .add .eax (.mem (at_ .edi (4 * k))),
   .store (at_ .esi (4 * k)) .eax]

def finish : List Instr := (List.range 16).flatMap addWord

/-- Restore `ebx, esi, edi` (via `eax`). -/
def restore : List Instr := [
  .mov .eax (.reg .esi), .mov .ebx (.mem (at_ .eax 64)), .mov .esi (.mem (at_ .eax 68)),
  .mov .edi (.mem (at_ .eax 72))]

def block : Prog isa :=
  .seq (.block (save ++ copy)) (.seq (rounds 10) (.block (finish ++ restore)))

end VG.Impl.ChaCha20.X86
