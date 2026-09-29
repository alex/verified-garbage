import VerifiedGarbage.TCB.X86.Isa

/-!
# GHASH: x86 (32-bit) implementation

`vg_ghash(h, y, data, n, scratch)`, cdecl: the arguments are at `[esp + 4]`
… `[esp + 20]`.

For each of the `n` blocks `X` at `data`, `Y := (Y ⊕ X) • H`, where `•` is
SP 800-38D Algorithm 1 bit by bit, as `Spec.Gcm.mul` defines it (as on
AArch64, `Impl/Gcm/AArch64.lean`):

* The blocks are big-endian: each 4-byte word is loaded and byte-swapped
  (`bswap`). A 128-bit value is four words, the first the most significant.
* `V` (starting at `H`) is in `eax`, `ebx`, `ecx`, `edx`; `edi` points to
  the scratch buffer throughout, which holds `Z` and the words of `Y ⊕ X`.
* Each step takes the most significant bit `xᵢ` of the first word left of
  `Y ⊕ X` (shifting it left by one bit, `add`, which sets CF to it) and
  turns it into the mask `m = 0 − xᵢ` (`sbb ebp, ebp`); `Z` accumulates
  `V & m`, so `Z := Z ⊕ V` exactly when `xᵢ = 1`.
* `V` is shifted right by one bit (`shr`, which sets CF to its lowest bit
  for the mask `0 − LSB₁(V)`; the model has no `rcr`, so each word's lowest
  bit moves into the top of the next with a rotation and a mask), and the
  reduction constant `R` (`0xE1` in the top byte) is XORed into it under
  the mask.
* The 32 steps of a word are a loop of `unroll` steps per iteration, and the
  four words a loop around it, which moves the next word to the first slot.
* The counters, the data pointer and the block count are in the scratch
  buffer. Every address is `esp` or a pointer plus a constant, and every
  branch depends only on `n`, so only the pointers and `n` can affect
  timing.

The scratch buffer's bytes are laid out as: `[0, 16)` the words of `Y ⊕ X`
still to be used, `[16, 32)` `Z`, `[32, 48)` the saved `ebx`, `esi`, `edi`
and `ebp`, then the data pointer, the blocks left, the words left and the
iterations left.
-/

namespace VG.Impl.Gcm.X86

open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- Argument `i` on entry (cdecl). -/
def argOp (i : Nat) : MemOp := at_ .esp (4 + 4 * i)

/-- The offsets of `Z`'s words, the data pointer and the counters. -/
def zOff (k : Nat) : Nat := 16 + 4 * k
def dOff : Nat := 48
def nOff : Nat := 52
def wcOff : Nat := 56
def scOff : Nat := 60

/-- The registers holding `V`'s words, the most significant first. -/
def vReg : Nat → Reg
  | 0 => .eax | 1 => .ebx | 2 => .ecx | _ => .edx

/-- Steps per iteration of the inner loop. -/
def unroll : Nat := 8

/-- The top bit, where the lowest bit of the word before goes. -/
def topBit : BitVec 32 := 0x80000000

/-- The top word of `R = 11100001 ‖ 0¹²⁰` (its other words are 0). -/
def rTop : BitVec 32 := 0xE1000000

/-- `Z ^= V & m`, word `k`. -/
def zUpd (k : Nat) : List Instr :=
  [.mov .esi (.reg (vReg k)), .alu .and .esi (.reg .ebp), .alu .xor .esi (.mem (at_ .edi (zOff k))),
   .store (at_ .edi (zOff k)) .esi]

/-- Word `k + 1 := (word k + 1 >> 1) | (word k << 31)`, and `word k >>= 1`. -/
def vCarry (k : Nat) : List Instr :=
  [.mov .esi (.reg (vReg k)), .shift .ror .esi 1, .alu .and .esi (.imm topBit),
   .alu .or (vReg (k + 1)) (.reg .esi), .shift .shr (vReg k) 1]

/-- One step of Algorithm 1. -/
def step : List Instr :=
  -- m := −xᵢ, and the first word of X shifted left
  [.mov .esi (.mem (at_ .edi 0)), .alu .add .esi (.reg .esi), .store (at_ .edi 0) .esi,
   .alu .sbb .ebp (.reg .ebp)] ++
  -- Z := Z ⊕ (V ∧ m)
  zUpd 0 ++ zUpd 1 ++ zUpd 2 ++ zUpd 3 ++
  -- m := −LSB₁(V), and V := (V >> 1) ⊕ (R ∧ m)
  [.shift .shr .edx 1, .alu .sbb .ebp (.reg .ebp)] ++ vCarry 2 ++ vCarry 1 ++ vCarry 0 ++
  [.alu .and .ebp (.imm rTop), .alu .xor .eax (.reg .ebp)]

/-- `unroll` steps, then the count (ZF is set after the last iteration). -/
def steps : List Instr :=
  (List.range unroll).flatMap (fun _ => step) ++
  [.mov .esi (.mem (at_ .edi scOff)), .alu .sub .esi (.imm 1), .store (at_ .edi scOff) .esi]

/-- After a word: move the next words down, and count it. -/
def nextWord : List Instr :=
  [.mov .esi (.mem (at_ .edi 4)), .store (at_ .edi 0) .esi,
   .mov .esi (.mem (at_ .edi 8)), .store (at_ .edi 4) .esi,
   .mov .esi (.mem (at_ .edi 12)), .store (at_ .edi 8) .esi,
   .mov .esi (.mem (at_ .edi wcOff)), .alu .sub .esi (.imm 1), .store (at_ .edi wcOff) .esi]

/-- One word of `Y ⊕ X`: 32 steps. -/
def word : Prog isa :=
  .seq (.block [.mov .esi (.imm (BitVec.ofNat 32 (32 / unroll))), .store (at_ .edi scOff) .esi])
    (.seq (.loop (.block steps) .ne) (.block nextWord))

/-- Word `w` of `Y ⊕ X`, into the scratch buffer (`esi` at the block, `ebp` at `Y`). -/
def loadX (w : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .ebp (4 * w))), .bswap .eax, .mov .ebx (.mem (at_ .esi (4 * w))), .bswap .ebx,
   .alu .xor .eax (.reg .ebx), .store (at_ .edi (4 * w)) .eax]

/-- Load `Y ⊕ X`, `Z := 0`, `V := H`, and the word count. -/
def load : List Instr :=
  [.mov .esi (.mem (at_ .edi dOff)), .mov .ebp (.mem (argOp 1))] ++
  loadX 0 ++ loadX 1 ++ loadX 2 ++ loadX 3 ++
  [.mov .eax (.imm 0)] ++ (List.range 4).map (fun k => .store (at_ .edi (zOff k)) .eax) ++
  [.mov .ebp (.mem (argOp 0))] ++
  (List.range 4).flatMap (fun k => [.mov (vReg k) (.mem (at_ .ebp (4 * k))), .bswap (vReg k)]) ++
  [.mov .esi (.imm 4), .store (at_ .edi wcOff) .esi]

/-- Store `Z` as the new `Y`, advance to the next block and count it (ZF is
set after the last block). -/
def store : List Instr :=
  [.mov .esi (.mem (argOp 1))] ++
  (List.range 4).flatMap (fun k =>
    [.mov .eax (.mem (at_ .edi (zOff k))), .bswap .eax, .store (at_ .esi (4 * k)) .eax]) ++
  [.mov .esi (.mem (at_ .edi dOff)), .alu .add .esi (.imm 16), .store (at_ .edi dOff) .esi,
   .mov .esi (.mem (at_ .edi nOff)), .alu .sub .esi (.imm 1), .store (at_ .edi nOff) .esi]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (.loop word .ne) (.block store))

/-- The callee-saved registers, and their offsets in the scratch buffer. -/
def savedRegs : List (Reg × Nat) := [(.ebx, 32), (.esi, 36), (.edi, 40), (.ebp, 44)]

/-- Save the registers, point `edi` at the scratch buffer, and store the data
pointer and the count (ZF is set if it is zero). -/
def prologue : List Instr :=
  [.mov .eax (.mem (argOp 4))] ++ savedRegs.map (fun (r, d) => .store (at_ .eax d) r) ++
  [.mov .edi (.reg .eax), .mov .eax (.mem (argOp 2)), .store (at_ .edi dOff) .eax,
   .mov .eax (.mem (argOp 3)), .store (at_ .edi nOff) .eax, .alu .test .eax (.reg .eax)]

/-- Restore the registers (`edi`, the base, last). -/
def restore : List Instr :=
  [.mov .ebx (.mem (at_ .edi 32)), .mov .esi (.mem (at_ .edi 36)), .mov .ebp (.mem (at_ .edi 44)),
   .mov .edi (.mem (at_ .edi 40))]

def ghash : Prog isa :=
  .seq (.block prologue) (.seq (.ite .e (.block []) (.loop body .ne)) (.block restore))

end VG.Impl.Gcm.X86
