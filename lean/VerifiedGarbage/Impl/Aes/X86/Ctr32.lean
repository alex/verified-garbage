import VerifiedGarbage.Impl.Aes.X86.Linear

/-!
# AES counter mode (GCM's `inc₃₂`), bitsliced, on x86 (32-bit)

`vg_aes_ctr32(schedule, rounds, counter, data, n, scratch)`, cdecl: the
arguments are at `[esp + 4]` … `[esp + 24]`.

Constant-time AES in the style of BearSSL's `aes_ct` (Thomas Pornin, MIT
licence): two blocks at a time, bitsliced in eight 32-bit words, which live
in slots `0 … 7` of the scratch buffer (`Linear.lean`, `Sbox.lean`). `edi`
points to the scratch buffer throughout; its bytes are laid out as:

* `[0, 256)`: the state and the S-box's spill slots;
* `[256, 272)`: the saved `ebx`, `esi`, `edi` and `ebp`;
* `[272, 288)`: the counter block: bytes 0–11 as three words, and the 32-bit
  counter as an integer;
* `[288, 296)`: the data pointer and the number of blocks left;
* `[1024, 1504)`: the bitsliced round keys, 32 bytes each, round key `j` at
  `1472 - 32 (rounds - j)`, so that the last is always at byte 1472.

The final counter `inc₃₂ⁿ(CB₁)` is written first. The round keys are
bitsliced once, from the last down, with the round in `esi`; then each group
of two blocks builds the counter blocks, bitslices them, encrypts them (the
round loop runs `esi` over the round keys until the last but one),
un-bitslices them and XORs the keystream into the data, two blocks or the
last one. The data pointer and the count are in `esi` and `ebp` while the
data is written, and stored back after.

Every address is `esp` or a pointer plus a constant, or computed from the
pointers and `rounds`, and every branch depends only on those and `n`, so
only the pointers, `rounds` and `n` can affect timing.
-/

namespace VG.Impl.Aes.X86

open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- Argument `i` on entry (cdecl). -/
def argOp (i : Nat) : MemOp := at_ .esp (4 + 4 * i)

def movI (d : Reg) (v : BitVec 32) : Instr := .mov d (.imm v)
def addI (d : Reg) (v : BitVec 32) : Instr := .alu .add d (.imm v)
def subI (d : Reg) (v : BitVec 32) : Instr := .alu .sub d (.imm v)
def addR (d s : Reg) : Instr := .alu .add d (.reg s)
def subR (d s : Reg) : Instr := .alu .sub d (.reg s)

/-- The callee-saved registers, and their offsets in the scratch buffer. -/
def savedRegs : List (Reg × Nat) := [(.ebx, 256), (.esi, 260), (.edi, 264), (.ebp, 268)]

/-- Load the scratch pointer (argument `k`) into `edi`, saving the registers. -/
def saveRegs (k : Nat) : List Instr :=
  [.mov .eax (.mem (argOp k))] ++ savedRegs.map (fun (r, d) => .store (at_ .eax d) r) ++
    [movR .edi .eax]

/-- Restore the registers (`edi`, the base, last). -/
def restoreRegs : List Instr :=
  [.mov .ebx (.mem (at_ .edi 256)), .mov .esi (.mem (at_ .edi 260)), .mov .ebp (.mem (at_ .edi 268)),
   .mov .edi (.mem (at_ .edi 264))]

/-- The offsets of the counter block's words, of the data pointer and of the count. -/
def cwOff (w : Nat) : Nat := 272 + 4 * w
def cNum : Nat := 284
def dOff : Nat := 288
def nOff : Nat := 292

/-- Copy the counter block (`counter`) to its words, and write the final
counter `(c + n) mod 2³²` back. -/
def ctrSetup : List Instr :=
  [.mov .ecx (.mem (argOp 2)),
   .mov .eax (.mem (at_ .ecx 0)), .store (at_ .edi (cwOff 0)) .eax,
   .mov .eax (.mem (at_ .ecx 4)), .store (at_ .edi (cwOff 1)) .eax,
   .mov .eax (.mem (at_ .ecx 8)), .store (at_ .edi (cwOff 2)) .eax,
   .mov .eax (.mem (at_ .ecx 12)), .bswap .eax, .store (at_ .edi cNum) .eax,
   .alu .add .eax (.mem (argOp 4)), .bswap .eax, .store (at_ .ecx 12) .eax]

/-- The byte offset of the last round key in the scratch buffer. -/
def lastKey : Nat := 1472

/-- `d := 2ᵏ d`. -/
def dbl (d : Reg) (k : Nat) : List Instr := (List.range k).map fun _ => addR d d

/-- `esi := rounds`: the key loop bitslices round key `esi` down to 0. -/
def keySetup : List Instr := [.mov .esi (.mem (argOp 1))]

/-- The round key `esi` of the schedule, as two blocks for `ortho`: its word
`w` in slots `2w` and `2w + 1`. -/
def keyLoad : List Instr :=
  [movR .eax .esi] ++ dbl .eax 4 ++ [.mov .ebx (.mem (argOp 0)), addR .eax .ebx] ++
  (List.range 4).flatMap fun w => [.mov .ebx (.mem (at_ .eax (4 * w))), st (2 * w) .ebx, st (2 * w + 1) .ebx]

/-- Store the bitsliced round key `esi` at `lastKey - 32 (rounds - esi)`. -/
def keyStore : List Instr :=
  [.mov .eax (.mem (argOp 1)), subR .eax .esi] ++ dbl .eax 5 ++
  [movR .ebx .edi, addI .ebx (BitVec.ofNat 32 lastKey), subR .ebx .eax] ++
  (List.range 8).flatMap fun k => [movS .eax k, .store (at_ .ebx (4 * k)) .eax]

/-- Bitslice round key `esi`, and step back (CF is set after round key 0). -/
def keyBody : List Instr := keyLoad ++ ortho ++ keyStore ++ [subI .esi 1]

/-- Store the data pointer and the count, and test the count. -/
def groupSetup : List Instr :=
  [.mov .eax (.mem (argOp 3)), .store (at_ .edi dOff) .eax,
   .mov .eax (.mem (argOp 4)), .store (at_ .edi nOff) .eax, .alu .test .eax (.reg .eax)]

/-- The counter blocks `c` and `c + 1`: block `b`'s word `w` in slot `2w + b`;
and `c := c + 2`. -/
def ctrBlock (b : Nat) : List Instr :=
  ((List.range 3).flatMap fun w => [.mov .eax (.mem (at_ .edi (cwOff w))), st (2 * w + b) .eax]) ++
  [.mov .eax (.mem (at_ .edi cNum)), addI .eax (BitVec.ofNat 32 b), .bswap .eax, st (6 + b) .eax]

def ctrBlocks : List Instr :=
  ctrBlock 0 ++ ctrBlock 1 ++
  [.mov .eax (.mem (at_ .edi cNum)), addI .eax 2, .store (at_ .edi cNum) .eax]

/-- `esi :=` the first round key, `edi + lastKey - 32 rounds`. -/
def keyStart : List Instr :=
  [.mov .esi (.mem (argOp 1))] ++ dbl .esi 5 ++
  [movR .eax .edi, addI .eax (BitVec.ofNat 32 lastKey), subR .eax .esi, movR .esi .eax]

/-- A middle round, with `esi` at the previous round key; loops until `esi`
is at the last round key but one. -/
def roundBody : List Instr :=
  [addI kp 32] ++ sboxCode ++ shiftRows ++ mixColumns ++ addRoundKey ++
  [movR .eax .edi, addI .eax (BitVec.ofNat 32 (lastKey - 32)), .alu .cmp kp (.reg .eax)]

/-- The last round. -/
def lastRound : List Instr := [addI kp 32] ++ sboxCode ++ shiftRows ++ addRoundKey

/-- Encrypt the two blocks in slots `0 … 7` (as `ortho` takes them). -/
def encrypt2 : Prog isa :=
  .seq (.block (ortho ++ keyStart ++ addRoundKey))
    (.seq (.loop (.block roundBody) .ne) (.block (lastRound ++ ortho)))

/-- XOR the keystream block `b` into data block `b` at `esi`. -/
def xorBlock (b : Nat) : List Instr :=
  (List.range 4).flatMap fun w =>
    [.mov .eax (.mem (at_ .esi (16 * b + 4 * w))), xorS .eax (2 * w + b),
     .store (at_ .esi (16 * b + 4 * w)) .eax]

/-- Two blocks, and on to the next two. -/
def xorTwo : List Instr := xorBlock 0 ++ xorBlock 1 ++ [addI .esi 32, subI .ebp 2]

/-- The last block. -/
def xorOne : List Instr := xorBlock 0 ++ [subR .ebp .ebp]

/-- XOR the keystream into one group (two blocks, or the last one), and
store the data pointer and the count back (ZF is set when none are left). -/
def xorGroup : Prog isa :=
  .seq (.block [.mov .esi (.mem (at_ .edi dOff)), .mov .ebp (.mem (at_ .edi nOff)), .alu .cmp .ebp (.imm 2)])
    (.seq (.ite .ae (.block xorTwo) (.block xorOne))
      (.block [.store (at_ .edi dOff) .esi, .store (at_ .edi nOff) .ebp, .alu .test .ebp (.reg .ebp)]))

/-- One group of (up to) two blocks. -/
def group : Prog isa := .seq (.block ctrBlocks) (.seq encrypt2 xorGroup)

def ctr32 : Prog isa :=
  .seq (.block (saveRegs 5 ++ ctrSetup ++ keySetup))
    (.seq (.loop (.block keyBody) .ae)
      (.seq (.block groupSetup)
        (.seq (.ite .e (.block []) (.loop group .ne)) (.block restoreRegs))))

end VG.Impl.Aes.X86
