import VerifiedGarbage.Impl.Aes.X86_64.Linear

/-!
# AES counter mode (GCM's `inc₃₂`), bitsliced, on x86-64

`vg_aes_ctr32(schedule = rdi, rounds = rsi, counter = rdx, data = rcx, n = r8, scratch = r9)`.

Constant-time AES in the style of BearSSL's `aes_ct64` (Thomas Pornin, MIT
licence): four blocks at a time, bitsliced in eight 64-bit registers
(`Linear.lean`, `Sbox.lean`).

* The callee-saved registers are saved in slots 48–53 of the scratch
  buffer, the counter block in slots 54–56: bytes 0–7, bytes 8–11 (the
  high half zero) and the 32-bit counter as an integer (in the low half).
* The final counter `inc₃₂ⁿ(CB₁)` is written first.
* The round keys are bitsliced once, into slots `128 + 8 (j + 14 - rounds)`
  for round `j`, so that the last is always at slot 240 (byte 1920). The
  loop runs from the last round key down, with `rounds` counting down in
  `r15`.
* Each group of four blocks: build the counter blocks, bitslice them,
  encrypt (the round loop runs `rsi` over the round keys until the last
  but one), un-bitslice, and XOR the keystream into the data, four blocks
  or the remaining one to three.
* Only `rdi` (the first round key), `rsi`, `rdx` (the data), `r8` (the
  blocks left), `r9` and `r15` during the key loop hold public values; no
  address and no branch depends on anything else.
-/

namespace VG.Impl.Aes.X86_64

open VG.X86_64

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- The callee-saved registers, and their slots. -/
def savedRegs : List (Reg × Nat) := [(.rbx, 48), (.rbp, 49), (.r12, 50), (.r13, 51), (.r14, 52), (.r15, 53)]

def saveRegs : List Instr := savedRegs.map fun (r, k) => st k r
def restoreRegs : List Instr := savedRegs.map fun (r, k) => movS r k

/-- The slots of the counter block. -/
def cLo : Nat := 54
def cHi : Nat := 55
def cNum : Nat := 56

/-- Load the counter block (`rdx`) into its slots, and write the final
counter `(c + n) mod 2³²` back; then move the data pointer to `rdx`. -/
def ctrSetup : List Instr :=
  [.mov .rax (.mem (at_ .rdx 0)), st cLo .rax,
   .mov32 .rax (.mem (at_ .rdx 8)), st cHi .rax,
   .mov32 .rax (.mem (at_ .rdx 12)), .bswap32 .rax, .store32 (slotAt sb cNum) .rax,
   .alu32 .add .rax (.reg .r8), .bswap32 .rax, .store32 (at_ .rdx 12) .rax,
   movR .rdx .rcx]

/-- The byte offset of the last round key in the scratch buffer. -/
def lastKey : Nat := 1920

/-- Set up the key loop: `r15 := rounds`, `rdi := schedule + 16 rounds`,
`rsi := r9 + lastKey`. -/
def keySetup : List Instr :=
  [movR .r15 .rsi, .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi),
   .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi), .alu .add .rdi (.reg .rsi),
   movR .rsi .r9, .alu .add .rsi (.imm (BitVec.ofNat 32 lastKey))]

/-- The round key at `rdi`, as four blocks for `toBs`. -/
def keyLoad : List Instr :=
  [.mov (q 0) (.mem (at_ .rdi 0)), .mov (q 4) (.mem (at_ .rdi 8)),
   movR (q 1) (q 0), movR (q 2) (q 0), movR (q 3) (q 0),
   movR (q 5) (q 4), movR (q 6) (q 4), movR (q 7) (q 4)]

/-- Store the bitsliced round key at `rsi`. -/
def keyStore : List Instr := (List.range 8).map fun j => .store (slotAt .rsi j) (q j)

/-- Step `rdi` and `rsi` back a round key, and `r15` down (CF is set when it
passes zero). -/
def keyStep : List Instr := [.alu .sub .rdi (.imm 16), .alu .sub .rsi (.imm 64), .alu .sub .r15 (.imm 1)]

/-- Bitslice the round key at `rdi` to `rsi`, and step back. -/
def keyBody : List Instr := keyLoad ++ toBs ++ keyStore ++ keyStep

/-- `rdi := ` the first round key. -/
def keyDone : List Instr := [movR .rdi .rsi, .alu .add .rdi (.imm 64)]

/-- The counter blocks `c + b` (`b < 4`): bytes 0–7 in `q b`, bytes 8–15 in
`q (b + 4)`; and `c := c + 4`. -/
def ctrBlock (b : Nat) : List Instr :=
  [movS (q b) cLo, .mov32 t0 (.mem (slotAt sb cNum)), .alu32 .add t0 (.imm (BitVec.ofNat 32 b)),
   .bswap32 t0, rorI t0 32, movS (q (b + 4)) cHi, xorR (q (b + 4)) t0]

def ctrBlocks : List Instr :=
  ctrBlock 0 ++ ctrBlock 1 ++ ctrBlock 2 ++ ctrBlock 3 ++
  [.mov32 t0 (.mem (slotAt sb cNum)), .alu32 .add t0 (.imm 4), .store32 (slotAt sb cNum) t0]

/-- A middle round, with `rsi` at the previous round key; loops until `rsi`
is at the last round key but one. -/
def roundBody : List Instr :=
  [.alu .add kp (.imm 64)] ++ sboxCode ++ shiftRows ++ mixColumns ++ addRoundKey ++
  [movR t0 sb, .alu .add t0 (.imm (BitVec.ofNat 32 (lastKey - 64))), .alu .cmp kp (.reg t0)]

/-- The last round. -/
def lastRound : List Instr := [.alu .add kp (.imm 64)] ++ sboxCode ++ shiftRows ++ addRoundKey

/-- Encrypt the four blocks in `q 0 … q 7` (as `toBs` takes them). -/
def encrypt4 : Prog isa :=
  .seq (.block (toBs ++ [movR kp .rdi] ++ addRoundKey))
    (.seq (.loop (.block roundBody) .ne) (.block (lastRound ++ fromBs)))

/-- XOR the keystream block `b` into data block `b`. -/
def xorBlock (b : Nat) : List Instr :=
  [.mov t0 (.mem (at_ .rdx (16 * b))), xorR t0 (q b), .store (at_ .rdx (16 * b)) t0,
   .mov t0 (.mem (at_ .rdx (16 * b + 8))), xorR t0 (q (b + 4)), .store (at_ .rdx (16 * b + 8)) t0]

/-- Four blocks, and on to the next four (ZF is set when none are left). -/
def xorFull : List Instr :=
  (List.range 4).flatMap xorBlock ++ [.alu .add .rdx (.imm 64), .alu .sub .r8 (.imm 4)]

/-- The last one to three blocks (and ZF set). -/
def xorTail : Prog isa :=
  .seq (.block (xorBlock 0 ++ [.alu .cmp .r8 (.imm 2)]))
    (.seq (.ite .ae (.seq (.block (xorBlock 1 ++ [.alu .cmp .r8 (.imm 3)]))
        (.ite .ae (.block (xorBlock 2)) (.block [])))
      (.block []))
    (.block [.alu .sub .r8 (.reg .r8)]))

/-- One group of (up to) four blocks. -/
def group : Prog isa :=
  .seq (.block ctrBlocks)
    (.seq encrypt4
      (.seq (.block [.alu .cmp .r8 (.imm 4)]) (.ite .ae (.block xorFull) xorTail)))

def ctr32 : Prog isa :=
  .seq (.block (saveRegs ++ ctrSetup ++ keySetup))
    (.seq (.loop (.block keyBody) .ae)
      (.seq (.block (keyDone ++ [.alu .test .r8 (.reg .r8)]))
        (.seq (.ite .e (.block []) (.loop group .ne)) (.block restoreRegs))))

end VG.Impl.Aes.X86_64
