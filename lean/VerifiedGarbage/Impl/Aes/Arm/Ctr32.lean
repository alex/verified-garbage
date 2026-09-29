import VerifiedGarbage.Impl.Aes.Arm.Linear

/-!
# AES counter mode (GCM's `inc₃₂`), bitsliced, on ARMv7

`vg_aes_ctr32(schedule = r0, rounds = r1, counter = r2, data = r3, n = [sp], scratch = [sp, #4])`.

Constant-time AES in the style of BearSSL's `aes_ct` (Thomas Pornin, MIT
licence): two blocks at a time, bitsliced in eight 32-bit registers
(`Linear.lean`, `Sbox.lean`).

* The callee-saved registers `r4`–`r11` and `lr` are saved in slots 32–40
  of the scratch buffer, the counter block in slots 41–44: its words 0–2
  (little-endian, as loaded) and the 32-bit counter as an integer.
* The final counter `inc₃₂ⁿ(CB₁)` is written first.
* The round keys are bitsliced once, into bytes `lastKey − 32 (rounds −
  j)` of the scratch buffer for round `j`, so that the last is always at
  byte `lastKey`. The loop runs from the last round key down, counting in
  `lr`, with the data pointer in `r8` (the scratch buffer's base is loaded
  again from the stack afterwards).
* Between groups, the data left is at `r10`, the number of blocks left in
  `r11`, and the first round key at `r12`; each group stores them in
  slots 45–47 (the encryption uses every other register) and loads them
  back.
* Each group of two blocks: build the counter blocks, bitslice them,
  encrypt (the round loop runs `kp` over the round keys until the last but
  one), un-bitslice, and XOR the keystream into the data, two blocks or the
  last one.
* Only the pointers, `rounds`, `n` and what is computed from them (the
  loop counters and the round key and data pointers, in registers or
  stored in the scratch buffer) are public; no address and no branch
  depends on anything else.
-/

namespace VG.Impl.Aes.Arm

open VG.Arm

/-- The callee-saved registers, and their slots. -/
def savedRegs : List (Reg × Nat) :=
  [(.r4, 32), (.r5, 33), (.r6, 34), (.r7, 35), (.r8, 36), (.r9, 37), (.r10, 38), (.r11, 39),
   (.lr, 40)]

/-- Save and restore them, with the scratch buffer's base in `b`. -/
def saveRegs (b : Reg) : List Instr := savedRegs.map fun (r, k) => .str r b (4 * k)
def restoreRegs (b : Reg) : List Instr := savedRegs.map fun (r, k) => .ldr r b (4 * k)

/-- The slots of the counter block. -/
def cW (k : Nat) : Nat := 41 + k
def cNum : Nat := 44

/-- The slots of the data pointer, the blocks left and the first round key. -/
def dSlot : Nat := 45
def lSlot : Nat := 46
def fkSlot : Nat := 47

/-- The byte offset of the last round key in the scratch buffer. -/
def lastKey : Nat := 2016

/-- Load the scratch buffer's base (to `r12`), save the registers, load the
counter block (`r2`) into its slots, and write the final counter
`(c + n) mod 2³²` back. -/
def prologue : List Instr :=
  [.ldrSp .r12 4] ++ saveRegs .r12 ++
  [.ldr t0 .r2 0, .str t0 .r12 (4 * cW 0), .ldr t0 .r2 4, .str t0 .r12 (4 * cW 1),
   .ldr t0 .r2 8, .str t0 .r12 (4 * cW 2),
   .ldr t0 .r2 12, .rev t0 t0, .str t0 .r12 (4 * cNum),
   .ldrSp t1 0, .dp .add t0 t0 (.reg t1), .rev t0 t0, .str t0 .r2 12]

/-- Set up the key loop: `kp := scratch + lastKey`, `r12 := schedule + 16
rounds`, `lr := rounds + 1` (the round keys left), `r8 := data`. -/
def keySetup : List Instr :=
  [.dp .add kp .r12 (.imm (BitVec.ofNat 32 lastKey)), .dp .add .r12 .r0 (.shifted .r1 .lsl 4),
   .dp .add .lr .r1 (.imm 1), movR .r8 .r3]

/-- The round key at `r12`, as two blocks for `ortho`. -/
def keyLoad : List Instr :=
  [.ldr (q 0) .r12 0, .ldr (q 2) .r12 4, .ldr (q 4) .r12 8, .ldr (q 6) .r12 12,
   movR (q 1) (q 0), movR (q 3) (q 2), movR (q 5) (q 4), movR (q 7) (q 6)]

/-- Store the bitsliced round key at `kp`. -/
def keyStore : List Instr := (List.range 8).map fun j => .str (q j) kp (4 * j)

/-- Step `r12` and `kp` back a round key, and count it. -/
def keyStep : List Instr :=
  [.dp .sub .r12 .r12 (.imm 16), .dp .sub kp kp (.imm 32), .subs .lr .lr (.imm 1)]

/-- Bitslice the round key at `r12` to `kp`, and step back. -/
def keyBody : List Instr := keyLoad ++ ortho ++ keyStore ++ keyStep

/-- After the key loop: the first round key to `r12`, the data pointer to
`r10`, the blocks left to `r11`, and the scratch buffer's base to `sb`. -/
def keyDone : List Instr :=
  [.dp .add .r12 kp (.imm 32), movR .r10 .r8, .ldrSp .r11 0, .ldrSp sb 4]

/-- The counter block `c + b` (`b < 2`): word `k` in `q (2k + b)`. -/
def ctrBlock (b : Nat) : List Instr :=
  [ldS (q b) (cW 0), ldS (q (2 + b)) (cW 1), ldS (q (4 + b)) (cW 2), ldS t0 cNum,
   .dp .add t0 t0 (.imm (BitVec.ofNat 32 b)), .rev (q (6 + b)) t0]

/-- The two counter blocks, and `c := c + 2`. -/
def ctrBlocks : List Instr :=
  ctrBlock 0 ++ ctrBlock 1 ++ [ldS t0 cNum, .dp .add t0 t0 (.imm 2), stS cNum t0]

/-- A middle round, with `kp` at the previous round key; loops until `kp`
is at the last round key but one. -/
def roundBody : List Instr :=
  [.dp .add kp kp (.imm 32)] ++ sboxCode ++ shiftRows ++ mixColumns ++ addRoundKey ++
  [.dp .sub t0 kp (.reg sb), .cmp t0 (.imm (BitVec.ofNat 32 (lastKey - 32)))]

/-- The last round. -/
def lastRound : List Instr := [.dp .add kp kp (.imm 32)] ++ sboxCode ++ shiftRows ++ addRoundKey

/-- Encrypt the two blocks in `q 0 … q 7` (as `ortho` takes them), with
`kp` at the first round key. -/
def encrypt2 : Prog isa :=
  .seq (.block (ortho ++ addRoundKey))
    (.seq (.loop (.block roundBody) .ne) (.block (lastRound ++ ortho)))

/-- XOR the keystream block `b` into data block `b` (at `r10`). -/
def xorBlock (b : Nat) : List Instr :=
  (List.range 4).flatMap fun k =>
    [.ldr .lr .r10 (16 * b + 4 * k), eorR .lr .lr (q (2 * k + b)), .str .lr .r10 (16 * b + 4 * k)]

/-- Two blocks, and on to the next two. -/
def xorFull : List Instr :=
  xorBlock 0 ++ xorBlock 1 ++ [.dp .add .r10 .r10 (.imm 32), .dp .sub .r11 .r11 (.imm 2)]

/-- The last block (and none left). -/
def xorTail : List Instr := xorBlock 0 ++ [.mov .r11 (.imm 0)]

/-- Store the data pointer, the blocks left and the first round key, and
point `kp` at the first round key. -/
def groupSave : List Instr :=
  [stS dSlot .r10, stS lSlot .r11, stS fkSlot .r12, movR kp .r12]

/-- Load them back. -/
def groupLoad : List Instr := [ldS .r10 dSlot, ldS .r11 lSlot, ldS .r12 fkSlot]

/-- One group of (up to) two blocks. -/
def group : Prog isa :=
  .seq (.block (groupSave ++ ctrBlocks))
    (.seq encrypt2
      (.seq (.block (groupLoad ++ [.mov kp (lsrOp .r11 1), .cmp kp (.imm 0)]))
        (.seq (.ite .ne (.block xorFull) (.block xorTail)) (.block [.cmp .r11 (.imm 0)]))))

def ctr32 : Prog isa :=
  .seq (.block (prologue ++ keySetup))
    (.seq (.loop (.block keyBody) .ne)
      (.seq (.block (keyDone ++ [.cmp .r11 (.imm 0)]))
        (.seq (.ite .eq (.block []) (.loop group .ne))
          (.block (.ldrSp .r12 4 :: restoreRegs .r12)))))

end VG.Impl.Aes.Arm
