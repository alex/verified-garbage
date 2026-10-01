import VerifiedGarbage.Impl.Aes.Arm.Ctr32

/-!
# AES-CMAC: 32-bit ARM implementation

`vg_cmac_aes_subkeys(schedule = r0, rounds = r1, subkeys = r2, scratch = r3)`,
`vg_cmac_aes_update(schedule = r0, rounds = r1, state = r2, data = r3, n = [sp], scratch = [sp + 4])`
and `vg_cmac_aes_finalize(key = r0, rounds = r1, state = r2, last = r3, last_len = [sp], scratch = [sp + 4])`
(see `VG.Spec.Cmac.aesSubkeysContract` and the others), composed of calls of
the verified `vg_aes_ctr32`, one block at a time: with a counter block `X`
and a zero data block, it leaves `CIPH_K(X)` in the data block.

`vg_aes_ctr32(schedule, rounds, counter, data, n, scratch)` takes `n` and
`scratch` on the stack: a frame pushes them (`push {rA, rB}`, `n = 1` in
`rA` at `[sp]`) around each call, and its pop loads `rA` back. So the
functions use 8 bytes of stack.

The scratch buffer (2176 bytes): `[0, 2048)` is the working space of
`vg_aes_ctr32`, `[2048, 2064)` the counter block, and `[2064, 2096)` our
caller's callee-saved registers and our return address `lr`.

* `subkeys` computes `L = CIPH_K(0)` into the first block of `subkeys`, and
  doubles it there (`K1`) and into the second block (`K2`): the block as a
  big-endian 128-bit integer in `r0:r1:r2:r3`, shifted left by one bit, and
  XORed with `0x87` masked by the bit shifted out. `r6` holds `subkeys` and
  `r5` the scratch buffer across the call.
* `update` keeps its arguments in `r4` (schedule), `r5` (rounds), `r6`
  (state), `r7` (data), `r8` (blocks left) and `r10` (scratch) across the
  calls; each block, the counter block is `C ⊕ Mᵢ` and the state, zeroed,
  receives `CIPH_K(C ⊕ Mᵢ)`.
* `finalize` forms `Mₙ` in the counter block: `Mₙ* ⊕ K1` for a complete
  block, else `Mₙ*` copied a byte at a time onto zeros, `0x80` after it, and
  XORed with `K2`. It XORs in the chaining value and calls `vg_aes_ctr32`
  last, keeping only the scratch buffer (in `r5`) across the call.

The model has no register-offset addressing: the last bytes are copied
through advancing pointers, counting down with `subs`. Only the pointers,
`rounds`, `n` and `last_len` can affect timing: the branches are on `n` and
`last_len`, and the doubling is masked.
-/

namespace VG.Impl.CmacAes.Arm

open VG.Arm

/-- `mov d, n`. -/
def mov (d n : Reg) : Instr := .mov d (.reg n)

/-- The offset of the counter block in the scratch buffer. -/
def cOff : Nat := 2048

/-- The call of `vg_aes_ctr32`, with `n` (1) in `ra` and the scratch buffer in
`rb` pushed as its stack arguments, and `ra` popped. -/
def ctrCall (ra rb : Reg) : Prog isa :=
  .frame (.push [ra, rb]) (.call "vg_aes_ctr32" Impl.Aes.Arm.ctr32) (.pop ra 8)

/-! ## `vg_cmac_aes_subkeys` -/

/-- Saves `r4`–`r6` and `lr`, keeps `subkeys` in `r6` and the scratch buffer
in `r5`, zeroes the counter block and the first block of `subkeys`, and sets
up the arguments of `vg_aes_ctr32`. -/
def subkeysPre : List Instr :=
  [.str .r4 .r3 2064, .str .r5 .r3 2068, .str .r6 .r3 2072, .str .lr .r3 2076, mov .r6 .r2, mov .r5 .r3,
   .mov .r12 (.imm 0), .str .r12 .r3 cOff, .str .r12 .r3 (cOff + 4), .str .r12 .r3 (cOff + 8),
   .str .r12 .r3 (cOff + 12), .str .r12 .r2 0, .str .r12 .r2 4, .str .r12 .r2 8, .str .r12 .r2 12,
   .dp .add .r2 .r5 (.imm (BitVec.ofNat 32 cOff)), mov .r3 .r6, .mov .r4 (.imm 1)]

/-- The block at `r6 + src`, doubled (`VG.Spec.Cmac.dbl 16`), to `r6 + dst`. -/
def dbl (src dst : Nat) : List Instr :=
  [.ldr .r0 .r6 src, .ldr .r1 .r6 (src + 4), .ldr .r2 .r6 (src + 8), .ldr .r3 .r6 (src + 12),
   .rev .r0 .r0, .rev .r1 .r1, .rev .r2 .r2, .rev .r3 .r3,
   .mov .r12 (.shifted .r0 .lsr 31), .mov .r4 (.imm 0), .dp .sub .r12 .r4 (.reg .r12),
   .dp .and .r12 .r12 (.imm 0x87),
   .mov .r0 (.shifted .r0 .lsl 1), .dp .orr .r0 .r0 (.shifted .r1 .lsr 31),
   .mov .r1 (.shifted .r1 .lsl 1), .dp .orr .r1 .r1 (.shifted .r2 .lsr 31),
   .mov .r2 (.shifted .r2 .lsl 1), .dp .orr .r2 .r2 (.shifted .r3 .lsr 31),
   .mov .r3 (.shifted .r3 .lsl 1), .dp .eor .r3 .r3 (.reg .r12),
   .rev .r0 .r0, .rev .r1 .r1, .rev .r2 .r2, .rev .r3 .r3,
   .str .r0 .r6 dst, .str .r1 .r6 (dst + 4), .str .r2 .r6 (dst + 8), .str .r3 .r6 (dst + 12)]

/-- `K1` over `L`, `K2` after it, and the saved registers restored. -/
def subkeysPost : List Instr :=
  dbl 0 0 ++ dbl 0 16 ++
    [.ldr .r4 .r5 2064, .ldr .r6 .r5 2072, .ldr .lr .r5 2076, .ldr .r5 .r5 2068]

def subkeys : Prog isa :=
  .seq (.block subkeysPre) (.seq (ctrCall .r4 .r5) (.block subkeysPost))

/-! ## `vg_cmac_aes_update` -/

/-- The registers saved in the scratch buffer, and where (`r10`, the base of
the restore, last). -/
def saved : List (Reg × Nat) :=
  [(.r4, 2064), (.r5, 2068), (.r6, 2072), (.r7, 2076), (.r8, 2080), (.r9, 2084), (.lr, 2092),
   (.r10, 2088)]

/-- Saves them, with the scratch buffer (the second stack argument) in `r12`. -/
def save : List Instr := .ldrSp .r12 4 :: saved.map fun (r, d) => .str r .r12 d

/-- Restores them, with `r10` (restored last) the scratch buffer. -/
def restore : List Instr := saved.map fun (r, d) => .ldr r .r10 d

/-- The arguments to their registers; Z is set if there are no blocks. -/
def setup : List Instr :=
  [mov .r4 .r0, mov .r5 .r1, mov .r6 .r2, mov .r7 .r3, .ldrSp .r8 0, mov .r10 .r12, .cmp .r8 (.imm 0)]

/-- The counter block `C ⊕ Mᵢ` (the state at `r6`, the block at `r7`), and
the state zeroed. -/
def chainIn : List Instr :=
  [.ldr .r0 .r6 0, .ldr .r1 .r7 0, .dp .eor .r0 .r0 (.reg .r1), .str .r0 .r10 cOff,
   .ldr .r0 .r6 4, .ldr .r1 .r7 4, .dp .eor .r0 .r0 (.reg .r1), .str .r0 .r10 (cOff + 4),
   .ldr .r0 .r6 8, .ldr .r1 .r7 8, .dp .eor .r0 .r0 (.reg .r1), .str .r0 .r10 (cOff + 8),
   .ldr .r0 .r6 12, .ldr .r1 .r7 12, .dp .eor .r0 .r0 (.reg .r1), .str .r0 .r10 (cOff + 12),
   .mov .r0 (.imm 0), .str .r0 .r6 0, .str .r0 .r6 4, .str .r0 .r6 8, .str .r0 .r6 12]

/-- The arguments of `vg_aes_ctr32` for the block. -/
def updArgs : List Instr :=
  [mov .r0 .r4, mov .r1 .r5, .dp .add .r2 .r10 (.imm (BitVec.ofNat 32 cOff)), mov .r3 .r6, .mov .r9 (.imm 1)]

/-- On to the next block (Z is set when none are left). -/
def advance : List Instr := [.dp .add .r7 .r7 (.imm 16), .subs .r8 .r8 (.imm 1)]

/-- One block. -/
def body : Prog isa :=
  .seq (.block (chainIn ++ updArgs)) (.seq (ctrCall .r9 .r10) (.block advance))

def update : Prog isa :=
  .seq (.block (save ++ setup)) (.seq (.ite .eq (.block []) (.loop body .ne)) (.block restore))

/-! ## `vg_cmac_aes_finalize` -/

/-- The four words at `pb + pd` and `qb + qd` XORed into `cb + cd`, with
`r12` and `lr`. -/
def xor4 (pb qb cb : Reg) (pd qd cd : Nat) : List Instr :=
  (List.range 4).flatMap fun i =>
    [.ldr .r12 pb (pd + 4 * i), .ldr .lr qb (qd + 4 * i), .dp .eor .r12 .r12 (.reg .lr),
     .str .r12 cb (cd + 4 * i)]

/-- Saves `r4`, `r5` and `lr`, keeps the scratch buffer in `r5` and `last_len`
in `r4`; Z is set if `last_len` is 16. -/
def finSave : List Instr :=
  [.ldrSp .r12 4, .str .r4 .r12 2064, .str .r5 .r12 2068, .str .lr .r12 2072, mov .r5 .r12,
   .ldrSp .r4 0, .cmp .r4 (.imm 16)]

/-- `Mₙ = Mₙ* ⊕ K1` (`K1` at `r0 + 240`), for a complete last block. -/
def full : List Instr := xor4 .r3 .r0 .r5 0 240 cOff

/-- The counter block zeroed, with `lr` pointing at it; Z is set if
`last_len` is 0. -/
def zero : List Instr :=
  [.mov .r12 (.imm 0), .str .r12 .r5 cOff, .str .r12 .r5 (cOff + 4), .str .r12 .r5 (cOff + 8),
   .str .r12 .r5 (cOff + 12), .dp .add .lr .r5 (.imm (BitVec.ofNat 32 cOff)), .cmp .r4 (.imm 0)]

/-- The `r4` (nonzero) bytes at `r3` copied to `lr`, advancing both. -/
def copy : Prog isa :=
  .loop (.block [.ldrb .r12 .r3 0, .strb .r12 .lr 0, .dp .add .r3 .r3 (.imm 1),
    .dp .add .lr .lr (.imm 1), .subs .r4 .r4 (.imm 1)]) .ne

/-- `0x80` after the bytes (at `lr`), and the block XORed with `K2` (at
`r0 + 256`). -/
def padK2 : List Instr :=
  [.mov .r12 (.imm 0x80), .strb .r12 .lr 0] ++ xor4 .r5 .r0 .r5 cOff 256 cOff

/-- `Mₙ = K2 ⊕ (Mₙ* ‖ 10ʲ)`, for a partial last block (`last_len < 16`). -/
def partialBlock : Prog isa :=
  .seq (.block zero) (.seq (.ite .eq (.block []) copy) (.block padK2))

/-- The counter block `C ⊕ Mₙ` (the state at `r2`), the state zeroed, and the
arguments of `vg_aes_ctr32` but the schedule (`r0`) and the rounds (`r1`),
which are ours. -/
def finArgs : List Instr :=
  xor4 .r5 .r2 .r5 cOff 0 cOff ++
    [.mov .r12 (.imm 0), .str .r12 .r2 0, .str .r12 .r2 4, .str .r12 .r2 8, .str .r12 .r2 12,
     mov .r3 .r2, .dp .add .r2 .r5 (.imm (BitVec.ofNat 32 cOff)), .mov .r4 (.imm 1)]

/-- Everything before the call. -/
def finPre : Prog isa :=
  .seq (.block finSave) (.seq (.ite .eq (.block full) partialBlock) (.block finArgs))

def finalize : Prog isa :=
  .seq finPre (.seq (ctrCall .r4 .r5) (.block [.ldr .r4 .r5 2064, .ldr .lr .r5 2072, .ldr .r5 .r5 2068]))

end VG.Impl.CmacAes.Arm
