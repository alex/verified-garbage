import VerifiedGarbage.Impl.Aes.X86_64.Callee

/-!
# AES-CMAC: x86-64 implementation

`vg_cmac_aes_subkeys(schedule = rdi, rounds = rsi, subkeys = rdx, scratch = rcx)`,
`vg_cmac_aes_update(schedule = rdi, rounds = rsi, state = rdx, data = rcx, n = r8, scratch = r9)`
and `vg_cmac_aes_finalize(key = rdi, rounds = rsi, state = rdx, last = rcx, last_len = r8, scratch = r9)`
(see `VG.Spec.Cmac.aesSubkeysContract` and the others), composed of calls of
the verified `vg_aes_ctr32`, one block at a time: with a counter block `X`
and a zero data block, it leaves `CIPH_K(X)` in the data block. They are
generic over the implementation of `vg_aes_ctr32` they call (`Ctr32`): each
is emitted once for each implementation (e.g. `vg_cmac_aes_update` calls
`vg_aes_ctr32`, and `vg_cmac_aes_update_aesni` calls `vg_aes_ctr32_aesni`).

The scratch buffer (2176 bytes): `[0, 2048)` is the working space of
`vg_aes_ctr32`, `[2048, 2064)` the counter block, and `[2064, 2112)` our
caller's callee-saved registers.

* `subkeys` computes `L = CIPH_K(0)` into the first block of `subkeys`, and
  doubles it there (`K1`) and into the second block (`K2`): the block as a
  big-endian 128-bit integer in `rax:rdx`, shifted left by one bit, and
  XORed with `0x87` masked by the bit shifted out. `rbx` holds `subkeys`
  and `rbp` the scratch buffer across the call.
* `update` keeps its arguments in `rbx` (schedule), `rbp` (rounds), `r12`
  (state), `r13` (data), `r14` (blocks left) and `r15` (scratch) across the
  calls; each block, the counter block is `C ⊕ Mᵢ` and the state, zeroed,
  receives `CIPH_K(C ⊕ Mᵢ)`.
* `finalize` forms `Mₙ` in the counter block: `Mₙ* ⊕ K1` for a complete
  block, else `Mₙ*` copied a byte at a time onto zeros, `0x80` after it, and
  XORed with `K2`. It XORs in the chaining value and calls `vg_aes_ctr32`
  last, so it keeps nothing across the call.

Only the pointers, `rounds`, `n` and `last_len` can affect timing: the
branches are on `n` and `last_len`, and the doubling is masked.
-/

namespace VG.Impl.CmacAes.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (Ctr32)

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- The offset of the counter block in the scratch buffer. -/
def cOff : Nat := 2048

/-- The arguments of `vg_aes_ctr32` for one block, other than the schedule
and the rounds: the counter block at `scr + cOff`, the data block at `out`,
`n = 1`, and the working space at `scr`. -/
def ctrArgs (scr out : Reg) : List Instr :=
  [.mov .r9 (.reg scr), .mov .rdx (.reg scr), .alu .add .rdx (.imm (BitVec.ofNat 32 cOff)),
   .mov .rcx (.reg out), .mov32 .r8 (.imm 1)]

/-! ## `vg_cmac_aes_subkeys` -/

/-- Saves `rbx` and `rbp`, keeps `subkeys` in `rbx` and the scratch buffer in
`rbp`, zeroes the counter block and the first block of `subkeys`, and sets up
the arguments of `vg_aes_ctr32`. -/
def subkeysPre : List Instr :=
  [.store (at_ .rcx 2064) .rbx, .store (at_ .rcx 2072) .rbp, .mov .rbx (.reg .rdx),
   .mov .rbp (.reg .rcx), .mov32 .rax (.imm 0), .store (at_ .rcx cOff) .rax,
   .store (at_ .rcx (cOff + 8)) .rax, .store (at_ .rdx 0) .rax, .store (at_ .rdx 8) .rax] ++
  ctrArgs .rbp .rbx

/-- The block at `rbx + src`, doubled (`VG.Spec.Cmac.dbl 16`), to `rbx + dst`. -/
def dbl (src dst : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .rbx src)), .bswap .rax, .mov .rdx (.mem (at_ .rbx (src + 8))), .bswap .rdx,
   .mov .rcx (.reg .rax), .shift .shr .rcx 63, .mov32 .r8 (.imm 0), .alu .sub .r8 (.reg .rcx),
   .alu .and .r8 (.imm 0x87),
   .mov .rcx (.reg .rdx), .shift .shr .rcx 63, .alu .add .rax (.reg .rax), .alu .or .rax (.reg .rcx),
   .alu .add .rdx (.reg .rdx), .alu .xor .rdx (.reg .r8),
   .bswap .rax, .bswap .rdx, .store (at_ .rbx dst) .rax, .store (at_ .rbx (dst + 8)) .rdx]

/-- `K1` over `L`, `K2` after it, and the saved registers restored. -/
def subkeysPost : List Instr :=
  dbl 0 0 ++ dbl 0 16 ++ [.mov .rbx (.mem (at_ .rbp 2064)), .mov .rbp (.mem (at_ .rbp 2072))]

def subkeys (c : Ctr32) : Prog isa :=
  .seq (.block subkeysPre) (.seq (.call c.name c.code) (.block subkeysPost))

/-! ## `vg_cmac_aes_update` -/

def saved : List (Reg × Nat) :=
  [(.rbx, 2064), (.rbp, 2072), (.r12, 2080), (.r13, 2088), (.r14, 2096), (.r15, 2104)]

def save : List Instr := saved.map fun (r, d) => .store (at_ .r9 d) r

/-- Restores the registers, with `r15` (restored last) the scratch buffer. -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .r15 d))

/-- The arguments to their registers; ZF is set if there are no blocks. -/
def setup : List Instr :=
  [.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx), .mov .r13 (.reg .rcx),
   .mov .r14 (.reg .r8), .mov .r15 (.reg .r9), .alu .test .r14 (.reg .r14)]

/-- The counter block `C ⊕ Mᵢ` (the state at `r12`, the block at `r13`), and
the state zeroed. -/
def chainIn : List Instr :=
  [.mov .rax (.mem (at_ .r12 0)), .alu .xor .rax (.mem (at_ .r13 0)), .store (at_ .r15 cOff) .rax,
   .mov .rax (.mem (at_ .r12 8)), .alu .xor .rax (.mem (at_ .r13 8)), .store (at_ .r15 (cOff + 8)) .rax,
   .mov32 .rax (.imm 0), .store (at_ .r12 0) .rax, .store (at_ .r12 8) .rax]

/-- The arguments of `vg_aes_ctr32` for the block. -/
def updArgs : List Instr := [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp)] ++ ctrArgs .r15 .r12

/-- On to the next block (ZF is set when none are left). -/
def advance : List Instr := [.alu .add .r13 (.imm 16), .alu .sub .r14 (.imm 1)]

/-- One block. -/
def body (c : Ctr32) : Prog isa :=
  .seq (.block (chainIn ++ updArgs)) (.seq (.call c.name c.code) (.block advance))

def update (c : Ctr32) : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.ite .e (.block []) (.loop (body c) .ne)) (.block restore))

/-! ## `vg_cmac_aes_finalize` -/

/-- `Mₙ = Mₙ* ⊕ K1` (`K1` at `rdi + 240`), for a complete last block. -/
def full : List Instr :=
  [.mov .rax (.mem (at_ .rcx 0)), .alu .xor .rax (.mem (at_ .rdi 240)), .store (at_ .r9 cOff) .rax,
   .mov .rax (.mem (at_ .rcx 8)), .alu .xor .rax (.mem (at_ .rdi 248)), .store (at_ .r9 (cOff + 8)) .rax]

/-- `[rcx + r10]` and `[r9 + r10 + cOff]`. -/
def lastByte : MemOp := { base := .rcx, index := some .r10 }
def padByte : MemOp := { base := .r9, index := some .r10, disp := cOff }

/-- The counter block zeroed; ZF is set if `last_len` is 0. -/
def zero : List Instr :=
  [.mov32 .rax (.imm 0), .store (at_ .r9 cOff) .rax, .store (at_ .r9 (cOff + 8)) .rax,
   .alu .test .r8 (.reg .r8)]

/-- The `last_len` (1 to 15) bytes at `rcx` copied to the counter block. -/
def copy : Prog isa :=
  .seq (.block [.mov32 .r10 (.imm 0)])
    (.loop (.block [.movzx8 .rax lastByte, .store8 padByte .rax, .alu .add .r10 (.imm 1),
      .alu .cmp .r10 (.reg .r8)]) .ne)

/-- `0x80` after the bytes, and the block XORed with `K2` (at `rdi + 256`). -/
def padK2 : List Instr :=
  [.mov32 .rax (.imm 0x80), .store8 { base := .r9, index := some .r8, disp := cOff } .rax,
   .mov .rax (.mem (at_ .r9 cOff)), .alu .xor .rax (.mem (at_ .rdi 256)), .store (at_ .r9 cOff) .rax,
   .mov .rax (.mem (at_ .r9 (cOff + 8))), .alu .xor .rax (.mem (at_ .rdi 264)),
   .store (at_ .r9 (cOff + 8)) .rax]

/-- `Mₙ = K2 ⊕ (Mₙ* ‖ 10ʲ)`, for a partial last block (`last_len < 16`). -/
def partialBlock : Prog isa :=
  .seq (.block zero) (.seq (.ite .e (.block []) copy) (.block padK2))

/-- The counter block `C ⊕ Mₙ` (the state at `rdx`), the state zeroed, and
the arguments of `vg_aes_ctr32` but the schedule (`rdi`) and the rounds
(`rsi`), which are ours. -/
def finArgs : List Instr :=
  [.mov .rax (.mem (at_ .r9 cOff)), .alu .xor .rax (.mem (at_ .rdx 0)), .store (at_ .r9 cOff) .rax,
   .mov .rax (.mem (at_ .r9 (cOff + 8))), .alu .xor .rax (.mem (at_ .rdx 8)),
   .store (at_ .r9 (cOff + 8)) .rax,
   .mov32 .rax (.imm 0), .store (at_ .rdx 0) .rax, .store (at_ .rdx 8) .rax,
   .mov .rcx (.reg .rdx), .mov .rdx (.reg .r9), .alu .add .rdx (.imm (BitVec.ofNat 32 cOff)),
   .mov32 .r8 (.imm 1)]

/-- Everything before the call. -/
def finPre : Prog isa :=
  .seq (.block [.alu .cmp .r8 (.imm 16)]) (.seq (.ite .e (.block full) partialBlock) (.block finArgs))

def finalize (c : Ctr32) : Prog isa := .seq finPre (.call c.name c.code)

end VG.Impl.CmacAes.X86_64
