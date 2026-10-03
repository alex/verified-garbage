import VerifiedGarbage.Impl.Aes.X86.Callee

/-!
# AES-CMAC: x86 (32-bit) implementation

`vg_cmac_aes_subkeys(schedule, rounds, subkeys, scratch)`,
`vg_cmac_aes_update(schedule, rounds, state, data, n, scratch)` and
`vg_cmac_aes_finalize(key, rounds, state, last, last_len, scratch)` (see
`VG.Spec.Cmac.aesSubkeysContract` and the others), every argument on the
stack (cdecl), composed of calls of the verified `vg_aes_ctr32`, one block
at a time: with a counter block `X` and a zero data block, it leaves
`CIPH_K(X)` in the data block.

Each call pushes the six arguments of `vg_aes_ctr32` (`schedule`, `rounds`,
the counter block, the data block, `n = 1` and the working space, last to
first) in a frame of its own, popped (into `eax`) when it returns: with the
return address the call stores, it uses the 28 bytes below `esp`. The
callee preserves `ebx`, `esi`, `edi` and `ebp`; our caller's values of those
are saved in the scratch buffer.

The scratch buffer (2176 bytes): `[0, 2048)` is the working space of
`vg_aes_ctr32`, `[2048, 2064)` the counter block, and `[2064, 2080)` our
caller's `ebx`, `esi`, `edi` and `ebp`.

* `subkeys` computes `L = CIPH_K(0)` into the first block of `subkeys`, and
  doubles it there (`K1`) and into the second block (`K2`): the block as a
  big-endian 128-bit integer in `eax:ecx:edx:esi`, shifted left by one bit
  (`add r, r`), and XORed with `0x87` masked by the bit shifted out.
* `update` keeps only the pointer to the next block (`esi`) across the
  calls, and reloads its other arguments from the stack; it stops when the
  pointer reaches `data + 16 n`. Each block, the counter block is `C ⊕ Mᵢ`
  and the state, zeroed, receives `CIPH_K(C ⊕ Mᵢ)`.
* `finalize` forms `Mₙ` in the counter block: `Mₙ* ⊕ K1` for a complete
  block, else `Mₙ*` copied a byte at a time onto zeros, `0x80` after it, and
  XORed with `K2`. It XORs in the chaining value and calls `vg_aes_ctr32`
  last.

Only the pointers, `rounds`, `n` and `last_len` can affect timing: the
branches are on `n` and `last_len`, and the doubling is masked.
-/

namespace VG.Impl.CmacAes.X86

open VG.X86

/-- `[b + d]` -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- The stack argument `i` (from 0), `[esp + 4 + 4 i]`. -/
def argOp (i : Nat) : Src := .mem (at_ .esp (4 + 4 * i))

/-- The offset of the counter block in the scratch buffer. -/
def cOff : Nat := 2048

/-- The callee-saved registers, and where they are saved in the scratch buffer. -/
def saved : List (Reg × Nat) := [(.ebx, 2064), (.esi, 2068), (.edi, 2072), (.ebp, 2076)]

/-- Save them, with the scratch buffer in `eax`. -/
def save : List Instr := saved.map fun (r, d) => .store (at_ .eax d) r

/-- Restore them, with the scratch buffer (the stack argument `i`) loaded into `eax`. -/
def restore (i : Nat) : List Instr := .mov .eax (argOp i) :: saved.map fun (r, d) => .mov r (.mem (at_ .eax d))

/-- The call of `vg_aes_ctr32(eax, ecx, edx, ebx, edi, ebp)`, its arguments
pushed last to first. -/
def ctrCall (c : Impl.Aes.X86.Ctr32) : Prog isa :=
  .frame (.push [.ebp, .edi, .ebx, .edx, .ecx, .eax]) (.call c.name c.code) (.pop .eax 6)

/-- The arguments of `vg_aes_ctr32` but the data block (`ebx`) and the
working space (`ebp`): the schedule and the rounds (our stack arguments 0
and 1), the counter block in the scratch buffer and `n = 1`. -/
def ctrArgs : List Instr :=
  [.mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .edx (.reg .ebp), .alu .add .edx (.imm (BitVec.ofNat 32 cOff)),
   .mov .edi (.imm 1)]

/-- The four words at `pb + pd` and `qb + qd` XORed into `cb + cd`, with
`eax` and `ecx`. -/
def xor4 (pb qb cb : Reg) (pd qd cd : Nat) : List Instr :=
  (List.range 4).flatMap fun i =>
    [.mov .eax (.mem (at_ pb (pd + 4 * i))), .mov .ecx (.mem (at_ qb (qd + 4 * i))), .alu .xor .eax (.reg .ecx),
     .store (at_ cb (cd + 4 * i)) .eax]

/-- The block at `b + d` zeroed, with `eax`. -/
def zero4 (b : Reg) (d : Nat) : List Instr :=
  .mov .eax (.imm 0) :: (List.range 4).map fun i => .store (at_ b (d + 4 * i)) .eax

/-! ## `vg_cmac_aes_subkeys` -/

/-- Saves the registers, keeps `subkeys` in `ebx` and the scratch buffer in
`ebp`, zeroes the counter block and the first block of `subkeys`, and sets
up the arguments of `vg_aes_ctr32`. -/
def subkeysPre : List Instr :=
  [.mov .eax (argOp 3)] ++ save ++ [.mov .ebp (.reg .eax), .mov .ebx (argOp 2)] ++ zero4 .ebp cOff ++
    zero4 .ebx 0 ++ ctrArgs

/-- The block at `ebx + src`, doubled (`VG.Spec.Cmac.dbl 16`), to `ebx + dst`. -/
def dbl (src dst : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .ebx src)), .mov .ecx (.mem (at_ .ebx (src + 4))), .mov .edx (.mem (at_ .ebx (src + 8))),
   .mov .esi (.mem (at_ .ebx (src + 12))), .bswap .eax, .bswap .ecx, .bswap .edx, .bswap .esi,
   .mov .edi (.reg .eax), .shift .shr .edi 31, .mov .ebp (.imm 0), .alu .sub .ebp (.reg .edi),
   .alu .and .ebp (.imm 0x87),
   .alu .add .eax (.reg .eax), .mov .edi (.reg .ecx), .shift .shr .edi 31, .alu .or .eax (.reg .edi),
   .alu .add .ecx (.reg .ecx), .mov .edi (.reg .edx), .shift .shr .edi 31, .alu .or .ecx (.reg .edi),
   .alu .add .edx (.reg .edx), .mov .edi (.reg .esi), .shift .shr .edi 31, .alu .or .edx (.reg .edi),
   .alu .add .esi (.reg .esi), .alu .xor .esi (.reg .ebp),
   .bswap .eax, .bswap .ecx, .bswap .edx, .bswap .esi,
   .store (at_ .ebx dst) .eax, .store (at_ .ebx (dst + 4)) .ecx, .store (at_ .ebx (dst + 8)) .edx,
   .store (at_ .ebx (dst + 12)) .esi]

/-- `K1` over `L`, `K2` after it, and the saved registers restored. -/
def subkeysPost : List Instr := dbl 0 0 ++ dbl 0 16 ++ restore 3

def subkeys (c : Impl.Aes.X86.Ctr32) : Prog isa := .seq (.block subkeysPre) (.seq (ctrCall c) (.block subkeysPost))

/-! ## `vg_cmac_aes_update` -/

/-- Saves the registers, and the pointer to the first block in `esi`; ZF is
set if there are no blocks. -/
def setup : List Instr :=
  [.mov .eax (argOp 5)] ++ save ++ [.mov .esi (argOp 3), .mov .eax (argOp 4), .alu .test .eax (.reg .eax)]

/-- The counter block `C ⊕ Mᵢ` (the state at `ebx`, the block at `esi`), the
state zeroed, and the arguments of `vg_aes_ctr32`. -/
def chainIn : List Instr :=
  [.mov .ebx (argOp 2), .mov .ebp (argOp 5)] ++ xor4 .ebx .esi .ebp 0 0 cOff ++ zero4 .ebx 0 ++ ctrArgs

/-- On to the next block; ZF is set once `esi` reaches `data + 16 n`. -/
def advance : List Instr :=
  [.alu .add .esi (.imm 16), .mov .eax (argOp 4), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
   .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (argOp 3), .alu .cmp .esi (.reg .eax)]

/-- One block. -/
def body (c : Impl.Aes.X86.Ctr32) : Prog isa := .seq (.block chainIn) (.seq (ctrCall c) (.block advance))

def update (c : Impl.Aes.X86.Ctr32) : Prog isa :=
  .seq (.block setup) (.seq (.ite .e (.block []) (.loop (body c) .ne)) (.block (restore 5)))

/-! ## `vg_cmac_aes_finalize` -/

/-- Saves the registers, keeps the scratch buffer in `ebp`; ZF is set if
`last_len` is 16. -/
def finSave : List Instr :=
  [.mov .eax (argOp 5)] ++ save ++ [.mov .ebp (.reg .eax), .mov .ecx (argOp 4), .alu .cmp .ecx (.imm 16)]

/-- `Mₙ = Mₙ* ⊕ K1` (`K1` at `key + 240`), for a complete last block. -/
def full : List Instr := [.mov .ebx (argOp 3), .mov .edx (argOp 0)] ++ xor4 .ebx .edx .ebp 0 240 cOff

/-- The counter block zeroed, `edi` pointing at it, `esi` at the last bytes
and `ecx` their number; ZF is set if there are none. -/
def zero : List Instr :=
  zero4 .ebp cOff ++ [.mov .edi (.reg .ebp), .alu .add .edi (.imm (BitVec.ofNat 32 cOff)), .mov .esi (argOp 3),
    .mov .ecx (argOp 4), .alu .test .ecx (.reg .ecx)]

/-- The `ecx` (nonzero) bytes at `esi` copied to `edi`, advancing both. -/
def copy : Prog isa :=
  .loop (.block [.movzx8 .eax (at_ .esi 0), .store8 (at_ .edi 0) .al, .alu .add .esi (.imm 1),
    .alu .add .edi (.imm 1), .alu .sub .ecx (.imm 1)]) .ne

/-- `0x80` after the bytes (at `edi`), and the block XORed with `K2` (at
`key + 256`). -/
def padK2 : List Instr :=
  [.mov .eax (.imm 0x80), .store8 (at_ .edi 0) .al, .mov .edx (argOp 0)] ++ xor4 .ebp .edx .ebp cOff 256 cOff

/-- `Mₙ = K2 ⊕ (Mₙ* ‖ 10ʲ)`, for a partial last block (`last_len < 16`). -/
def partialBlock : Prog isa :=
  .seq (.block zero) (.seq (.ite .e (.block []) copy) (.block padK2))

/-- The counter block `C ⊕ Mₙ` (the state at `ebx`), the state zeroed, and
the arguments of `vg_aes_ctr32`. -/
def finArgs : List Instr :=
  [.mov .ebx (argOp 2)] ++ xor4 .ebp .ebx .ebp cOff 0 cOff ++ zero4 .ebx 0 ++ ctrArgs

/-- Everything before the call. -/
def finPre : Prog isa :=
  .seq (.block finSave) (.seq (.ite .e (.block full) partialBlock) (.block finArgs))

def finalize (c : Impl.Aes.X86.Ctr32) : Prog isa := .seq finPre (.seq (ctrCall c) (.block (restore 5)))

end VG.Impl.CmacAes.X86
