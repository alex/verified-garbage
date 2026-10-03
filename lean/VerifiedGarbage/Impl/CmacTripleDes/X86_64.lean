import VerifiedGarbage.Impl.CmacTripleDes.X86_64.Round

/-!
# TDEA-CMAC (3DES-CMAC): x86-64 implementation

`vg_cmac_triple_des_init(key = rdi, key_len = rsi, out = rdx, scratch = rcx)`,
`vg_cmac_triple_des_update(schedule = rdi, state = rsi, data = rdx, n = rcx, scratch = r8)`
and `vg_cmac_triple_des_finalize(key = rdi, state = rsi, last = rdx, last_len = rcx, scratch = r8)`
(see `VG.Spec.Cmac.tdesInitContract` and the others). Each encrypts blocks
with `block` (`X86_64/Round.lean`), inline: the block as a big-endian 64-bit
integer in `rax`, the key schedule at `r14` and the scratch buffer at `r15`.

The scratch buffer: slots 0–5 (bytes `[0, 48)`) are the block's, slots
6–11 hold our caller's callee-saved registers, and slots 12–14 are working
space: `init`'s three DES keys, `update`'s data pointer and the blocks
left, `finalize`'s last block `Mₙ`.

* `init` reads the three DES keys (the third is the first for a 16-byte
  key), writes their round keys (`roundKeys`, 128 bytes each) to `out`, and
  then encrypts the zero block with them (`L`) and doubles it twice, as a
  64-bit integer: shifted left by one bit, and XORed with `0x1b` masked by
  the bit shifted out.
* `update` keeps the state pointer in `rbp`, and the data pointer and the
  blocks left in slots 12 and 13; each block, `rax` is `C ⊕ Mᵢ`.
* `finalize` forms `Mₙ` in slot 12, as AES-CMAC's does (`Impl/CmacAes`):
  `Mₙ* ⊕ K1` for a complete block, else `Mₙ*` copied a byte at a time onto
  zeros, `0x80` after it, and XORed with `K2`.

Only the pointers, `key_len`, `n` and `last_len` can affect timing: the
branches are on them and on counters, and the doubling is masked.
-/

namespace VG.Impl.CmacTripleDes.X86_64

open VG.X86_64

/-- Our caller's callee-saved registers, and their slots. -/
def saved : List (Reg × Nat) := [(.rbx, 48), (.rbp, 56), (.r12, 64), (.r13, 72), (.r14, 80), (.r15, 88)]

/-- Saves the registers to the scratch buffer at `scr`. -/
def save (scr : Reg) : List Instr := saved.map fun (r, d) => .store (at_ scr d) r

/-- Restores the registers, with `r15` (restored last) the scratch buffer. -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .r15 d))

/-! ## `vg_cmac_triple_des_init` -/

/-- The DES key at `[rdi + d]`, as a big-endian integer, to slot `k`. -/
def keyWord (d k : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .rdi d)), .bswap .rax, .store (at_ .r15 (8 * k)) .rax]

/-- Saves the registers, and the three DES keys to slots 12–14: `K3` is
`K1` if `key_len` is 16. -/
def initPre : Prog isa :=
  .seq (.block (save .rcx ++ [.mov .r15 (.reg .rcx), .mov .rbp (.reg .rdx)] ++ keyWord 0 12 ++
      keyWord 8 13 ++ [.alu .cmp .rsi (.imm 16)]))
    (.seq (.ite .e (.block [.mov .rax (.mem (at_ .rdi 0))]) (.block [.mov .rax (.mem (at_ .rdi 16))]))
      (.block [.bswap .rax, .store (at_ .r15 112) .rax, .mov .rbx (.reg .r15), .alu .add .rbx (.imm 96),
        .mov32 .r10 (.imm 3)]))

/-- The round keys of the DES key at `[rbx]` to `[rbp]`, and on to the next. -/
def keysBody : List Instr :=
  [.mov .rax (.mem (at_ .rbx 0))] ++ roundKeys ++
    [.alu .add .rbp (.imm 128), .alu .add .rbx (.imm 8), .alu .sub .r10 (.imm 1)]

/-- The block in `rax`, doubled (`VG.Spec.Cmac.dbl 8`), and stored at
`[rbp + d]` (as bytes). -/
def dbl (d : Nat) : List Instr :=
  [.mov .rcx (.reg .rax), .shift .shr .rcx 63, .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rcx),
   .alu .and .rdx (.imm 0x1b), .alu .add .rax (.reg .rax), .alu .xor .rax (.reg .rdx),
   .mov .rcx (.reg .rax), .bswap .rcx, .store (at_ .rbp d) .rcx]

def init : Prog isa :=
  .seq initPre (.seq (.loop (.block keysBody) .ne)
    (.seq (.block [.mov .r14 (.reg .rbp), .alu .sub .r14 (.imm 384), .mov32 .rax (.imm 0)])
      (.seq block (.block (dbl 0 ++ dbl 8 ++ restore)))))

/-! ## `vg_cmac_triple_des_update` -/

/-- Saves the registers and the arguments; ZF is set if there are no blocks. -/
def updPre : List Instr :=
  save .r8 ++ [.mov .r15 (.reg .r8), .mov .r14 (.reg .rdi), .mov .rbp (.reg .rsi),
    .store (at_ .r15 96) .rdx, .store (at_ .r15 104) .rcx, .alu .test .rcx (.reg .rcx)]

/-- `C ⊕ Mᵢ`, as a big-endian integer, into `rax`. -/
def chainIn : List Instr :=
  [.mov .rcx (.mem (at_ .r15 96)), .mov .rax (.mem (at_ .rbp 0)), .alu .xor .rax (.mem (at_ .rcx 0)),
   .bswap .rax]

/-- `rax` stored to the state, and on to the next block (ZF is set when none
are left). -/
def chainOut : List Instr :=
  [.bswap .rax, .store (at_ .rbp 0) .rax, .mov .rcx (.mem (at_ .r15 96)), .alu .add .rcx (.imm 8),
   .store (at_ .r15 96) .rcx, .mov .rax (.mem (at_ .r15 104)), .alu .sub .rax (.imm 1),
   .store (at_ .r15 104) .rax]

def updBody : Prog isa := .seq (.block chainIn) (.seq block (.block chainOut))

def update : Prog isa :=
  .seq (.block updPre) (.seq (.ite .e (.block []) (.loop updBody .ne)) (.block restore))

/-! ## `vg_cmac_triple_des_finalize` -/

/-- `Mₙ = Mₙ* ⊕ K1` (`K1` at `rdi + 384`) into `rax`, for a complete last block. -/
def full : List Instr := [.mov .rax (.mem (at_ .rdx 0)), .alu .xor .rax (.mem (at_ .rdi 384))]

/-- `[rdx + r10]` and `[r15 + r10 + 96]`. -/
def lastByte : MemOp := { base := .rdx, index := some .r10 }
def padByte : MemOp := { base := .r15, index := some .r10, disp := 96 }

/-- Slot 12 zeroed; ZF is set if `last_len` is 0. -/
def zero : List Instr := [.mov32 .rax (.imm 0), .store (at_ .r15 96) .rax, .alu .test .rcx (.reg .rcx)]

/-- The `last_len` (1 to 7) bytes at `rdx` copied to slot 12. -/
def copy : Prog isa :=
  .seq (.block [.mov32 .r10 (.imm 0)])
    (.loop (.block [.movzx8 .rax lastByte, .store8 padByte .rax, .alu .add .r10 (.imm 1),
      .alu .cmp .r10 (.reg .rcx)]) .ne)

/-- `0x80` after the bytes, and the block XORed with `K2` (at `rdi + 392`)
into `rax`. -/
def padK2 : List Instr :=
  [.mov32 .rax (.imm 0x80), .store8 { base := .r15, index := some .rcx, disp := 96 } .rax,
   .mov .rax (.mem (at_ .r15 96)), .alu .xor .rax (.mem (at_ .rdi 392))]

/-- `Mₙ = K2 ⊕ (Mₙ* ‖ 10ʲ)` into `rax`, for a partial last block (`last_len < 8`). -/
def partialBlock : Prog isa :=
  .seq (.block zero) (.seq (.ite .e (.block []) copy) (.block padK2))

/-- Saves the registers and sets them up; `Mₙ` into `rax`. -/
def finPre : Prog isa :=
  .seq (.block (save .r8 ++ [.mov .r15 (.reg .r8), .mov .r14 (.reg .rdi), .mov .rbp (.reg .rsi),
      .alu .cmp .rcx (.imm 8)]))
    (.ite .e (.block full) partialBlock)

def finalize : Prog isa :=
  .seq finPre (.seq (.block [.alu .xor .rax (.mem (at_ .rbp 0)), .bswap .rax])
    (.seq block (.block ([.bswap .rax, .store (at_ .rbp 0) .rax] ++ restore))))

end VG.Impl.CmacTripleDes.X86_64
