import VerifiedGarbage.Impl.CmacTripleDes.X86.Round

/-!
# TDEA-CMAC (3DES-CMAC): x86 (32-bit) implementation

`vg_cmac_triple_des_init(key, key_len, out, scratch)`,
`vg_cmac_triple_des_update(schedule, state, data, n, scratch)` and
`vg_cmac_triple_des_finalize(key, state, last, last_len, scratch)` (see
`VG.Spec.Cmac.tdesInitContract` and the others), every argument on the
stack (cdecl). Each encrypts blocks with `block` (`X86/Round.lean`), inline:
the block as a big-endian 64-bit integer in `eax:edx` (its high and low
words), the key schedule at `esi` and the scratch buffer at `ebp`. The block
uses every register, so the functions save our caller's `ebx`, `esi`, `edi`
and `ebp` in the scratch buffer, and reload their arguments from the stack.

The scratch buffer: bytes `[0, 84)` are the block's (`X86/Round.lean`);
`[84, 100)` hold our caller's `ebx`, `esi`, `edi` and `ebp`; `[100, 124)` are
`init`'s three DES keys (each as its high and low words); `[128, 136)`
`update`'s next block and blocks left; and `[136, 144)` `finalize`'s last
block `Mₙ`.

* `init` reads the three DES keys (the third is the first for a 16-byte
  key), writes their round keys (`roundKeys`, 128 bytes each) to `out`
  (`edi`, advancing), and then encrypts the zero block with them (`L`) and
  doubles it twice, as a 64-bit integer: shifted left by one bit (`add r,
  r`), and XORed with `0x1b` masked by the bit shifted out.
* `update` reloads the data pointer each block; after the block, it loads
  it and the count before it stores the state, and stores them back after.
* `finalize` forms `Mₙ` in `eax:edx` as little-endian words: `Mₙ* ⊕ K1` for
  a complete block, else `Mₙ*` copied a byte at a time onto zeros, `0x80`
  after it, and XORed with `K2`.

Only the pointers, `key_len`, `n` and `last_len` can affect timing: the
branches are on them and on counters, and the doubling is masked.
-/

namespace VG.Impl.CmacTripleDes.X86

open VG.X86

/-- `[esp + d]`: on entry, the argument `d / 4 - 1`. -/
def stk (d : Nat) : Src := .mem (at_ .esp d)

/-- Our caller's callee-saved registers, and where they are saved (`ebp`,
the base of the restore, last). -/
def saved : List (Reg × Nat) := [(.ebx, 84), (.esi, 88), (.edi, 92), (.ebp, 96)]

/-- Saves the registers to the scratch buffer at `eax`. -/
def save : List Instr := saved.map fun (r, d) => .store (at_ .eax d) r

/-- Restores the registers, with `ebp` (restored last) the scratch buffer. -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .ebp d))

/-! ## `vg_cmac_triple_des_init` -/

/-- The word at `[ecx + d]`, byte-reversed, to `[ebp + o]`. -/
def keyWord (d o : Nat) : List Instr := [.mov .eax (.mem (at_ .ecx d)), .bswap .eax, .store (at_ .ebp o) .eax]

/-- Saves the registers, and the three DES keys to `[ebp + 100]` (`K3` is
`K1` if `key_len` is 16), with `esi` pointing at them, `edi` at `out` and
`edx` counting them. -/
def initPre : Prog isa :=
  .seq (.block ([.mov .eax (stk 16)] ++ save ++ [.mov .ebp (.reg .eax), .mov .ecx (stk 4)] ++ keyWord 0 100 ++
      keyWord 4 104 ++ keyWord 8 108 ++ keyWord 12 112 ++ [.mov .eax (stk 8), .alu .cmp .eax (.imm 16)]))
    (.seq (.ite .e (.block [.mov .eax (.mem (at_ .ecx 0)), .mov .edx (.mem (at_ .ecx 4))])
        (.block [.mov .eax (.mem (at_ .ecx 16)), .mov .edx (.mem (at_ .ecx 20))]))
      (.block [.bswap .eax, .bswap .edx, .store (at_ .ebp 116) .eax, .store (at_ .ebp 120) .edx,
        .mov .esi (.reg .ebp), .alu .add .esi (.imm 100), .mov .edi (stk 12), .mov .edx (.imm 3)]))

/-- The round keys of the DES key at `[esi]` to `[edi]`, and on to the next. -/
def keysBody : List Instr :=
  roundKeys ++ [.alu .add .edi (.imm 128), .alu .add .esi (.imm 8), .alu .sub .edx (.imm 1)]

/-- The block in `eax:edx`, doubled (`VG.Spec.Cmac.dbl 8`), and stored at
`[edi + d]` (as bytes). -/
def dbl (d : Nat) : List Instr :=
  [.mov .ecx (.reg .eax), .shift .shr .ecx 31, .mov .ebx (.imm 0), .alu .sub .ebx (.reg .ecx),
   .alu .and .ebx (.imm 0x1b), .mov .ecx (.reg .edx), .shift .shr .ecx 31, .alu .add .eax (.reg .eax),
   .alu .or .eax (.reg .ecx), .alu .add .edx (.reg .edx), .alu .xor .edx (.reg .ebx),
   .mov .ecx (.reg .eax), .bswap .ecx, .store (at_ .edi d) .ecx, .mov .ecx (.reg .edx), .bswap .ecx,
   .store (at_ .edi (d + 4)) .ecx]

def init : Prog isa :=
  .seq initPre (.seq (.loop (.block keysBody) .ne)
    (.seq (.block [.mov .esi (stk 12), .mov .eax (.imm 0), .mov .edx (.imm 0)])
      (.seq block (.block ([.mov .edi (stk 12), .alu .add .edi (.imm 384)] ++ dbl 0 ++ dbl 8 ++ restore)))))

/-! ## `vg_cmac_triple_des_update` -/

/-- Saves the registers and the arguments; ZF is set if there are no blocks. -/
def updPre : List Instr :=
  [.mov .eax (stk 20)] ++ save ++
  [.mov .ebp (.reg .eax), .mov .esi (stk 4), .mov .eax (stk 12), .store (at_ .ebp 128) .eax,
   .mov .eax (stk 16), .store (at_ .ebp 132) .eax, .alu .cmp .eax (.imm 0)]

/-- `C ⊕ Mᵢ`, as a big-endian integer, into `eax:edx`. -/
def chainIn : List Instr :=
  [.mov .ecx (stk 8), .mov .edi (.mem (at_ .ebp 128)), .mov .eax (.mem (at_ .ecx 0)),
   .mov .edx (.mem (at_ .ecx 4)), .alu .xor .eax (.mem (at_ .edi 0)), .alu .xor .edx (.mem (at_ .edi 4)),
   .bswap .eax, .bswap .edx]

/-- `eax:edx` stored to the state, and on to the next block (ZF is set when
none are left). -/
def chainOut : List Instr :=
  [.mov .ecx (stk 8), .mov .edi (.mem (at_ .ebp 128)), .mov .ebx (.mem (at_ .ebp 132)), .bswap .eax,
   .bswap .edx, .store (at_ .ecx 0) .eax, .store (at_ .ecx 4) .edx, .alu .add .edi (.imm 8),
   .alu .sub .ebx (.imm 1), .store (at_ .ebp 128) .edi, .store (at_ .ebp 132) .ebx, .alu .cmp .ebx (.imm 0)]

def updBody : Prog isa := .seq (.block chainIn) (.seq block (.block chainOut))

def update : Prog isa :=
  .seq (.block updPre) (.seq (.ite .e (.block []) (.loop updBody .ne)) (.block restore))

/-! ## `vg_cmac_triple_des_finalize` -/

/-- `Mₙ = Mₙ* ⊕ K1` (`K1` at `esi + 384`) into `eax:edx`, for a complete last block. -/
def full : List Instr :=
  [.mov .ecx (stk 12), .mov .eax (.mem (at_ .ecx 0)), .mov .edx (.mem (at_ .ecx 4)),
   .alu .xor .eax (.mem (at_ .esi 384)), .alu .xor .edx (.mem (at_ .esi 388))]

/-- `[ebp + 136]` zeroed, with `edi` pointing at it, `ecx` at the last bytes
and `edx` counting them; ZF is set if `last_len` is 0. -/
def zero : List Instr :=
  [.mov .eax (.imm 0), .store (at_ .ebp 136) .eax, .store (at_ .ebp 140) .eax, .mov .edi (.reg .ebp),
   .alu .add .edi (.imm 136), .mov .ecx (stk 12), .mov .edx (stk 16), .alu .cmp .edx (.imm 0)]

/-- The `edx` (nonzero) bytes at `ecx` copied to `edi`, advancing both. -/
def copy : Prog isa :=
  .loop (.block [.movzx8 .eax (at_ .ecx 0), .store8 (at_ .edi 0) .al, .alu .add .ecx (.imm 1),
    .alu .add .edi (.imm 1), .alu .sub .edx (.imm 1)]) .ne

/-- `0x80` after the bytes (at `edi`), and the block XORed with `K2` (at
`esi + 392`) into `eax:edx`. -/
def padK2 : List Instr :=
  [.mov .eax (.imm 0x80), .store8 (at_ .edi 0) .al, .mov .eax (.mem (at_ .ebp 136)),
   .mov .edx (.mem (at_ .ebp 140)), .alu .xor .eax (.mem (at_ .esi 392)), .alu .xor .edx (.mem (at_ .esi 396))]

/-- `Mₙ = K2 ⊕ (Mₙ* ‖ 10ʲ)` into `eax:edx`, for a partial last block (`last_len < 8`). -/
def partialBlock : Prog isa :=
  .seq (.block zero) (.seq (.ite .e (.block []) copy) (.block padK2))

/-- Saves the registers and sets them up; `Mₙ` into `eax:edx`. -/
def finPre : Prog isa :=
  .seq (.block ([.mov .eax (stk 20)] ++ save ++
      [.mov .ebp (.reg .eax), .mov .esi (stk 4), .mov .eax (stk 16), .alu .cmp .eax (.imm 8)]))
    (.ite .e (.block full) partialBlock)

/-- `C ⊕ Mₙ` as a big-endian integer into `eax:edx`. -/
def finMid : List Instr :=
  [.mov .ecx (stk 8), .alu .xor .eax (.mem (at_ .ecx 0)), .alu .xor .edx (.mem (at_ .ecx 4)), .bswap .eax,
   .bswap .edx]

def finalize : Prog isa :=
  .seq finPre (.seq (.block finMid)
    (.seq block (.block ([.mov .ecx (stk 8), .bswap .eax, .bswap .edx, .store (at_ .ecx 0) .eax,
      .store (at_ .ecx 4) .edx] ++ restore))))

end VG.Impl.CmacTripleDes.X86
